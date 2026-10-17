#!/usr/bin/env perl
# The generated parts of formalization.yaml: `status.main_results` (the theorems of config.json, with
# their files and their axioms as code/lean/check.out records them) and `alignment.statements`, the
# statement map, which maps each numbered statement of the paper to its Lean declarations with their
# modules and to its scripts with their recorded outputs. The map is read from the macros that
# paper/main.tex places right after each \label (they print nothing in the PDF):
#   \leanmap{A, B}        the Lean declarations of the statement, full names
#   \codemap{S > O, ...}  a script S of the repository with its recorded outputs O
#   \mapnote{text}        how the formal or computed result differs from the statement
# The numbers of the statements come from the aux file of a build of the paper. A statement with a
# \leanmap has `status: proved`, one with only a \codemap `status: other`, any other numbered
# statement `status: not-formalized`. Every declaration must be found in exactly one module of
# Tammes15/ outside Tammes15/Challenge, and every path of a \codemap must exist.
#
# Usage, from the root of the repository, after a build of paper/main.tex (its aux file AUX):
#   perl code/paper/statement_map.pl AUX formalization.yaml           writes the two blocks between their markers
#   perl code/paper/statement_map.pl --check AUX formalization.yaml   exit 1 if they are not up to date
use strict;
use warnings;
use File::Find;

my $check = @ARGV && $ARGV[0] eq '--check' ? shift @ARGV : '';
my ($aux, $yaml) = @ARGV;
die "usage: statement_map.pl [--check] AUX formalization.yaml\n" unless defined $yaml;

# ---- numbers of the labels ---------------------------------------------------------------
my %num;
open my $ah, '<', $aux or die "$aux: $!";
while (<$ah>) { $num{$1} = $2 if /^\\newlabel\{([^}]+)\}\{\{([^}]*)\}/; }
close $ah;

# ---- the argument of a macro, with balanced braces ---------------------------------------
sub arg {
  my ($s, $i) = @_;    # $i at the opening brace
  my $d = 0;
  for my $j ($i .. length($s) - 1) {
    my $c = substr($s, $j, 1);
    $d++ if $c eq '{';
    if ($c eq '}' && --$d == 0) { return (substr($s, $i + 1, $j - $i - 1), $j + 1); }
  }
  die "unbalanced braces at offset $i\n";
}

my %kind = (theorem => 'Theorem', lemma => 'Lemma', proposition => 'Proposition',
  corollary => 'Corollary', definition => 'Definition', remark => 'Remark', step => 'Computation',
  question => 'Question', mainproposition => 'Proposition', maintheorem => 'Theorem', search => 'Search', section => 'Section', subsection => 'Section');
my $numbered = qr/theorem|lemma|proposition|corollary|definition|remark|step|question|mainproposition|maintheorem|search/;

sub rows {
  my ($file) = @_;
  open my $fh, '<', $file or die "$file: $!";
  my $src = do { local $/; <$fh> };
  close $fh;
  $src =~ s/(?<!\\)%[^\n]*//g;    # comments
  my (@rows, %seen);
  while ($src =~ /(\\begin\{($numbered)\}(?:\[[^\]]*\])?|\\(section|subsection)\*?\{)/g) {
    my ($env, $sec, $p) = ($2, $3, pos($src));
    if ($sec) { (undef, $p) = arg($src, $p - 1); }
    next unless substr($src, $p) =~ /^\s*\\label\{([^}]+)\}/;
    my $label = $1;
    $p += $+[0];
    my %m;
    while (substr($src, $p) =~ /^\s*\\(leanmap|codemap|mapnote)\{/) {
      my $name = $1;
      ($m{$name}, $p) = arg($src, $p + $+[0] - 1);
    }
    next if $sec && !%m;          # sections are listed only when they carry a map
    next if $seen{$label}++;
    my $n = $num{$label} // die "$label: no number in $aux\n";
    push @rows, [($kind{$env // $sec}) . " $n", $label, \%m];
  }
  return @rows;
}

sub text {    # a macro argument as plain text: \ref{..} as its number, $x$ kept as TeX
  my ($t) = @_;
  $t =~ s/\\ref\{([^}]+)\}/$num{$1} \/\/ die "$1: no number in $aux\n"/ge;
  $t =~ s/\\texttt\{([^}]*)\}/`$1`/g;
  $t =~ s/~/ /g;
  $t =~ s/\s+/ /g;
  $t =~ s/^ | $//g;
  return $t;
}

sub yq {    # a YAML double-quoted string
  my ($t) = @_;
  $t =~ s/\\/\\\\/g;
  $t =~ s/"/\\"/g;
  return "\"$t\"";
}

# ---- the module of each declaration ------------------------------------------------------
# A declaration `A.B.c` is in the file that declares `c`, `B.c` or `A.B.c` and whose namespaces cover
# the rest of the name.
my %files;
find({ no_chdir => 1, wanted => sub {
  return unless /\.lean$/ && !m{^Tammes15/Challenge[/.]};
  open my $fh, '<', $_ or die "$_: $!";
  $files{$_} = do { local $/; <$fh> };
  close $fh;
} }, 'Tammes15');

my %module;
sub module_of {
  my ($full) = @_;
  return $module{$full} if exists $module{$full};
  my @parts = split /\./, $full;
  my @hits;
  for my $f (sort keys %files) {
    my $src = $files{$f};
    my %ns = map { $_ => 1 } map { split /\./ } ($src =~ /^\s*namespace\s+(\S+)/mg);
    for my $k (0 .. $#parts) {
      my $decl = join '.', @parts[$k .. $#parts];
      next unless $src =~ /^(?:[@\[][^\n]*\n)?\s*(?:private\s+|protected\s+|noncomputable\s+|nonrec\s+)*(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque)\s+(?:_root_\.)?\Q$decl\E(?=[\s:({\[])/m;
      next if grep { !$ns{$_} } @parts[0 .. $k - 1];
      push @hits, $f;
      last;
    }
  }
  die "$full: declared in " . (@hits ? join(', ', @hits) : 'no file') . "\n" unless @hits == 1;
  (my $m = $hits[0]) =~ s/\.lean$//;
  $m =~ s{/}{.}g;
  return $module{$full} = [$m, $hits[0]];
}

sub names { grep { length } map { s/^\s+|\s+$//gr } split /,/, $_[0] // '' }

# ---- alignment.statements ----------------------------------------------------------------
sub statements {
  my @out;
  for my $r (@_) {
    my ($what, $label, $m) = @$r;
    my @lean = names($m->{leanmap});
    my (@scripts, @outputs);
    for my $e (names($m->{codemap})) {
      my ($s, $o) = split /\s*>\s*/, $e, 2;
      my @o = split ' ', $o // '';
      -e $_ or die "$label: $_ does not exist\n" for ($s, @o);
      push @scripts, $s;
      push @outputs, @o;
    }
    my $status = @lean ? 'proved' : @scripts ? 'other' : 'not-formalized';
    push @out, "    - source: " . yq("$what of the paper ($label)"), "      status: $status";
    if (@lean) {
      push @out, "      lean:", map { "        - " . yq($_) } @lean;
      my %seen;
      push @out, "      module:", map { "        - " . yq($_) } grep { !$seen{$_}++ } map { module_of($_)->[0] } @lean;
    }
    if (@scripts) {
      push @out, "      script:", map { "        - " . yq($_) } @scripts;
      push @out, "      output:", map { "        - " . yq($_) } @outputs;
    }
    my $note = text($m->{mapnote} // '');
    $note =~ s/^not formalized(?:; |$)// unless @lean;
    push @out, "      note: " . yq($note) if length $note;
  }
  return @out;
}

# ---- status.main_results -----------------------------------------------------------------
sub main_results {
  open my $ch, '<', 'config.json' or die "config.json: $!";
  my $cfg = do { local $/; <$ch> };
  close $ch;
  my ($list) = $cfg =~ /"theorem_names"\s*:\s*\[([^\]]*)\]/ or die "config.json: no theorem_names\n";
  my @thms = $list =~ /"([^"]+)"/g;
  open my $rh, '<', 'code/lean/check.out' or die "code/lean/check.out: $!";
  my %ax;
  while (<$rh>) { $ax{$1} = $2 if /^'([^']+)' depends on axioms: \[([^\]]*)\]/; }
  close $rh;
  my @out;
  for my $t (@thms) {
    my $a = $ax{$t} // die "$t: no axioms line in code/lean/check.out\n";
    push @out, "    - declaration: " . yq($t), "      file: " . yq(module_of($t)->[1]), "      sorry_count: 0",
      "      axioms: [" . join(', ', map { yq($_) } split /,\s*/, $a) . "]", "      comparator_config: \"config.json\"",
      "      literature_dependencies: []";
  }
  return @out;
}

my @main = rows('paper/main.tex');
my %blocks = ('main-results' => [main_results()], 'statement-map' => [statements(@main)]);

open my $yh, '<', $yaml or die "$yaml: $!";
my @lines = map { s/\n$//r } <$yh>;
close $yh;
my $ok = 1;
for my $name (sort keys %blocks) {
  my $BEGIN = "    # $name begin: generated by code/paper/statement_map.pl, do not edit";
  my $END   = "    # $name end";
  my ($b) = grep { $lines[$_] eq $BEGIN } 0 .. $#lines;
  my ($e) = grep { $lines[$_] eq $END } 0 .. $#lines;
  die "$yaml: the markers of $name are missing\n" unless defined $b && defined $e && $b < $e;
  my @gen = ($BEGIN, @{ $blocks{$name} }, $END);
  $ok &&= join("\n", @lines[$b .. $e]) eq join("\n", @gen);
  splice @lines, $b, $e - $b + 1, @gen;
}
my $counts = scalar(@main) . " statements, " . scalar(grep { /^    - declaration:/ } @{ $blocks{'main-results'} }) . " main results";
if ($check) {
  print $ok ? "statement map: up to date ($counts)\n" : "statement map: NOT up to date ($counts)\n";
  exit($ok ? 0 : 1);
}
open my $wh, '>', $yaml or die "$yaml: $!";
print $wh map { "$_\n" } @lines;
close $wh;
print "statement map: $counts written to $yaml\n";
