#!/usr/bin/perl
# Declaration chunks of a Lean file of the eight-point code, and its Fin n variant.
#   probe_mix.pl chunks FILE        one line per top-level command: id, first line, last line,
#                                   kind, name, number of `Fin 8` occurrences (tab separated)
#   probe_mix.pl next FILE MODULE LOG REVERTED
#                                   the chunks to put back after a failed build: those with an
#                                   error; if all of them are already back, the chunks of FILE whose
#                                   name occurs in the error messages of the chunks put back (a
#                                   declaration they use at Fin 8). One line per chunk: id, reason
#                                   (errors are read for the file PROBE_PATH/MODULE.lean, default
#                                   Lean_Code/)
#   probe_mix.pl keys FILE          one line per chunk: id, kind, name, occurrence of (kind, name)
#                                   in FILE (1, 2, ...): the key of a chunk that line numbers, the
#                                   credit header and renamed lines do not change
#   probe_mix.pl apply FILE MODULE KEEP
#                                   FILE with `Fin 8` replaced by `Fin nPts` except in the chunks
#                                   whose key (MODULE, kind, name, occurrence) is a row of the file
#                                   KEEP (tab separated; further columns are the reason): the
#                                   generalization of the vendored code (code/vendor/vendor.sh)
#   probe_mix.pl mix FILE REVERTED  FILE with `Fin 8` replaced by `Fin nPts` (auto-bound implicit,
#                                   Lean's default options), except in the chunks whose ids are
#                                   listed in the file REVERTED (one id per line), kept as written
# A chunk starts at a column-0 line that begins a command (a docstring or attribute line belongs
# to the declaration after it) and ends before the next one; block comments are skipped. The
# replacement never changes the number of lines, so error lines of the variant are lines of FILE.
use strict; use warnings;
my ($mode, $file, $rev) = @ARGV;
open my $fh, '<', $file or die "$file: $!"; my @l = <$fh>; close $fh;
my @start; my @kind; my @name;
my $incomment = 0; my $prefix = 0;   # inside /- -/ ; a docstring or attribute awaits its decl
my $decl = qr/^(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local)\s+)*(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom|example)\b\s*([^\s:({\[]*)/;
for my $i (0 .. $#l) {
  my $s = $l[$i];
  if ($incomment) { $incomment = 0 if $s =~ /-\/\s*$/ || $s =~ /-\//; next; }
  if ($s =~ /^\/--/) {                       # docstring: starts the chunk of the next decl
    push @start, $i; push @kind, 'decl'; push @name, '?'; $prefix = 1;
    $incomment = 1 unless $s =~ /-\/\s*$/; next; }
  if ($s =~ /^\/-/) {                        # other block comment: a chunk of its own
    push @start, $i; push @kind, 'comment'; push @name, '-';
    $incomment = 1 unless $s =~ /-\/\s*$/; $prefix = 0; next; }
  next if $s =~ /^\s/ || $s =~ /^$/ || $s =~ /^--/ || $s =~ /^\|/;
  if ($s =~ /^@\[/ && $s !~ $decl) {         # attribute on its own line
    if (!$prefix) { push @start, $i; push @kind, 'decl'; push @name, '?'; $prefix = 1; } next; }
  (my $t = $s) =~ s/^@\[[^\]]*\]\s*//;
  if ($t =~ $decl) {
    if ($prefix) { $kind[-1] = $1; $name[-1] = $2; $prefix = 0; }
    else { push @start, $i; push @kind, $1; push @name, $2; }
    next; }
  if ($prefix) { $prefix = 0; }              # a docstring before a non-decl command
  my ($cmd) = $s =~ /^(\S+)/;
  push @start, $i; push @kind, $cmd; push @name, '-';
}
my @end = map { ($_ < $#start) ? $start[$_ + 1] - 1 : $#l } 0 .. $#start;
my %seen; my @occ = map { ++$seen{"$kind[$_]\t$name[$_]"} } 0 .. $#start;
if ($mode eq 'chunks') {
  for my $c (0 .. $#start) {
    my $n = 0; $n += () = $l[$_] =~ /\bFin 8\b/g for $start[$c] .. $end[$c];
    printf "%d\t%d\t%d\t%s\t%s\t%d\n", $c, $start[$c] + 1, $end[$c] + 1, $kind[$c], $name[$c], $n;
  }
} elsif ($mode eq 'keys') {
  printf "%d\t%s\t%s\t%d\n", $_, $kind[$_], $name[$_], $occ[$_] for 0 .. $#start;
} elsif ($mode eq 'apply') {
  my ($mod, $kf) = @ARGV[2, 3]; my %k;
  open my $kh, '<', $kf or die "$kf: $!";
  while (<$kh>) { chomp; my @f = split /\t/; next unless @f >= 4 && $f[0] eq $mod; $k{"$f[1]\t$f[2]\t$f[3]"} = 1 }
  my @keep = (0) x @l; my $found = 0;
  for my $c (0 .. $#start) { next unless $k{"$kind[$c]\t$name[$c]\t$occ[$c]"}; $found++; $keep[$_] = 1 for $start[$c] .. $end[$c]; }
  die "apply: $mod: " . (scalar(keys %k) - $found) . " keep rows match no chunk\n" if $found != keys %k;
  for my $i (0 .. $#l) { my $s = $l[$i]; $s =~ s/\bFin 8\b/Fin nPts/g unless $keep[$i]; print $s; }
} elsif ($mode eq 'mix') {
  my %r; if (defined $rev && -e $rev) { open my $rf, '<', $rev or die; while (<$rf>) { chomp; $r{$_} = 1 if /\S/ } }
  my @keep = (0) x @l;
  for my $c (keys %r) { $keep[$_] = 1 for $start[$c] .. $end[$c]; }
  for my $i (0 .. $#l) { my $s = $l[$i]; $s =~ s/\bFin 8\b/Fin nPts/g unless $keep[$i]; print $s; }
} elsif ($mode eq q{next}) {
  my ($mod, $log, $revf) = @ARGV[2 .. 4];
  my %r; if (-e $revf) { open my $rf, q{<}, $revf or die; while (<$rf>) { chomp; $r{$_} = 1 if /\S/ } }
  open my $lf, q{<}, $log or die "$log: $!"; my @msg; my $cur;
  while (my $s = <$lf>) {
    if ($s =~ /^(error|warning|info|trace|\S+ \[\d+\/\d+\]|Some required|- )/) {
      $cur = undef;
      my $pp = $ENV{PROBE_PATH} // q{Lean_Code/};
      if ($s =~ /^error: \Q$pp$mod\E\.lean:(\d+):\d+: ?(.*)/) { $cur = [$1, $2, $s]; push @msg, $cur; }
      next; }
    $cur->[2] .= $s if $cur;
  }
  my $chunk = sub { my $L = shift; for my $c (0 .. $#start) { return $c if $start[$c] + 1 <= $L && $L <= $end[$c] + 1 } -1 };
  my %new;
  for my $m (@msg) { my $c = $chunk->($m->[0]); next if $c < 0 || $r{$c} || $new{$c};
    my @x = grep { /\S/ } split /\n/, $m->[2]; $x[0] = $m->[1];
    (my $e = join(q{ | }, @x[0 .. ($#x < 2 ? $#x : 2)])) =~ s/\s+/ /g; $new{$c} = substr($e, 0, 240); }
  if (!%new) {
    for my $m (@msg) { my $c = $chunk->($m->[0]); next if $c < 0 || !$r{$c};
      for my $d (0 .. $#start) { next if $r{$d} || $new{$d} || $name[$d] =~ /^[-?]$/;
        my $nm = quotemeta $name[$d];
        $new{$d} = "used at Fin 8 by $name[$c]" if $m->[2] =~ /(?<![\w.'])$nm(?![\w.'])/; } }
  }
  print "$_\t$new{$_}\n" for sort { $a <=> $b } keys %new;
} else { die "usage: probe_mix.pl chunks|keys|apply|next|mix FILE ...\n"; }
