#!/usr/bin/perl
# Where the eight-point face chain uses the bound `c ≤ aInf` (aInf = (2√2 - 1)/7, the cosine of the
# eight-point separation; false for 15 points, where c = cos d15 is about 0.59 > aInf = 0.26).
# Reads the source modules given as arguments (the import closure of the face chain), splits
# them into top-level declarations (as probe_mix.pl), and prints, for each declaration whose text
# mentions aInf: module, name, whether aInf is in a hypothesis of the statement (the name of that
# hypothesis) and the declarations of the list it passes the hypothesis to. A declaration that uses
# the hypothesis without passing it on (a tactic, a term that is not one of these declarations)
# is marked LEAF: that is where the value of aInf enters a proof.
# Run: perl aInf_uses.pl DIR/*.lean > aInf_uses.out   (no Lean process)
use strict; use warnings;
my (%text, %mod, %sig, @order);
my $decl = qr/^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|scoped|local)\s+)*(?:theorem|lemma|def|abbrev|structure|instance|class|inductive)\s+(\S+)/;
for my $f (@ARGV) {
  (my $m = $f) =~ s{.*/}{}; $m =~ s/\.lean$//;
  open my $fh, '<', $f or die; my @l = <$fh>; close $fh;
  my ($cur, $ns) = (undef, '');
  for my $s (@l) {
    if ($s =~ /^namespace (\S+)/) { $ns = $1 eq 'SquareAntiprismVerification' ? '' : "$1."; $cur = undef; next; }
    if ($s =~ /^end /) { $ns = '' ; $cur = undef; next; }
    if ($s =~ $decl) { $cur = $1; $cur = "$ns$cur" if $ns && $cur !~ /\./; push @order, $cur; $mod{$cur} = $m; $text{$cur} = ''; }
    elsif ($s =~ /^\S/ && $s !~ /^(--|\/-|\|)/) { $cur = undef; }
    $text{$cur} .= $s if defined $cur;
  }
}
my %hyp;
for my $n (@order) {
  my $t = $text{$n}; next unless $t =~ /aInf/;
  my ($st) = $t =~ /^(.*?):=/s; $st //= $t;
  my @h = $st =~ /\((\w+)\s*:\s*[^()]*≤\s*aInf\)/g;
  $hyp{$n} = [@h];
}
print "module\tdeclaration\thypotheses c ≤ aInf\tpassed to\tLEAF\n";
for my $n (@order) {
  next unless exists $hyp{$n};
  my $t = $text{$n}; my ($st, $body) = $t =~ /^(.*?):=(.*)$/s; $body //= '';
  my @h = @{$hyp{$n}}; my (%to, $leaf);
  for my $h (@h) {
    for my $line (split /\n/, $body) {
      next unless $line =~ /\b\Q$h\E\b/;
      my $passed = 0;
      for my $o (keys %hyp) { next if $o eq $n || !@{$hyp{$o}}; (my $short = $o) =~ s/.*\.//;
        if ($line =~ /(?<![\w.])(?:\Q$o\E|\Q$short\E)\b/) { $to{$o} = 1; $passed = 1; } }
      $leaf = 1 unless $passed;
    }
  }
  my $uses = ($body =~ /aInf/) ? 1 : 0; $leaf = 1 if !@h && $uses;
  printf "%s\t%s\t%s\t%s\t%s\n", $mod{$n}, $n, (join(',', @h) || '-'), (join(',', sort keys %to) || '-'), ($leaf ? "LEAF" : "-");
}
