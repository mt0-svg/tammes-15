#!/usr/bin/perl
# The listed hand changes of the vendored eight-point code (code/vendor/handfix.tsv), on
# top of the renaming of code/vendor/vendor.sh and before the `Fin 8` generalization.
#   handfix.pl apply FILE MODULE SOURCE FIXES   FILE (a renamed vendored file) with the rows of
#       FIXES for MODULE applied: the line of FILE that comes from line LINE of SOURCE (the
#       upstream file) must equal OLD, and becomes the marker line
#       `-- tammes-15 port change: REASON.` (indented as OLD) followed by NEW
#   handfix.pl undo FILE MODULE FIXES           the inverse: each marker line of a row of FIXES
#       followed by its NEW lines becomes OLD again (for code/vendor/vendor_check.sh)
# FIXES is tab separated: module, source line, old, new, reason; in `new` the two characters \n
# separate lines. Lines are compared as written in the upstream file (`Fin 8`, not `Fin nPts`),
# so `apply` runs before the generalization and `undo` after it is undone.
use strict; use warnings;
my $mode = shift @ARGV;
my $mark = '-- tammes-15 port change: ';
sub rows { my ($f, $mod) = @_; my @r;
  open my $h, '<', $f or die "$f: $!";
  while (<$h>) { chomp; next if /^#/ || !/\S/; my @c = split /\t/, $_, -1;
    die "$f: row with " . scalar(@c) . " columns: $_\n" unless @c == 5;
    next unless $c[0] eq $mod; $c[3] =~ s/\\n/\n/g; push @r, [@c]; }
  close $h; @r; }
sub slurp { my $f = shift; open my $h, '<', $f or die "$f: $!"; my @l = <$h>; close $h; chomp @l; @l; }
sub ind { $_[0] =~ /^(\s*)/; $1 }
if ($mode eq 'apply') {
  my ($file, $mod, $src, $fixes) = @ARGV;
  my @l = slurp($file); my @s = slurp($src);
  # map source lines to lines of FILE: skip the three credit lines, the port-change markers of
  # vendor.sh and the option line after each; the other lines correspond one to one
  my @at; my $j = 0; my $skip = 0;
  for my $i (3 .. $#l) {
    if ($skip) { $skip = 0; next; }
    if ($l[$i] =~ /^\s*\Q$mark\E/) { $skip = 1; next; }
    $at[$j++] = $i; }
  die "$file: $j lines against " . scalar(@s) . " in $src\n" unless $j == @s;
  my @r = sort { $b->[1] <=> $a->[1] } rows($fixes, $mod);
  for my $r (@r) { my ($m, $n, $old, $new, $why) = @$r; my $i = $at[$n - 1];
    die "$mod:$n: source line is not OLD\n" unless $s[$n - 1] eq $old;
    die "$mod:$n: vendored line is not OLD\n" unless $l[$i] eq $old;
    splice @l, $i, 1, ind($old) . $mark . $why . '.', split(/\n/, $new, -1); }
  print "$_\n" for @l;
} elsif ($mode eq 'undo') {
  my ($file, $mod, $fixes) = @ARGV;
  my @l = slurp($file);
  # rows with the same text (the same line in two declarations) are undone together: as many
  # matches as rows
  my %cnt; $cnt{join "\t", @{$_}[2 .. 4]}++ for rows($fixes, $mod);
  for my $key (sort keys %cnt) { my ($old, $new, $why) = split /\t/, $key, -1;
    my @nl = split /\n/, $new, -1; my $head = ind($old) . $mark . $why . '.'; my @hit;
    for my $i (0 .. $#l - @nl) {
      next unless $l[$i] eq $head;
      next if grep { $l[$i + 1 + $_] ne $nl[$_] } 0 .. $#nl;
      push @hit, $i; }
    die "$mod: " . scalar(@hit) . " markers for $cnt{$key} rows of: $old\n" unless @hit == $cnt{$key};
    splice @l, $_, 1 + @nl, $old for reverse @hit; }
  print "$_\n" for @l;
} else { die "usage: handfix.pl apply FILE MODULE SOURCE FIXES | undo FILE MODULE FIXES\n"; }
