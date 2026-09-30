#!/usr/bin/perl
# The samples of the replays (replay_mpfr.sh, mpfr_sample_check.sh, make_sample.sh), chosen by hash so
# that they depend on no tool version.
# Usage: code/impl1/sample_pick.pl SEED JOB M < INDICES
# Reads graph indices (decimal, one per line, no duplicates) and prints, in increasing order, the M of
# them whose string "SEED:JOB:INDEX" has the least SHA-256 digest in lowercase hex, compared as strings
# byte by byte (for example "777:full_k0_0:12345"; ties, which do not occur, go to the smaller index).
use strict;
use warnings;
use Digest::SHA qw(sha256_hex);
my ($seed, $job, $m) = @ARGV;
chomp(my @ids = <STDIN>);
my @keyed = sort { $a->[0] cmp $b->[0] or $a->[1] <=> $b->[1] } map { [sha256_hex("$seed:$job:$_"), $_] } @ids;
die "sample_pick.pl: $job has " . @ids . " indices, fewer than $m\n" if $m > @ids;
print "$_\n" for sort { $a <=> $b } map { $_->[1] } @keyed[0 .. $m - 1];
