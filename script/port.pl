#!/usr/bin/env perl

# SEE ALSO THE DOCUMENTATION IN port.sh
#
# This perl script is for porting files from the standard library to the HoTT library
#
# (1) create a file "port.txt", with a list of entries "foo:bar" (or "foo;bar"),
#     one per line
# (2) put this script and port.txt in the same directory, and make sure
#     the script is executable.
# (3) use "[path]/port.pl [path]/source [path]/target" to do the renaming.
#     On a Unix system, at least, you can use wildcards.
#
# -> You can write foo;bar to replace all occurrences,
#    even if they are a substring of a longer expression (useful for e.g. notation)
#
# Example: if you put rename.pl and port.txt in lean/library, then
# from that directory type
#
#   ./rename.pl data/nat/*.lean
#
# to do all the renamings in data/nat. Alternative, change to that directory,
# and type
#
# ../../rename.pl *.lean
#
# Notes:
#
# We assume identifiers have only letters, numbers, _, or "'" or ".".
#
# See http://perldoc.perl.org/perlfaq5.html, "How can I use Perl's i option from
# within a program?" for information on the method used to change a file in place.
#
# See also http://perldoc.perl.org/File/Find.html for information on how to write
# a subroutine that will traverse a directory tree.
#
use strict;
use warnings;
use Cwd 'abs_path';
use File::Basename;
use File::Spec::Functions;
use File::Copy;
use feature 'unicode_strings';

# the global list of renamings
my %renamings = ();
my %literalrenamings = ();
my %literalrenamings2 = ();

# get the list of renamings from the file
sub get_renamings {
    if (scalar(@ARGV)%2==1) {die "ERROR: odd number of arguments provided"}
    %literalrenamings2 = @ARGV;
    my $fullname = catfile(dirname(abs_path($0)), "port.txt");
    open (my $renaming_file, "<", $fullname) or die $!;
    while (<$renaming_file>) {
	if (/([\w'.]+)[:]([\w'.]+)\n/) {
	    $renamings{$1} = $2;
	} elsif (/(.+)[;](.+)\n/) {
	    $literalrenamings{$1} = $2;
	}
    }
    close $renaming_file or die $!;
}

# print them out - for debugging
sub show_renamings {
    foreach my $key (keys %renamings) {
	print $key, " => ", $renamings{$key}, "\n";
    }
    print "\n";
    foreach my $lkey (keys %literalrenamings2) {
	print $lkey, " -> ", $literalrenamings2{$lkey}, "\n";
    }
    foreach my $lkey (keys %literalrenamings) {
	print $lkey, " -> ", $literalrenamings{$lkey}, "\n";
    }
}

# rename all identifiers a file; original goes in file.orig
sub rename_in_file {
    my $filename = shift;
    local($^I, @ARGV) = ('.orig', $filename);
    while (<>) {
	foreach my $lkey (keys %literalrenamings2) {
	    # replace all instances of lkey
	    if (/$lkey/) {print STDOUT "renamed ", $lkey, "\n"; }
	    # else {print STDOUT "WARNING: didn't rename ", $lkey, " to ", $literalrenamings2{$lkey}, "\n";}
	    s/$lkey/$literalrenamings2{$lkey}/g
	}
	foreach my $key (keys %renamings) {
	    # replace instances of key, not preceeded by a letter, and not
	    # followed by a letter, number, or '
	    s/(?<![a-zA-z])$key(?![\w'])/$renamings{$key}/g;
	}
	foreach my $lkey (keys %literalrenamings) {
	    # replace all instances of lkey
	    s/$lkey/$literalrenamings{$lkey}/g;
	}
	print;
    }
}

my $oldfile = shift;
my $newfile = shift;
print "copying ", $oldfile, " to ",$newfile, ".\n";
copy($oldfile,$newfile) or die "Copy failed: $!";
get_renamings;
# show_renamings;
rename_in_file $newfile;
unlink $newfile.".orig";
