#!/usr/bin/env perl

# This perl script is for doing batch renamings of identifiers. To use it:
#
# (1) create a file "renamings.txt", with a list of entries "foo:bar",
#     one per line
# (2) put this script and renamings.txt in the same directory, and make sure
#     the script is executable.
# (3) use "[path]/rename.pl [path]/file" to do the renaming.
#     On a Unix system, at least, you can use wildcards.
#
# Example: if you put rename.pl and renamings.txt in lean/library, then 
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

# the global list of renamings
my %renamings = ();

# get the list of renamings from the file
sub get_renamings {
    my $fullname = catfile(dirname(abs_path($0)), "renamings.txt");
    open (my $renaming_file, "<", $fullname) or die $!;
    while (<$renaming_file>) {
	if (/([\w'.]+)[:]([\w'.]+)\n/) {
	    $renamings{$1} = $2;
	}
    }
    close $renaming_file or die $!;
}

# print them out - for debugging
sub show_renamings {
    foreach my $key (keys %renamings) {
	print $key, " => ", $renamings{$key}, "\n";
    }
}

# rename all identifiers a file; original goes in file.orig
sub rename_in_file {
    my $filename = shift;
    local($^I, @ARGV) = ('.orig', $filename);
    while (<>) {
	foreach my $key (keys %renamings) {
	    # replace instances of key, not preceeded by a letter, and not
	    # followed by a letter, number, ', or .
	    s/(?<![a-zA-z])$key(?![w'.])/$renamings{$key}/g;
	}
	print;
    }
}

get_renamings;
# show_renamings;
foreach (@ARGV) {
    rename_in_file $_;
}

