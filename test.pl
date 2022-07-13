#!/usr/bin/perl -I/home/phil/perl/cpan/NasmX86/lib
#-------------------------------------------------------------------------------
# Test Nasm:X86
# Philip R Brenan at gmail dot com, Appa Apps Ltd Inc, 2021-2022
#-------------------------------------------------------------------------------
use warnings FATAL => qw(all);
use strict;
BEGIN{say STDERR "TESTTTT1111"}
use Nasm::X86 qw(:all);
BEGIN{say STDERR "TESTTTT2222"}
use utf8;
use Test::More;

say STDERR "TESTTTT3333";

Mov rax, 1;
PrintOutRegisterInHex rax;
ok Assemble eq => <<END;
   rax: .... .... .... ...1
END

done_testing;
