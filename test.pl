#!/usr/bin/perl
#-------------------------------------------------------------------------------
# Test Nasm:X86
# Philip R Brenan at gmail dot com, Appa Apps Ltd Inc, 2021-2022
#-------------------------------------------------------------------------------
use warnings FATAL => qw(all);
use strict;
use Nasm::X86 qw(:all);
use utf8;
use Test::More;

Mov rax, 1;
PrintOutRegisterInHex rax;
ok Assemble eq => <<END;
   rax: .... .... .... ...1
END

done_testing;
