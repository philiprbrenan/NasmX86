use Nasm::X86 qw(:all);
use Test::More;

Mov rax, 1;
PrintOutRegisterInHex rax;

ok Assemble eq => <<END;
   rax: .... .... .... ...1
END

done_testing;
