#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/ -I. -I/home/phil/perl/cpan/AsmC/lib/
#91909
#-------------------------------------------------------------------------------
# Generate X86 assembler code using Perl as a macro pre-processor.
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2021
#-------------------------------------------------------------------------------
# podDocumentation (\A.{80})\s+(#.*\Z) \1\2
# rdi and rsi are free so they cannot be relied on across calls
# tree::print - speed up decision as to whether we are on a tree or not
# 0x401000 from sde-mix-out addresses to get offsets in z.txt
# Make hash accept parameters at: #THash
# if (0) in tests from subroutine conversion
# Document that V > 0 is required to create a boolean test
# Make sure that we are using bts and bzhi as much as possible in mask situations
# Update PrintOut to use V2 every where then rename
# Replace calls to Tree::position with Tree::down
# Make Pop return a tree when it is on a sub tree
package Nasm::X86;
our $VERSION = "20211204";
use warnings FATAL => qw(all);
use strict;
use Carp qw(confess cluck);
use Data::Dump qw(dump);
use Data::Table::Text qw(:all);
use Time::HiRes qw(time);
use feature qw(say current_sub);
use utf8;

makeDieConfess;

my %rodata;                                                                     # Read only data already written
my %rodatas;                                                                    # Read only string already written
my %subroutines;                                                                # Subroutines generated
my @rodata;                                                                     # Read only data
my @data;                                                                       # Data
my @bss;                                                                        # Block started by symbol
my @text;                                                                       # Code
my @extern;                                                                     # External symbols imports for linking with C libraries
my @link;                                                                       # Specify libraries which to link against in the final assembly stage
my $interpreter = q(-I /usr/lib64/ld-linux-x86-64.so.2);                        # The ld command needs an interpreter if we are linking with C.
my $develop     = -e q(/home/phil/);                                            # Developing
my $sdeMixOut   = q(sde-mix-out.txt);                                           # Emulator output file

our $stdin      = 0;                                                            # File descriptor for standard input
our $stdout     = 1;                                                            # File descriptor for standard output
our $stderr     = 2;                                                            # File descriptor for standard error

our $TraceMode  = 0;                                                            # 1: writes trace data into rax after every instruction to show the call stack by line number in this file for the instruction being executed.  This information is then visible in the sde trace from whence it is easily extracted to give a trace back for instructions executed in this mode.  This mode assumes that you will not be using the mm0 register (most people are not)and that you have any IDE like Geany that can interpret a Perl error line number and position on that line in this file.

my %Registers;                                                                  # The names of all the registers
my %RegisterContaining;                                                         # The largest register containing a register
my @GeneralPurposeRegisters = qw(rax rbx rcx rdx rsi rdi), map {"r$_"} 8..15;   # General purpose registers
my $bitsInByte;                                                                 # The number of bits in a byte
my @declarations;                                                               # Register and instruction declarations

BEGIN{
  $bitsInByte  = 8;                                                             # The number of bits in a byte
  my %r = (    map {$_=>[ 8,  '8'  ]}  qw(al bl cl dl r8b r9b r10b r11b r12b r13b r14b r15b r8l r9l r10l r11l r12l r13l r14l r15l sil dil spl bpl ah bh ch dh));
     %r = (%r, map {$_=>[16,  's'  ]}  qw(cs ds es fs gs ss));
     %r = (%r, map {$_=>[16,  '16' ]}  qw(ax bx cx dx r8w r9w r10w r11w r12w r13w r14w r15w si di sp bp));
     %r = (%r, map {$_=>[32,  '32a']}  qw(eax  ebx ecx edx esi edi esp ebp));
     %r = (%r, map {$_=>[32,  '32b']}  qw(r8d r9d r10d r11d r12d r13d r14d r15d));
     %r = (%r, map {$_=>[80,  'f'  ]}  qw(st0 st1 st2 st3 st4 st5 st6 st7));
     %r = (%r, map {$_=>[64,  '64' ]}  qw(rax rbx rcx rdx r8 r9 r10 r11 r12 r13 r14 r15 rsi rdi rsp rbp rip rflags));
     %r = (%r, map {$_=>[64,  '64m']}  qw(mm0 mm1 mm2 mm3 mm4 mm5 mm6 mm7));
     %r = (%r, map {$_=>[128, '128']}  qw(xmm0 xmm1 xmm2 xmm3 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 xmm16 xmm17 xmm18 xmm19 xmm20 xmm21 xmm22 xmm23 xmm24 xmm25 xmm26 xmm27 xmm28 xmm29 xmm30 xmm31));
     %r = (%r, map {$_=>[256, '256']}  qw(ymm0 ymm1 ymm2 ymm3 ymm4 ymm5 ymm6 ymm7 ymm8 ymm9 ymm10 ymm11 ymm12 ymm13 ymm14 ymm15 ymm16 ymm17 ymm18 ymm19 ymm20 ymm21 ymm22 ymm23 ymm24 ymm25 ymm26 ymm27 ymm28 ymm29 ymm30 ymm31));
     %r = (%r, map {$_=>[512, '512']}  qw(zmm0 zmm1 zmm2 zmm3 zmm4 zmm5 zmm6 zmm7 zmm8 zmm9 zmm10 zmm11 zmm12 zmm13 zmm14 zmm15 zmm16 zmm17 zmm18 zmm19 zmm20 zmm21 zmm22 zmm23 zmm24 zmm25 zmm26 zmm27 zmm28 zmm29 zmm30 zmm31));
     %r = (%r, map {$_=>[64,  'm'  ]}  qw(k0 k1 k2 k3 k4 k5 k6 k7));

  %Registers = %r;                                                              # Register names

  my sub registerContaining($@)
   {my ($r, @r) = @_;                                                           # Register, contents
    $RegisterContaining{$r} = $r;                                               # A register contains itself
    $RegisterContaining{$_} = $r for @r;                                        # Registers contained by a register
   }

  registerContaining("k$_")                                            for 0..7;
  registerContaining("zmm$_",   "ymm$_", "xmm$_")                      for 0..31;
  registerContaining("r${_}x", "e${_}x", "${_}x",  "${_}l",  "${_}h")  for qw(a b c d);
  registerContaining("r${_}",  "r${_}l", "r${_}w", "r${_}b", "r${_}d") for 8..15;
  registerContaining("r${_}p", "e${_}p", "${_}p",  "${_}pl")           for qw(s b);
  registerContaining("r${_}i", "e${_}i", "${_}i", "${_}il")            for qw(s d);
  my @i0 = qw(cpuid lahf leave popfq pushfq rdtsc ret syscall);                 # Zero operand instructions

  my @i1 = split /\s+/, <<END;                                                  # Single operand instructions
align bswap call dec div idiv  inc jmp ja jae jb jbe jc jcxz je jecxz jg jge jl jle
jna jnae jnb jnbe jnc jne jng jnge jnl jnle jno jnp jns jnz jo jp jpe jpo jrcxz
js jz loop neg not seta setae setb setbe setc sete setg setge setl setle setna setnae
setnb setnbe setnc setne setng setnge setnl setno setnp setns setnz seto setp
setpe setpo sets setz pop push
END

  my @i2 =  split /\s+/, <<END;                                                 # Double operand instructions
add and bt btc btr bts
cmova cmovae cmovb cmovbe cmovc cmove cmovg cmovge cmovl cmovle
cmovna cmovnae cmovnb cmp
enter
imul
kmov knot kortest ktest lea lzcnt mov movd movq movw  movdqa
or popcnt sal sar shl shr sub test tzcnt
vcvtudq2pd vcvtuqq2pd vcvtudq2ps vmovdqu vmovdqu32 vmovdqu64 vmovdqu8
vpcompressd vpcompressq vpexpandd vpexpandq xchg xor
vmovd vmovq
mulpd
pslldq psrldq
vpmovb2m vpmovw2m Vpmovd2m vpmovq2m

vsqrtpd
vmovdqa32 vmovdqa64
END
# print STDERR join ' ', sort @i2; exit;

  my @i2qdwb =  split /\s+/, <<END;                                             # Double operand instructions which have qdwb versions
vpmovm2
vpbroadcast
END

  my @i3 =  split /\s+/, <<END;                                                 # Triple operand instructions
andn
bzhi
imul3
kadd kand kandn kor kshiftl kshiftr kunpck kxnor kxor

vdpps
vprolq
vgetmantps
vaddd
vmulpd vaddpd
END

  my @i3qdwb =  split /\s+/, <<END;                                             # Triple operand instructions which have qdwb versions
pinsr pextr valign vpand vpandn vpcmpeq vpor vpxor vptest vporvpcmpeq vpinsr vpextr vpadd vpsub vpmull
END

  my @i4 =  split /\s+/, <<END;                                                 # Quadruple operand instructions
END

  my @i4qdwb =  split /\s+/, <<END;                                             # Quadruple operand instructions which have qdwb versions
vpcmpu
END

  if (1)                                                                        # Add variants to mask instructions
   {my @k2  = grep {m/\Ak/} @i2; @i2  = grep {!m/\Ak/} @i2;
    my @k3  = grep {m/\Ak/} @i3; @i3  = grep {!m/\Ak/} @i3;
    for my $s(qw(b w d q))
     {push @i2, $_.$s for grep {m/\Ak/} @k2;
      push @i3, $_.$s for grep {m/\Ak/} @k3;
     }
   }

  if (1)                                                                        # Add qdwb versions of instructions
   {for my $o(@i2qdwb)
     {push @i2, $o.$_ for qw(b w d q);
     }
    for my $o(@i3qdwb)
     {push @i3, $o.$_ for qw(b w d q);
     }
    for my $o(@i4qdwb)
     {push @i4, $o.$_ for qw(b w d q);
     }
   }

  for my $r(sort keys %r)                                                       # Create register definitions
   {if (1)
     {my $s = "sub $r\{q($r)\}";
      push @declarations, $r;
      eval $s;
      confess "$s$@ "if $@;
     }
    if (1)
     {my $b = $r{$r}[0] / $bitsInByte;
      my $s = "sub ${r}Size\{$b}";
      eval $s;
      confess "$s$@ "if $@;
     }
   }

  my %v = map {$$_[1]=>1} values %r;
  for my $v(sort keys %v)                                                       # Types of register
   {my @r = grep {$r{$_}[1] eq $v} sort keys %r;
    my $s = "sub registers_$v\{".dump(\@r)."}";
    eval $s;
    confess "$s$@" if $@;
   }

  if (1)                                                                        # Instructions that take zero operands
   {my $s = '';
    for my $i(@i0)
      {my $I = ucfirst $i;
       push @declarations, $I;
       $s .= <<END;
       sub $I()
        {\@_ == 0 or confess "No arguments allowed";
         push \@text, qq($i\\n);
        }
END
     }
    eval $s;
    confess "$s$@" if $@;
   }

  if (1)                                                                        # Instructions that take one operand
   {my $s = '';
    for my $i(@i1)
      {my $I = ucfirst $i;
       push @declarations, $I;
       $s .= <<END;
       sub $I
        {my (\$target) = \@_;
         \@_ == 1 or confess "One argument required, not ".scalar(\@_);
         push \@text, qq($i \$target\\n);
        }
END
     }
    eval $s;
    confess "$s$@" if $@;
   }

  if (1)                                                                        # Instructions that take two operands
   {my $s = '';
    for my $i(@i2)
      {my $I = ucfirst $i;
       push @declarations, $I;
       $s .= <<END;
       sub $I(\@)
        {my (\$target, \$source) = \@_;
         \@_ == 2 or confess "Two arguments required, not ".scalar(\@_);
         &traceInstruction(q($i));
         push \@text, qq($i \$target, \$source\\n);
        }
END
     }
    eval $s;
    confess "$s$@" if $@;
   }

  if (1)                                                                        # Instructions that take three operands
   {my $s = '';
    for my $i(@i3)
      {my $I = ucfirst $i;
       push @declarations, $I;
       my $j = $i =~ s(\d\Z) ()r;                                               # Remove number of parameters designated
       $s .= <<END;
       sub $I(\@)
        {my (\$target, \$source, \$bits) = \@_;
         \@_ == 3 or confess "Three arguments required, not ".scalar(\@_);
         push \@text, qq($j \$target, \$source, \$bits\\n);
        }
END
     }
    eval "$s$@";
    confess $@ if $@;
   }

  if (1)                                                                        # Instructions that take four operands
   {my $s = '';
    for my $i(@i4)
      {my $I = ucfirst $i;
       push @declarations, $I;
       $s .= <<END;
       sub $I(\@)
        {my (\$target, \$source, \$bits, \$zero) = \@_;
         \@_ == 4 or confess "Four arguments required, not ".scalar(\@_);
         push \@text, qq($i \$target, \$source, \$bits, \$zero\\n);
        }
END
     }
    eval "$s$@";
    confess $@ if $@;
   }

  sub traceInstruction($)                                                       # Trace the location of this instruction in  the source code
   {my ($i) = @_;                                                               # Instruction
    return unless $TraceMode and $i =~ m(\Amov\Z);                              # Trace just these instructions and only when tracing is enabled
    my @c;

    push @text, <<END;                                                          # Tracing destroys mm0 so that we can use r11
  movq mm0, r11;
END

    for(1..100)                                                                 # Write line numbers of traceback
     {my @c = caller $_;
      last unless @c;
      $c[3] =~ s(Nasm::X86::) ();
      my (undef, undef, $line, $file) = @c;
      push @text, <<END;
  mov r11, $line;
END
     }

    push @text, <<END;                                                          # Restore r11 from destroyed mm0
  movq r11, mm0;
END
   }
 }

sub byteRegister($)                                                             # The byte register corresponding to a full size register
 {my ($r) = @_;                                                                 # Full size register
  if ($r =~ m(\Ar([abcd])x\Z)) {return $1."l"};
  return dil if $r eq rdi;
  return sil if $r eq rsi;
  $r."b"
 }

sub wordRegister($)                                                             # The word register corresponding to a full size register
 {my ($r) = @_;                                                                 # Full size register
  if ($r =~ m(\Ar([abcd])x\Z)) {return $1."x"};
  return di if $r eq rdi;
  return si if $r eq rsi;
  $r."w"
 }

sub dWordRegister($)                                                            # The double word register corresponding to a full size register
 {my ($r) = @_;                                                                 # Full size register
  if ($r =~ m(\Ar([abcd])x\Z)) {return "e".$1."x"};
  return edi if $r eq rdi;
  return esi if $r eq rsi;
  $r."d"
 }

sub Subroutine(&%);                                                             # Create a subroutine that can be called in assembler code.

#D1 Data                                                                        # Layout data

my $Labels = 0;

sub Label(;$)                                                                   #P Create a unique label or reuse the one supplied.
 {return "l".++$Labels unless @_;                                               # Generate a label
  $_[0];                                                                        # Use supplied label
 }

sub SetLabel(;$)                                                                # Create (if necessary) and set a label in the code section returning the label so set.
 {my ($l) = @_;                                                                 # Label
  $l //= Label;
  push @text, <<END;                                                            # Define bytes
  $l:
END
  $l                                                                            # Return label name
 }

sub Ds(@)                                                                       # Layout bytes in memory and return their label.
 {my (@d) = @_;                                                                 # Data to be laid out
  my $d = join '', @_;
     $d =~ s(') (\')gs;
  my $l = Label;
  push @data, <<END;                                                            # Define bytes
  $l: db  '$d';
END
  $l                                                                            # Return label
 }

sub Rs(@)                                                                       # Layout bytes in read only memory and return their label.
 {my (@d) = @_;                                                                 # Data to be laid out
  my $d = join '', @_;
  my @e;
  for my $e(split //, $d)
   {if ($e !~ m([A-Z0-9])i) {push @e, sprintf("0x%x", ord($e))} else {push @e, qq('$e')}
   }
  my $e = join ', ', @e;
  my $L = $rodatas{$e};
  return $L if defined $L;                                                      # Data already exists so return it
  my $l = Label;                                                                # New label for new data
  $rodatas{$e} = $l;                                                            # Record label
  push @rodata, <<END;                                                          # Define bytes
  $l: db  $e, 0;
END
  $l                                                                            # Return label
 }

sub Rutf8(@)                                                                    # Layout a utf8 encoded string as bytes in read only memory and return their label.
 {my (@d) = @_;                                                                 # Data to be laid out
  confess unless @_;
  my $d = join '', @_; ## No need to join and split
  my @e;
  for my $e(split //, $d)
   {my $o  = ord $e;                                                            # Effectively the utf32 encoding of each character
    my $u  = convertUtf32ToUtf8($o);
    my $x  = sprintf("%08x", $u);
    my $o1 = substr($x, 0, 2);
    my $o2 = substr($x, 2, 2);
    my $o3 = substr($x, 4, 2);
    my $o4 = substr($x, 6, 2);
    if    ($o <= (1 << 7))  {push @e,                $o4}
    elsif ($o <= (1 << 11)) {push @e,           $o3, $o4}
    elsif ($o <= (1 << 16)) {push @e,      $o2, $o3, $o4}
    else                    {push @e, $o1, $o2, $o3, $o4}
   }

  my $e = join ', ',map {"0x$_"}  @e;
  my $L = $rodatas{$e};
  return $L if defined $L;                                                      # Data already exists so return it
  my $l = Label;                                                                # New label for new data
  $rodatas{$e} = $l;                                                            # Record label
  push @rodata, <<END;                                                          # Define bytes
  $l: db  $e, 0;
END
  $l                                                                            # Return label
 }

sub Dbwdq($@)                                                                   #P Layout data.
 {my ($s, @d) = @_;                                                             # Element size, data to be laid out
  my $d = join ', ', @d;
  my $l = Label;
  push @data, <<END;
  $l: d$s $d
END
  $l                                                                            # Return label
 }

sub Db(@)                                                                       # Layout bytes in the data segment and return their label.
 {my (@bytes) = @_;                                                             # Bytes to layout
  Dbwdq 'b', @_;
 }
sub Dw(@)                                                                       # Layout words in the data segment and return their label.
 {my (@words) = @_;                                                             # Words to layout
  Dbwdq 'w', @_;
 }
sub Dd(@)                                                                       # Layout double words in the data segment and return their label.
 {my (@dwords) = @_;                                                            # Double words to layout
  Dbwdq 'd', @_;
 }
sub Dq(@)                                                                       # Layout quad words in the data segment and return their label.
 {my (@qwords) = @_;                                                            # Quad words to layout
  Dbwdq 'q', @_;
 }

sub Rbwdq($@)                                                                   #P Layout data.
 {my ($s, @d) = @_;                                                             # Element size, data to be laid out
  my $d = join ', ', map {$_ =~ m(\A\d+\Z) ? sprintf "0x%x", $_ : $_} @d;       # Data to be laid out
  if (my $c = $rodata{$s}{$d})                                                  # Data already exists so return it
   {return $c
   }
  my $l = Label;                                                                # New data - create a label
  push @rodata, <<END;                                                          # Save in read only data
  $l: d$s $d
END
  $rodata{$s}{$d} = $l;                                                         # Record label
  $l                                                                            # Return label
 }

sub Rb(@)                                                                       # Layout bytes in the data segment and return their label.
 {my (@bytes) = @_;                                                             # Bytes to layout
  Rbwdq 'b', @_;
 }
sub Rw(@)                                                                       # Layout words in the data segment and return their label.
 {my (@words) = @_;                                                             # Words to layout
  Rbwdq 'w', @_;
 }
sub Rd(@)                                                                       # Layout double words in the data segment and return their label.
 {my (@dwords) = @_;                                                            # Double words to layout
  Rbwdq 'd', @_;
 }
sub Rq(@)                                                                       # Layout quad words in the data segment and return their label.
 {my (@qwords) = @_;                                                            # Quad words to layout
  Rbwdq 'q', @_;
 }

my $Pi = "3.141592653589793238462";

sub Pi32 {Rd("__float32__($Pi)")}                                               #P Pi as a 32 bit float.
sub Pi64 {Rq("__float32__($Pi)")}                                               #P Pi as a 64 bit float.

#D1 Registers                                                                   # Operations on registers

#D2 Size                                                                        # Sizes of each register

sub RegisterSize($)                                                             # Return the size of a register.
 {my ($r) = @_;                                                                 # Register
  $r = &registerNameFromNumber($r);
  defined($r) or confess;
  defined($Registers{$r}) or confess "No such registers as: $r";
  eval "${r}Size()";
 }

#D2 Push, Pop, Peek                                                             # Generic versions of push, pop, peek

sub PushRR(@)                                                                   #P Push registers onto the stack without tracking.
 {my (@r) = @_;                                                                 # Register
  my $w = RegisterSize rax;
  for my $r(map {&registerNameFromNumber($_)} @r)
   {my $size = RegisterSize $r;
    $size or confess "No such register: $r";
    if    ($size > $w)                                                          # Wide registers
     {Sub rsp, $size;
      Vmovdqu32 "[rsp]", $r;
     }
    elsif ($r =~ m(\Ak))                                                        # Mask as they do not respond to push
     {Sub rsp, $size;
      Kmovq "[rsp]", $r;
     }
    else                                                                        # Normal register
     {Push $r;
     }
   }
 }

my @PushR;                                                                      # Track pushes

sub PushR(@)                                                                    #P Push registers onto the stack.
 {my (@r) = @_;                                                                 # Registers
  push @PushR, [@r];
# CommentWithTraceBack;
  PushRR   @r;                                                                  # Push
  scalar(@PushR)                                                                # Stack depth
 }

sub PopRR(@)                                                                    #P Pop registers from the stack without tracking.
 {my (@r) = @_;                                                                 # Register
  my $w = RegisterSize rax;
  for my $r(reverse map{&registerNameFromNumber($_)}  @r)                       # Pop registers in reverse order
   {my $size = RegisterSize $r;
    if    ($size > $w)
     {Vmovdqu32 $r, "[rsp]";
      Add rsp, $size;
     }
    elsif ($r =~ m(\Ak))
     {Kmovq $r, "[rsp]";
      Add rsp, $size;
     }
    else
     {Pop $r;
     }
   }
 }

sub PopR(@)                                                                     # Pop registers from the stack. Use the last stored set if none explicitly supplied.  Pops are done in reverse order to match the original pushing order.
 {my (@r) = @_;                                                                 # Register
  @PushR or confess "No stacked registers";
  my $r = pop @PushR;
  dump(\@r) eq dump($r) or confess "Mismatched registers:\n".dump($r, \@r) if @r;
  PopRR @$r;                                                                    # Pop registers from the stack without tracking
# CommentWithTraceBack;
 }

#D2 General                                                                     # Actions specific to general purpose registers

sub registerNameFromNumber($)                                                   # Register name from number where possible
 {my ($r) = @_;                                                                 # Register number
  return "zmm$r" if $r =~ m(\A(16|17|18|19|20|21|22|23|24|25|26|27|28|29|30|31)\Z);
  return   "r$r" if $r =~ m(\A(8|9|10|11|12|13|14|15)\Z);
  return   "k$r" if $r =~ m(\A(0|1|2|3|4|5|6|7)\Z);
  $r
 }

sub ChooseRegisters($@)                                                         # Choose the specified numbers of registers excluding those on the specified list.
 {my ($number, @registers) = @_;                                                # Number of registers needed, Registers not to choose
  my %r = (map {$_=>1} map {"r$_"} 8..15);
  delete $r{$_} for @registers;
  $number <= keys %r or confess "Not enough registers available";
  sort keys %r
 }

sub InsertZeroIntoRegisterAtPoint($$)                                           # Insert a zero into the specified register at the point indicated by another general purpose or mask register moving the higher bits one position to the left.
 {my ($point, $in) = @_;                                                        # Register with a single 1 at the insertion point, register to be inserted into.

  ref($point) and confess "Point must be a register";

  PushR my ($mask, $low, $high) = ChooseRegisters(3, $in, $point);              # Choose three work registers and push them
  if (&CheckMaskRegister($point))                                               # Mask register showing point
   {Kmovq $mask, $point;
   }
  else                                                                          # General purpose register showing point
   {Mov  $mask, $point;
   }

  Dec  $mask;                                                                   # Fill mask to the right of point with ones
  Andn $high, $mask, $in;                                                       # Part of in be shifted
  Shl  $high, 1;                                                                # Shift high part
  And  $in,  $mask;                                                             # Clear high part of target
  Or   $in,  $high;                                                             # Or in new shifted high part
  PopR;                                                                         # Restore stack
 }

sub InsertOneIntoRegisterAtPoint($$)                                            # Insert a one into the specified register at the point indicated by another register.
 {my ($point, $in) = @_;                                                        # Register with a single 1 at the insertion point, register to be inserted into.
  InsertZeroIntoRegisterAtPoint($point, $in);                                   # Insert a zero
  if (&CheckIfMaskRegisterNumber($point))                                       # Mask register showing point
   {my ($r) = ChooseRegisters(1, $in);                                          # Choose a general purpose register to place the mask in
    PushR $r;
    Kmovq $r, $point;
    Or   $in, $r;                                                               # Make the zero a one
    PopR;
   }
  else                                                                          # General purpose register showing point
   {Or $in, $point;                                                             # Make the zero a one
   }
 }

#D2 Save and Restore                                                            # Saving and restoring registers via the stack

my @syscallSequence = qw(rax rdi rsi rdx r10 r8 r9);                            # The parameter list sequence for system calls

sub SaveFirstFour(@)                                                            # Save the first 4 parameter registers making any parameter registers read only.
 {my (@keep) = @_;                                                              # Registers to mark as read only
  my $N = 4;
  PushRR $_ for @syscallSequence[0..$N-1];
  $N * &RegisterSize(rax);                                                      # Space occupied by push
 }

sub RestoreFirstFour()                                                          # Restore the first 4 parameter registers.
 {my $N = 4;
  PopRR $_ for reverse @syscallSequence[0..$N-1];
 }

sub RestoreFirstFourExceptRax()                                                 # Restore the first 4 parameter registers except rax so it can return its value.
 {my $N = 4;
  PopRR $_ for reverse @syscallSequence[1..$N-1];
  Add rsp, 1*RegisterSize(rax);
 }

sub SaveFirstSeven()                                                            # Save the first 7 parameter registers.
 {my $N = 7;
  PushRR $_ for @syscallSequence[0..$N-1];
  $N * 1*RegisterSize(rax);                                                     # Space occupied by push
 }

sub RestoreFirstSeven()                                                         # Restore the first 7 parameter registers.
 {my $N = 7;
  PopRR $_ for reverse @syscallSequence[0..$N-1];
 }

sub RestoreFirstSevenExceptRax()                                                # Restore the first 7 parameter registers except rax which is being used to return the result.
 {my $N = 7;
  PopRR $_ for reverse @syscallSequence[1..$N-1];
  Add rsp, 1*RegisterSize(rax);
 }

sub ClearRegisters(@)                                                           # Clear registers by setting them to zero.
 {my (@registers) = @_;                                                         # Registers
  my $w = RegisterSize rax;
  for my $r(map{registerNameFromNumber $_} @registers)                          # Each register
   {my $size = RegisterSize $r;
    Xor    $r, $r     if $size == $w and $r !~ m(\Ak);
    Kxorq  $r, $r, $r if $size == $w and $r =~ m(\Ak);
    Vpxorq $r, $r, $r if $size  > $w;
   }
 }

sub SetZF()                                                                     # Set the zero flag.
 {Cmp rax, rax;
 }

sub ClearZF()                                                                   # Clear the zero flag.
 {PushR rax;
  Mov rax, 1;
  Cmp rax, 0;
  PopR rax;
 }

#D2 x, y, zmm                                                                   # Actions specific to mm registers

sub xmm(@)                                                                      # Add xmm to the front of a list of register expressions.
 {my (@r) = @_;                                                                 # Register numbers
  map {"xmm$_"} @_;
 }

sub ymm(@)                                                                      # Add ymm to the front of a list of register expressions.
 {my (@r) = @_;                                                                 # Register numbers
  map {"ymm$_"} @_;
 }

sub zmm(@)                                                                      # Add zmm to the front of a list of register expressions.
 {my (@r) = @_;                                                                 # Register numbers
  map {"zmm$_"} @_;
 }

sub zmmM($$)                                                                    # Add zmm to the front of a register number and a mask after it
 {my ($z, $m) = @_;                                                             # Zmm number, mask register
  "zmm$z\{k$m}"
 }

sub zmmMZ($$)                                                                   # Add zmm to the front of a register number and mask and zero after it
 {my ($z, $m) = @_;                                                             # Zmm number, mask register number
  "zmm$z\{k$m}\{z}"
 }

sub LoadZmm($@)                                                                 # Load a numbered zmm with the specified bytes.
 {my ($zmm, @bytes) = @_;                                                       # Numbered zmm, bytes
  my $b = Rb(@bytes);
  Vmovdqu8 "zmm$zmm", "[$b]";
 }

sub checkZmmRegister($)                                                         # Check that a register is a zmm register
 {my ($z) = @_;                                                                 # Parameters
  $z =~ m(\A(0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|16|17|18|19|20|21|22|23|24|25|26|27|28|29|30|31)\Z) or confess "$z is not the number of a zmm register";
 }

sub bRegFromZmm($$$)                                                            # Load the specified register from the byte at the specified offset located in the numbered zmm.
 {my ($register, $zmm, $offset) = @_;                                           # Register to load, numbered zmm register to load from, constant offset in bytes
  @_ == 3 or confess "Three parameters";
  my $z = registerNameFromNumber $zmm;
  $offset >= 0 && $offset <= RegisterSize zmm0 or
    confess "Offset $offset Out of range";

  PushRR $z;                                                                    # Push source register

  my $b = byteRegister $register;                                               # Corresponding byte register

  Mov $b, "[rsp+$offset]";                                                      # Load byte register from offset
  Add rsp, RegisterSize $z;                                                     # Pop source register
 }

sub bRegIntoZmm($$$)                                                            # Put the byte content of the specified register into the byte in the numbered zmm at the specified offset in the zmm.
 {my ($register,  $zmm, $offset) = @_;                                          # Register to load, numbered zmm register to load from, constant offset in bytes
  @_ == 3 or confess "Three parameters";
  $offset >= 0 && $offset <= RegisterSize zmm0 or confess "Out of range";

  PushR $zmm;                                                                   # Push source register

  my $b = byteRegister $register;                                               # Corresponding byte register

  Mov "[rsp+$offset]", $b;                                                      # Save byte at specified offset
  PopR;                                                                         # Reload zmm
 }

sub wRegFromZmm($$$)                                                            # Load the specified register from the word at the specified offset located in the numbered zmm.
 {my ($register, $zmm, $offset) = @_;                                           # Register to load, numbered zmm register to load from, constant offset in bytes
  @_ == 3 or confess "Three parameters";
  my $z = registerNameFromNumber $zmm;
  $offset >= 0 && $offset <= RegisterSize zmm0 or
    confess "Offset $offset Out of range";

  PushRR $z;                                                                    # Push source register

  my $w = wordRegister $register;                                               # Corresponding word register

  Mov $w, "[rsp+$offset]";                                                      # Load word register from offset
  Add rsp, RegisterSize $z;                                                     # Pop source register
 }

sub wRegIntoZmm($$$)                                                            # Put the specified register into the word in the numbered zmm at the specified offset in the zmm.
 {my ($register,  $zmm, $offset) = @_;                                          # Register to load, numbered zmm register to load from, constant offset in bytes
  @_ == 3 or confess "Three parameters";
  $offset >= 0 && $offset <= RegisterSize zmm0 or confess "Out of range";

  PushR $zmm;                                                                   # Push source register

  my $w = wordRegister $register;                                               # Corresponding word register

  Mov "[rsp+$offset]", $w;                                                      # Save word at specified offset
  PopR;                                                                         # Reload zmm
 }

sub LoadRegFromMm($$$)                                                          # Load the specified register from the numbered zmm at the quad offset specified as a constant number.
 {my ($mm, $offset, $reg) = @_;                                                 # Mm register, offset in quads, general purpose register to load
  @_ == 3 or confess "Three parameters";
  my $w = RegisterSize rax;                                                     # Size of rax
  my $W = RegisterSize $mm;                                                     # Size of mm register
  Vmovdqu64 "[rsp-$W]", $mm;                                                    # Write below the stack
  Mov $reg, "[rsp+$w*$offset-$W]";                                              # Load register from offset
 }

sub SaveRegIntoMm($$$)                                                          # Save the specified register into the numbered zmm at the quad offset specified as a constant number.
 {my ($mm, $offset, $reg) = @_;                                                 # Mm register, offset in quads, general purpose register to load
  @_ == 3 or confess "Three parameters";
  my $w = RegisterSize rax;                                                     # Size of rax
  my $W = RegisterSize $mm;                                                     # Size of mm register
  Vmovdqu64 "[rsp-$W]", $mm;                                                    # Write below the stack
  Mov "[rsp+$w*$offset-$W]", $reg;                                              # Save register into offset
  Vmovdqu64 $mm, "[rsp-$W]";                                                    # Reload from the stack
 }

sub getBwdqFromMm($$$)                                                          # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable.
 {my ($size, $mm, $offset) = @_;                                                # Size of get, mm register, offset in bytes either as a constant or as a variable
  @_ == 3 or confess "Three parameters";

  my $o;                                                                        # The offset into the mm register
  if (ref($offset))                                                             # The offset is being passed in a variable
   {$offset->setReg($o = rsi);
   }
  else                                                                          # The offset is being passed as a register expression
   {$o = $offset;
   }

  my $w = RegisterSize $mm;                                                     # Size of mm register
  Vmovdqu32 "[rsp-$w]", $mm;                                                    # Write below the stack

  ClearRegisters rdi if $size !~ m(q|d);                                        # Clear the register if necessary
  Mov  byteRegister(rdi), "[rsp+$o-$w]" if $size =~ m(b);                       # Load byte register from offset
  Mov  wordRegister(rdi), "[rsp+$o-$w]" if $size =~ m(w);                       # Load word register from offset
  Mov dWordRegister(rdi), "[rsp+$o-$w]" if $size =~ m(d);                       # Load double word register from offset
  Mov rdi,                "[rsp+$o-$w]" if $size =~ m(q);                       # Load register from offset

  V("$size at offset $offset in $mm", rdi);                                     # Create variable
 }

sub bFromX($$)                                                                  # Get the byte from the numbered xmm register and return it in a variable.
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMm('b', "xmm$xmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub wFromX($$)                                                                  # Get the word from the numbered xmm register and return it in a variable.
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMm('w', "xmm$xmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub dFromX($$)                                                                  # Get the double word from the numbered xmm register and return it in a variable.
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMm('d', "xmm$xmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub qFromX($$)                                                                  # Get the quad word from the numbered xmm register and return it in a variable.
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMm('q', "xmm$xmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub bFromZ($$)                                                                  # Get the byte from the numbered zmm register and return it in a variable.
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromMm('b', "zmm$zmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub wFromZ($$)                                                                  # Get the word from the numbered zmm register and return it in a variable.
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromMm('w', "zmm$zmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub dFromZ($$)                                                                  # Get the double word from the numbered zmm register and return it in a variable.
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromMm('d', "zmm$zmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub qFromZ($$)                                                                  # Get the quad word from the numbered zmm register and return it in a variable.
 {my ($zmm, $offset) = @_;                                                      # Numbered zmm, offset in bytes
  getBwdqFromMm('q', "zmm$zmm", $offset)                                        # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

#D2 Mask                                                                        # Operations on mask registers

sub CheckMaskRegister($)                                                        # Check that a register is in fact a numbered mask register
 {my ($reg) = @_;                                                               # Register to check
  @_ == 1 or confess "One parameter";
  $Registers{$reg} && $reg =~ m(\Ak[0-7]\Z)
 }

sub CheckIfMaskRegisterNumber($)                                                # Check that a register is in fact a mask register.
 {my ($mask) = @_;                                                              # Mask register to check
  @_ == 1 or confess "One parameter";
  $mask =~ m(\Ak?[0-7]\Z)
 }

sub CheckMaskRegisterNumber($)                                                  # Check that a register is in fact a mask register and confess if it is not.
 {my ($mask) = @_;                                                              # Mask register to check
  @_ == 1 or confess "One parameter";
  $mask =~ m(\Ak?[0-7]\Z) or confess "Not the number of a mask register: $mask";
 }

sub SetMaskRegister($$$)                                                        # Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere.
 {my ($mask, $start, $length) = @_;                                             # Number of mask register to set, register containing start position or 0 for position 0, register containing end position
  @_ == 3 or confess "Three parameters";
  CheckMaskRegisterNumber($mask);

  PushR 15, 14;
  Mov r15, -1;
  if ($start)                                                                   # Non zero start
   {Mov  r14, $start;
    Bzhi r15, r15, r14;
    Not  r15;
    Add  r14, $length;
   }
  else                                                                          # Starting at zero
   {Mov r14, $length;
   }
  Bzhi r15, r15, r14;
  Kmovq "k$mask", r15;
  PopR;
 }

sub LoadConstantIntoMaskRegister($$)                                            # Set a mask register equal to a constant.
 {my ($mask, $value) = @_;                                                      # Number of mask register to load, constant to load
  @_ == 2 or confess "Two parameters";
  CheckMaskRegisterNumber $mask;
  $mask     = registerNameFromNumber $mask;
  Mov rdi, $value;                                                              # Load mask into a general purpose register
  Kmovq $mask, rdi;                                                             # Load mask register from general purpose register
 }

sub createBitNumberFromAlternatingPattern($@)                                   # Create a number from a bit pattern.
 {my ($prefix, @values) = @_;                                                   # Prefix bits, +n 1 bits -n 0 bits
  @_ > 1 or confess "Four or more parameters required";                         # Must have some values

  $prefix =~ m(\A[01]*\Z) or confess "Prefix must be binary";                   # Prefix must be binary
  grep {$_ == 0} @values and confess "Values must not be zero";                 # No value may be zero

  for my $i(0..$#values-1)                                                      # Check values alternate
   {($values[$i] > 0 && $values[$i+1] > 0  or
     $values[$i] < 0 && $values[$i+1] < 0) and confess "Signs must alternate";
   }

  my $b = "0b$prefix";
  for my $v(@values)                                                            # String representation of bit string
   {$b .= '1' x +$v if $v > 0;
    $b .= '0' x -$v if $v < 0;
   }

  my $n = eval $b;
  confess $@ if $@;
  $n
 }

sub LoadBitsIntoMaskRegister($$@)                                               # Load a bit string specification into a mask register in two clocks.
 {my ($mask, $prefix, @values) = @_;                                            # Number of mask register to load, prefix bits, +n 1 bits -n 0 bits
  @_ > 2 or confess "Three or more parameters required";                        # Must have some values

  LoadConstantIntoMaskRegister                                                  # Load the specified binary constant into a mask register
    ($mask, createBitNumberFromAlternatingPattern $prefix, @values)
 }

#D1 Comparison codes                                                            # The codes used to specify what sort of comparison to perform

my $Vpcmp = genHash("Nasm::X86::CompareCodes",                                  # Compare codes for "Vpcmp"
  eq=>0,                                                                        # Equal
  lt=>1,                                                                        # Less than
  le=>2,                                                                        # Less than or equals
  ne=>4,                                                                        # Not equals
  ge=>5,                                                                        # Greater than or equal
  gt=>6,                                                                        # Greater than
 );

#D1 Structured Programming                                                      # Structured programming constructs

sub If($$;$)                                                                    # If statement.
 {my ($jump, $then, $else) = @_;                                                # Jump op code of variable, then - required , else - optional
  @_ >= 2 && @_ <= 3 or confess;

  ref($jump) or $jump =~ m(\AJ(c|e|g|ge|gt|h|l|le|nc|ne|ns|nz|s|z)\Z)
             or confess "Invalid jump: $jump";

  if (ref($jump))                                                               # Variable expression,  if it is non zero perform the then block else the else block
   { __SUB__->(q(Jnz), $then, $else);
   }
  elsif (!$else)                                                                # No else
   {my $end = Label;
    push @text, <<END;
    $jump $end;
END
    &$then;
    SetLabel $end;
   }
  else                                                                          # With else
   {my $endIf     = Label;
    my $startElse = Label;
    push @text, <<END;
    $jump $startElse
END
    &$then;
    Jmp $endIf;
    SetLabel $startElse;
    &$else;
    SetLabel  $endIf;
   }
 }

sub Then(&)                                                                     # Then block for an If statement.
 {my ($block) = @_;                                                             # Then block
  $block;
 }

sub Else(&)                                                                     # Else block for an If statement.
 {my ($block) = @_;                                                             # Else block
  $block;
 }

sub OR(@)                                                                       # Return a variable containing 1 if any of the conditions is true else 0 by evaluating the conditions in order and stopping as soon as the result is known.
 {my (@c) = @_;                                                                 # Conditions enclosed in subs
  my $r = &V(or => 0);
  &Block(sub
   {my ($end, $start) = @_;
    for my $c(@c)
     {If &$c, Then {$r->copy(1); Jmp $end}
     }
   });
  $r
 }

sub AND(@)                                                                      # Return a variable containing 1 if all of the conditions are true else 0 by evaluating the conditions in order and stopping as soon as the result is known.
 {my (@c) = @_;                                                                 # Conditions enclosed in subs
  my $r = &V(and => 1);
  &Block(sub
   {my ($end, $start) = @_;
    for my $c(@c)
     {If &$c, Then {}, Else {$r->copy(0); Jmp $end}
     }
   });
  $r
 }

sub Ef(&$;$)                                                                    # Else if block for an If statement.
 {my ($condition, $then, $else) = @_;                                           # Condition, then block, else block
  sub
  {If (&$condition, $then, $else);
  }
 }

sub IfEq($;$)                                                                   # If equal execute the then block else the else block.
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jne), $then, $else);                                                     # Opposite code
 }

sub IfNe($;$)                                                                   # If not equal execute the then block else the else block.
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Je), $then, $else);                                                      # Opposite code
 }

sub IfNz($;$)                                                                   # If the zero flag is not set then execute the then block else the else block.
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jz), $then, $else);                                                      # Opposite code
 }

sub IfZ($;$)                                                                    # If the zero flag is set then execute the then block else the else block.
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jnz), $then, $else);                                                     # Opposite code
 }

sub IfC($;$)                                                                    # If the carry flag is set then execute the then block else the else block.
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jnc), $then, $else);                                                     # Opposite code
 }

sub IfNc($;$)                                                                   # If the carry flag is not set then execute the then block else the else block.
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jc), $then, $else);                                                      # Opposite code
 }

sub IfLt($;$)                                                                   # If less than execute the then block else the else block.
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jge), $then, $else);                                                     # Opposite code
 }

sub IfLe($;$)                                                                   # If less than or equal execute the then block else the else block.
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jg), $then, $else);                                                      # Opposite code
 }

sub IfGt($;$)                                                                   # If greater than execute the then block else the else block.
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jle), $then, $else);                                                     # Opposite code
 }

sub IfGe($;$)                                                                   # If greater than or equal execute the then block else the else block.
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jl), $then, $else);                                                      # Opposite code
 }

sub IfS($;$)                                                                    # If signed greater than or equal execute the then block else the else block.
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Jns), $then, $else);                                                     # Opposite code
 }

sub IfNs($;$)                                                                   # If signed less than execute the then block else the else block.
 {my ($then, $else) = @_;                                                       # Then - required , else - optional
  If(q(Js), $then, $else);                                                      # Opposite code
 }

sub Pass(&)                                                                     # Pass block for an L<OrBlock>.
 {my ($block) = @_;                                                             # Block
  $block;
 }

sub Fail(&)                                                                     # Fail block for an L<AndBlock>.
 {my ($block) = @_;                                                             # Block
  $block;
 }

sub Block(&)                                                                    # Execute a block of code with labels supplied for the start and end of this code
 {my ($code) = @_;                                                              # Block of code
  @_ == 1 or confess "One parameter";
  SetLabel(my $start = Label);                                                  # Start of block
  my $end  = Label;                                                             # End of block
  &$code($end, $start);                                                         # Code with labels supplied
  SetLabel $end;                                                                # End of block
 }

sub AndBlock(&;$)                                                               # Short circuit B<and>: execute a block of code to test conditions which, if all of them pass, allows the first block to continue successfully else if one of the conditions fails we execute the optional fail block.
 {my ($test, $fail) = @_;                                                       # Block, optional failure block
  @_ == 1 or @_ == 2 or confess "One or two parameters";
  SetLabel(my $start = Label);                                                  # Start of test block
  my $Fail = @_ == 2 ? Label : undef;                                           # Start of fail block
  my $end  = Label;                                                             # End of both blocks
  &$test(($Fail // $end), $end, $start);                                        # Test code plus success code
  if ($fail)
   {Jmp $end;                                                                   # Skip the fail block if we succeed in reaching the end of the test block which is the expected behavior for short circuited B<and>.
    SetLabel $Fail;
    &$fail($end, $Fail, $start);                                                # Execute when true
   }
  SetLabel $end;                                                                # Exit block
 }

sub OrBlock(&;$)                                                                # Short circuit B<or>: execute a block of code to test conditions which, if one of them is met, leads on to the execution of the pass block, if all of the tests fail we continue withe the test block.
 {my ($test, $pass) = @_;                                                       # Tests, optional block to execute on success
  @_ == 1 or @_ == 2 or confess "One or two parameters";
  SetLabel(my $start = Label);                                                  # Start of test block
  my $Pass = @_ == 2 ? Label : undef;                                           # Start of pass block
  my $end  = Label;                                                             # End of both blocks
  &$test(($Pass // $end), $end, $start);                                        # Test code plus fail code
  if ($pass)
   {Jmp $end;                                                                   # Skip the pass block if we succeed in reaching the end of the test block which is the expected behavior for short circuited B<or>.
    SetLabel $Pass;
    &$pass($end, $Pass, $start);                                                # Execute when true
   }
  SetLabel $end;                                                                # Exit block
 }

sub For(&$$;$)                                                                  # For - iterate the block as long as register is less than limit incrementing by increment each time. Nota Bene: The register is not explicitly set to zero as you might want to start at some other number.
 {my ($block, $register, $limit, $increment) = @_;                              # Block, register, limit on loop, increment on each iteration
  @_ == 3 or @_ == 4 or confess;
  $increment //= 1;                                                             # Default increment
  my $next = Label;                                                             # Next iteration
  &Comment("For $register $limit");
  my $start = Label;
  my $end   = Label;
  SetLabel $start;
  Cmp $register, $limit;
  Jge $end;

  &$block($start, $end, $next);                                                 # Start, end and next labels

  SetLabel $next;                                                               # Next iteration starting with after incrementing
  if ($increment == 1)
   {Inc $register;
   }
  else
   {Add $register, $increment;
   }
  Jmp $start;                                                                   # Restart loop
  SetLabel $end;                                                                # Exit loop
 }

sub ForIn(&$$$$)                                                                # For - iterate the full block as long as register plus increment is less than than limit incrementing by increment each time then increment the last block for the last non full block.
 {my ($full, $last, $register, $limitRegister, $increment) = @_;                # Block for full block, block for last block , register, register containing upper limit of loop, increment on each iteration
  @_ == 5 or confess;
  my $start = Label;
  my $end   = Label;

  SetLabel $start;                                                              # Start of loop
  PushR $register;                                                              # Save the register so we can test that there is still room
  Add   $register, $increment;                                                  # Add increment
  Cmp   $register, $limitRegister;                                              # Test that we have room for increment
  PopR  $register;                                                              # Remove increment
  Jge   $end;

  &$full;

  Add $register, $increment;                                                    # Increment for real
  Jmp $start;
  SetLabel $end;

  Sub $limitRegister, $register;                                                # Size of remainder
  IfNz                                                                          # Non remainder
  Then
   {&$last;                                                                     # Process remainder
   }
 }

sub ForEver(&)                                                                  # Iterate for ever.
 {my ($block) = @_;                                                             # Block to iterate
  @_ == 1 or confess "One parameter";
  &Comment("ForEver");
  my $start = Label;                                                            # Start label
  my $end   = Label;                                                            # End label

  SetLabel $start;                                                              # Start of loop

  &$block($start, $end);                                                        # End of loop

  Jmp $start;                                                                   # Restart loop
  SetLabel $end;                                                                # End of loop
 }

#D2 Trace back                                                                  # Generate a subroutine calll trace back

my @VariableStack = (1);                                                        # Counts the number of parameters and variables on the stack in each invocation of L<Subroutine>.  There is at least one variable - the first holds the traceback.

sub SubroutineStartStack()                                                      #P Initialize a new stack frame.  The first quad of each frame has the address of the name of the sub in the low dword, and the parameter count in the upper byte of the quad.  This field is all zeroes in the initial frame.
 {push @VariableStack, 1;                                                       # Counts the number of variables on the stack in each invocation of L<Subroutine>.  The first quad provides the traceback.
 }

sub PrintTraceBack($)                                                           # Trace the call stack.
 {my ($channel) = @_;                                                           # Channel to write on

  my $s = Subroutine
   {PushR my @save = (rax, rdi, r9, r10, r8, r12, r13, r14, r15);
    my $stack     = r15;
    my $count     = r14;
    my $index     = r13;
    my $parameter = r12;                                                        # Number of parameters
    my $maxCount  = r8;                                                         # Maximum number of parameters - should be r11 when we have found out why r11 does not print correctly.
    my $depth     = r10;                                                        # Depth of trace back
    ClearRegisters @save;

    Mov $stack, rbp;                                                            # Current stack frame
    AndBlock                                                                    # Each level
     {my ($fail, $end, $start) = @_;                                            # Fail block, end of fail block, start of test block
      Mov $stack, "[$stack]";                                                   # Up one level
      Mov rax, "[$stack-8]";
      Mov $count, rax;
      Shr $count, 56;                                                           # Top byte contains the parameter count
      Cmp $count, $maxCount;                                                    # Compare this count with maximum so far
      Cmovg $maxCount, $count;                                                  # Update count if greater
      Shl rax, 8; Shr rax, 8;                                                   # Remove parameter count
      Je $end;                                                                  # Reached top of stack if rax is zero
      Inc $depth;                                                               # Depth of trace back
      Jmp $start;                                                               # Next level
     };

    Mov $stack, rbp;                                                            # Current stack frame
    &PrintNL($channel);                                                         # Print title
    &PrintString($channel, "Subroutine trace back, depth: ");
    PushR rax;
    Mov rax, $depth;
    &PrintRaxRightInDec(V(width=>2), $channel);
    PopR rax;
    &PrintNL($channel);

    AndBlock                                                                    # Each level
     {my ($fail, $end, $start) = @_;                                            # Fail block, end of fail block, start of test block
      Mov $stack, "[$stack]";                                                   # Up one level
      Mov rax, "[$stack-8]";
      Mov $count, rax;
      Shr $count, 56;                                                           # Top byte contains the parameter count
      Shl rax, 8; Shr rax, 8;                                                   # Remove parameter count
      Je $end;                                                                  # Reached top of stack
      Cmp $count, 0;                                                            # Check for parameters
      IfGt
      Then                                                                      # One or more parameters
       {Mov $index, 0;
        For
         {my ($start, $end, $next) = @_;
          Mov $parameter, $index;
          Add $parameter, 2;                                                    # Skip traceback
          Shl $parameter, 3;                                                    # Each parameter is a quad
          Neg $parameter;                                                       # Offset from stack
          Add $parameter, $stack;                                               # Position on stack
          Mov $parameter, "[$parameter]";                                       # Parameter reference to variable
          Push rax;
          Mov rax, "[$parameter]";                                              # Variable content
          &PrintRaxInHex($channel);
          Pop rax;
          &PrintSpace($channel, 4);
         } $index, $count;
        For                                                                     # Vertically align subroutine names
         {my ($start, $end, $next) = @_;
          &PrintSpace($channel, 23);
         } $index, $maxCount;
       };

      StringLength(&V(string => rax))->setReg(rdi);                             # Length of name of subroutine
      &PrintMemoryNL($channel);                                                 # Print name of subroutine
      Jmp $start;                                                               # Next level
     };
    &PrintNL($channel);
    PopR;
   } name => "SubroutineTraceBack_$channel";

  $s->call;
 }

sub PrintErrTraceBack($)                                                        # Print sub routine track back on stderr and then exit with a message.
 {my ($message) = @_;                                                           # Reason why we are printing the trace back and then stopping
  &PrintErrStringNL($message);
  PrintTraceBack($stderr);
  Exit(1);
 }

sub PrintOutTraceBack($)                                                        # Print sub routine track back on stdout and then exit with a message.
 {my ($message) = @_;                                                           # Reason why we are printing the trace back and then stopping
  &PrintOutStringNL($message);
  PrintTraceBack($stdout);
  Exit(1);
 }

sub OnSegv()                                                                    # Request a trace back followed by exit on a B<segv> signal.
 {my $s = Subroutine                                                            # Subroutine that will cause an error to occur to force a trace back to be printed
   {my $end = Label;
    Jmp $end;                                                                   # Jump over subroutine definition
    my $start = SetLabel;
    Enter 0, 0;                                                                 # Inline code of signal handler
    Mov r15, rbp;                                                               # Preserve the new stack frame
    Mov rbp, "[rbp]";                                                           # Restore our last stack frame
    PrintOutTraceBack 'Segmentation error';                                     # Print our trace back
    Mov rbp, r15;                                                               # Restore supplied stack frame
    Exit(0);                                                                    # Exit so we do not trampoline. Exit with code zero to show that the program is functioning correctly, else L<Assemble> will report an error.
    Leave;
    Ret;
    SetLabel $end;

    Mov r15, 0;                                                                 # Push sufficient zeros onto the stack to make a structure B<sigaction> as described in: https://www.man7.org/linux/man-pages/man2/sigaction.2.html
    Push r15 for 1..16;

    Mov r15, $start;                                                            # Actual signal handler
    Mov "[rsp]", r15;                                                           # Show as signal handler
    Mov "[rsp+0x10]", r15;                                                      # Add as trampoline as well - which is fine because we exit in the handler so this will never be called
    Mov r15, 0x4000000;                                                         # Mask to show we have a trampoline which is, apparently, required on x86
    Mov "[rsp+0x8]", r15;                                                       # Confirm we have a trampoline

    Mov rax, 13;                                                                # B<Sigaction> from B<kill -l>
    Mov rdi, 11;                                                                # Confirmed B<SIGSEGV = 11> from B<kill -l> and tracing with B<sde64>
    Mov rsi, rsp;                                                               # Structure B<sigaction> structure on stack
    Mov rdx, 0;                                                                 # Confirmed by trace
    Mov r10, 8;                                                                 # Found by tracing B<signal.c> with B<sde64> it is the width of the signal set and mask. B<signal.c> is reproduced below.
    Syscall;
    Add rsp, 128;
   } [], name=>"on segv";

  $s->call;
 }

# Subroutine                                                                    # Define and call subroutines

sub copyStructureMinusVariables($)                                              # Copy a non recursive structure ignoring variables
 {my ($s) = @_;                                                                 # Structure to copy

  my %s = %$s;
  for my $k(sort keys %s)                                                       # Look for sub structures
   {if (my $r = ref($s{$k}))
     {$s{$k} = __SUB__->($s{$k}) unless $r =~ m(\AVariable\Z);                  # We do not want to copy the variables yet because we are going to make them into references.
     }
   }

  bless \%s, ref $s;                                                            # Return a copy of the structure
 }

sub Subroutine(&%)                                                              # Create a subroutine that can be called in assembler code.
 {my ($block, %options) = @_;                                                   # Block of code as a sub, options
  @_ >= 1 or confess "Subroutine requires at least a block";

  if (1)                                                                        # Validate options
   {my %o = %options;
    delete $o{$_} for qw(parameters structures name call trace);
    if (my @i = sort keys %o)
     {confess "Invalid parameters: ".join(', ',@i);
     }
   }

  my $name = $options{name};                                                    # Subroutine name
  $name or confess "Name required for subroutine, use name=>";
  if ($name and my $s = $subroutines{$name})                                    # Return the label of a pre-existing copy of the code possibly after running the subroutine. Make sure that the subroutine name is different for different subs as otherwise the unexpected results occur.
   {return $s unless $TraceMode and $options{trace};                            # If we are tracing and this subroutine is marked as traceable we always generate a new version of it so that we can trace each specific instance to get the exact context in which this subroutine was called rather than the context in which the original copy was called.
   }

  my $parameters = $options{parameters};                                        # Optional parameters block
  if (1)                                                                        # Check for duplicate parameters
   {my %c;
    $c{$_}++ && confess "Duplicate parameter $_" for @$parameters;
   }

  SubroutineStartStack;                                                         # Open new stack layout with references to parameters
  my %parameters = map {$_ => R($_)} @$parameters;                              # Create a reference for each parameter.

  my %structureCopies;                                                          # Copies of the structures being passed that can be use inside the subroutine to access their variables in the stack frame of the subroutine
  if (my $structures = $options{structures})                                    # Structure provided in the parameter list
   {for my $name(sort keys %$structures)                                        # Each structure passed
     {$structureCopies{$name} = copyStructureMinusVariables($$structures{$name})# A new copy of the structure with its variables left in place
     }
   }

  my $end   =    Label; Jmp $end;                                               # End label.  Subroutines are only ever called - they are not executed in-line so we jump over the implementation of the subroutine.  This can cause several forward jumps in a row if a number of subroutines are defined together.
  my $start = SetLabel;                                                         # Start label

  my $s = $subroutines{$name} = genHash(__PACKAGE__."::Subroutine",             # Subroutine definition
    start              => $start,                                               # Start label for this subroutine which includes the enter instruction used to create a new stack frame
    end                => $end,                                                 # End label for this subroutine
    name               => $name,                                                # Name of the subroutine from which the entry label is located
    variables          => {%parameters},                                        # Map parameters to references at known positions in the sub
    structureCopies    => \%structureCopies,                                    # Copies of the structures passed to this subroutine with their variables replaced with references
    structureVariables => {},                                                   # Map structure variables to references at known positions in the sub
    offset             => undef,                                                # The offset of this routine in its library if it is in a library
    options            => \%options,                                            # Options used by the author of the subroutine
    parameters         => $parameters,                                          # Parameters definitions supplied by the author of the subroutine which get mapped in to parameter variables.
    vars               => $VariableStack[-1],                                   # Number of variables in subroutine
    nameString         => Rs($name),                                            # Name of the sub as a string constant in read only storage
    block              => $block,                                               # Block used to generate this subroutine
   );

  if (my $structures = $options{structures})                                    # Map structures
   {$s->mapStructureVariables(\%structureCopies);
   }

  my $E = @text;                                                                # Code entry that will contain the Enter instruction
  Enter 0, 0;                                                                   # The Enter instruction is 4 bytes long
  &$block({%parameters}, {%structureCopies}, $s);                               # Code with parameters and structures

  my $V = pop @VariableStack;                                                   # Number of variables in subroutine stack frame. As parameters and structures are mapped into variables in the subroutine stack frame these variables will be included in the count as well.

  Leave if $V;                                                                  # Remove frame if there was one
  Ret;                                                                          # Return from the sub
  SetLabel $end;                                                                # The end point of the sub where we return to normal code
  my $w = RegisterSize rax;
  $text[$E] = $V ? <<END : '';                                                  # Rewrite enter instruction now that we know how much stack space we need
  Enter $V*$w, 0
END

  $s                                                                            # Return subroutine definition
 }

sub Nasm::X86::Subroutine::mapStructureVariables($$@)                           # Find the paths to variables in the copies of the structures passed as parameters and replace those variables with references so that in the subroutine we can refer to these variables regardless of where they are actually defined
 {my ($sub, $S, @P) = @_;                                                       # Sub definition, copies of source structures, path through copies of source structures to a variable that becomes a reference
  for my $s(sort keys %$S)                                                      # Source keys
   {my $e = $$S{$s};
    my $r = ref $e;
    next unless $r;

    if ($r =~ m(Variable)i)                                                     # Replace a variable with a reference in the copy of a structure passed in as a parameter
     {push @P, $s;
      my $R = $sub->structureVariables->{dump([@P])} = $$S{$s} = R($e->name);   # Path to a reference in the copy of a structure passed as as a parameter
      pop @P;
     }
    else                                                                        # A reference to something else - for the moment we assume that structures are built from non recursive hash references
     {push @P, $s;                                                              # Extend path
      $sub->mapStructureVariables($e, @P);                                      # Map structure variable
      pop @P;
     }
   }
 }

sub Nasm::X86::Subroutine::uploadStructureVariablesToNewStackFrame($$@)         # Create references to variables in parameter structures from variables in the stack frame of the subroutine.
 {my ($sub, $S, @P) = @_;                                                       # Sub definition, Source tree of input structures, path through sourtce structures tree

  for my $s(sort keys %$S)                                                      # Source keys
   {my $e = $$S{$s};
    my $r = ref $e;
    next unless $r;                                                             # Element in structure is not a variable or another hash describing a sub structure
    if ($r =~ m(Variable)i)                                                     # Variable located
     {push @P, $s;                                                              # Extend path
      my $p = dump([@P]);                                                       # Path as string
      my $R = $sub->structureVariables->{$p};                                   # Reference
      if (defined($R))
       {$sub->uploadToNewStackFrame($e, $R);                                    # Reference to structure variable from subroutine stack frame
       }
      else                                                                      # Unable to locate the corresponding reference
       {confess "No entry for $p in structure variables";
       }
      pop @P;
     }
    else                                                                        # A hash that is not a variable and is therefore assumed to be a non recursive substructure
     {push @P, $s;
      $sub->uploadStructureVariablesToNewStackFrame($e, @P);
      pop @P;
     }
   }
 }

sub Nasm::X86::Subroutine::uploadToNewStackFrame($$$)                           #P Map a variable in the current stack into a reference in the next stack frame being the one that will be used by this sub
 {my ($sub, $source, $target) = @_;                                             # Subroutine descriptor, source variable in the current stack frame, the reference in the new stack frame
  my $label = $source->label;                                                   # Source in current frame

  if ($source->reference)                                                       # Source is a reference
   {Mov r15, "[$label]";
   }
  else                                                                          # Source is not a reference
   {Lea r15, "[$label]";
   }

  my $q = $target->label;
     $q =~ s(rbp) (rsp);                                                        # Labels are based off the stack frame but we are building a new stack frame here so we must rename the stack pointer.
  my $w = RegisterSize r15;
  Mov "[$q-$w*2]", r15;                                                         # Step over subroutine name pointer and previous frame pointer.
 }

sub Nasm::X86::Subroutine::call($%)                                             #P Call a sub optionally passing it parameters.
 {my ($sub, %options) = @_;                                                     # Subroutine descriptor, options

  if (1)                                                                        # Validate options
   {my %o = %options;
    delete $o{$_} for qw(parameters structures override library);               # Parameters are variables, structures are Perl data structures with variables embedded in them,  override is a variable that contains the actual address of the subroutine
    if (my @i = sort keys %o)
     {confess "Invalid parameters: ".join(', ',@i);
     }
   }

  my $parameters = $options{parameters};                                        # Parameters hash
  !$parameters or ref($parameters) =~ m(hash)i or confess
    "Parameters must be formatted as a hash";

  my $structures = $options{structures};                                        # Structures hash
  !$structures or ref($structures) =~ m(hash)i or confess
    "Structures must be formatted as a hash";

  if ($parameters)                                                              # Check for invalid or missing parameters
   {my %p = map {$_=>1} $sub->parameters->@*;
    my @m;
    for my $p(sort keys %$parameters)
     {push @m, "Invalid parameter: '$p'" unless $p{$p};
     }
    for my $p(sort keys %p)
     {push @m, "Missing parameter: '$p'" unless defined $$parameters{$p};
     }
    if (@m)
     {push @m, "Valid parameters : ";
           $m[-1] .= join ", ", map {"'$_'"} sort $sub->parameters->@*;
      confess join '', map {"$_\n"} @m;
     }
   }
  elsif ($sub->parameters->@*)
   {confess "Parameters required";
   }

  if ($structures)                                                              # Check for invalid or missing structures
   {my %s = $sub->options->{structures}->%*;
    my @m;
    for my $s(sort keys %$structures)
     {push @m, "Invalid structure: '$s'" unless $s{$s};
     }
    for my $s(sort keys %s)
     {push @m, "Missing structure: '$s'" unless $$structures{$s};
     }
    if (@m)
     {push @m, "Valid structures : ";
           $m[-1] .= join ", ", map {"'$_'"} sort keys %s;
      confess join '', map {"$_\n"} @m;
     }
   }
  elsif ($sub->options and $sub->options->{structures} and $sub->options->{structures}->%*)
   {confess "Structures required";
   }

  my $new = sub                                                                 # Regenerate the subroutine if we are tracing in general and this sybroutineis specifically traceable.  We do not trace all subroutines because the generated asm code would be big.
   {if ($sub->options->{trace} and $TraceMode)
     {return Subroutine(sub{$$sub{block}->&*}, $sub->options->%*);
     }
    undef
   }->();

  my $w = RegisterSize r15;
  PushR 15;                                                                     # Use this register to transfer between the current frame and the next frame
  Mov "dword[rsp  -$w*3]", Rs($sub->name);                                      # Point to subroutine name
  Mov "byte [rsp-1-$w*2]", $sub->vars;                                          # Number of parameters to enable trace back with parameters

  for my $name(sort keys $parameters->%*)                                       # Upload the variables referenced by the parameters to the new stack frame
   {my $s = $$parameters{$name};
    my $t = $sub->variables->{$name};
    $sub->uploadToNewStackFrame($s, $t);
   }

  if ($structures)                                                              # Upload the variables of each referenced structure to the new stack frame
   {$sub->uploadStructureVariablesToNewStackFrame($structures);
   }

  if (my $l = $options{library})                                                # A variable containing the start address of a library
   {$l->setReg(rdi);
    if (my $o = $sub->offset)                                                   # The offset of the entry point into the library
     {$o->setReg(rsi);
      Add rdi, rsi;
      Call rdi;
     }
    else
     {confess "Supply the address of the containing library";
     }
   }
  elsif (my $o = $options{override})                                            # A variable containing the address of the subroutine to call
   {$o->setReg(rdi);
    Call rdi;
   }
  else                                                                          # Call via label
   {if ($new)                                                                   # Call new generation created for tracing
     {Call $new->start;
     }
    else                                                                        # Call original generation
     {Call $sub->start;
     }
   }
  PopR;
 }

#D1 Comments                                                                    # Inserts comments into the generated assember code.

sub CommentWithTraceBack(@)                                                     # Insert a comment into the assembly code with a traceback showing how it was generated.
 {my (@comment) = @_;                                                           # Text of comment
  my $c = join "", @comment;
#  eval {confess};
#  my $p = dump($@);
  my $p = &subNameTraceBack =~ s(Nasm::X86::) ()gsr;
  push @text, <<END;
; $c  $p
END
 }

sub Comment(@)                                                                  # Insert a comment into the assembly code.
 {my (@comment) = @_;                                                           # Text of comment
  my $c = join "", @comment;
  my ($p, $f, $l) = caller;
  push @text, <<END;
; $c at $f line $l
END
 }

sub DComment(@)                                                                 # Insert a comment into the data segment.
 {my (@comment) = @_;                                                           # Text of comment
  my $c = join "", @comment;
  push @data, <<END;
; $c
END
 }

sub RComment(@)                                                                 # Insert a comment into the read only data segment.
 {my (@comment) = @_;                                                           # Text of comment
  my $c = join "", @comment;
  push @data, <<END;
; $c
END
 }

#D1 Print                                                                       # Print

sub PrintNL($)                                                                  # Print a new line to stdout  or stderr.
 {my ($channel) = @_;                                                           # Channel to write on
  @_ == 1 or confess "One parameter";

  my $s = Subroutine
   {SaveFirstFour;
    Mov rax, 1;
    Mov rdi, $channel;                                                          # Write below stack
    my $w = RegisterSize rax;
    Lea  rsi, "[rsp-$w]";
    Mov "QWORD[rsi]", 10;
    Mov rdx, 1;
    Syscall;
    RestoreFirstFour
   } name => qq(PrintNL_$channel);

  $s->call;
 }

sub PrintErrNL()                                                                # Print a new line to stderr.
 {@_ == 0 or confess;
  PrintNL($stderr);
 }

sub PrintOutNL()                                                                # Print a new line to stderr.
 {@_ == 0 or confess;
  PrintNL($stdout);
 }

sub PrintString($@)                                                             # Print a constant string to the specified channel.
 {my ($channel, @string) = @_;                                                  # Channel, Strings
  @_ >= 2 or confess "Two or more parameters";

  my $c = join ' ', @string;
  my $l = length($c);
  my $a = Rs($c);

  my $s = Subroutine
   {SaveFirstFour;
    Mov rax, 1;
    Mov rdi, $channel;
    Lea rsi, "[$a]";
    Mov rdx, $l;
    Syscall;
    RestoreFirstFour;
   } name => "PrintString_${channel}_${c}";

  $s->call;
 }

sub PrintStringNL($@)                                                           # Print a constant string to the specified channel followed by a new line.
 {my ($channel, @string) = @_;                                                  # Channel, Strings
  PrintString($channel, @string);
  PrintNL    ($channel);
 }

sub PrintErrString(@)                                                           # Print a constant string to stderr.
 {my (@string) = @_;                                                            # String
  PrintString($stderr, @string);
 }

sub PrintErrStringNL(@)                                                         # Print a constant string to stderr followed by a new line.
 {my (@string) = @_;                                                            # String
  PrintErrString(@string);
  PrintErrNL;
 }

sub PrintOutString(@)                                                           # Print a constant string to stdout.
 {my (@string) = @_;                                                            # String
  PrintString($stdout, @string);
 }

sub PrintOutStringNL(@)                                                         # Print a constant string to stdout followed by a new line.
 {my (@string) = @_;                                                            # String
  PrintOutString(@string);
  PrintOutNL;
 }

sub PrintCString($$)                                                            # Print a zero terminated C style string addressed by a variable on the specified channel.
 {my ($channel, $string) = @_;                                                  # Channel, String

  PushR rax, rdi;
  my $length = &StringLength($string);                                          # Length of string
  $string->setReg(rax);
  $length->setReg(rdi);
  &PrintOutMemory();                                                            # Print string
  PopR;
 }

sub PrintCStringNL($$)                                                          # Print a zero terminated C style string addressed by a variable on the specified channel followed by a new line.
 {my ($channel, $string) = @_;                                                  # Channel, Strings
  PrintCString($channel, $string);
  PrintNL     ($channel);
 }

sub PrintSpace($;$)                                                             # Print a constant number of spaces to the specified channel.
 {my ($channel, $spaces) = @_;                                                  # Channel, number of spaces if not one.
  PrintString($channel, ' ' x ($spaces // 1));
 }

sub PrintErrSpace(;$)                                                           # Print  a constant number of spaces to stderr.
 {my ($spaces) = @_;                                                            # Number of spaces if not one.
  PrintErrString(' ', $spaces);
 }

sub PrintOutSpace(;$)                                                           # Print a constant number of spaces to stdout.
 {my ($spaces) = @_;                                                            # Number of spaces if not one.
  PrintOutString(' ' x $spaces);
 }


sub hexTranslateTable                                                           #P Create/address a hex translate table and return its label.
 {my $h = '0123456789ABCDEF';
  my @t;
  for   my $i(split //, $h)
   {for my $j(split //, $h)
     {my $h = "$i$j";
         $h =~ s(\A00) (..);
         $h =~ s(\A0)  (.);
      push @t, $h;
     }
   }
   Rs @t                                                                        # Constant strings are only saved if they are unique, else a read only copy is returned.
 }

sub PrintRaxInHex($;$)                                                          # Write the content of register rax in hexadecimal in big endian notation to the specified channel.
 {my ($channel, $end) = @_;                                                     # Channel, optional end byte
  @_ == 1 or @_ == 2 or confess "One or two parameters";
  my $hexTranslateTable = hexTranslateTable;
  $end //= 7;                                                                   # Default end byte

  my $s = Subroutine
   {SaveFirstFour;                                                              # Rax is a parameter
    Mov rdx, rax;                                                               # Content to be printed
    Mov rdi, 2;                                                                 # Length of a byte in hex

    for my $i((7-$end)..7)                                                      # Each byte
     {my $s = $bitsInByte*$i;
      Mov rax, rdx;
      Shl rax, $s;                                                              # Push selected byte high
      Shr rax, (RegisterSize(rax) - 1) * $bitsInByte;                           # Push select byte low
      Shl rax, 1;                                                               # Multiply by two because each entry in the translation table is two bytes long
      Lea rsi, "[$hexTranslateTable]";
      Add rax, rsi;
      PrintMemory($channel);                                                    # Print memory addressed by rax for length specified by rdi
      PrintString($channel, ' ') if $i % 2 and $i < 7;
     }
    RestoreFirstFour;
   } name => "PrintOutRaxInHexOn-$channel-$end";

  $s->call;
 }

sub PrintErrRaxInHex()                                                          # Write the content of register rax in hexadecimal in big endian notation to stderr.
 {@_ == 0 or confess;
  PrintRaxInHex($stderr);
 }

sub PrintErrRaxInHexNL()                                                        # Write the content of register rax in hexadecimal in big endian notation to stderr followed by a new line.
 {@_ == 0 or confess;
  PrintRaxInHex($stderr);
  PrintErrNL;
 }

sub PrintOutRaxInHex()                                                          # Write the content of register rax in hexadecimal in big endian notation to stout.
 {@_ == 0 or confess;
  PrintRaxInHex($stdout);
 }

sub PrintOutRaxInHexNL()                                                        # Write the content of register rax in hexadecimal in big endian notation to stdout followed by a new line.
 {@_ == 0 or confess;
  PrintRaxInHex($stdout);
  PrintOutNL;
 }

sub PrintRax_InHex($;$)                                                         # Write the content of register rax in hexadecimal in big endian notation to the specified channel replacing zero bytes with __.
 {my ($channel, $end) = @_;                                                     # Channel, optional end byte
  @_ == 1 or @_ == 2 or confess "One or two parameters";
  my $hexTranslateTable = hexTranslateTable;
  $end //= 7;                                                                   # Default end byte

  my $s = Subroutine
   {SaveFirstFour;                                                              # Rax is a parameter
    Mov rdx, rax;                                                               # Content to be printed
    Mov rdi, 2;                                                                 # Length of a byte in hex

    for my $i((7-$end)..7)                                                      # Each byte
     {my $s = $bitsInByte*$i;
      Mov rax, rdx;
      Shl rax, $s;                                                              # Push selected byte high
      Shr rax, (RegisterSize(rax) - 1) * $bitsInByte;                           # Push select byte low
      Cmp rax, 0;
      IfEq                                                                      # Print __ for zero bytes
      Then
       {PrintString($channel, "__");
       },
      Else                                                                      # Print byte in hexadecimal otherwise
       {Shl rax, 1;                                                             # Multiply by two because each entry in the translation table is two bytes long
        Lea rsi, "[$hexTranslateTable]";
        Add rax, rsi;
        PrintMemory($channel);                                                  # Print memory addressed by rax for length specified by rdi
       };
      PrintString($channel, ' ') if $i % 2 and $i < 7;
     }
    RestoreFirstFour;
   } name => "PrintOutRax_InHexOn-$channel-$end";

   $s->call;
 }

sub PrintErrRax_InHex()                                                         # Write the content of register rax in hexadecimal in big endian notation to stderr.
 {@_ == 0 or confess;
  PrintRax_InHex($stderr);
 }

sub PrintErrRax_InHexNL()                                                       # Write the content of register rax in hexadecimal in big endian notation to stderr followed by a new line.
 {@_ == 0 or confess;
  PrintRax_InHex($stderr);
  PrintErrNL;
 }

sub PrintOutRax_InHex()                                                         # Write the content of register rax in hexadecimal in big endian notation to stout.
 {@_ == 0 or confess;
  PrintRax_InHex($stdout);
 }

sub PrintOutRax_InHexNL()                                                       # Write the content of register rax in hexadecimal in big endian notation to stdout followed by a new line.
 {@_ == 0 or confess;
  PrintRax_InHex($stdout);
  PrintOutNL;
 }

sub PrintOutRaxInReverseInHex                                                   # Write the content of register rax to stderr in hexadecimal in little endian notation.
 {@_ == 0 or confess;
  Comment "Print Rax In Reverse In Hex";
  Push rax;
  Bswap rax;
  PrintOutRaxInHex;
  Pop rax;
 }

sub PrintOneRegisterInHex($$)                                                   # Print the named register as a hex string.
 {my ($channel, $r) = @_;                                                       # Channel to print on, register to print
  @_ == 2 or confess "Two parameters";

  my $s = Subroutine
   {if   ($r =~ m(\Ar))                                                         # General purpose register
     {if ($r =~ m(\Arax\Z))                                                     # General purpose register - rax
       {PrintRaxInHex($channel);
       }
      else                                                                      # General purpose register not rax
       {PushR rax;
        Mov rax, $r;
        PrintRaxInHex($channel);
        PopR;
       }
     }
    elsif ($r =~ m(\Ak))                                                        # Mask register
     {PushR rax;
      Kmovq rax, $r;
      PrintRaxInHex($channel);
      PopR;
     }
    elsif ($r =~ m(\Axmm))                                                      # Xmm register
     {PushR rax, $r, 7;
      Mov rax, 0b10;
      Kmovq k7, rax;
      Vpcompressq "$r\{k7}", $r;
      Vmovq rax, $r;
      PrintRaxInHex($channel);
      PopR;

      PrintString($channel, "  ");                                              # Separate blocks of bytes with a space
      PushR rax;
      Vmovq rax, $r;
      PrintRaxInHex($channel);
      PopR;
     }
    elsif ($r =~ m(\Aymm))                                                      # Ymm register
     {PushR rax, $r, 7;
      Mov rax, 0b1100;
      Kmovq k7, rax;
      Vpcompressq "$r\{k7}", $r;
      PrintOneRegisterInHex($channel, $r =~ s(\Ay) (x)r);                       # Upper half
      PopR;

      PrintString($channel, " - ");                                             # Separate blocks of bytes with a space

      PrintOneRegisterInHex($channel, $r =~ s(\Ay) (x)r);                       # Lower half
     }
    elsif ($r =~ m(\Azmm))                                                      # Zmm register
     {PushR rax, $r, 7;
      Mov rax, 0b11110000;
      Kmovq k7, rax;
      Vpcompressq "$r\{k7}", $r;
      PrintOneRegisterInHex($channel, $r =~ s(\Az) (y)r);                       # Upper half
      PopR;

      PrintString($channel, " + ");                                             # Separate blocks of bytes with a space
      PrintOneRegisterInHex($channel, $r =~ s(\Az) (y)r);                       # Lower half
     }
   } name => "PrintOneRegister${r}InHexOn$channel";                             # One routine per register printed

  PushR $r;
  $s->call;
  PopR;
 }

sub PrintErrOneRegisterInHex($)                                                 # Print the named register as a hex string on stderr.
 {my ($r) = @_;                                                                 # Register to print
  @_ == 1 or confess "One parameter";
  PrintOneRegisterInHex($stderr, $r)
 }

sub PrintErrOneRegisterInHexNL($)                                               # Print the named register as a hex string on stderr followed by new line.
 {my ($r) = @_;                                                                 # Register to print
  @_ == 1 or confess "One parameter";
  PrintOneRegisterInHex($stderr, $r);
  PrintErrNL;
 }

sub PrintOutOneRegisterInHex($)                                                 # Print the named register as a hex string on stdout.
 {my ($r) = @_;                                                                 # Register to print
  @_ == 1 or confess "One parameter";
  PrintOneRegisterInHex($stdout, $r)
 }

sub PrintOutOneRegisterInHexNL($)                                               # Print the named register as a hex string on stdout followed by new line.
 {my ($r) = @_;                                                                 # Register to print
  @_ == 1 or confess "One parameter";
  PrintOneRegisterInHex($stdout, $r);
  PrintOutNL;
 }

sub PrintRegisterInHex($@)                                                      # Print the named registers as hex strings.
 {my ($channel, @r) = @_;                                                       # Channel to print on, names of the registers to print
  @_ >= 2 or confess "Two or more parameters required";

  for my $r(map{registerNameFromNumber $_} @r)                                  # Each register to print
   {PrintString($channel,  sprintf("%6s: ", $r));                               # Register name
    PrintOneRegisterInHex $channel, $r;
    PrintNL($channel);
   }
 }

sub PrintErrRegisterInHex(@)                                                    # Print the named registers as hex strings on stderr.
 {my (@r) = @_;                                                                 # Names of the registers to print
  PrintRegisterInHex $stderr, @r;
 }

sub PrintOutRegisterInHex(@)                                                    # Print the named registers as hex strings on stdout.
 {my (@r) = @_;                                                                 # Names of the registers to print
  PrintRegisterInHex $stdout, @r;
 }

sub PrintOutRipInHex                                                            #P Print the instruction pointer in hex.
 {@_ == 0 or confess;
  my @regs = qw(rax);

  my $s = Subroutine
   {PushR @regs;
    my $l = Label;
    push @text, <<END;
$l:
END
    Lea rax, "[$l]";                                                            # Current instruction pointer
    PrintOutString "rip: ";
    PrintOutRaxInHex;
    PrintOutNL;
    PopR @regs;
   } name=> "PrintOutRipInHex";

  $s->call;
 }

sub PrintOutRflagsInHex                                                         #P Print the flags register in hex.
 {@_ == 0 or confess;
  my @regs = qw(rax);

  my $s = Subroutine
   {PushR @regs;
    Pushfq;
    Pop rax;
    PrintOutString "rfl: ";
    PrintOutRaxInHex;
    PrintOutNL;
    PopR @regs;
   } name=> "PrintOutRflagsInHex";

  $s->call;
 }

sub PrintOutRegistersInHex                                                      # Print the general purpose registers in hex.
 {@_ == 0 or confess "No parameters required";

  my $s = Subroutine
   {#PrintOutRipInHex;
    PrintOutRflagsInHex;

    my @regs = qw(rax);
    PushR @regs;

    my $w = registers_64();
    for my $r(sort @$w)
     {next if $r =~ m(rip|rflags|rbp|rsp);                                      # Modified by print routines so pointless to print
      if ($r eq rax)
       {Pop rax;
        Push rax
       }
      PrintOutString reverse(pad(reverse($r), 3)).": ";
      Mov rax, $r;
      PrintOutRaxInHex;
      PrintOutNL;
     }
    PopR @regs;
   } name=> "PrintOutRegistersInHex";

  $s->call;
 }

sub PrintErrZF                                                                  # Print the zero flag without disturbing it on stderr.
 {@_ == 0 or confess;

  Pushfq;
  IfNz Then {PrintErrStringNL "ZF=0"}, Else {PrintErrStringNL "ZF=1"};
  Popfq;
 }

sub PrintOutZF                                                                  # Print the zero flag without disturbing it on stdout.
 {@_ == 0 or confess "No parameters";

  Pushfq;
  IfNz Then {PrintOutStringNL "ZF=0"}, Else {PrintOutStringNL "ZF=1"};
  Popfq;
 }

#D2 Print hexadecimal                                                           # Print numbers in hexadecimal right justified in a field

sub PrintRightInHex($$$)                                                        # Print out a number in hex right justified in a field of specified width on the specified channel
 {my ($channel, $number, $width) = @_;                                          # Channel, number as a variable, width of output field as a variable
  @_ == 3 or confess "Three parameters required";

  $channel =~ m(\A(1|2)\Z) or confess "Invalid channel should be stderr or stdout";
  ref($number) =~ m(variable)i or confess "number must be a variable";
  ref($width)  =~ m(variable)i or confess "width must be a variable";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    PushR rax, rdi, r14, r15, xmm0;
    ClearRegisters xmm0;
    $$p{number}->setReg(14);

    K(loop => 16)->for(sub
     {Mov r15, r14;                                                             # Load xmm0 with hexadecimal digits
      And r15, 0xf;
      Cmp r15, 9;
      IfGt
      Then
       {Add r15, ord('A') - 10;
       },
      Else
       {Add r15, ord('0');
       };
      Pslldq xmm0, 1;
      Pinsrb xmm0, r15b, 0;
      Shr r14, 4;
     });

    Block    ##IMPROVE                                                          # Translate leading zeros to spaces
     {my ($end) = @_;
      for my $i(0..14)
       {Pextrb r15, xmm0, $i;
        Cmp r15b, ord('0');
        Jne $end;
        Mov r15, ord(' ');
        Pinsrb xmm0, r15b, $i;
       }
     };

    PushR xmm0;                                                                 # Print xmm0 within the width of the field
    Mov rax, rsp;
    $$p{width}->setReg(rdi);
    Add rax, 16;
    Sub rax, rdi;
    &PrintOutMemory();
    PopR;
    PopR;
   } name => "PrintRightInHex_${channel}",
     parameters=>[qw(width number)];

  $s->call(parameters => {number => $number, width=>$width});
 }

sub PrintErrRightInHex($$)                                                      # Write the specified variable in hexadecimal right justified in a field of specified width on stderr.
 {my ($number, $width) = @_;                                                    # Number as a variable, width of output field as a variable
  @_ == 2 or confess "Two parameters required";
  PrintRightInHex($stderr, $number, $width);
 }

sub PrintErrRightInHexNL($$)                                                    # Write the specified variable in hexadecimal right justified in a field of specified width on stderr followed by a new line.
 {my ($number, $width) = @_;                                                    # Number as a variable, width of output field as a variable
  @_ == 2 or confess "Two parameters required";
  PrintRightInHex($stderr, $number, $width);
  PrintErrNL;
 }

sub PrintOutRightInHex($$)                                                      # Write the specified variable in hexadecimal right justified in a field of specified width on stdout.
 {my ($number, $width) = @_;                                                    # Number as a variable, width of output field as a variable
  @_ == 2 or confess "Two parameters required";
  PrintRightInHex($stdout, $number, $width);
 }

sub PrintOutRightInHexNL($$)                                                    # Write the specified variable in hexadecimal right justified in a field of specified width on stdout followed by a new line.
 {my ($number, $width) = @_;                                                    # Number as a variable, width of output field as a variable
  @_ == 2 or confess "Two parameters required";
  PrintRightInHex($stdout, $number, $width);
  PrintOutNL;
 }

#D2 Print binary                                                                # Print numbers in binary right justified in a field

sub PrintRightInBin($$$)                                                        # Print out a number in hex right justified in a field of specified width on the specified channel
 {my ($channel, $number, $width) = @_;                                          # Channel, number as a variable, width of output field as a variable
  @_ == 3 or confess "Three parameters required";

  $channel =~ m(\A(1|2)\Z) or confess "Invalid channel should be stderr or stdout";
  ref($number) =~ m(variable)i or confess "number must be a variable";
  ref($width)  =~ m(variable)i or confess "width must be a variable";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    PushR rax, rdi, rsi, r14, r15;
    $$p{number}->setReg(rax);
    Mov rsi, rsp;
    my $bir = RegisterSize(rax) * $bitsInByte;
    Mov r14, rsi;
    Sub rsp, $bir;                                                              # Allocate space on the stack for the maximum length bit string written out as characters

    K(loop => $bir)->for(sub                                                    # Load bits onto stack as characters
     {Dec r14;
      Mov r15, rax;
      And r15, 1;
      Cmp r15, 0;
      IfNe
      Then
       {Mov "byte[r14]", ord('1');
       },
      Else
       {Mov "byte[r14]", ord('0');
       };
      Shr rax, 1;
     });

    K(loop => $bir)->for(sub                                                    # Replace leading zeros with spaces
     {my ($index, $start, $next, $end) = @_;
      Cmp "byte[r14]",ord('0');
      IfEq
      Then
       {Mov "byte[r14]", ord(' ');
       },
      Else
       {Jmp $end;
       };
      Inc r14;
     });

    Mov rax, rsp;                                                               # Write stack in a field of specified width
    $$p{width}->setReg(rdi);
    Add rax, $bir;
    Sub rax, rdi;
    PrintMemory($channel);
    Mov rsp, rsi;                                                               # Restore stack
    PopR;
   } name => "PrintRightInBin_${channel}",
     parameters=>[qw(width number)];

  $s->call(parameters => {number => $number, width=>$width});
 }

sub PrintErrRightInBin($$)                                                      # Write the specified variable in binary right justified in a field of specified width on stderr.
 {my ($number, $width) = @_;                                                    # Number as a variable, width of output field as a variable
  @_ == 2 or confess "Two parameters required";
  PrintRightInBin($stderr, $number, $width);
 }

sub PrintErrRightInBinNL($$)                                                    # Write the specified variable in binary right justified in a field of specified width on stderr followed by a new line.
 {my ($number, $width) = @_;                                                    # Number as a variable, width of output field as a variable
  @_ == 2 or confess "Two parameters required";
  PrintRightInBin($stderr, $number, $width);
  PrintErrNL;
 }

sub PrintOutRightInBin($$)                                                      # Write the specified variable in binary right justified in a field of specified width on stdout.
 {my ($number, $width) = @_;                                                    # Number as a variable, width of output field as a variable
  @_ == 2 or confess "Two parameters required";
  PrintRightInBin($stdout, $number, $width);
 }

sub PrintOutRightInBinNL($$)                                                    # Write the specified variable in binary right justified in a field of specified width on stdout followed by a new line.
 {my ($number, $width) = @_;                                                    # Number as a variable, width of output field as a variable
  @_ == 2 or confess "Two parameters required";
  PrintRightInBin($stdout, $number, $width);
  PrintOutNL;
 }

#D2 Print in decimal                                                            # Print numbers in decimal right justified in fields of specified width.

sub PrintRaxInDec($)                                                            # Print rax in decimal on the specified channel.
 {my ($channel) = @_;                                                           # Channel to write on
  @_ == 1 or confess "One parameter";

  my $s = Subroutine
   {PushR rax, rdi, rdx, r9, r10;
    Mov r9, 0;                                                                  # Number of decimal digits
    Mov r10, 10;                                                                # Base of number system
    my $convert = SetLabel;
      Mov rdx, 0;                                                               # Rdx must be clear to receive remainder
      Idiv r10;                                                                 # Remainder after integer division by 10
      Add rdx, 48;                                                              # Convert remainder to ascii
      Push rdx;                                                                 # Save remainder
      Inc r9;                                                                   # Number of digits
      Cmp rax, 0;
    Jnz $convert;

    Mov rdi, 1;                                                                 # Length of each write

    my $print = SetLabel;                                                       # Print digits
      Mov rax, rsp;
      PrintMemory($channel);
      Dec r9;                                                                   # Number of digits
      Pop rax;                                                                  # Remove digit from stack
    Jnz $print;

    PopR;
   } name => "PrintRaxInDec_$channel";

  $s->call;
 }

sub PrintOutRaxInDec                                                            # Print rax in decimal on stdout.
 {PrintRaxInDec($stdout);
 }

sub PrintOutRaxInDecNL                                                          # Print rax in decimal on stdout followed by a new line.
 {PrintOutRaxInDec;
  PrintOutNL;
 }

sub PrintErrRaxInDec                                                            # Print rax in decimal on stderr.
 {PrintRaxInDec($stderr);
 }

sub PrintErrRaxInDecNL                                                          # Print rax in decimal on stderr followed by a new line.
 {PrintErrRaxInDec;
  PrintErrNL;
 }

sub PrintRaxRightInDec($$)                                                      # Print rax in decimal right justified in a field of the specified width on the specified channel.
 {my ($width, $channel) = @_;                                                   # Width, channel

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    PushR rax, rdi, rdx, r9, r10;
    Mov r9, 0;                                                                  # Number of decimal digits
    Mov r10, 10;                                                                # Base of number system
    my $convert = SetLabel;
      Mov rdx, 0;                                                               # Rdx must be clear to receive remainder
      Idiv r10;                                                                 # Remainder after integer division by 10
      Add rdx, 48;                                                              # Convert remainder to ascii
      Push rdx;                                                                 # Save remainder
      Inc r9;                                                                   # Number of digits
      Cmp rax, 0;
    Jnz $convert;

    Mov rdi, 1;                                                                 # Length of each write
    $$p{width}->setReg(10);                                                     # Pad to this width if necessary
    Cmp r9, r10;
    IfLt
    Then                                                                        # Padding required
     {(V(width => r10) - V(actual => r9))->spaces($channel);
     };

    my $print = SetLabel;                                                       # Print digits
      Mov rax, rsp;
      PrintMemory($channel);
      Dec r9;                                                                   # Number of digits
      Pop rax;                                                                  # Remove digit from stack
    Jnz $print;

    PopR;
   } parameters=>[qw(width)], name => "PrintRaxRightInDec_${channel}";

  $s->call(parameters=>{width => $width});
 }

sub PrintErrRaxRightInDec($)                                                    # Print rax in decimal right justified in a field of the specified width on stderr.
 {my ($width) = @_;                                                             # Width
  PrintRaxRightInDec($width, $stderr);
 }

sub PrintErrRaxRightInDecNL($)                                                  # Print rax in decimal right justified in a field of the specified width on stderr followed by a new line.
 {my ($width) = @_;                                                             # Width
  PrintRaxRightInDec($width, $stderr);
  PrintErrNL;
 }

sub PrintOutRaxRightInDec($)                                                    # Print rax in decimal right justified in a field of the specified width on stdout.
 {my ($width) = @_;                                                             # Width
  PrintRaxRightInDec($width, $stdout);
 }

sub PrintOutRaxRightInDecNL($)                                                  # Print rax in decimal right justified in a field of the specified width on stdout followed by a new line.
 {my ($width) = @_;                                                             # Width
  PrintRaxRightInDec($width, $stdout);
  PrintOutNL;
 }

sub PrintRaxAsText($)                                                           # Print the string in rax on the specified channel.
 {my ($channel) = @_;                                                           # Channel to write on
  @_ == 1 or confess "One parameter";

  my $w = RegisterSize rax;
  PushR rdi, rdx, rax;
  Lzcnt rdi, rax;
  Shr rdi, 3;
  Mov rdx, rdi;
  Mov rdi, 8;
  Sub rdi, rdx;

  Mov rax, rsp;
  PrintMemory($channel);
  PopR;
 }

sub PrintOutRaxAsText                                                           # Print rax as text on stdout.
 {PrintRaxAsText($stdout);
 }

sub PrintOutRaxAsTextNL                                                         # Print rax as text on stdout followed by a new line.
 {PrintRaxAsText($stdout);
  PrintOutNL;
 }

sub PrintErrRaxAsText                                                           # Print rax as text on stderr.
 {PrintRaxAsText($stderr);
 }

sub PrintErrRaxAsTextNL                                                         # Print rax as text on stderr followed by a new line.
 {PrintRaxAsText($stderr);
  PrintOutNL;
 }

sub PrintRaxAsChar($)                                                           # Print the ascii character in rax on the specified channel.
 {my ($channel) = @_;                                                           # Channel to write on
  @_ == 1 or confess "One parameter";

  PushR rdi, rax;
  Mov rax, rsp;
  Mov rdi, 1;
  PrintMemory($channel);
  PopR;
 }

sub PrintOutRaxAsChar                                                           # Print the character in on stdout.
 {PrintRaxAsChar($stdout);
 }

sub PrintOutRaxAsCharNL                                                         # Print the character in on stdout followed by a new line.
 {PrintRaxAsChar($stdout);
  PrintOutNL;
 }

sub PrintErrRaxAsChar                                                           # Print the character in on stderr.
 {PrintRaxAsChar($stderr);
 }

sub PrintErrRaxAsCharNL                                                         # Print the character in on stderr followed by a new line.
 {PrintRaxAsChar($stderr);
  PrintOutNL;
 }

#D1 Variables                                                                   # Variable definitions and operations

#D2 Definitions                                                                 # Variable definitions

sub Variable($;$%)                                                              # Create a new variable with the specified name initialized via an optional expression.
 {my ($name, $expr, %options) = @_;                                             # Name of variable, optional expression initializing variable, options
  my $size   = 3;                                                               # Size  of variable in bytes as a power of 2
  my $width  = 2**$size;                                                        # Size of variable in bytes
  my $const  = $options{constant}  // 0;                                        # Constant
  my $ref    = $options{reference} // 0;                                        # Reference

  $ref and $const and confess "Reference to constant";

  my $label;
  if ($const)                                                                   # Constant variable
   {defined($expr) or confess "Value required for constant";
    $expr =~ m(r) and confess
     "Cannot use register expression $expr to initialize a constant";
    RComment qq(Constant name: "$name", value $expr);
    $label = Rq($expr);
   }
  else                                                                          # Local variable: Position on stack of variable
   {my $stack = ++$VariableStack[-1];
    $label = "rbp-8*($stack)";

    if (defined $expr)                                                          # Initialize variable if an initializer was supplied
     {if ($Registers{$expr} and $expr =~ m(\Ar))                                # Expression is ready to go
       {Mov "[$label]", $expr;
       }
      else                                                                      # Transfer expression
       {PushR 15;
        Mov r15, $expr;
        Mov "[$label]", r15;
        PopR;
       }
     }
   }

  genHash(__PACKAGE__."::Variable",                                             # Variable definition
    constant  => $const,                                                        # Constant if true
    expr      => $expr,                                                         # Expression that initializes the variable
    label     => $label,                                                        # Address in memory
    name      => $name,                                                         # Name of the variable
#    level     => scalar @VariableStack,                                        # Lexical level
    reference => $options{reference},                                           # Reference to another variable
#    width     => RegisterSize(rax),                                            # Size of the variable in bytes
   );
 }

#sub G(*;$%)                                                                    # Define a global variable. Global variables with the same name are not necessarily the same variable.  Two global variables are identical iff they have have the same label field.
# {my ($name, $expr, %options) = @_;                                            # Name of variable, initializing expression, options
#  &Variable($name, $expr, global => 1, %options);
# }

sub K($$)                                                                       # Define a constant variable.
 {my ($name, $expr) = @_;                                                       # Name of variable, initializing expression
  &Variable(@_, constant => 1)
 }

sub R(*)                                                                        # Define a reference variable.
 {my ($name) = @_;                                                              # Name of variable
  my $r = &Variable($name);                                                     # The referring variable is 64 bits wide
  $r->reference = 1;                                                            # Mark variable as a reference
  $r                                                                            # Size of the referenced variable
 }

sub V($$)                                                                       # Define a variable.
 {my ($name, $expr) = @_;                                                       # Name of variable, initializing expression
  &Variable(@_)
 }

#D2 Print variables                                                             # Print the values of variables or the memory addressed by them

sub Nasm::X86::Variable::dump($$$;$$)                                           #P Dump the value of a variable to the specified channel adding an optional title and new line if requested.
 {my ($left, $channel, $newLine, $title1, $title2) = @_;                        # Left variable, channel, new line required, optional leading title, optional trailing title
  @_ >= 3 or confess;
  PushR rax, rdi;
  my $label = $left->label;                                                     # Address in memory
  Mov rax, "[$label]";
  Mov rax, "[rax]" if $left->reference;
  PrintString  ($channel, $title1//$left->name.": ") unless defined($title1) && $title1 eq '';
  PrintRaxInHex($channel);
  PrintString  ($channel, $title2) if defined $title2;
  PrintNL      ($channel) if $newLine;
  PopR;
 }

sub Nasm::X86::Variable::err($;$$)                                              # Dump the value of a variable on stderr.
 {my ($left, $title1, $title2) = @_;                                            # Left variable, optional leading title, optional trailing title
  $left->dump($stderr, 0, $title1, $title2);
 }

sub Nasm::X86::Variable::out($;$$)                                              # Dump the value of a variable on stdout.
 {my ($left, $title1, $title2) = @_;                                            # Left variable, optional leading title, optional trailing title
  $left->dump($stdout, 0, $title1, $title2);
 }

sub Nasm::X86::Variable::errNL($;$$)                                            # Dump the value of a variable on stderr and append a new line.
 {my ($left, $title1, $title2) = @_;                                            # Left variable, optional leading title, optional trailing title
  $left->dump($stderr, 1, $title1, $title2);
 }

sub Nasm::X86::Variable::d($;$$)                                                # Dump the value of a variable on stderr and append a new line.
 {my ($left, $title1, $title2) = @_;                                            # Left variable, optional leading title, optional trailing title
  $left->dump($stderr, 1, $title1, $title2);
 }

sub Nasm::X86::Variable::outNL($;$$)                                            # Dump the value of a variable on stdout and append a new line.
 {my ($left, $title1, $title2) = @_;                                            # Left variable, optional leading title, optional trailing title
  $left->dump($stdout, 1, $title1, $title2);
 }

sub Nasm::X86::Variable::debug($)                                               # Dump the value of a variable on stdout with an indication of where the dump came from.
 {my ($left) = @_;                                                              # Left variable
  PushR rax, rdi;
  Mov rax, $left->label;                                                        # Address in memory
  Mov rax, "[rax]";
  &PrintErrString(pad($left->name, 32).": ");
  &PrintErrRaxInHex();
  my ($p, $f, $l) = caller(0);                                                  # Position of caller in file
  &PrintErrString("               at $f line $l");
  &PrintErrNL();
  PopR;
 }

#D3 Decimal representation                                                      # Print out a variable as a decimal number

sub Nasm::X86::Variable::errInDec($;$$)                                         # Dump the value of a variable on stderr in decimal.
 {my ($number, $title1, $title2) = @_;                                          # Number as variable, optional leading title, optional trailing title
  PrintErrString($title1 // $number->name.": ");
  PushR rax;
  $number->setReg(rax);
  PrintRaxInDec($stderr);
  PopR;
  PrintErrString($title2) if $title2;
 }

sub Nasm::X86::Variable::errInDecNL($;$$)                                       # Dump the value of a variable on stderr in decimal followed by a new line.
 {my ($number, $title1, $title2) = @_;                                          # Number as variable, optional leading title, optional trailing title
  $number->errInDec($title1, $title2);
  PrintErrNL;
 }

sub Nasm::X86::Variable::outInDec($;$$)                                         # Dump the value of a variable on stdout in decimal.
 {my ($number, $title1, $title2) = @_;                                          # Number as variable, optional leading title, optional trailing title
  PrintOutString($title1 // $number->name.": ");
  PushR rax;
  $number->setReg(rax);
  PrintRaxInDec($stdout);
  PopR;
  PrintOutString($title2) if $title2;
 }

sub Nasm::X86::Variable::outInDecNL($;$$)                                       # Dump the value of a variable on stdout in decimal followed by a new line.
 {my ($number, $title1, $title2) = @_;                                          # Number as variable, optional leading title, optional trailing title
  $number->outInDec($title1, $title2);
  PrintOutNL;
 }

#D3 Decimal representation right justified                                      # Print out a variable as a decimal number right adjusted in a field of specified width

sub Nasm::X86::Variable::rightInDec($$$)                                        # Dump the value of a variable on the specified channel as a decimal  number right adjusted in a field of specified width.
 {my ($number, $channel, $width) = @_;                                          # Number as variable, channel, width
  PushR rax;
  $number->setReg(rax);
  PrintRaxRightInDec($width, $channel);
  PopR;
 }

sub Nasm::X86::Variable::errRightInDec($$)                                      # Dump the value of a variable on stderr as a decimal number right adjusted in a field of specified width.
 {my ($number, $width) = @_;                                                    # Number, width
  $number->rightInDec($stdout, $width);
 }

sub Nasm::X86::Variable::errRightInDecNL($$)                                    # Dump the value of a variable on stderr as a decimal number right adjusted in a field of specified width followed by a new line.
 {my ($number, $width) = @_;                                                    # Number, width
  $number->rightInDec($stdout, $width);
  PrintErrNL;
 }

sub Nasm::X86::Variable::outRightInDec($$)                                      # Dump the value of a variable on stdout as a decimal number right adjusted in a field of specified width.
 {my ($number, $width) = @_;                                                    # Number, width
  $number->rightInDec($stdout, $width);
 }

sub Nasm::X86::Variable::outRightInDecNL($$)                                    # Dump the value of a variable on stdout as a decimal number right adjusted in a field of specified width followed by a new line.
 {my ($number, $width) = @_;                                                    # Number, width
  $number->rightInDec($stdout, $width);
  PrintOutNL;
 }

#D2 Hexadecimal representation, right justified                                 # Print number variables in hexadecimal right justified in fields of specified width.

sub Nasm::X86::Variable::rightInHex($$$)                                        # Write the specified variable number in hexadecimal right justified in a field of specified width to the specified channel.
 {my ($number, $channel, $width) = @_;                                          # Number to print as a variable, channel to print on, width of output field
  @_ == 3 or confess "Three parameters";
  PrintRightInHex($channel, $number, $width);
 }

sub Nasm::X86::Variable::errRightInHex($$)                                      # Write the specified variable number in hexadecimal right justified in a field of specified width to stderr
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInHex($stderr, $number, $width);
 }

sub Nasm::X86::Variable::errRightInHexNL($$)                                    # Write the specified variable number in hexadecimal right justified in a field of specified width to stderr followed by a new line
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInHex($stderr, $number, $width);
  PrintErrNL;
 }

sub Nasm::X86::Variable::outRightInHex($$)                                      # Write the specified variable number in hexadecimal right justified in a field of specified width to stdout
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInHex($stdout, $number, $width);
 }

sub Nasm::X86::Variable::outRightInHexNL($$)                                    # Write the specified variable number in hexadecimal right justified in a field of specified width to stdout followed by a new line
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInHex($stdout, $number, $width);
  PrintOutNL;
 }

#D2 Binary representation, right justified                                      # Print number variables in binary right justified in fields of specified width.

sub Nasm::X86::Variable::rightInBin($$$)                                        # Write the specified variable number in binary right justified in a field of specified width to the specified channel.
 {my ($number, $channel, $width) = @_;                                          # Number to print as a variable, channel to print on, width of output field
  @_ == 3 or confess "Three parameters";
  PrintRightInBin($channel, $number, $width);
 }

sub Nasm::X86::Variable::errRightInBin($$)                                      # Write the specified variable number in binary right justified in a field of specified width to stderr
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInBin($stderr, $number, $width);
 }

sub Nasm::X86::Variable::errRightInBinNL($$)                                    # Write the specified variable number in binary right justified in a field of specified width to stderr followed by a new line
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInBin($stderr, $number, $width);
  PrintErrNL;
 }

sub Nasm::X86::Variable::outRightInBin($$)                                      # Write the specified variable number in binary right justified in a field of specified width to stdout
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInBin($stdout, $number, $width);
 }

sub Nasm::X86::Variable::outRightInBinNL($$)                                    # Write the specified variable number in binary right justified in a field of specified width to stdout followed by a new line
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInBin($stdout, $number, $width);
  PrintOutNL;
 }

#D3 Spaces                                                                      # Print out a variable number of spaces

sub Nasm::X86::Variable::spaces($$)                                             # Print the specified number of spaces to the specified channel.
 {my ($count, $channel) = @_;                                                   # Number of spaces, channel
  @_ == 2 or confess "Two parameters";
  $count->for(sub {PrintSpace $channel});
 }

sub Nasm::X86::Variable::errSpaces($)                                           # Print the specified number of spaces to stderr.
 {my ($count) = @_;                                                             # Number of spaces
  @_ == 1 or confess "One parameter";
  $count->spaces($stderr);
 }

sub Nasm::X86::Variable::outSpaces($)                                           # Print the specified number of spaces to stdout.
 {my ($count) = @_;                                                             # Number of spaces
  @_ == 1 or confess "One parameter";
  $count->spaces($stdout);
 }

#D3 C style zero terminated strings                                             # Print out C style zero terminated strings.

sub Nasm::X86::Variable::errCString($)                                          # Print a zero terminated C style string addressed by a variable on stderr.
 {my ($string) = @_;                                                            # String
  @_ == 1 or confess "One parameter";
  PrintCString($stderr, $string);
 }

sub Nasm::X86::Variable::errCStringNL($)                                        # Print a zero terminated C style string addressed by a variable on stderr followed by a new line.
 {my ($string) = @_;                                                            # String
  @_ == 1 or confess "One parameter";
  $string->errCString($string);
  PrintErrNL;
 }

sub Nasm::X86::Variable::outCString($)                                          # Print a zero terminated C style string addressed by a variable on stdout.
 {my ($string) = @_;                                                            # String
  @_ == 1 or confess "One parameter";
  PrintCString($stdout, $string);
 }

sub Nasm::X86::Variable::outCStringNL($)                                        # Print a zero terminated C style string addressed by a variable on stdout followed by a new line.
 {my ($string) = @_;                                                            # String
  @_ == 1 or confess "One parameter";
  $string->outCString;
  PrintOutNL;
 }

#D2 Addressing                                                                  # Create references to variables and dereference variables

sub Nasm::X86::Variable::address($)                                             # Create a variable that contains the address of another variable
 {my ($source) = @_;                                                            # Source variable
  @_ == 1 or confess "One parameter";
  Lea rdi, $source->addressExpr;                                                # Address of variable
  V("addr ".$source->name => rdi)                                               # Return variable containing address of source
 }

sub Nasm::X86::Variable::dereference($)                                         # Create a variable that contains the contents of the variable addressed by the specified variable
 {my ($address) = @_;                                                           # Source variable
  @_ == 1 or confess "One parameter";
  $address->setReg(rdi);                                                        # Address of referenced variable
  Mov rdi, "[rdi]";                                                             # Content of referenced variable
  V "deref ".$address->name => rdi                                              # Return variable containing content of addressed variable
 }

sub Nasm::X86::Variable::update($$)                                             # Update the content of the addressed variable with the content of the specified variable
 {my ($address, $content) = @_;                                                 # Source variable, content
  @_ == 2 or confess "Two parameters";
  PushR 14, 15;
  $address->setReg(14);                                                         # Address of referenced variable
  $content->setReg(15);                                                         # Content
  Mov "[r14]", r15;                                                             # Move content to addressed variable;
  PopR;
 }

sub addressAndLengthOfConstantStringAsVariables($)                              # Return the address and length of a constant string as two variables.
 {my ($string) = @_;                                                            # Constant string
  use bytes;
  my $L = length($string);
  my $l = K length => $L;
  return ($l, $l) unless $L;
  my $s = V string => Rutf8 $string;
  ($s, $l)
 }

#D2 Operations                                                                  # Variable operations

if (1)                                                                          # Define operator overloading for Variables
 {package Nasm::X86::Variable;
  use overload
    '+'  => \&add,
    '-'  => \&sub,
    '*'  => \&times,
    '/'  => \&divide,
    '%'  => \&mod,
   '=='  => \&eq,
   '!='  => \&ne,
   '>='  => \&ge,
    '>'  => \&gt,
   '<='  => \&le,
   '<'   => \&lt,
   '++'  => \&inc,
   '--'  => \&dec,
   '""'  => \&str,
#  '&'   => \&and,                                                              # We use the zero flag as the bit returned by a Boolean operation so we cannot implement '&' or '|' which were previously in use because '&&' and '||' and "and" and "or" are all disallowed in Perl operator overloading.
#  '|'   => \&or,
   '+='  => \&plusAssign,
   '-='  => \&minusAssign,
   '='   => \&equals,
   '<<'  => \&shiftLeft,
   '>>'  => \&shiftRight,
  '!'    => \&not,
 }

sub Nasm::X86::Variable::call($)                                                # Execute the call instruction for a target whose address is held in the specified variable.
 {my ($target) = @_;                                                            # Variable containing the address of the code to call
  $target->setReg(rdi);                                                         # Address of code to call
  Call rdi;                                                                     # Call referenced code
 }

sub Nasm::X86::Variable::addressExpr($;$)                                       # Create a register expression to address an offset form a variable
 {my ($left, $offset) = @_;                                                     # Left variable, optional offset
  my $o = $offset ? "+$offset" : "";
  "[".$left-> label."$o]"
 }

sub Nasm::X86::Variable::clone($$)                                              # Clone a variable to make a new variable.
 {my ($variable, $name) = @_;                                                   # Variable to clone, new name for variable
  @_ == 2 or confess "Two parameters";
  my $c = V($name => undef);                                                    # Use supplied name or fall back on existing name
  $c->copy($variable);                                                          # Copy into created variable
  $c                                                                            # Return the clone of the variable
 }

sub Nasm::X86::Variable::copy($$)                                               # Copy one variable into another.
 {my ($left, $right) = @_;                                                      # Left variable, right variable
  @_ == 2 or confess "Two parameters";

  my $l = $left ->addressExpr;
  my $r = ref($right) ? $right->addressExpr : $right;                           # Variable address or register expression (which might in fact be a constant)

  Mov rdi, $r;                                                                  # Load right hand side

  if (ref($right) and $right->reference)                                        # Dereference a reference
   {Mov rdi, "[rdi]";
   }

  if ($left ->reference)                                                        # Copy a reference
   {Mov rsi, $l;
    Mov "[rsi]", rdi;
   }
  else                                                                          # Copy a non reference
   {Mov $l, rdi;
   }
  $left                                                                         # Return the variable on the left now that it has had the right hand side copied into it.
 }

sub Nasm::X86::Variable::copyRef($$)                                            # Copy a reference to a variable.
 {my ($left, $right) = @_;                                                      # Left variable, right variable
  @_ == 2 or confess "Two parameters";

  $left->reference  or confess "Left hand side must be a reference";

  my $l = $left ->addressExpr;
  my $r = $right->addressExpr;

  if ($right->reference)                                                        # Right is a reference so we copy its value to create a new reference to the original data
   {Mov rdi, $r;
   }
  else                                                                          # Right is not a reference so we copy its address to make a reference to the data
   {Lea rdi, $r;
   }
  Mov $l, rdi;                                                                  # Save value of address in left

  $left;                                                                        # Chain
 }

sub Nasm::X86::Variable::copyZF($)                                              # Copy the current state of the zero flag into a variable.
 {my ($var) = @_;                                                               # Variable
  @_ == 1 or confess "One parameter";

  my $a = $var->addressExpr;                                                    # Address of the variable

  PushR rax;
  Lahf;                                                                         # Save flags to ah: (SF:ZF:0:AF:0:PF:1:CF)
  Shr ah, 6;                                                                    # Put zero flag in bit zero
  And ah, 1;                                                                    # Isolate zero flag
  Mov $a, ah;                                                                   # Save zero flag
  PopR;
 }

sub Nasm::X86::Variable::copyZFInverted($)                                      # Copy the opposite of the current state of the zero flag into a variable.
 {my ($var) = @_;                                                               # Variable
  @_ == 1 or confess "One parameter";

  my $a = $var->addressExpr;                                                    # Address of the variable

  PushR rax, 15;
  Lahf;                                                                         # Save flags to ah: (SF:ZF:0:AF:0:PF:1:CF)
  Shr ah, 6;                                                                    # Put zero flag in bit zero
  Not ah;                                                                       # Invert zero flag
  And ah, 1;                                                                    # Isolate zero flag
  if ($var->reference)                                                          # Dereference and save
   {PushR rdx;
    Mov rdx, $a;
    Mov "[rdx]", ah;                                                            # Save zero flag
    PopR rdx;
   }
  else                                                                          # Save without dereferencing
   {Mov $a, ah;                                                                 # Save zero flag
   }
  PopR;
 }

sub Nasm::X86::Variable::equals($$$)                                            # Equals operator.
 {my ($op, $left, $right) = @_;                                                 # Operator, left variable,  right variable
  $op
 }

sub Nasm::X86::Variable::assign($$$)                                            # Assign to the left hand side the value of the right hand side.
 {my ($left, $op, $right) = @_;                                                 # Left variable, operator, right variable
  $left->constant and confess "cannot assign to a constant";

  Comment "Variable assign";
  PushR 14, 15;
  Mov r14, $left ->addressExpr;
  if ($left->reference)                                                         # Dereference left if necessary
   {Mov r14, "[r14]";
   }
  if (!ref($right))                                                             # Load right constant
   {Mov r15, $right;
   }
  else                                                                          # Load right variable
   {Mov r15, $right->addressExpr;
    if ($right->reference)                                                      # Dereference right if necessary
     {Mov r15, "[r15]";
     }
   }
  &$op(r14, r15);
  if ($left->reference)                                                         # Store in reference on left if necessary
   {PushR 13;
    Mov r13, $left->addressExpr;
    Mov "[r13]", r14;
    PopR;
   }
  else                                                                          # Store in variable
   {Mov $left ->addressExpr, r14;
   }
  PopR;

  $left;
 }

sub Nasm::X86::Variable::plusAssign($$)                                         # Implement plus and assign.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  $left->assign(\&Add, $right);
 }

sub Nasm::X86::Variable::minusAssign($$)                                        # Implement minus and assign.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  $left->assign(\&Sub, $right);
 }

sub Nasm::X86::Variable::arithmetic($$$$)                                       # Return a variable containing the result of an arithmetic operation on the left hand and right hand side variables.
 {my ($op, $name, $left, $right) = @_;                                          # Operator, operator name, Left variable,  right variable

  my $l = $left ->addressExpr;
  my $r = ref($right) ? $right->addressExpr : $right;                           # Right can be either a variable reference or a constant

  Comment "Arithmetic Start";
  PushR 14, 15;
  Mov r15, $l;
  if ($left->reference)                                                         # Dereference left if necessary
   {Mov r15, "[r15]";
   }
  Mov r14, $r;
  if (ref($right) and $right->reference)                                        # Dereference right if necessary
   {Mov r14, "[r14]";
   }
  &$op(r15, r14);
  my $v = V(join(' ', '('.$left->name, $name, (ref($right) ? $right->name : $right).')'), r15);
  PopR;
  Comment "Arithmetic End";

  return $v;
 }

sub Nasm::X86::Variable::add($$)                                                # Add the right hand variable to the left hand variable and return the result as a new variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::arithmetic(\&Add, q(add), $left, $right);
 }

sub Nasm::X86::Variable::sub($$)                                                # Subtract the right hand variable from the left hand variable and return the result as a new variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::arithmetic(\&Sub, q(sub), $left, $right);
 }

sub Nasm::X86::Variable::times($$)                                              # Multiply the left hand variable by the right hand variable and return the result as a new variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::arithmetic(\&Imul, q(times), $left, $right);
 }

sub Nasm::X86::Variable::division($$$)                                          # Return a variable containing the result or the remainder that occurs when the left hand side is divided by the right hand side.
 {my ($op, $left, $right) = @_;                                                 # Operator, Left variable,  right variable

  my $l = $left ->addressExpr;
  my $r = ref($right) ? $right->addressExpr : $right;                           # Right can be either a variable reference or a constant
  PushR rax, rdx, 15;
  Mov rax, $l;
  Mov rax, "[rax]" if $left->reference;
  Mov r15, $r;
  Mov r15, "[r15]" if ref($right) and $right->reference;
  Idiv r15;
  my $v = V(join(' ', '('.$left->name, $op, (ref($right) ? $right->name : '').')'), $op eq "%" ? rdx : rax);
  PopR;
  $v;
 }

sub Nasm::X86::Variable::divide($$)                                             # Divide the left hand variable by the right hand variable and return the result as a new variable.
 {my ($left, $right) = @_;                                                      # Left variable, right variable
  Nasm::X86::Variable::division("/", $left, $right);
 }

sub Nasm::X86::Variable::mod($$)                                                # Divide the left hand variable by the right hand variable and return the remainder as a new variable.
 {my ($left, $right) = @_;                                                      # Left variable, right variable
  Nasm::X86::Variable::division("%", $left, $right);
 }

sub Nasm::X86::Variable::shiftLeft($$)                                          # Shift the left hand variable left by the number of bits specified in the right hand variable and return the result as a new variable.
 {my ($left, $right) = @_;                                                      # Left variable, right variable
  PushR rcx, 15;
  $left ->setReg(15);                                                           # Value to shift
  confess "Variable required not $right" unless ref($right);
  $right->setReg(rcx);                                                          # Amount to shift
  Shl r15, cl;                                                                  # Shift
  my $r = V "shift left" => r15;                                                # Save result in a new variable
  PopR;
  $r
 }

sub Nasm::X86::Variable::shiftRight($$)                                         # Shift the left hand variable right by the number of bits specified in the right hand variable and return the result as a new variable.
 {my ($left, $right) = @_;                                                      # Left variable, right variable
  PushR rcx, 15;
  $left ->setReg(15);                                                           # Value to shift
  confess "Variable required not $right" unless ref($right);
  $right->setReg(rcx);                                                          # Amount to shift
  Shr r15, cl;                                                                  # Shift
  my $r = V "shift right" => r15;                                               # Save result in a new variable
  PopR;
  $r
 }

sub Nasm::X86::Variable::not($)                                                 # Form two complement of left hand side and return it as a variable.
 {my ($left) = @_;                                                              # Left variable
  $left->setReg(rdi);                                                           # Value to negate
  Not rdi;                                                                      # Two's complement
  V "neg" => rdi;                                                               # Save result in a new variable
 }

sub Nasm::X86::Variable::boolean($$$$)                                          # Combine the left hand variable with the right hand variable via a boolean operator.
 {my ($sub, $op, $left, $right) = @_;                                           # Operator, operator name, Left variable,  right variable

  !ref($right) or ref($right) =~ m(Variable) or confess "Variable expected";
  my $r = ref($right) ? $right->addressExpr : $right;                           # Right can be either a variable reference or a constant

  Comment "Boolean Arithmetic Start";
  PushR 15;

  Mov r15, $left ->addressExpr;
  if ($left->reference)                                                         # Dereference left if necessary
   {Mov r15, "[r15]";
   }
  if (ref($right) and $right->reference)                                        # Dereference on right if necessary
   {PushR 14;
    Mov r14, $right ->addressExpr;
    Mov r14, "[r14]";
    Cmp r15, r14;
    PopR;
   }
  elsif (ref($right))                                                           # Variable but not a reference on the right
   {Cmp r15, $right->addressExpr;
   }
  else                                                                          # Constant on the right
   {Cmp r15, $right;
   }

  &$sub(sub {Mov  r15, 1}, sub {Mov  r15, 0});
  my $v = V(join(' ', '('.$left->name, $op, (ref($right) ? $right->name : '').')'), r15);

  PopR;
  Comment "Boolean Arithmetic end";

  $v
 }

sub Nasm::X86::Variable::booleanZF($$$$)                                        # Combine the left hand variable with the right hand variable via a boolean operator and indicate the result by setting the zero flag if the result is true.
 {my ($sub, $op, $left, $right) = @_;                                           # Operator, operator name, Left variable,  right variable

  !ref($right) or ref($right) =~ m(Variable) or confess "Variable expected";
  my $r = ref($right) ? $right->addressExpr : $right;                           # Right can be either a variable reference or a constant

  Comment "Boolean ZF Arithmetic Start";
  PushR 15;

  Mov r15, $left ->addressExpr;
  if ($left->reference)                                                         # Dereference left if necessary
   {Mov r15, "[r15]";
   }
  if (ref($right) and $right->reference)                                        # Dereference on right if necessary
   {PushR 14;
    Mov r14, $right ->addressExpr;
    Mov r14, "[r14]";
    Cmp r15, r14;
    PopR;
   }
  elsif (ref($right))                                                           # Variable but not a reference on the right
   {Cmp r15, $right->addressExpr;
   }
  else                                                                          # Constant on the right
   {Cmp r15, $right;
   }

  &$sub(sub {Cmp rsp, rsp}, sub {Test rsp, rsp});

  PopR;
  Comment "Boolean ZF Arithmetic end";

  V(empty => undef);                                                            # Return an empty variable so that If regenerates the follow on code
 }

sub Nasm::X86::Variable::booleanC($$$$)                                         # Combine the left hand variable with the right hand variable via a boolean operator using a conditional move instruction.
 {my ($cmov, $op, $left, $right) = @_;                                          # Conditional move instruction name, operator name, Left variable,  right variable

  !ref($right) or ref($right) =~ m(Variable) or confess "Variable expected";
  my $r = ref($right) ? $right->addressExpr : $right;                           # Right can be either a variable reference or a constant

  PushR 15;
  Mov r15, $left ->addressExpr;
  if ($left->reference)                                                         # Dereference left if necessary
   {Mov r15, "[r15]";
   }
  if (ref($right) and $right->reference)                                        # Dereference on right if necessary
   {PushR 14;
    Mov r14, $right ->addressExpr;
    Mov r14, "[r14]";
    Cmp r15, r14;
    PopR;
   }
  elsif (ref($right))                                                           # Variable but not a reference on the right
   {Cmp r15, $right->addressExpr;
   }
  else                                                                          # Constant on the right
   {Cmp r15, $right;
   }

  Mov r15, 1;                                                                   # Place a one below the stack
  my $w = RegisterSize r15;
  Mov "[rsp-$w]", r15;
  Mov r15, 0;                                                                   # Assume the result was false
  &$cmov(r15, "[rsp-$w]");                                                      # Indicate true result
  my $v = V(join(' ', '('.$left->name, $op, (ref($right) ? $right->name : '').')'), r15);
  PopR;

  $v
 }

sub Nasm::X86::Variable::eq($$)                                                 # Check whether the left hand variable is equal to the right hand variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanZF(\&IfEq, q(eq), $left, $right);
 }

sub Nasm::X86::Variable::ne($$)                                                 # Check whether the left hand variable is not equal to the right hand variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanZF(\&IfNe, q(ne), $left, $right);
 }

sub Nasm::X86::Variable::ge($$)                                                 # Check whether the left hand variable is greater than or equal to the right hand variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanZF(\&IfGe, q(ge), $left, $right);
 }

sub Nasm::X86::Variable::gt($$)                                                 # Check whether the left hand variable is greater than the right hand variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanZF(\&IfGt, q(gt), $left, $right);
 }

sub Nasm::X86::Variable::le($$)                                                 # Check whether the left hand variable is less than or equal to the right hand variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanZF(\&IfLe, q(le), $left, $right);
 }

sub Nasm::X86::Variable::lt($$)                                                 # Check whether the left hand variable is less than the right hand variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanZF(\&IfLt, q(lt), $left, $right);
 }

sub Nasm::X86::Variable::isRef($)                                               # Check whether the specified  variable is a reference to another variable.
 {my ($variable) = @_;                                                          # Variable
  my $n = $variable->name;                                                      # Variable name
  $variable->reference
 }

sub Nasm::X86::Variable::setReg($$)                                             # Set the named registers from the content of the variable.
 {my ($variable, $register) = @_;                                               # Variable, register to load

  my $r = registerNameFromNumber $register;
  if (CheckMaskRegister($r))                                                    # Mask register is being set
   {if ($variable->isRef)
     {confess "Cannot set a mask register to the address of a variable";
     }
    else
     {PushR 15;
      Mov r15, $variable->addressExpr;
      Kmovq $r, r15;
      PopR;
     }
   }
  else                                                                          # Set normal register
   {if ($variable->isRef)
     {Mov $r, $variable->addressExpr;
      Mov $r, "[$r]";
     }
    else
     {Mov $r, $variable->addressExpr;
     }
   }

  $register                                                                     # name of register being set
 }

sub Nasm::X86::Variable::getReg($$)                                             # Load the variable from a register expression.
 {my ($variable, $register) = @_;                                               # Variable, register expression to load
  @_ == 2 or confess "Two parameters";
  my $r = registerNameFromNumber $register;
  if ($variable->isRef)                                                         # Move to the location referred to by this variable
   {Comment "Get variable value from register $r";
    my $p = $r eq r15 ? r14 : r15;
    PushR $p;
    Mov $p, $variable->addressExpr;
    Mov "[$p]", $r;
    PopR $p;
   }
  else                                                                          # Move to this variable
   {Mov $variable->addressExpr, $r;
   }
  $variable                                                                     # Chain
 }

sub Nasm::X86::Variable::getConst($$)                                           # Load the variable from a constant in effect setting a variable to a specified value.
 {my ($variable, $constant) = @_;                                               # Variable, constant to load
  @_ == 2 or confess "Two parameters";
  Mov rdi, $constant;
  $variable->getReg(rdi);
 }

sub Nasm::X86::Variable::incDec($$)                                             # Increment or decrement a variable.
 {my ($left, $op) = @_;                                                         # Left variable operator, address of operator to perform inc or dec
  $left->constant and confess "Cannot increment or decrement a constant";
  my $l = $left->addressExpr;
  if ($left->reference)
   {PushR r14, r15;                                                             # Violates the r14/r15 rule if removed
    Mov r15, $l;
    Mov r14, "[r15]";
    &$op(r14);
    Mov "[r15]", r14;
    PopR;
    return $left;
   }
  else
   {PushR r15;
    Mov r15, $l;
    &$op(r15);
    Mov $l, r15;
    PopR;
    return $left;
   }
 }

sub Nasm::X86::Variable::inc($)                                                 # Increment a variable.
 {my ($left) = @_;                                                              # Variable
  $left->incDec(\&Inc);
 }

sub Nasm::X86::Variable::dec($)                                                 # Decrement a variable.
 {my ($left) = @_;                                                              # Variable
  $left->incDec(\&Dec);
 }

sub Nasm::X86::Variable::str($)                                                 # The name of the variable.
 {my ($left) = @_;                                                              # Variable
  $left->name;
 }

sub Nasm::X86::Variable::min($$)                                                # Minimum of two variables.
 {my ($left, $right) = @_;                                                      # Left variable, right variable or constant
  PushR 12, 14, 15;
  $left->setReg(14);

  if (ref($right))                                                              # Right hand side is a variable
   {$right->setReg(15);
   }
  else                                                                          # Right hand side is a constant
   {Mov r15, $right;
   }

  Cmp r14, r15;
  Cmovg  r12, r15;
  Cmovle r12, r14;
  my $r = V("min", r12);
  PopR;
  $r
 }

sub Nasm::X86::Variable::max($$)                                                # Maximum of two variables.
 {my ($left, $right) = @_;                                                      # Left variable, right variable or constant
  PushR 12, 14, 15;
  $left->setReg(14);

  if (ref($right))                                                              # Right hand side is a variable
   {$right->setReg(15);
   }
  else                                                                          # Right hand side is a constant
   {Mov r15, $right;
   }

  Cmp r14, r15;
  Cmovg  r12, r14;
  Cmovle r12, r15;

  my $r = V("max", r12);
  PopR;
  $r
 }

sub Nasm::X86::Variable::and($$)                                                # And two variables.
 {my ($left, $right) = @_;                                                      # Left variable, right variable
  PushR 14, 15;
  Mov r14, 0;
  $left->setReg(15);
  Cmp r15, 0;
  &IfNe (
    sub
     {$right->setReg(15);
      Cmp r15, 0;
      &IfNe(sub {Add r14, 1});
     }
   );
  my $r = V("And(".$left->name.", ".$right->name.")", r14);
  PopR;
  $r
 }

sub Nasm::X86::Variable::or($$)                                                 # Or two variables.
 {my ($left, $right) = @_;                                                      # Left variable, right variable
  PushR 14, 15;
  Mov r14, 1;
  $left->setReg(15);
  Cmp r15, 0;
  &IfEq (
    sub
     {$right->setReg(15);
      Cmp r15, 0;
      &IfEq(sub {Mov r14, 0});
     }
   );
  my $r = V("Or(".$left->name.", ".$right->name.")", r14);
  PopR;
  $r
 }

sub Nasm::X86::Variable::setMask($$$)                                           # Set the mask register to ones starting at the specified position for the specified length and zeroes elsewhere.
 {my ($start, $length, $mask) = @_;                                             # Variable containing start of mask, variable containing length of mask, mask register
  @_ == 3 or confess "Three parameters";

  PushR 13, 14, 15;
  Mov r15, -1;
  if ($start)                                                                   # Non zero start
   {$start->setReg(14);
    Bzhi r15, r15, r14;
    Not  r15;
    ref($length) or confess "Not a variable";
    $length->setReg(13);
    Add  r14, r13;
   }
  else                                                                          # Starting at zero
   {confess "Deprecated: use setMaskFirst instead";
     $length->setReg(13);
    Mov r14, $length;
   }
  Bzhi r15, r15, r14;
  Kmovq $mask, r15;
  PopR;
 }

sub Nasm::X86::Variable::setMaskFirst($$)                                       # Set the first bits in the specified mask register.
 {my ($length, $mask) = @_;                                                     # Variable containing length to set, mask register
  @_ == 2 or confess "Two parameters";

  PushR my ($l, $b) = ChooseRegisters(2, $mask);                                # Choose two registers not the mask register
  Mov $b, -1;
  $length->setReg($l);
  Bzhi $b, $b, $l;
  Kmovq $mask, $b if $mask =~ m(\Ak)i;                                          # Set mask register if provided
  Mov   $mask, $b if $mask =~ m(\Ar)i;                                          # Set general purpose register if provided
  PopR;
 }

sub Nasm::X86::Variable::setMaskBit($$)                                         # Set a bit in the specified mask register retaining the other bits.
 {my ($index, $mask) = @_;                                                      # Variable containing bit position to set, mask register
  @_ == 2 or confess "Two parameters";
  $mask =~ m(\Ak)i or confess "Mask register required";
  PushR my ($l, $b) = (r14, r15);
  Kmovq $b, $mask;
  $index->setReg($l);
  Bts $b, $l;
  Kmovq $mask, $b;                                                              # Set mask register if provided
  PopR;
 }

sub Nasm::X86::Variable::clearMaskBit($$)                                       # Clear a bit in the specified mask register retaining the other bits.
 {my ($index, $mask) = @_;                                                      # Variable containing bit position to clear, mask register
  @_ == 2 or confess "Two parameters";
  $mask =~ m(\Ak)i or confess "Mask register required";

  PushR my $l = r14, $b = r15;
  Kmovq $b, $mask;
  $index->setReg($l);
  Btc $b, $l;
  Kmovq $mask, $b;                                                              # Set mask register if provided
  PopR;
 }

sub Nasm::X86::Variable::setBit($$)                                             # Set a bit in the specified register retaining the other bits.
 {my ($index, $mask) = @_;                                                      # Variable containing bit position to set, mask register
  @_ == 2 or confess "Two parameters";

  PushR my ($l) = ChooseRegisters(1, $mask);                                    # Choose a register
  $index->setReg($l);
  Bts $mask, $l;
  PopR;
 }

sub Nasm::X86::Variable::clearBit($$)                                           # Clear a bit in the specified mask register retaining the other bits.
 {my ($index, $mask) = @_;                                                      # Variable containing bit position to clear, mask register
  @_ == 2 or confess "Two parameters";

  PushR my ($l) = ChooseRegisters(1, $mask);                                    # Choose a register
  $index->setReg($l);
  Btc $mask, $l;
  PopR;
 }

sub Nasm::X86::Variable::setZmm($$$$)                                           # Load bytes from the memory addressed by specified source variable into the numbered zmm register at the offset in the specified offset moving the number of bytes in the specified variable.
 {my ($source, $zmm, $offset, $length) = @_;                                    # Variable containing the address of the source, number of zmm to load, variable containing offset in zmm to move to, variable containing length of move
  @_ == 4 or confess;
  ref($offset) && ref($length) or confess "Missing variable";                   # Need variables of offset and length
  Comment "Set Zmm $zmm from Memory";
  PushR 7, 14, 15;
  $offset->setMask($length, k7);                                                # Set mask for target
  $source->setReg(15);
  $offset->setReg(14);                                                          # Position memory for target
  Sub r15, r14;                                                                 # Position memory for target
  Vmovdqu8 "zmm${zmm}{k7}", "[r15]";                                            # Read from memory
  PopR;
 }

sub Nasm::X86::Variable::loadZmm($$)                                            # Load bytes from the memory addressed by the specified source variable into the numbered zmm register.
 {my ($source, $zmm) = @_;                                                      # Variable containing the address of the source, number of zmm to get
  @_ == 2 or confess "Two parameters";

  $source->setReg(rdi);
  Vmovdqu8 "zmm$zmm", "[rdi]";
 }

sub Nasm::X86::Variable::bFromZ($$$)                                            # Get the byte from the numbered zmm register and put it in a variable.
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  $variable->copy(getBwdqFromMm 'b', "zmm$zmm", $offset);                       # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::wFromZ($$$)                                            # Get the word from the numbered zmm register and put it in a variable.
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  $variable->copy(getBwdqFromMm 'w', "zmm$zmm", $offset);                       # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::dFromZ($$$)                                            # Get the double word from the numbered zmm register and put it in a variable.
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  $variable->copy(getBwdqFromMm 'd', "zmm$zmm", $offset);                       # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::qFromZ($$$)                                            # Get the quad word from the numbered zmm register and put it in a variable.
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  $variable->copy(getBwdqFromMm 'q', "zmm$zmm", $offset);                       # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::dFromPointInZ($$)                                      # Get the double word from the numbered zmm register at a point specified by the variable and return it in a variable.
 {my ($point, $zmm) = @_;                                                       # Point, numbered zmm
  PushR 7, 14, 15, $zmm;
  $point->setReg(15);
  Kmovq k7, r15;
  my ($z) = zmm $zmm;
  Vpcompressd "$z\{k7}", $z;
  Vpextrd r15d, xmm($zmm), 0;                                                   # Extract dword from corresponding xmm
  my $r = V d => r15;
  PopR;
  $r;
 }

sub Nasm::X86::Variable::dIntoPointInZ($$$)                                     # Put the variable double word content into the numbered zmm register at a point specified by the variable.
 {my ($point, $zmm, $content) = @_;                                             # Point, numbered zmm, content to be inserted as a variable
  PushR 7, 14, 15;
  $content->setReg(14);
  $point->setReg(15);
  Kmovq k7, r15;
  Vpbroadcastd zmmM($zmm, 7), r14d;                                             # Insert dword at desired location
  PopR;
 }

sub Nasm::X86::Variable::putBwdqIntoMm($$$$)                                    # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register.
 {my ($content, $size, $mm, $offset) = @_;                                      # Variable with content, size of put, numbered zmm, offset in bytes
  @_ == 4 or confess "Four parameters";

  my $o;                                                                        # The offset into the mm register
  if (ref($offset))                                                             # The offset is being passed in a variable
   {$offset->setReg($o = rsi);
   }
  else                                                                          # The offset is being passed as a register expression
   {$o = $offset;
    Comment "Put $size at $offset in $mm";
    $offset >= 0 && $offset <= RegisterSize $mm or
      confess "Out of range" if $offset =~ m(\A\d+\Z);                          # Check the offset if it is a number
   }

  $content->setReg(rsi);
  my $w = RegisterSize $mm;                                                     # Size of mm register
  Vmovdqu32 "[rsp-$w]", $mm;                                                    # Write below the stack
  Mov "[rsp+$o-$w]",  byteRegister(rsi) if $size =~ m(b);                       # Write byte register
  Mov "[rsp+$o-$w]",  wordRegister(rsi) if $size =~ m(w);                       # Write word register
  Mov "[rsp+$o-$w]", dWordRegister(rsi) if $size =~ m(d);                       # Write double word register
  Mov "[rsp+$o-$w]", rsi                if $size =~ m(q);                       # Write register
  Vmovdqu32 $mm, "[rsp-$w]";                                                    # Read below the stack
 }

sub Nasm::X86::Variable::bIntoX($$$)                                            # Place the value of the content variable at the byte in the numbered xmm register.
 {my ($content, $xmm, $offset) = @_;                                            # Variable with content, numbered xmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  $content->putBwdqIntoMm('b', "xmm$xmm", $offset)                              # Place the value of the content variable at the word in the numbered xmm register
 }

sub Nasm::X86::Variable::wIntoX($$$)                                            # Place the value of the content variable at the word in the numbered xmm register.
 {my ($content, $xmm, $offset) = @_;                                            # Variable with content, numbered xmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  $content->putBwdqIntoMm('w', "xmm$xmm", $offset)                              # Place the value of the content variable at the byte|word|double word|quad word in the numbered xmm register
 }

sub Nasm::X86::Variable::dIntoX($$$)                                            # Place the value of the content variable at the double word in the numbered xmm register.
 {my ($content, $xmm, $offset) = @_;                                            # Variable with content, numbered xmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  $content->putBwdqIntoMm('d', "xmm$xmm", $offset)                              # Place the value of the content variable at the byte|word|double word|quad word in the numbered xmm register
 }

sub Nasm::X86::Variable::qIntoX($$$)                                            # Place the value of the content variable at the quad word in the numbered xmm register.
 {my ($content, $xmm, $offset) = @_;                                            # Variable with content, numbered xmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  $content->putBwdqIntoMm('q', "xmm$xmm", $offset)                              # Place the value of the content variable at the byte|word|double word|quad word in the numbered xmm register
 }

sub Nasm::X86::Variable::bIntoZ($$$)                                            # Place the value of the content variable at the byte in the numbered zmm register.
 {my ($content, $zmm, $offset) = @_;                                            # Variable with content, numbered zmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  checkZmmRegister($zmm);
  $content->putBwdqIntoMm('b', "zmm$zmm", $offset)                              # Place the value of the content variable at the word in the numbered zmm register
 }

sub Nasm::X86::Variable::putWIntoZmm($$$)                                       # Place the value of the content variable at the word in the numbered zmm register.
 {my ($content, $zmm, $offset) = @_;                                            # Variable with content, numbered zmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  checkZmmRegister($zmm);
  $content->putBwdqIntoMm('w', "zmm$zmm", $offset)                              # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register
 }

sub Nasm::X86::Variable::dIntoZ($$$)                                            # Place the value of the content variable at the double word in the numbered zmm register.
 {my ($content, $zmm, $offset) = @_;                                            # Variable with content, numbered zmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  checkZmmRegister($zmm);
  $content->putBwdqIntoMm('d', "zmm$zmm", $offset)                              # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register
 }

sub Nasm::X86::Variable::qIntoZ($$$)                                            # Place the value of the content variable at the quad word in the numbered zmm register.
 {my ($content, $zmm, $offset) = @_;                                            # Variable with content, numbered zmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  checkZmmRegister $zmm;
  $content->putBwdqIntoMm('q', "zmm$zmm", $offset)                              # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register
 }

#D2 Memory                                                                      # Actions on memory described by variables

sub Nasm::X86::Variable::clearMemory($$)                                        # Clear the memory described in this variable.
 {my ($address, $size) = @_;                                                    # Address of memory to clear, size of the memory to clear
  @_ == 2 or confess "Two parameters";
  &ClearMemory(size=>$size, address=>$address);                                 # Free the memory
 }

sub Nasm::X86::Variable::copyMemory($$$)                                        # Copy from one block of memory to another.
 {my ($target, $source, $size) = @_;                                            # Address of target, address of source, length to copy
  @_ == 3 or confess "Three parameters";
  &CopyMemory($source, $target, $size);                                         # Copy the memory
 }

sub Nasm::X86::Variable::printMemory($$$)                                       # Print the specified number of bytes from the memory addressed by the variable on the specified channel.
 {my ($address, $channel, $size) = @_;                                          # Address of memory, channel to print on as a constant, number of bytes to print
  @_ == 3 or confess "Three parameters";

  PushR rax, rdi;
  $address->setReg(rax);
  $size->setReg(rdi);
  &PrintMemory($channel);
  PopR;
 }

sub Nasm::X86::Variable::printErrMemory($$)                                     # Print the specified number of bytes of the memory addressed by the variable on stdout.
 {my ($address, $size) = @_;                                                    # Address of memory, number of bytes to print
  @_ == 2 or confess "Two parameters";
  $address->printMemory($stderr, $size);
 }

sub Nasm::X86::Variable::printErrMemoryNL($$)                                   # Print the specified number of bytes of the memory addressed by the variable on stdout followed by a new line.
 {my ($address, $size) = @_;                                                    # Address of memory, number of bytes to print
  @_ == 2 or confess "Two parameters";
  $address->printErrMemory($size);
  PrintErrNL;
 }

sub Nasm::X86::Variable::printOutMemory($$)                                     # Print the specified number of bytes of the memory addressed by the variable on stdout.
 {my ($address, $size) = @_;                                                    # Address of memory, number of bytes to print
  @_ == 2 or confess "Two parameters";
  $address->printMemory($stdout, $size);
 }

sub Nasm::X86::Variable::printOutMemoryNL($$)                                   # Print the specified number of bytes of the memory addressed by the variable on stdout followed by a new line.
 {my ($address, $size) = @_;                                                    # Address of memory, number of bytes to print
  @_ == 2 or confess "Two parameters";
  $address->printOutMemory($size);
  PrintOutNL;
 }

sub Nasm::X86::Variable::printMemoryInHexNL($$$)                                # Write, in hexadecimal, the memory addressed by a variable to stdout or stderr.
 {my ($address, $channel, $size) = @_;                                          # Address of memory, channel to print on, number of bytes to print
  @_ == 3 or confess "Three parameters";
  PushR rax, rdi;
  $address->setReg(rax);
  $size->setReg(rdi);
  &PrintMemoryInHex($channel);
  &PrintNL($channel);
  PopR;
 }

sub Nasm::X86::Variable::printErrMemoryInHexNL($$)                              # Write the memory addressed by a variable to stderr.
 {my ($address, $size) = @_;                                                    # Address of memory, number of bytes to print
  @_ == 2 or confess "Two parameters";
  $address->printMemoryInHexNL($stderr, $size);
 }

sub Nasm::X86::Variable::printOutMemoryInHexNL($$)                              # Write the memory addressed by a variable to stdout.
 {my ($address, $size) = @_;                                                    # Address of memory, number of bytes to print
  @_ == 2 or confess "Two parameters";
  $address->printMemoryInHexNL($stdout, $size);
 }

sub Nasm::X86::Variable::freeMemory($$)                                         # Free the memory addressed by this variable for the specified length.
 {my ($address, $size) = @_;                                                    # Address of memory to free, size of the memory to free
  @_ == 2 or confess "Two parameters";
  &FreeMemory($address, $size);                                                 # Free the memory
 }

sub Nasm::X86::Variable::allocateMemory($)                                      # Allocate the specified amount of memory via mmap and return its address.
 {my ($size) = @_;                                                              # Size
  @_ == 1 or confess "One parameter";
  AllocateMemory($size);
 }

#D2 Structured Programming with variables                                       # Structured programming operations driven off variables.

sub Nasm::X86::Variable::for($&)                                                # Iterate a block a variable number of times.
 {my ($limit, $block) = @_;                                                     # Number of times, Block
  @_ == 2 or confess "Two parameters";
  Comment "Variable::For $limit";
  my $index = V(q(index), 0);                                                   # The index that will be incremented
  my $start = Label;
  my $next  = Label;
  my $end   = Label;
  SetLabel $start;                                                              # Start of loop

  If $index >= $limit, sub {Jge $end};                                          # Condition

  &$block($index, $start, $next, $end);                                         # Execute block

  SetLabel $next;                                                               # Next iteration
  $index++;                                                                     # Increment
  Jmp $start;
  SetLabel $end;
 }

#D1 Operating system                                                            # Interacting with the operating system.

#D2 Processes                                                                   # Create and manage processes

sub Fork()                                                                      # Fork: create and execute a copy of the current process.
 {@_ == 0 or confess;
  Comment "Fork";
  Mov rax, 57;
  Syscall
 }

sub GetPid()                                                                    # Get process identifier.
 {@_ == 0 or confess;
  Comment "Get Pid";

  Mov rax, 39;
  Syscall
 }

sub GetPidInHex()                                                               # Get process identifier in hex as 8 zero terminated bytes in rax.
 {@_ == 0 or confess;
  Comment "Get Pid";
  my $hexTranslateTable = hexTranslateTable;

  my $s = Subroutine
   {SaveFirstFour;
    Mov rax, 39;                                                                # Get pid
    Syscall;
    Mov rdx, rax;                                                               # Content to be printed

    ClearRegisters rax;                                                         # Save a trailing 00 on the stack
    Push ax;
    for my $i(reverse 5..7)
     {my $s = 8*$i;
      Mov rdi,rdx;
      Shl rdi,$s;                                                               # Push selected byte high
      Shr rdi,56;                                                               # Push select byte low
      Shl rdi,1;                                                                # Multiply by two because each entry in the translation table is two bytes long
      Mov ax, "[$hexTranslateTable+rdi]";
      Push ax;
     }
    Pop rax;                                                                    # Get result from stack
    RestoreFirstFourExceptRax;
   } name => "GetPidInHex";

  $s->call;
 }

sub GetPPid()                                                                   # Get parent process identifier.
 {@_ == 0 or confess;
  Comment "Get Parent Pid";

  Mov rax, 110;
  Syscall
 }

sub GetUid()                                                                    # Get userid of current process.
 {@_ == 0 or confess;
  Comment "Get User id";

  Mov rax, 102;
  Syscall
 }

sub WaitPid()                                                                   # Wait for the pid in rax to complete.
 {@_ == 0 or confess;
  Comment "WaitPid - wait for the pid in rax";

    my $s = Subroutine
   {SaveFirstSeven;
    Mov rdi,rax;
    Mov rax, 61;
    Mov rsi, 0;
    Mov rdx, 0;
    Mov r10, 0;
    Syscall;
    RestoreFirstSevenExceptRax;
   } name => "WaitPid";

  $s->call;
 }

sub ReadTimeStampCounter()                                                      # Read the time stamp counter and return the time in nanoseconds in rax.
 {@_ == 0 or confess;

  my $s = Subroutine
   {Comment "Read Time-Stamp Counter";
    PushR rdx;
    ClearRegisters rax;
    Cpuid;
    Rdtsc;
    Shl rdx,32;
    Or rax,rdx;
    PopR;
   } name => "ReadTimeStampCounter";

  $s->call;
 }

#D2 Memory                                                                      # Allocate and print memory

sub PrintMemoryInHex($)                                                         # Dump memory from the address in rax for the length in rdi on the specified channel. As this method prints in blocks of 8 up to 7 bytes will be missing from the end unless the length is a multiple of 8 .
 {my ($channel) = @_;                                                           # Channel
  @_ == 1 or confess "One parameter";
  Comment "Print out memory in hex on channel: $channel";

  my $s = Subroutine
   {my $size = RegisterSize rax;
    SaveFirstFour;

    Test rdi, 0x7;                                                              # Round the number of bytes to be printed
    IfNz
    Then                                                                        # Round up
     {Add rdi, 8;
     };
    And rdi, 0x3f8;                                                             # Limit the number of bytes to be printed to 1024

    Mov rsi, rax;                                                               # Position in memory
    Lea rdi,"[rax+rdi-$size+1]";                                                # Upper limit of printing with an 8 byte register
    For                                                                         # Print string in blocks
     {Mov rax, "[rsi]";
      Bswap rax;
      PrintRaxInHex($channel);
      Mov rdx, rsi;
      Add rdx, $size;
      Cmp rdx, rdi;
      IfLt
      Then
       {PrintString($channel, "  ");
       }
     } rsi, rdi, $size;
    RestoreFirstFour;
   } name=> "PrintOutMemoryInHexOnChannel$channel";

  $s->call;
 }

sub PrintErrMemoryInHex                                                         # Dump memory from the address in rax for the length in rdi on stderr.
 {@_ == 0 or confess "No parameters";
  PrintMemoryInHex($stderr);
 }

sub PrintOutMemoryInHex                                                         # Dump memory from the address in rax for the length in rdi on stdout.
 {@_ == 0 or confess "No parameters";
  PrintMemoryInHex($stdout);
 }

sub PrintErrMemoryInHexNL                                                       # Dump memory from the address in rax for the length in rdi and then print a new line.
 {@_ == 0 or confess "No parameters";
  PrintMemoryInHex($stderr);
  PrintNL($stderr);
 }

sub PrintOutMemoryInHexNL                                                       # Dump memory from the address in rax for the length in rdi and then print a new line.
 {@_ == 0 or confess "No parameters";
  PrintMemoryInHex($stdout);
  PrintNL($stdout);
 }

sub PrintMemory_InHex($)                                                        # Dump memory from the address in rax for the length in rdi on the specified channel. As this method prints in blocks of 8 up to 7 bytes will be missing from the end unless the length is a multiple of 8 .
 {my ($channel) = @_;                                                           # Channel
  @_ == 1 or confess "One parameter";
  Comment "Print out memory in hex on channel: $channel";

  my $s = Subroutine
   {my $size = RegisterSize rax;
    SaveFirstFour;

    Test rdi, 0x7;                                                              # Round the number of bytes to be printed
    IfNz
    Then                                                                        # Round up
     {Add rdi, 8;
     };
    And rdi, 0x3f8;                                                             # Limit the number of bytes to be printed to 1024

    Mov rsi, rax;                                                               # Position in memory
    Lea rdi,"[rax+rdi-$size+1]";                                                # Upper limit of printing with an 8 byte register
    For                                                                         # Print string in blocks
     {Mov rax, "[rsi]";
      Bswap rax;
      PrintRax_InHex($channel);
      Mov rdx, rsi;
      Add rdx, $size;
      Cmp rdx, rdi;
      IfLt
      Then
       {PrintString($channel, "  ");
       }
     } rsi, rdi, $size;
    RestoreFirstFour;
   } name=> "PrintOutMemory_InHexOnChannel$channel";

  $s->call;
 }

sub PrintErrMemory_InHex                                                        # Dump memory from the address in rax for the length in rdi on stderr.
 {@_ == 0 or confess;
  PrintMemory_InHex($stderr);
 }

sub PrintOutMemory_InHex                                                        # Dump memory from the address in rax for the length in rdi on stdout.
 {@_ == 0 or confess;
  PrintMemory_InHex($stdout);
 }

sub PrintErrMemory_InHexNL                                                      # Dump memory from the address in rax for the length in rdi and then print a new line.
 {@_ == 0 or confess;
  PrintMemory_InHex($stderr);
  PrintNL($stderr);
 }

sub PrintOutMemory_InHexNL                                                      # Dump memory from the address in rax for the length in rdi and then print a new line.
 {@_ == 0 or confess;
  PrintMemory_InHex($stdout);
  PrintNL($stdout);
 }

sub PrintMemory($)                                                              # Print the memory addressed by rax for a length of rdi on the specified channel.
 {my ($channel) = @_;                                                           # Channel
  @_ == 1 or confess "One parameter";

  my $s = Subroutine
   {Comment "Print memory on channel: $channel";
    SaveFirstFour;
    Mov rsi, rax;
    Mov rdx, rdi;
    Mov rax, 1;
    Mov rdi, $channel;
    Syscall;
    RestoreFirstFour;
   } name => "PrintOutMemoryOnChannel$channel";

  $s->call;
 }

sub PrintMemoryNL                                                               # Print the memory addressed by rax for a length of rdi on the specified channel followed by a new line.
 {my ($channel) = @_;                                                           # Channel
  @_ == 1 or confess "One parameter";
  PrintMemory($channel);
  PrintNL($channel);
 }

sub PrintErrMemory                                                              # Print the memory addressed by rax for a length of rdi on stderr.
 {@_ == 0 or confess;
  PrintMemory($stdout);
 }

sub PrintOutMemory                                                              # Print the memory addressed by rax for a length of rdi on stdout.
 {@_ == 0 or confess;
  PrintMemory($stdout);
 }

sub PrintErrMemoryNL                                                            # Print the memory addressed by rax for a length of rdi followed by a new line on stderr.
 {@_ == 0 or confess;
  PrintErrMemory;
  PrintErrNL;
 }

sub PrintOutMemoryNL                                                            # Print the memory addressed by rax for a length of rdi followed by a new line on stdout.
 {@_ == 0 or confess;
  PrintOutMemory;
  PrintOutNL;
 }

sub AllocateMemory($)                                                           # Allocate the variable specified amount of memory via mmap and return its address as a variable.
 {my ($size) = @_;                                                              # Size as a variable
  @_ == 1 or confess "Size required";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Allocate memory";
    SaveFirstSeven;

    my %d = getSystemConstantsFromIncludeFile "linux/mman.h",                   # Memory map constants
      qw(MAP_PRIVATE MAP_ANONYMOUS PROT_WRITE PROT_READ);

    my $pa = $d{MAP_PRIVATE} | $d{MAP_ANONYMOUS};
    my $wr = $d{PROT_WRITE}  | $d{PROT_READ};

    Mov rax, 9;                                                                 # Memory map
    $$p{size}->setReg(rsi);                                                     # Amount of memory
    Xor rdi, rdi;                                                               # Anywhere
    Mov rdx, $wr;                                                               # Read write protections
    Mov r10, $pa;                                                               # Private and anonymous map
    Mov r8,  -1;                                                                # File descriptor for file backing memory if any
    Mov r9,  0;                                                                 # Offset into file
    Syscall;
    Cmp rax, -1;                                                                # Check return code
    IfEq
    Then
     {PrintErrTraceBack "Cannot allocate memory, return code -1";
     };
    Cmp eax, 0xffffffea;                                                        # Check return code
    IfEq
    Then
     {PrintErrTraceBack "Cannot allocate memory, return code 0xffffffea";
     };
    Cmp rax, -12;                                                               # Check return code
    IfEq
    Then
     {PrintErrTraceBack "Cannot allocate memory, return code -12";
     };
     $$p{address}->getReg(rax);                                                 # Amount of memory

    RestoreFirstSeven;
   } parameters=>[qw(address size)], name => 'AllocateMemory';

  $s->call(parameters=>{size=>$size, address => my $address = V address => 0});

  $address;
 }

sub FreeMemory($$)                                                              # Free memory specified by variables.
 {my ($address, $size) = @_;                                                    # Variable address of memory, variable size of memory
  @_ == 2 or confess "Address, size to free";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    SaveFirstFour;
    Mov rax, 11;                                                                # Munmap
    $$p{address}->setReg(rdi);                                                  # Address
    $$p{size}   ->setReg(rsi);                                                  # Length
    Syscall;
    RestoreFirstFour;
   } parameters=>[qw(size address)], name=> 'FreeMemory';

  $s->call(parameters => {address=>$address, size=>$size});
 }

sub ClearMemory($$)                                                             # Clear memory wit a variable address and variable length
 {my ($address, $size) = @_;                                                    # Address of memory as a variable, size of memory as a variable
  @_ == 2 or confess "address, size required";
  Comment "Clear memory";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    PushR zmm0, rax, rdi, rsi, rdx;
    $$p{address}->setReg(rax);
    $$p{size}   ->setReg(rdi);
    Lea rdx, "[rax+rdi]";                                                       # Address of upper limit of buffer

    ClearRegisters zmm0;                                                        # Clear the register that will be written into memory

    Mov rsi, rdi;                                                               # Modulus the size of zmm
    And rsi, 0x3f;                                                              # Remainder modulo 64
    Cmp rsi, 0;                                                                 # Test remainder
    IfNz sub                                                                    # Need to align so that the rest of the clear can be done in full zmm blocks
     {PushR 7;
      V(align => rsi)->setMaskFirst(k7);                                        # Set mask bits
      Vmovdqu8 "[rax]{k7}", zmm0;                                               # Masked move to memory
      PopR;
      Add rax, rsi;                                                             # Update point to clear from
      Sub rdi, rsi;                                                             # Reduce clear length
     };

    For                                                                         # Clear remaining memory in full zmm blocks
     {Vmovdqu64 "[rax]", zmm0;
     } rax, rdx, RegisterSize zmm0;

    PopR;
   } parameters=>[qw(size address)], name => 'ClearMemory';

  $s->call(parameters => {address => $address, size => $size});
 }

sub CopyMemory($$$)                                                             # Copy memory.
 {my ($source, $target, $size) = @_;                                            # Source address variable, target address variable, length variable
  @_ == 3 or confess "Source, target, size required";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    SaveFirstSeven;
    $$p{source}->setReg(rsi);
    $$p{target}->setReg(rax);
    $$p{size}  ->setReg(rdi);
    ClearRegisters rdx;
    For                                                                         # Clear memory
     {Mov "r8b", "[rsi+rdx]";
      Mov "[rax+rdx]", "r8b";
     } rdx, rdi, 1;
    RestoreFirstSeven;
   } parameters=>[qw(source target size)], name => 'CopyMemory';

  $s->call(parameters=>{source => $source, target=>$target, size=>$size});
 }

#D2 Files                                                                       # Interact with the operating system via files.

sub OpenRead()                                                                  # Open a file, whose name is addressed by rax, for read and return the file descriptor in rax.
 {@_ == 0 or confess "Zero parameters";

  my $s = Subroutine
   {my %s = getSystemConstantsFromIncludeFile  "fcntl.h", qw(O_RDONLY);         # Constants for reading a file

    SaveFirstFour;
    Mov rdi,rax;
    Mov rax,2;
    Mov rsi, $s{O_RDONLY};
    Xor rdx,rdx;
    Syscall;
    RestoreFirstFourExceptRax;
   } name=> "OpenRead";

  $s->call;
 }

sub OpenWrite()                                                                 # Create the file named by the terminated string addressed by rax for write.
 {@_ == 0 or confess "Zero parameters";

  my $s = Subroutine
   {my %s = getSystemConstantsFromIncludeFile                                   # Constants for creating a file
      "fcntl.h", qw(O_CREAT O_WRONLY);
    my $write = $s{O_WRONLY} | $s{O_CREAT};

    SaveFirstFour;
    Mov rdi, rax;
    Mov rax, 2;
    Mov rsi, $write;
    Mov rdx, 0x1c0;                                                             # Permissions: u=rwx  1o=x 4o=r 8g=x 10g=w 20g=r 40u=x 80u=r 100u=r 200=T 400g=S 800u=S #0,2,1000, nothing
    Syscall;

    RestoreFirstFourExceptRax;
   } name=> "OpenWrite";

  $s->call;
 }

sub CloseFile()                                                                 # Close the file whose descriptor is in rax.
 {@_ == 0 or confess "Zero parameters";

  my $s = Subroutine
   {Comment "Close a file";
    SaveFirstFour;
    Mov rdi, rax;
    Mov rax, 3;
    Syscall;
    RestoreFirstFourExceptRax;
   } name=> "CloseFile";

  $s->call;
 }

sub StatSize()                                                                  # Stat a file whose name is addressed by rax to get its size in rax.
 {@_ == 0 or confess "Zero parameters";

  my ($F, $S) = (q(sys/stat.h), q(struct stat));                                # Get location of struct stat.st_size field
  my $Size = getStructureSizeFromIncludeFile $F, $S;
  my $off  = getFieldOffsetInStructureFromIncludeFile $F, $S, q(st_size);

  my $s = Subroutine
   {Comment "Stat a file for size";
    SaveFirstFour;
    Mov rdi, rax;                                                               # File name
    Mov rax,4;
    Lea rsi, "[rsp-$Size]";
    Syscall;
    Mov rax, "[$off+rsp-$Size]";                                                # Place size in rax
    RestoreFirstFourExceptRax;
   } name=> "StatSize";

  $s->call;
 }

sub ReadChar()                                                                  # Read a character from stdin and return it in rax else return -1 in rax if no character was read.
 {@_ == 0 or confess "Zero parameters";
  my $s = Subroutine
   {my ($p) = @_;
    SaveFirstFour;                                                              # Generated code

    Mov rax, 0;                                                                 # Read
    Mov rdi, 0;                                                                 # Stdin
    Lea rsi, "[rsp-8]";                                                         # Make space on stack
    Mov rdx, 1;                                                                 # One character
    Syscall;

    Cmp rax, 1;
    IfEq
    Then
     {Mov al, "[rsp-8]";
     },
    Else
     {Mov rax, -1;
     };

    RestoreFirstFourExceptRax;
   } name => 'ReadChar';

  $s->call
 }

sub ReadLine()                                                                  # Reads up to 8 characters followed by a terminating return and place them into rax.
 {@_ == 0 or confess "Zero parameters";
  my $s = Subroutine
   {my ($p) = @_;
    PushR rcx, 14, 15;
    ClearRegisters rax, rcx, r14, r15;

    (V max => RegisterSize(rax))->for(sub                                       # Read each character
     {my ($index, $start, $next, $end) = @_;

      ReadChar;
      Cmp rax, 0xf0;                                                            # Too high
      IfGe Then {Jmp $end};
      Cmp rax, 0xa;                                                             # Too low
      IfLe Then {Jmp $end};
      $index->setReg(rcx);
      Shl rcx, 3;
      Shl rax, cl;                                                              # Move into position
      Or r15, rax;
      Add rcx, $bitsInByte;
     });

    Mov rax, r15;                                                               # Return result in rax
    PopR;
   } name => 'ReadLine';

  $s->call
 }

sub ReadInteger()                                                               # Reads an integer in decimal and returns it in rax.
 {@_ == 0 or confess "Zero parameters";
  my $s = Subroutine
   {my ($p) = @_;
    PushR 15;
    ClearRegisters rax, r15;

    (V max => RegisterSize(rax))->for(sub                                       # Read each character
     {my ($index, $start, $next, $end) = @_;

      ReadChar;
      Cmp rax, 0x3A;                                                            # Too high
      IfGe Then {Jmp $end};
      Cmp rax, 0x29;                                                            # Too low
      IfLe Then {Jmp $end};
      Imul r15, 10;                                                             # Move into position
      Sub rax, 0x30;
      Add r15, rax;
     });

    Mov rax, r15;                                                               # Return result in rax
    PopR;
   } name => 'ReadInteger';

  $s->call
 }

sub ReadFile($)                                                                 # Read a file into memory.
 {my ($File) = @_;                                                              # Variable addressing a zero terminated string naming the file
  @_ == 1 or confess "One parameter required";

  my $s = Subroutine
   {my ($p) = @_;
    Comment "Read a file into memory";
    SaveFirstSeven;                                                             # Generated code
    my $size = V(size => undef);
    my $fdes = V(fdes => undef);

    $$p{file}->setReg(rax);                                                     # File name

    StatSize;                                                                   # File size
    $size->getReg(rax);                                                         # Save file size

    $$p{file}->setReg(rax);                                                     # File name
    OpenRead;                                                                   # Open file for read
    $fdes->getReg(rax);                                                         # Save file descriptor

    my %d  = getSystemConstantsFromIncludeFile                                  # Memory map constants
     "linux/mman.h", qw(MAP_PRIVATE PROT_READ PROT_EXEC);
    my $pa = $d{MAP_PRIVATE};
    my $ro = $d{PROT_READ};
    my $ex = $d{PROT_EXEC};

    Mov rax, 9;                                                                 # Memory map
    $size->setReg(rsi);                                                         # Amount of memory
    Xor rdi, rdi;                                                               # Anywhere
    Mov rdx, $ro | $ex;                                                         # Read/execute contents
    Mov r10, $pa;                                                               # Private and anonymous map
    $fdes->setReg(r8);                                                          # File descriptor for file backing memory
    Mov r9,  0;                                                                 # Offset into file
    Syscall;
    $size       ->setReg(rdi);
    $$p{address}->getReg(rax);
    $$p{size}   ->getReg(rdi);
    RestoreFirstSeven;
   } parameters=>[qw(file address size)], name => 'ReadFile';

  my $file    = ref($File) ? $File : V file => Rs $File;
  my $size    = V(size    => undef);
  my $address = V(address => undef);
  $s->call(parameters=>{file => $file, size=>$size, address=>$address});

  ($address, $size)                                                             # Return address and size of mapped file
 }

sub executeFileViaBash($)                                                       # Execute the file named in a variable
 {my ($file) = @_;                                                              # File variable
  @_ == 1 or confess "File required";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    SaveFirstFour;
    Fork;                                                                       # Fork

    Test rax, rax;

    IfNz                                                                        # Parent
    Then
     {WaitPid;
     },
    Else                                                                        # Child
     {$$p{file}->setReg(rdi);
      Mov rsi, 0;
      Mov rdx, 0;
      Mov rax, 59;
      Syscall;
     };
    RestoreFirstFour;
   } parameters=>[qw(file)], name => 'executeFileViaBash';

  $s->call(parameters=>{file => $file});
 }

sub unlinkFile($)                                                               # Unlink the named file.
 {my ($file) = @_;                                                              # File variable
  @_ == 1 or confess "File required";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    SaveFirstFour;
    $$p{file}->setReg(rdi);
    Mov rax, 87;
    Syscall;
    RestoreFirstFour;
   } parameters=>[qw(file)], name => 'unlinkFile';

  $s->call(parameters=>{file => $file});
 }

#D1 Hash functions                                                              # Hash functions

sub Hash()                                                                      # Hash a string addressed by rax with length held in rdi and return the hash code in r15.
 {@_ == 0 or confess;

  my $s = Subroutine                                                            # Read file
   {Comment "Hash";

    PushR rax, rdi, k1, zmm0, zmm1;                                             # Save registers
    PushR 15;
    Vpbroadcastq zmm0, rdi;                                                     # Broadcast length through ymm0
    Vcvtuqq2pd   zmm0, zmm0;                                                    # Convert to lengths to float
    Vgetmantps   zmm0, zmm0, 4;                                                 # Normalize to 1 to 2, see: https://hjlebbink.github.io/x86doc/html/VGETMANTPD.html

    Add rdi, rax;                                                               # Upper limit of string

    ForIn                                                                       # Hash in ymm0 sized blocks
     {Vmovdqu ymm1, "[rax]";                                                    # Load data to hash
      Vcvtudq2pd zmm1, ymm1;                                                    # Convert to float
      Vgetmantps zmm0, zmm0, 4;                                                 # Normalize to 1 to 2, see: https://hjlebbink.github.io/x86doc/html/VGETMANTPD.html

      Vmulpd zmm0, zmm1, zmm0;                                                  # Multiply current hash by data
     }
    sub                                                                         # Remainder in partial block
     {Mov r15, -1;
      Bzhi r15, r15, rdi;                                                       # Clear bits that we do not wish to load
      Kmovq k1, r15;                                                            # Take up mask
      Vmovdqu8 "ymm1{k1}", "[rax]";                                             # Load data to hash

      Vcvtudq2pd zmm1, ymm1;                                                    # Convert to float
      Vgetmantps   zmm0, zmm0, 4;                                               # Normalize to 1 to 2, see: https://hjlebbink.github.io/x86doc/html/VGETMANTPD.html

      Vmulpd zmm0, zmm1, zmm0;                                                  # Multiply current hash by data
     }, rax, rdi, RegisterSize ymm0;

    Vgetmantps   zmm0, zmm0, 4;                                                 # Normalize to 1 to 2, see: https://hjlebbink.github.io/x86doc/html/VGETMANTPD.html

    Mov r15, 0b11110000;                                                        # Top 4 to bottom 4
    Kmovq k1, r15;
    Vpcompressq  "zmm1{k1}", zmm0;
    Vaddpd       ymm0, ymm0, ymm1;                                              # Top 4 plus bottom 4

    Mov r15, 0b1100;                                                            # Top 2 to bottom 2
    Kmovq k1, r15;
    Vpcompressq  "ymm1{k1}", ymm0;
    Vaddpd       xmm0, xmm0, xmm1;                                              # Top 2 plus bottom 2

    Pslldq       xmm0, 2;                                                       # Move centers into double words
    Psrldq       xmm0, 4;
    Mov r15, 0b0101;                                                            # Centers to lower quad
    Kmovq k1, r15;
    Vpcompressd  "xmm0{k1}", xmm0;                                              # Compress to lower quad
    PopR r15;

    Vmovq r15, xmm0;                                                            # Result in r15

    PopR;
   } name=> "Hash";

  $s->call;
 }

#D1 Unicode                                                                     # Convert between utf8 and utf32

sub convert_rax_from_utf32_to_utf8                                              # Convert a utf32 character held in rax to a utf8 character held in rax
 {@_ and confess "Zero parameters";

  my $s = Subroutine
   {PushR 14, 15;
    Block
     {my ($success) = @_;                                                       # As shown at: https://en.wikipedia.org/wiki/UTF-8
      Cmp rax, 0x7f;                                                            # Ascii
      IfLe Then {Jmp $success};

      Cmp rax, 0x7ff;                                                           # Char size is: 2 bytes
      IfLe
      Then
       {Mov r15, rax;

        Shr r15, 6;                                                             # High byte
        And r15, 0x1f;
        Or  r15, 0xc0;

        Mov r14, rax;                                                           # Low byte
        And r14, 0x3f;
        Or  r14, 0x80;
        Shl r14, 8;
        Or r15, r14;
        Mov rax, r15;
        Jmp $success;
       };

      Cmp rax, 0xffff;                                                          # Char size is: 3 bytes
      IfLe
      Then
       {Mov r15, rax;

        Shr r15, 12;                                                            # High byte
        And r15, 0x0f;
        Or  r15, 0xe0;

        Mov r14, rax;                                                           # Middle byte
        Shr r14, 6;
        And r14, 0x3f;
        Or  r14, 0x80;
        Shl r14, 8;
        Or r15, r14;

        Mov r14, rax;                                                           # Low byte
        And r14, 0x3f;
        Or  r14, 0x80;
        Shl r14, 16;
        Or r15, r14;

        Mov rax, r15;
        Jmp $success;
       };

      Cmp rax, 0x10ffff;                                                        # Char size is: 4 bytes
      IfLe
      Then
       {Mov r15, rax;

        Shr r15, 18;                                                            # High byte
        And r15, 0x03;
        Or  r15, 0xf0;

        Mov r14, rax;                                                           # Middle byte
        Shr r14, 12;
        And r14, 0x3f;
        Or  r14, 0x80;
        Shl r14, 8;
        Or r15, r14;

        Mov r14, rax;                                                           # Middle byte
        Shr r14, 6;
        And r14, 0x3f;
        Or  r14, 0x80;
        Shl r14, 16;
        Or r15, r14;

        Mov r14, rax;                                                           # Low byte
        And r14, 0x3f;
        Or  r14, 0x80;
        Shl r14, 24;
        Or r15, r14;
        Mov rax, r15;
        Jmp $success;
       };
     };

    PopR;
   } name => 'convert_rax_from_utf32_to_utf8';

  $s->call;
 } # convert_rax_from_utf32_to_utf8

sub GetNextUtf8CharAsUtf32($)                                                   # Get the next UTF-8 encoded character from the addressed memory and return it as a UTF-32 char.
 {my ($in) = @_;                                                                # Address of utf8 character as a variable
  @_ == 1 or confess "One parameter";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters

    PushR 11, 12, 13, 14, 15;
    $$p{fail}->getConst(0);                                                     # Clear failure indicator
    $$p{in}->setReg(15);                                                        # Character to convert
    ClearRegisters 14;                                                          # Move to byte register below does not clear the entire register
    Mov r14b, "[r15]";
    Block
     {my ($success) = @_;                                                       # As shown at: https://en.wikipedia.org/wiki/UTF-8

      Cmp r14, 0x7f;                                                            # Ascii
      IfLe
      Then
       {$$p{out}->getReg(r14);
        $$p{size}->copy(1);
        Jmp $success;
       };

      Cmp r14, 0xdf;                                                            # Char size is: 2 bytes
      IfLe
      Then
       {Mov r13b, "[r15+1]";
        And r13, 0x3f;
        And r14, 0x1f;
        Shl r14, 6;
        Or  r14,  r13;
        $$p{out}->getReg(r14);
        $$p{size}->copy(2);
        Jmp $success;
       };

      Cmp r14, 0xef;                                                            # Char size is: 3 bytes
      IfLe
      Then
       {Mov r12b, "[r15+2]";
        And r12, 0x3f;
        Mov r13b, "[r15+1]";
        And r13, 0x3f;
        And r14, 0x0f;
        Shl r13,  6;
        Shl r14, 12;
        Or  r14,  r13;
        Or  r14,  r12;
        $$p{out}->getReg(r14);
        $$p{size}->copy(3);
        Jmp $success;
       };

      Cmp r14, 0xf7;                                                            # Char size is: 4 bytes
      IfLe
      Then
       {Mov r11b, "[r15+3]";
        And r11, 0x3f;
        Mov r12b, "[r15+2]";
        And r12, 0x3f;
        Mov r13b, "[r15+1]";
        And r13, 0x3f;
        And r14, 0x07;
        Shl r12,  6;
        Shl r13, 12;
        Shl r14, 18;
        Or  r14,  r13;
        Or  r14,  r12;
        Or  r14,  r11;
        $$p{out}->getReg(r14);
        $$p{size}->copy(4);
        Jmp $success;
       };

      $$p{fail}->getConst(1);                                                   # Conversion failed
     };

    PopR;
   } parameters=>[qw(in out  size  fail)], name => 'GetNextUtf8CharAsUtf32';

  my $out  = V(out  => 0);                                                      # Utf32 equivalent
  my $size = V(size => 0);                                                      # Size of utf8 converted
  my $fail = V(fail => 0);                                                      # Failed if true else false

  $s->call(parameters=>{in=>$in, out=>$out, size=>$size, fail=>$fail});

 ($out, $size, $fail)                                                           # Output character variable, output size of input, output error if any

 } # GetNextUtf8CharAsUtf32

sub ConvertUtf8ToUtf32($$)                                                      # Convert an allocated block  string of utf8 to an allocated block of utf32 and return its address and length.
 {my ($a8, $s8) = @_;                                                           # utf8 string address variable, utf8 length variable
  @_ == 2 or confess "Two parameters";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    PushR 10, 11, 12, 13, 14, 15;

    my $a8      = $$p{a8};                                                      # Address of utf8
    my $s8      = $$p{s8};                                                      # Length of utf8 in bytes
    my $size    = $$p{s8} * RegisterSize(eax);                                  # Maximum possible length of corresponding utf32
    my $address = AllocateMemory $size;                                         # Allocate a buffer for utf32
    $$p{a32}->copy($address);                                                   # Address of allocation
    $$p{s32}->copy($size);                                                      # Size of allocation

     $a8     ->setReg(14);                                                      # Current position in input string
    ($a8+$s8)->setReg(15);                                                      # Upper limit of input string
    $address->setReg(13);                                                       # Current position in output string
    ClearRegisters 12;                                                          # Number of characters in output string

    $s8->for(sub                                                                # Loop through input string  converting each utf8 sequence to utf32
     {my ($index, $start, $next, $end) = @_;
      my ($out, $size, $fail) = GetNextUtf8CharAsUtf32 V(in => r14);            # Get next utf-8 character and convert it to utf32
      If $fail > 0,
      Then
       {$$p{fail}->copy($fail);
        Jmp $end;
       };

      Inc r12;                                                                  # Count characters converted
      $out->setReg(r11);                                                        # Output character

      Mov  "[r13]",  r11d;
      Add    r13,    RegisterSize eax;                                          # Move up 32 bits output string
      $size->setReg(r10);                                                       # Decoded this many bytes
      Add   r14, r10;                                                           # Move up in input string
      Cmp   r14, r15;
      Jge $end;                                                                 # Exhausted input string
    });

    $$p{count} ->getReg(r12);                                                   # Number of unicode points converted from utf8 to utf32
    PopR;
   } parameters=>[qw(a8 s8 a32 s32 count fail)], name => 'ConvertUtf8ToUtf32';

  my $a32   = V(a32   => 0);
  my $s32   = V(s32   => 0);
  my $count = V(count => 0);
  my $fail  = V(fail  => 0);                                                    # Assume we will succeed

  $s->call(parameters=>
    {a8  => $a8,  s8  => $s8,
     a32 => $a32, s32 => $s32, count=>$count, fail => $fail});

  ($a32, $s32, $count, $fail)                                                   # utf32 string address as a variable, utf32 area length as a variable, number of characters converted, fail if one else zero
 } # ConvertUtf8ToUtf32

#   4---+---3---+---2---+---1---+---0  Octal not decimal
# 0  CCCCCCCC                          ClassifyInRange                  C == classification
# 1  XXXXXXXX                          ClassifyWithInRange              X == offset in range
# 2  CCCCCCCC                XXXXXXXX  ClassifyWithInRangeAndSaveOffset C == classification, X == offset in range 0-2**10

sub ClassifyRange($$$)                                                          #P Implementation of ClassifyInRange and ClassifyWithinRange.
 {my ($recordOffsetInRange, $address, $size) = @_;                              # Record offset in classification in high byte if 1 else in classification if 2, variable address of utf32 string to classify, variable length of utf32 string to classify
  @_ == 3 or confess "Three parameters";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $finish = Label;

    PushR my @save =  (($recordOffsetInRange ? (r11, r12, r13) : ()),           # More registers required if we are recording position in range
                       r14, r15, k6, k7, zmm 29..31);

    Mov r15, 0x88888888;                                                        # Create a mask for the classification bytes
    Kmovq k7, r15;
    Kshiftlq k6, k7, 32;                                                        # Move mask into upper half of register
    Korq  k7, k6, k7;                                                           # Classification bytes masked by k7

    Knotq k7, k7;                                                               # Utf32 characters mask
    Vmovdqu8 "zmm31\{k7}{z}", zmm1;                                             # Utf32 characters at upper end of each range
    Vmovdqu8 "zmm30\{k7}{z}", zmm0;                                             # Utf32 characters at lower end of each range

    $$p{address}->setReg(15);                                                   # Address of first utf32 character
    $$p{size}->for(sub                                                          # Process each utf32 character in the block of memory
     {my ($index, $start, $next, $end) = @_;

      Mov r14d, "[r15]";                                                        # Load utf32 character
      Add r15, RegisterSize r14d;                                               # Move up to next utf32 character
      Vpbroadcastd       zmm29, r14d;                                           # Process 16 copies of the utf32 character
      Vpcmpud  k7,       zmm29, zmm30, 5;                                       # Look for start of range
      Vpcmpud "k6\{k7}", zmm29, zmm31, 2;                                       # Look for end of range
      Ktestw k6, k6;                                                            # Was there a match ?
      Jz $next;                                                                 # No character was matched
                                                                                # Process matched character
      if ($recordOffsetInRange == 1)                                            # Record offset in classification range in high byte as used for bracket matching
       {Vpcompressd "zmm29\{k6}", zmm0;                                         # Place classification byte at start of xmm29
        Vpextrd r13d, xmm29, 0;                                                 # Extract start of range
        Mov r12, r13;                                                           # Copy start of range
        Shr r12, 24;                                                            # Classification start
        And r13, 0x00ffffff;                                                    # Range start
        Sub r14, r13;                                                           # Offset in range
        Add r12, r14;                                                           # Offset in classification
        Mov "[r15-1]", r12b;                                                    # Save classification in high byte as in case 1 above.
       }
      elsif ($recordOffsetInRange == 2)                                         # Record classification in high byte and offset in classification range in low byte as used for alphabets
       {Vpcompressd "zmm29\{k6}", zmm0;                                         # Place classification byte and start of range at start of xmm29
        Vpextrd r13d, xmm29, 0;                                                 # Extract start of range specification
        Mov r12, r13;                                                           # Range classification code and start of range
        Shr r12, 24; Shl r12, 24;                                               # Clear low three bytes
        And r13, 0x00ffffff;                                                    # Utf Range start minus classification code

        Vpcompressd "zmm29\{k6}", zmm1;                                         # Place start of alphabet at start of xmm29
        Vpextrd r11d, xmm29, 0;                                                 # Extract offset of alphabet in range
        Shr r11, 24;                                                            # Alphabet offset
        Add r11, r14;                                                           # Range start plus utf32
        Sub r11, r13;                                                           # Offset of utf32 in alphabet range
        Or  r12, r11;                                                           # Case 2 above
        Mov "[r15-4]", r12d;                                                    # Save offset of utf32 in alphabet range in low bytes as in case 2 above.
       }
      else                                                                      # Record classification in high byte
       {Vpcompressd "zmm29\{k6}", zmm0;                                         # Place classification byte at start of xmm29
        Vpextrb "[r15-1]", xmm29, 3;                                            # Extract and save classification in high byte as in case 0 above.
       }
     });

    SetLabel $finish;
    PopR;
   } parameters=>[qw(address size)],
     name => "ClassifyRange_$recordOffsetInRange";

  $s->call(parameters=>{address=>$address, size=>$size});
 } # ClassifyRange

sub ClassifyInRange($$)                                                         # Character classification: classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1 formatted in double words with each double word in zmm0 having the classification in the highest 8 bits and with zmm0 and zmm1 having the utf32 character at the start (zmm0) and end (zmm1) of each range in the lowest 18 bits.  The classification bits from the first matching range are copied into the high (unused) byte of each utf32 character in the block of memory.  The effect is to replace the high order byte of each utf32 character with a classification code saying what type of character we are working.
 {my ($address, $size) = @_;                                                    # Variable address of utf32 string to classify, variable length of utf32 string to classify
  @_ == 2 or confess "Two parameters required";
  ClassifyRange(0, $address, $size);
 }

sub ClassifyWithInRange($$)                                                     # Bracket classification: Classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1 formatted in double words with the classification range in the high byte of each dword in zmm0 and the utf32 character at the start (zmm0) and end (zmm1) of each range in the lower 18 bits of each dword.  The classification bits from the position within the first matching range are copied into the high (unused) byte of each utf32 character in the block of memory.  With bracket matching this gives us a normalized bracket number.
 {my ($address, $size) = @_;                                                    # Variable address of utf32 string to classify, variable length of utf32 string to classify
  @_ == 2 or confess "Two parameters required";
  ClassifyRange(1, $address, $size);
 }

sub ClassifyWithInRangeAndSaveOffset($$)                                        # Alphabetic classification: classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1 formatted in double words with the classification code in the highest byte of each double word in zmm0 and the offset of the first element in the range in the highest byte of each dword in zmm1.  The lowest 18 bits of each double word in zmm0 and zmm1  contain the utf32 characters marking the start and end of each range. The classification bits from zmm1 for the first matching range are copied into the high byte of each utf32 character in the block of memory.  The offset in the range is copied into the lowest byte of each utf32 character in the block of memory.  The middle two bytes are cleared.  The classification byte is placed in the lowest byte of the utf32 character.
 {my ($address, $size) = @_;                                                    # Variable address of utf32 string to classify, variable length of utf32 string to classify
  @_ == 2 or confess "Two parameters required";
  ClassifyRange(2, $address, $size);
 }

#   4---+---3---+---2---+---1---+---0  Octal not decimal
#    CCCCCCCC        XXXXXXXXXXXXXXXX  ClassifyWithInRangeAndSaveWordOffset C == classification, X == offset in range 0-2**16

sub ClassifyWithInRangeAndSaveWordOffset($$$)                                   # Alphabetic classification: classify the utf32 characters in a block of memory of specified length using a range specification held in zmm0, zmm1, zmm2 formatted in double words. Zmm0 contains the low end of the range, zmm1 the high end and zmm2 contains the range offset in the high word of each Dword and the lexical classification on the lowest byte of each dword. Each utf32 character recognized is replaced by a dword whose upper byte is the lexical classification and whose lowest word is the range offset.
 {my ($address, $size, $classification) = @_;                                   # Variable address of string of utf32 characters, variable size of string in utf32 characters, variable one byte classification code for this range
  @_ == 3 or confess "Three parameters required";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    my $finish = Label;

    PushR 12, 13, 14, 15, 6, 7, 29..31;

    $$p{address}->setReg(15);                                                   # Address of first utf32 character
    $$p{size}->for(sub                                                          # Process each utf32 character in the block of memory
     {my ($index, $start, $next, $end) = @_;

      Mov r14d, "[r15]";                                                        # Load utf32 character
      Add r15, RegisterSize r14d;                                               # Move up to next utf32 character
      Vpbroadcastd       zmm31, r14d;                                           # Process 16 copies of the utf32 character
      Vpcmpud  k7,       zmm31, zmm0, 5;                                        # Look for start of range
      Vpcmpud "k6\{k7}", zmm31, zmm1, 2;                                        # Look for end of range
      Ktestw k6, k6;                                                            # Was there a match ?
      Jz $next;                                                                 # No character was matched
                                                                                # Process matched character
      Vpcompressd "zmm31\{k6}", zmm2;                                           # Corresponding classification and offset
      Vpextrd r13d, xmm31, 0;                                                   # Extract start of range specification - we can subtract this from the character to get its offset in this range
      Mov r12, r14;                                                             # Range classification code and start of range
      Sub r12, r13;                                                             # We now have the offset in the range

      $$p{classification}->setReg(13);                                          # Classification code
      Shl r13, 24;                                                              # Shift classification code into position
      Or  r12, r13;                                                             # Position classification code
      Mov "[r15-4]", r12d;                                                      # Classification in highest byte of dword, offset in range in lowest word
     });
    PopR;
   } parameters => [qw(address size classification)],
     name       => "ClassifyWithInRangeAndSaveWordOffset";

  $s->call(parameters=>{address=>$address, size=>$size,
           classification=>$classification});
 } # ClassifyWithInRangeAndSaveWordOffset

sub Nasm::X86::Variable::dClassify($$$)                                         # Classify the dword in a variable between ranges held in zmm registers and return the index of the matching range.
 {my ($d, $low, $high) = @_;                                                    # Variable containing a dword, zmm number not 31 holding the low end of each range, zmm number not 31 holding the high end of each range
  @_ == 3 or confess "Three parameters required";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters

    PushR 15, 5, 6, 7, 31;
    $$p{d}->setReg(15);                                                         # Dword to classify
    Vpbroadcastd zmm31, r15d;                                                   # 16 copies of the dword
    Vpcmpud  k7, zmm($low,  31), $Vpcmp->le;                                    # Look for start of range
    Vpcmpud  k6, zmm($high, 31), $Vpcmp->ge;                                    # Look for end of range
    Kandq k5, k6, k7;                                                           # Look for end of range
    Kmovq r15, k5;                                                              # Recover point
    $$p{point}->getReg(15);                                                     # Return point
    PopR;
   } parameters => [qw(d point)],
     name       => "Nasm::X86::Variable::dClassify";

  my $point = V point => 0;                                                     # Point of matching range or zero if no match
  $s->call(parameters=>{d=>$d, point=>$point});
  $point
 } # dClassify

#D1 C Strings                                                                   # C strings are a series of bytes terminated by a zero byte.

sub Cstrlen()                                                                   #P Length of the C style string addressed by rax returning the length in r15.
 {@_ == 0 or confess "Deprecated in favor of StringLength";

  my $s = Subroutine                                                            # Create area
   {PushR rax, rdi, rcx;
    Mov rdi, rax;
    Mov rcx, -1;
    ClearRegisters rax;
    push @text, <<END;
    repne scasb
END
    Mov r15, rcx;
    Not r15;
    Dec r15;
    PopR;
   } name => "Cstrlen";

  $s->call;
 }

sub StringLength($)                                                             # Length of a zero terminated string.
 {my ($string) = @_;                                                            # String
  @_ == 1 or confess "One parameter: zero terminated string";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    PushR rax, rdi, rcx;
    $$p{string}->setReg(rax);                                                   # Address string
    Mov rdi, rax;
    Mov rcx, -1;
    ClearRegisters rax;
    push @text, <<END;
    repne scasb
END
    Not rcx;
    Dec rcx;
    $$p{size}->getReg(rcx);                                                     # Save length
    PopR;
   } parameters => [qw(string size)], name => 'StringLength';

  $s->call(parameters=>{string=>$string, size => my $z = V size => 0});         # Variable that holds the length of the string

  $z
 }

#D1 Areas                                                                       # An area is single extensible block of memory which contains other data structures such as strings, arrays, trees within it.

our $AreaFreeChain = 0;                                                         # The key of the Yggdrasil tree entry in the area recording the start of the free chain

sub DescribeArea(%)                                                             # Describe a relocatable area.
 {my (%options) = @_;                                                           # Optional variable addressing the start of the area
  my $N = 4096;                                                                 # Initial size of area
  my $w = RegisterSize 31;

  my $quad = RegisterSize rax;                                                  # Field offsets
  my $size = 0;
  my $used = $size + $quad;                                                     # Amount of memory in the area that has been used - includes the free chain.
  my $free = $used + $quad;                                                     # Free chain blocks = freed zmm blocks
  my $tree = $free + $quad;                                                     # Start of Yggdrasil,
  my $data = $w;                                                                # Data starts in the next zmm block

  genHash(__PACKAGE__."::Area",                                                 # Definition of area
    N          => $N,                                                           # Initial allocation
    sizeOffset => $size,                                                        # Size field offset
    usedOffset => $used,                                                        # Used field offset
    freeOffset => $tree,                                                        # Free chain offset
    treeOffset => $tree,                                                        # Yggdrasil - a tree of global variables in this area
    dataOffset => $data,                                                        # The start of the data
    address    => ($options{address} // V address => 0),                        # Variable that addresses the memory containing the area
    zmmBlock   => $w,                                                           # Size of a zmm block - 64 bytes
    nextOffset => $w - RegisterSize(eax),                                       # Position of next offset on free chain
   );
 }

sub CreateArea(%)                                                               # Create an relocatable area and returns its address in rax. We add a chain header so that 64 byte blocks of memory can be freed and reused within the area.
 {my (%options) = @_;                                                           # Free=>1 adds a free chain.
  my $area = DescribeArea;                                                      # Describe an area
  my $N     = $area->N;
  my $used  = $area->usedOffset;
  my $data  = $area->dataOffset;
  my $size  = $area->sizeOffset;

  my $s = Subroutine                                                            # Allocate area
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    my $area = AllocateMemory K size=> $N;                                      # Allocate memory and save its location in a variable

    PushR rax;
    $$s{area}->address->copy($area);                                            # Save address of area
    $area->setReg(rax);
    Mov "dword[rax+$used]", $data;                                              # Initially used space
    Mov "dword[rax+$size]", $N;                                                 # Size
    PopR;
   } structures=>{area=>$area}, name => 'CreateArea';

  $s->call(structures=>{area=>$area});                                          # Variable that holds the reference to the area which is updated when the area is reallocated

  $area
 }

sub Nasm::X86::Area::free($)                                                    # Free an area
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";
  FreeMemory($area->address, $area->size)
 }

sub Nasm::X86::Area::used($)                                                    # Return the currently used size of an area as a variable.
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";

  SaveFirstFour;
  $area->address->setReg(rax);                                                  # Address area
  Mov rdx, "[rax+$$area{usedOffset}]";                                          # Used
  Sub rdx, $area->dataOffset;                                                   # Subtract size of header so we get the actual amount in use
  my $size = V 'area used up' => rdx;                                           # Save length in a variable
  RestoreFirstFour;
  $size                                                                         # Return variable length
 }

sub Nasm::X86::Area::size($)                                                    # Get the size of an area as a variab;e.
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";

  PushR rax;
  $area->address->setReg(rax);                                                  # Address area
  Mov rax, "[rax+$$area{sizeOffset}]";                                          # Get size
  my $size = V 'size of area' => rax;                                           # Save size in a variable
  PopR;
  $size                                                                         # Return size
 }

sub Nasm::X86::Area::updateSpace($$)                                            #P Make sure that the variable addressed area has enough space to accommodate content of the variable size.
 {my ($area, $size) = @_;                                                       # Area descriptor, variable size needed
  @_ == 2 or confess "Two parameters";

  my $s = Subroutine
   {my ($p, $s) = @_;                                                           # Parameters, structures
    PushR rax, 10, 12..15;
    my $base     = rax;                                                         # Base of area
    my $size     = r15;                                                         # Current size
    my $used     = r14;                                                         # Currently used space
    my $request  = r13;                                                         # Requested space
    my $newSize  = r12;                                                         # New size needed
    my $proposed = r10;                                                         # Proposed size

    my $area = $$s{area};                                                       # Address area
    $area->address->setReg($base);                                              # Address area
    $$p{size}->setReg($request);                                                # Requested space

    Mov $size, "[$base+$$area{sizeOffset}]";
    Mov $used, "[$base+$$area{usedOffset}]";
    Mov $newSize, $used;
    Add $newSize, $request;

    Cmp $newSize,$size;                                                         # New size needed
    IfGt                                                                        # New size is bigger than current size
    Then                                                                        # More space needed
     {Mov $proposed, 4096 * 1;                                                  # Minimum proposed area size
      K(loop=>36)->for(sub                                                      # Maximum number of shifts
       {my ($index, $start, $next, $end) = @_;
        Shl $proposed, 1;                                                       # New proposed size
        Cmp $proposed, $newSize;                                                # Big enough?
        Jge $end;                                                               # Big enough!
       });

      my $address = AllocateMemory V size => $proposed;                         # Create new area
      CopyMemory($area->address, $address, $area->size);                        # Copy old area into new area
      FreeMemory $area->address, $area->size;                                   # Free previous memory previously occupied area
      $area->address->copy($address);                                           # Save new area address
      $address->setReg($base);                                                  # Address area
      Mov "[$base+$$area{sizeOffset}]", $proposed;                              # Save the new size in the area
     };

    PopR;
   } parameters => [qw(size)],
     structures => {area => $area},
     name       => 'Nasm::X86::Area::updateSpace';

  $s->call(parameters=>{size => $size}, structures=>{area => $area});
 } # updateSpace

sub Nasm::X86::Area::makeReadOnly($)                                            # Make an area read only.
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Make an area readable";
    SaveFirstFour;
    $$p{address}->setReg(rax);
    Mov rdi, rax;                                                               # Address of area
    Mov rsi, "[rax+$$area{sizeOffset}]";                                        # Size of area

    Mov rdx, 1;                                                                 # Read only access
    Mov rax, 10;
    Syscall;
    RestoreFirstFour;                                                           # Return the possibly expanded area
   } parameters=>[qw(address)], name => 'Nasm::X86::Area::makeReadOnly';

  $s->call(parameters=>{address => $area->address});
 }

sub Nasm::X86::Area::makeWriteable($)                                           # Make an area writable.
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    Comment "Make an area writable";
    SaveFirstFour;
    $$p{address}->setReg(rax);
    Mov rdi, rax;                                                               # Address of area
    Mov rsi, "[rax+$$area{sizeOffset}]";                                        # Size of area
    Mov rdx, 3;                                                                 # Read only access
    Mov rax, 10;
    Syscall;
    RestoreFirstFour;                                                           # Return the possibly expanded area
   } parameters=>[qw(address)], name => 'Nasm::X86::Area::makeWriteable';

  $s->call(parameters=>{address => $area->address});
 }

#D2 Alloc/Free                                                                  # Allocate and free memory in an area, either once only but in variable size blocks or reusably in zmm sized blocks via the free block chain.

sub Nasm::X86::Area::allocate($$)                                               # Allocate the variable amount of space in the variable addressed area and return the offset of the allocation in the area as a variable.
 {my ($area, $size) = @_;                                                       # Area descriptor, variable amount of allocation
  @_ == 2 or confess "Two parameters";

  SaveFirstFour;
  $area->updateSpace($size);                                                    # Update space if needed
  $area->address->setReg(rax);
  Mov rsi, "[rax+$$area{usedOffset}]";                                          # Currently used
  my $offset = V(offset => rsi);                                                # Variable to hold offset of allocation
  $size  ->setReg(rdi);
  Add rsi, rdi;
  Mov "[rax+$$area{usedOffset}]", rsi;                                          # Update currently used
  RestoreFirstFour;
  $offset
 }

sub Nasm::X86::Area::allocZmmBlock($)                                           # Allocate a block to hold a zmm register in the specified area and return the offset of the block as a variable.
 {my ($area) = @_;                                                              # Area
  @_ == 1 or confess "One parameter";
  my $offset = V(offset => 0);                                                  # Variable to hold offset of allocation

  PushR rax, my $first = r14, my $second = r15, 31;
  my $firstD = $first.'d'; my $secondD = $second.'d';

  $area->address->setReg(rax);                                                  # Address of area
  Mov $firstD, "[rax+$$area{freeOffset}]";                                      # Offset of first block in free chain if such a block exists
  Cmp $first, 0;
  IfGt
  Then                                                                          # Free block available
   {$area->getZmmBlock(V (offset => $first), 31);                               # Load the first block on the free chain
    dFromZ(31, 0)->setReg($second);                                             # The location of the second block if any
    Mov "[rax+$$area{freeOffset}]", $secondD;                                   # Offset of first block in free chain if such a block exists
    ClearRegisters 31;                                                          # Clear the zmm block - possibly this only needs to be done if we are reusing a block
    $offset->getReg($first);                                                    # First block is the allocated block
    $area->putZmmBlock($offset, 31);
   },
  Else                                                                          # Cannot reuse a free block so allocate
   {$offset->copy($area->allocate(K size => $area->zmmBlock));                  # Copy offset of allocation
   };
  PopR;

  $offset                                                                       # Return offset of allocated block
 }

sub Nasm::X86::Area::freeZmmBlock($$)                                           #P Free a block in an area by placing it on the free chain.
 {my ($area, $offset) = @_;                                                     # Area descriptor, offset of zmm block to be freed
  @_ == 2 or confess "Two parameters";

  PushR rax, my $first = r14, my $second = r15, zmm7;
  my $firstD = $first.'d'; my $secondD = $second.'d';
  $area->address->setReg(rax);                                                  # Address of area
  Mov $secondD, "[rax+$$area{freeOffset}]";                                     # Offset of first block in free chain if such a block exists
  ClearRegisters zmm7;
  Movd xmm7, $secondD;
  $area->putZmmBlock($offset, 7);
  $offset->setReg($first);                                                      # Offset if what will soon be the first block on the free chain
  Mov "[rax+$$area{freeOffset}]", $firstD;                                      # Offset of first block in free chain if such a block exists
  PopR;
 }

sub Nasm::X86::Area::freeChainSpace($)                                          # Count the number of blocks available on the free chain
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameters";
  my $count = V('free chain blocks' => 0);

  PushR rax, my $first = r15, 31;
  my $firstD = $first.'d';

  $area->address->setReg(rax);                                                  # Address of area
  Mov $firstD, "[rax+$$area{freeOffset}]";                                      # Offset of first block in free chain if such a block exists
  V( loop => 99)->for(sub                                                       # Loop through free block chain
   {my ($index, $start, $next, $end) = @_;
    Cmp $first, 0;
    IfEq Then{Jmp $end};                                                        # No more free blocks
    $area->getZmmBlock(V(offset => $first), 31);                                # Load the first block on the free chain
    dFromZ(31, 0)->setReg($first);                                              # The location of the second block if any
    $count++                                                                    # Increment count of number of  blocks on the free chain
   });
  PopR;
  $count * RegisterSize 31;
 }

sub Nasm::X86::Area::getZmmBlock($$$)                                           #P Get the block with the specified offset in the specified string and return it in the numbered zmm.
 {my ($area, $block, $zmm) = @_;                                                # Area descriptor, offset of the block as a variable, number of zmm register to contain block
  @_ == 3 or confess "Three parameters";

  my $a = rdi;                                                                  # Work registers
  my $o = rsi;

  $area->address->setReg($a);                                                   # Area address
  $block->setReg($o);                                                           # Offset of block in area

  Cmp $o, $area->dataOffset;
  IfLt                                                                          # We could have done this using variable arithmetic, but such arithmetic is expensive and so it is better to use register arithmetic if we can.
  Then
   {PrintErrTraceBack "Attempt to get block before start of area";
   };

  Vmovdqu64 "zmm$zmm", "[$a+$o]";                                               # Read from memory
 }

sub Nasm::X86::Area::putZmmBlock($$$)                                           #P Write the numbered zmm to the block at the specified offset in the specified area.
 {my ($area, $block, $zmm) = @_;                                                # Area descriptor, offset of the block as a variable, number of zmm register to contain block
  @_ == 3 or confess "Three parameters";

  my $a = rdi;                                                                  # Work registers
  my $o = rsi;

  $area->address->setReg($a);                                                   # Area address
  $block->setReg($o);                                                           # Offset of block in area

  Cmp $o, $area->dataOffset;
  IfLt                                                                          # We could have done this using variable arithmetic, but such arithmetic is expensive and so it is better to use register arithmetic if we can.
  Then
   {PrintErrTraceBack "Attempt to put block before start of area";
   };

  Vmovdqu64 "[$a+$o]", "zmm$zmm";                                               # Read from memory
 }

sub Nasm::X86::Area::clearZmmBlock($$)                                          #P Clear the zmm block at the specified offset in the area
 {my ($area, $offset) = @_;                                                     # Area descriptor, offset of the block as a variable
  @_ == 2 or confess "Two parameters";

  PushR 31;                                                                     # Clear a zmm block
  ClearRegisters 31;
  $area->putZmmBlock($offset, 31);
  PopR;
 }

#D2 Yggdrasil                                                                   # The world tree from which we can address so many other things

sub Nasm::X86::Area::checkYggdrasilCreated($)                                   #P Return a tree descriptor to the Yggdrasil world tree for an area.  If Yggdrasil has not been created the B<found> variable will be zero else one.
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";

  my $t = $area->DescribeTree;                                                  # Tree descriptor for Yggdrasil
  PushR rax;
  $area->address->setReg(rax);                                                  #P Address underlying area
  Mov rax, "[rax+$$area{treeOffset}]";                                          # Address Yggdrasil
  my $v = V('Yggdrasil', rax);                                                  # Offset to Yggdrasil if it exists else zero
  Cmp rax, 0;                                                                   # Does Yggdrasil even exist?
  IfNe
  Then                                                                          # Yggdrasil has been created so we can address it
   {$t->first->copy(rax);
    $t->found->copy(1);
   },
  Else                                                                          # Yggdrasil has not been created
   {$t->found->copy(0);
   };
  Cmp rax, 0;                                                                   # Restate whether Yggdrasil exists so that we can test its status quickly in the following code.
  PopR rax;
  $t
 }

sub Nasm::X86::Area::establishYggdrasil($)                                      #P Return a tree descriptor to the Yggdrasil world tree for an area creating the world tree Yggdrasil if it has not already been created.
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";

  my $t = $area->DescribeTree;                                                  # Tree descriptor for Yggdrasil
  PushR rax, rdi;
  $area->address->setReg(rax);                                                  #P Address underlying area
  Mov rdi, "[rax+$$area{treeOffset}]";                                          # Address Yggdrasil
  Cmp rdi, 0;                                                                   # Does Yggdrasil even exist?
  IfNe
  Then                                                                          # Yggdrasil has already been created so we can address it
   {$t->first->copy(rdi);
   },
  Else                                                                          # Yggdrasil has not been created
   {my $T = $area->CreateTree();
    $T->first->setReg(rdi);
    $t->first->copy(rdi);
    Mov "[rax+$$area{treeOffset}]", rdi;                                        # Save offset of Yggdrasil
   };
  PopR;
  $t
 }

#D2 Areas as Strings                                                            # Use the memory supplied by the area as a string - however, in general, this is too slow unless coupled with another slow operation such as executing a command, mapping a file or writing to a file.

sub Nasm::X86::Area::appendMemory($$$)                                          # Append the variable addressed content in memory of variable size to the specified area.
 {my ($area, $address, $size) = @_;                                             # Area descriptor, variable address of content, variable length of content
  @_ == 3 or confess "Three parameters";

  my $used = "[rax+$$area{usedOffset}]";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    SaveFirstFour;
    my $area = $$s{area};
    $area->address->setReg(rax);
    my $oldUsed = V("used", $used);
    $area->updateSpace($$p{size});                                              # Update space if needed

    my $target  = $oldUsed + $area->address;
    CopyMemory($$p{address}, $target, $$p{size});                               # Copy data into the area

    my $newUsed = $oldUsed + $$p{size};

    $area->address->setReg(rax);                                                # Update used field
    $newUsed->setReg(rdi);
    Mov $used, rdi;

    RestoreFirstFour;
   } structures => {area => $area},
     parameters => [qw(address size)],
     name       => 'Nasm::X86::Area::m';

  $s->call(structures => {area => $area},
           parameters => {address => $address, size => $size});
 }

sub Nasm::X86::Area::q($$)                                                      # Append a constant string to the area.
 {my ($area, $string) = @_;                                                     # Area descriptor, string
  @_ == 2 or confess "Two parameters";

  my $s = Rs($string);
  $area->appendMemory(V('address', $s), V('size', length($string)));
 }

sub Nasm::X86::Area::ql($$)                                                     # Append a quoted string containing new line characters to the specified area.
 {my ($area, $const) = @_;                                                      # Area, constant
  @_ == 2 or confess "Two parameters";
  for my $l(split /\s*\n/, $const)
   {$area->q($l);
    $area->nl;
   }
 }

sub Nasm::X86::Area::char($$)                                                   # Append a character expressed as a decimal number to the specified area.
 {my ($area, $char) = @_;                                                       # Area descriptor, number of character to be appended
  @_ == 2 or confess "Two parameters";
  my $s = Rb(ord($char));
  $area->appendMemory(V(address => $s), K size => 1);                           # Move data
 }

sub Nasm::X86::Area::nl($)                                                      # Append a new line to the area addressed by rax.
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";
  $area->char("\n");
 }

sub Nasm::X86::Area::zero($)                                                    # Append a trailing zero to the area addressed by rax.
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";
  $area->char("\0");
 }

sub Nasm::X86::Area::append($@)                                                 # Append one area to another.
 {my ($target, $source) = @_;                                                   # Target area descriptor, source area descriptor
  @_ == 2 or confess "Two parameters";

  SaveFirstFour;
  $source->address->setReg(rax);
  Mov rdi, "[rax+$$source{usedOffset}]";
  Sub rdi, $source->dataOffset;
  Lea rsi, "[rax+$$source{dataOffset}]";
  $target->appendMemory(V(address => rsi), V size => rdi);
  RestoreFirstFour;
 }

sub Nasm::X86::Area::clear($)                                                   # Clear an area
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    PushR rax, rdi;
    $$p{address}->setReg(rax);
    Mov rdi, $area->dataOffset;
    Mov "[rax+$$area{usedOffset}]", rdi;
    ClearRegisters rdi;
    Mov "[rax+$$area{freeOffset}]", rdi;
    Mov "[rax+$$area{treeOffset}]", rdi;
    PopR;
   } parameters=>[qw(address)], name => 'Nasm::X86::Area::clear';

  $s->call(parameters=>{address => $area->address});
 }

sub Nasm::X86::Area::write($$)                                                  # Write the content of the specified area to a file specified by a zero terminated string.
 {my ($area, $file) = @_;                                                       # Area descriptor, variable addressing file name
  @_ == 2 or confess "Two parameters";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    SaveFirstFour;

    $$p{file}->setReg(rax);
    OpenWrite;                                                                  # Open file
    my $file = V(fd => rax);                                                    # File descriptor

    $$p{address}->setReg(rax);                                                  # Write file
    Lea rsi, "[rax+$$area{dataOffset}]";
    Mov rdx, "[rax+$$area{usedOffset}]";
    Sub rdx, $area->dataOffset;

    Mov rax, 1;                                                                 # Write content to file
    $file->setReg(rdi);
    Syscall;

    $file->setReg(rax);
    CloseFile;
    RestoreFirstFour;
   } parameters=>[qw(file address)], name => 'Nasm::X86::Area::write';

  $s->call(parameters=>{address => $area->address, file => $file});
 }

sub Nasm::X86::Area::read($@)                                                   # Read a file specified by a variable addressed zero terminated string and place the contents of the file into the named area.
 {my ($area, $file) = @_;                                                       # Area descriptor, variable addressing file name
  @_ == 2 or confess "Two parameters";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    Comment "Read an area";
    my ($address, $size) = ReadFile $$p{file};
    my $area = $$s{area};
    $area->appendMemory($address, $size);                                       # Move data into area
    FreeMemory($size, $address);                                                # Free memory allocated by read
   } structures => {area=>$area},
     parameters => [qw(file)],
     name       => 'Nasm::X86::Area::read';

  $s->call(structures => {area => $area}, parameters => {file => $file});
 }

sub Nasm::X86::Area::out($)                                                     # Print the specified area on sysout.
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    SaveFirstFour;
    $$p{address}->setReg(rax);

    Mov rdi, "[rax+$$area{usedOffset}]";                                        # Length to print
    Sub rdi, $area->dataOffset;                                                 # Length to print
    Lea rax, "[rax+$$area{dataOffset}]";                                        # Address of data field
    PrintOutMemory;
    RestoreFirstFour;
   } parameters=>[qw(address)], name => 'Nasm::X86::Area::out';

  $s->call(parameters=>{address => $area->address});
 }

sub Nasm::X86::Area::outNL($)                                                   # Print the specified area on sysout followed by a new line.
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";

  $area->out;
  PrintOutNL;
 }

sub Nasm::X86::Area::printOut($$$)                                              # Print part of the specified area on sysout.
 {my ($area, $offset, $length) = @_;                                            # Area descriptor, offset, length
  @_ == 3 or confess "Three parameters";

  PushR rax, rdi, rsi;
  ($area->address + $offset)->setReg(rax);
  $length                   ->setReg(rdi);
  PrintOutMemoryNL;
  PopR;
 }

#sub Nasm::X86::Area::outPartNL($)                                               # Print part of the specified area on sysout followed by a new line.
# {my ($area) = @_;                                                              # Area descriptor
#  @_ == 1 or confess "One parameter";
#
#  $area->outPart;
#  PrintOutNL;
# }
#
sub Nasm::X86::Area::dump($$;$)                                                 # Dump details of an area.
 {my ($area, $title, $depth) = @_;                                              # Area descriptor, title string, optional variable number of 64 byte blocks to dump
  @_ == 2 or @_ == 3 or confess "Two or three parameters";
  my $blockSize = 64;                                                           # Print in blocks of this size

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    PushR rax, rdi;
    my $area = $$s{area};
    $area->address->setReg(rax);                                                # Get address of area
    PrintOutString("Area   ");

    PushR rax;                                                                  # Print size
    Mov rax, "[rax+$$area{sizeOffset}]";
    PrintOutString "  Size: ";
    PrintOutRaxRightInDec K width => 8;
    PrintOutString "  ";
    PopR rax;

    PushR rax;                                                                  # Print size
    Mov rax, "[rax+$$area{usedOffset}]";
    PrintOutString("  Used: ");
    PrintOutRaxRightInDec  K width => 8;
    PrintOutNL;
    PopR rax;

    $$p{depth}->for(sub                                                         # Print the requested number of blocks
     {my ($index, $start, $next, $end) = @_;
      Mov rdi, $blockSize;                                                      # Length of each print
      ($index*RegisterSize(zmm31))->out('', ' | ');
      my $address = $area->address + $index * $blockSize;                       # Address of block to print
      $address->setReg(rax);
      PrintOutMemory_InHexNL;
     });

    PopR;
   } structures=>{area=>$area},
     parameters=>[qw(depth)],
     name => "Nasm::X86::Area::dump";

  PrintOutStringNL $title;
  $s->call(structures=>{area=>$area}, parameters=>{depth => ($depth // V('depth', 4))});
 }

#D1 Tree                                                                        # Tree constructed as sets of blocks in an area.

sub DescribeTree(%)                                                             #P Return a descriptor for a tree with the specified options.
 {my (%options) = @_;                                                           # Tree description options

  confess "Maximum keys must be less than or equal to 14"
    unless ($options{length}//0) <= 14;                                         # Maximum number of keys is 14

  my $b = RegisterSize 31;                                                      # Size of a block == size of a zmm register
  my $o = RegisterSize eax;                                                     # Size of a double word

  my $keyAreaWidth = $b - $o * 2 ;                                              # Key / data area width  in bytes
  my $kwdw   = $keyAreaWidth / $o;                                              # Number of keys in a maximal block
  my $length = $options{length} // $keyAreaWidth / $o;                          # Length of block to split

  confess "Length must be greater than 2, not: $length" unless $length > 2;     # Check minimum length
  confess "Length must be less than or equal to $kwdw, not $length"             # Check maximum length
    unless $length <= $kwdw;

  my $l2 = int($length/2);                                                      # Minimum length of length after splitting

  my $usage = sub
   {return {} unless my $u = $options{usage};
    my $r = ref $u;                                                             # Usage expressed as:
    return {$u=>1}            unless $r;                                        # Scalar
    return $u                 if $r =~ m(hash)i;                                # Hash
    return {map {$_=> 1} @$u} if $r =~ m(array)i;                               # Array
    confess qq(Unexpected usage parameter of type: $r\n).dump($u);
   }->();

  genHash(__PACKAGE__."::Tree",                                                 # Tree
    area        => ($options{area} // DescribeArea),                            # Area definition.
    length       => $length,                                                    # Number of keys in a maximal block
    lengthLeft   => $l2,                                                        # Left minimal number of keys
    lengthMiddle => $l2 + 1,                                                    # Number of splitting key counting from 1
    lengthMin    => $length - 1 - $l2,                                          # The smallest number of keys we are allowed in any node other than a root node.
    lengthOffset => $keyAreaWidth,                                              # Offset of length in keys block.  The length field is a word - see: "MultiWayTree.svg"
    lengthRight  => $length - 1 - $l2,                                          # Right minimal number of keys
    loop         => $b - $o,                                                    # Offset of keys, data, node loop.
    maxKeys      => $length,                                                    # Maximum number of keys allowed in this tree which might well ne less than the maximum we can store in a zmm.
    offset       => V(offset  => 0),                                            # Offset of last node found
    splittingKey => ($l2 + 1) * $o,                                             # Offset at which to split a full block
    treeBits     => $keyAreaWidth + 2,                                          # Offset of tree bits in keys block.  The tree bits field is a word, each bit of which tells us whether the corresponding data element is the offset (or not) to a sub tree of this tree .
    treeBitsMask => 0x3fff,                                                     # Total of 14 tree bits
    keyDataMask  => 0x3fff,                                                     # Key data mask
    nodeMask     => 0x7fff,                                                     # Node mask
    up           => $keyAreaWidth,                                              # Offset of up in data block.
    width        => $o,                                                         # Width of a key or data slot.
    zWidth       => $b,                                                         # Width of a zmm register
    zWidthD      => $b / $o,                                                    # Width of a zmm in double words being the element size
    maxKeysZ     => $b / $o - 2,                                                # The maximum possible number of keys in a zmm register
    maxNodesZ    => $b / $o - 1,                                                # The maximum possible number of nodes in a zmm register

    rootOffset   => $o * 0,                                                     # Offset of the root field in the first block - the root field contains the offset of the block containing the keys of the root of the tree
    upOffset     => $o * 1,                                                     # Offset of the up field which points to any containing tree
    sizeOffset   => $o * 2,                                                     # Offset of the size field which tells us the number of  keys in the tree
    middleOffset => $o * ($l2 + 0),                                             # Offset of the middle slot in bytes
    rightOffset  => $o * ($l2 + 1),                                             # Offset of the first right slot in bytes

    usage        => $usage,                                                     # How this tree is being used so that we can map operators into subroutine calls

    compare      => V(compare => 0),                                            # Last comparison result -1, 0, +1
    data         => V(data    => 0),                                            # Variable containing the current data
    debug        => V(debug   => 0),                                            # Write debug trace if true
    first        => V(first   => 0),                                            # Variable addressing offset to first block of the tree which is the header block
    found        => V(found   => 0),                                            # Variable indicating whether the last find was successful or not
    index        => V(index   => 0),                                            # Index of key in last node found
    key          => V(key     => 0),                                            # Variable containing the current key
    offset       => V(key     => 0),                                            # Variable containing the offset of the block containing the current key
    subTree      => V(subTree => 0),                                            # Variable indicating whether the last find found a sub tree
   );
 }

sub Nasm::X86::Area::DescribeTree($%)                                           #P Return a descriptor for a tree in the specified area with the specified options.
 {my ($area, %options) = @_;                                                    # Area descriptor, options for tree
  @_ >= 1 or confess;

  DescribeTree(area=>$area, %options)
 }

sub Nasm::X86::Area::CreateTree($%)                                             # Create a tree in an area.
 {my ($area, %options) = @_;                                                    # Area description, tree options
  @_ % 2 == 1 or confess "Odd number of parameters required";

  my $tree = $area->DescribeTree(%options);                                     # Return a descriptor for a tree in the specified area

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    my $tree  = $$s{tree};                                                      # Tree
    $tree->first->copy($tree->area->allocZmmBlock);                             # Allocate header

   } structures=>{area => $area, tree => $tree},
     name => 'Nasm::X86::Area::CreateTree';

  $s->call(structures=>{area => $area, tree => $tree});

  $tree                                                                         # Description of array
 }

sub Nasm::X86::Tree::describeTree($%)                                           # Create a description of a tree
 {my ($tree, %options) = @_;                                                    # Tree descriptor, {first=>first node of tree if not the existing first node; area=>area used by tree if not the existing area}
  @_ >= 1 or confess "At least one parameter";

  $tree->area->DescribeTree(%options);                                          # Return a descriptor for a tree
 }

sub Nasm::X86::Tree::position($$)                                               # Create a new tree description for a tree positioned at the specified location
 {my ($tree, $first) = @_;                                                      # Tree descriptor, offset of tree
  my $t = $tree->describeTree;

  $t->first->copy($first);                                                      # Variable addressing offset to first block of keys.
  $t                                                                            # Return new descriptor
 }

sub Nasm::X86::Tree::reposition($$)                                             # Reposition an existing tree at the specified location
 {my ($tree, $first) = @_;                                                      # Tree descriptor, offset to reposition on
  $tree->first->copy($first);                                                   # Variable addressing offset to first block of keys.
  $tree                                                                         # Return existing tree descriptor
 }

sub Nasm::X86::Tree::cloneDescriptor($)                                         # Clone the descriptor of a tree to make a new tree descriptor
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess "One parameter";
  my $t = $tree->describeTree;                                                  # New tree descriptor
  $t->first->copy($tree->first);                                                # Load new descriptor from original descriptor
  $t                                                                            # Return new descriptor
 }

sub Nasm::X86::Tree::copyDescriptor($$)                                         # Copy the description of one tree into another
 {my ($target, $source) = @_;                                                   # The target of the copy, the source of the copy
  @_ == 2 or confess "Two parameters";
  $target->first->copy($source->first);                                         # Load the target from the source
  $target                                                                       # Return target
 }

sub Nasm::X86::Tree::down($)                                                    # Use the current B<find> result held in B<data> to position on the referenced subtree at the next level down.
 {my ($tree) = @_;                                                              # Tree descriptor which has just completed a successful find
  @_ == 1 or confess "One parameter";
  $tree->first->copy($tree->data);                                              # The next sub tree down is addressed by the B<data> field of the tree descriptor
  $tree                                                                         # Return original descriptor
 }

sub Nasm::X86::Tree::copyDescription($)                                         #P Make a copy of a tree descriptor
 {my ($tree) = @_;                                                              # Tree descriptor
  my $t = $tree->describeTree;

  $t->data   ->copy($tree->data );                                              # Variable containing the last data found
  $t->debug  ->copy($tree->debug);                                              # Write debug trace if true
  $t->first  ->copy($tree->first);                                              # Variable addressing offset to first block of keys.
  $t->found  ->copy($tree->found);                                              # Variable indicating whether the last find was successful or not
  $t->index  ->copy($tree->index);                                              # Index of key in last node found
  $t->subTree->copy($tree->subTree);                                            # Variable indicating whether the last find found a sub tree
  $t                                                                            # Return new descriptor
 }

sub Nasm::X86::Tree::firstFromMemory($$)                                        #P Load the first block for a tree into the numbered zmm.
 {my ($tree, $zmm) = @_;                                                        # Tree descriptor, number of zmm to contain first block
  @_ == 2 or confess "Two parameters";
  my $base = rdi; my $offset = rsi;
  $tree->area->address->setReg($base);
  $tree->first->setReg($offset);
  Vmovdqu64 zmm($zmm), "[$base+$offset]";
 }

sub Nasm::X86::Tree::firstIntoMemory($$)                                        #P Save the first block of a tree in the numbered zmm back into memory.
 {my ($tree, $zmm) = @_;                                                        # Tree descriptor, number of zmm containing first block
  @_ == 2 or confess "Two parameters";
  my $base = rdi; my $offset = rsi;
  $tree->area->address->setReg($base);
  $tree->first->setReg($offset);
  Vmovdqu64  "[$base+$offset]", zmm($zmm);
 }

sub Nasm::X86::Tree::rootIntoFirst($$$)                                         #P Put the contents of a variable into the root field of the first block of a tree when held in a zmm register.
 {my ($tree, $zmm, $value) = @_;                                                # Tree descriptor, number of zmm containing first block, variable containing value to put
  @_ == 3 or confess "Three parameters";
  $value->dIntoZ($zmm, $tree->rootOffset);
 }

sub Nasm::X86::Tree::rootFromFirst($$)                                          #P Return a variable containing the offset of the root block of a tree from the first block when held in a zmm register.
 {my ($tree, $zmm) = @_;                                                        # Tree descriptor, number of zmm containing first block
  @_ == 2 or confess "Two parameters";
  dFromZ $zmm, $tree->rootOffset;
 }

sub Nasm::X86::Tree::root($$$)                                                  #P Check whether the specified offset refers to the root of a tree when the first block is held in a zmm register. The result is returned by setting the zero flag to one if the offset is the root, else to zero.
 {my ($t, $F, $offset) = @_;                                                    # Tree descriptor, zmm register holding first block, offset of block as a variable
  @_ == 3 or confess "Three parameters";
  my $root = $t->rootFromFirst($F);                                             # Get the offset of the corresponding data block
  $root == $offset                                                              # Check whether the offset is in fact the root
 }

sub Nasm::X86::Tree::sizeFromFirst($$)                                          #P Return a variable containing the number of keys in the specified tree when the first block is held in a zmm register..
 {my ($tree, $zmm) = @_;                                                        # Tree descriptor, number of zmm containing first block
  @_ == 2 or confess "Two parameters";
  dFromZ $zmm, $tree->sizeOffset;
 }

sub Nasm::X86::Tree::sizeIntoFirst($$$)                                         #P Put the contents of a variable into the size field of the first block of a tree  when the first block is held in a zmm register.
 {my ($tree, $zmm, $value) = @_;                                                # Tree descriptor, number of zmm containing first block, variable containing value to put
  @_ == 3 or confess "Three parameters";
  $value->dIntoZ($zmm, $tree->sizeOffset);
 }

sub Nasm::X86::Tree::incSizeInFirst($$)                                         #P Increment the size field in the first block of a tree when the first block is held in a zmm register.
 {my ($tree, $zmm) = @_;                                                        # Tree descriptor, number of zmm containing first block
  @_ == 2 or confess "Two parameters";
  my $s = dFromZ $zmm, $tree->sizeOffset;
  $tree->sizeIntoFirst($zmm, $s+1);
 }

sub Nasm::X86::Tree::incSize($)                                                 #P Increment the size of a tree
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess "One parameter";
  PushR 31;
  $tree->firstFromMemory(31);
  $tree->incSizeInFirst (31);
  $tree->firstIntoMemory(31);
  PopR;
 }

sub Nasm::X86::Tree::decSizeInFirst($$)                                         #P Decrement the size field in the first block of a tree when the first block is held in a zmm register.
 {my ($tree, $zmm) = @_;                                                        # Tree descriptor, number of zmm containing first block
  @_ == 2 or confess "Two parameters";
  my $s = dFromZ $zmm, $tree->sizeOffset;
  If $s == 0,
  Then
   {PrintErrTraceBack "Cannot decrement zero length tree";
   };
  $tree->sizeIntoFirst($zmm, $s-1);
 }

sub Nasm::X86::Tree::decSize($)                                                 #P Decrement the size of a tree
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess "One parameter";
  PushR 31;
  $tree->firstFromMemory(31);
  $tree->decSizeInFirst (31);
  $tree->firstIntoMemory(31);
  PopR;
 }

sub Nasm::X86::Tree::size($)                                                    # Return in a variable the number of elements currently in the tree.
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess "One parameter";
  PushR my $F = 31;
  $tree->firstFromMemory($F);
  my $s = $tree->sizeFromFirst($F);
  $s->name = q(size of tree);
  PopR;
  $s
 }

sub Nasm::X86::Tree::allocBlock($$$$)                                           #P Allocate a keys/data/node block and place it in the numbered zmm registers.
 {my ($tree, $K, $D, $N) = @_;                                                  # Tree descriptor, numbered zmm for keys, numbered zmm for data, numbered zmm for children
  @_ == 4 or confess "4 parameters";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    my $t = $$s{tree};                                                          # Tree
    my $area = $t->area;                                                        # Area
    my $k = $area->allocZmmBlock;                                               # Keys
    my $d = $area->allocZmmBlock;                                               # Data
    my $n = $area->allocZmmBlock;                                               # Children

    PushR 8;
    $t->putLoop($d, $K);                                                        # Set the link from key to data
    $t->putLoop($n, $D);                                                        # Set the link from data to node
    $t->putLoop($t->first, $N);                                                 # Set the link from node to tree first block

    $$p{address}->copy($k);                                                     # Address of block
    PopR;
   } structures => {tree => $tree},
     parameters => [qw(address)],
     name       => qq(Nasm::X86::Tree::allocBlock::${K}::${D}::${N});           # Create a subroutine for each combination of registers encountered

  $s->call(structures => {tree => $tree},
           parameters => {address =>  my $a = V address => 0});

  $a
 } # allocBlock

sub Nasm::X86::Tree::freeBlock($$$$$)                                           #P Free a keys/data/node block whose keys  block entry is located at the specified offset.
 {my ($tree, $k, $K, $D, $N) = @_;                                              # Tree descriptor, offset of keys block, numbered zmm for keys, numbered zmm for data, numbered zmm for children
  @_ == 5 or confess "Five parameters";
  my $d = $tree->getLoop($K);
  my $n = $tree->getLoop($D);

  $tree->area->freeZmmBlock($_) for $k, $d, $n;                                 # Free the component zmm blocks
 } # freeBlock

sub Nasm::X86::Tree::upFromData($$)                                             #P Up from the data zmm in a block in a tree
 {my ($tree, $zmm) = @_;                                                        # Tree descriptor, number of zmm containing data block
  @_ == 2 or confess "Two parameters";
  dFromZ $zmm, $tree->up;
 }

sub Nasm::X86::Tree::upIntoData($$$)                                            #P Up into the data zmm in a block in a tree
 {my ($tree, $value, $zmm) = @_;                                                # Tree descriptor, variable containing value to put, number of zmm containing first block
  @_ == 3 or confess "Three parameters";
  $value->dIntoZ($zmm, $tree->up);
 }

sub Nasm::X86::Tree::lengthFromKeys($$)                                         #P Get the length of the keys block in the numbered zmm and return it as a variable.
 {my ($t, $zmm) = @_;                                                           # Tree descriptor, zmm number
  @_ == 2 or confess "Two parameters";

  bFromZ($zmm, $t->lengthOffset);                                               # The length field as a variable
 }

sub Nasm::X86::Tree::lengthIntoKeys($$$)                                        #P Get the length of the block in the numbered zmm from the specified variable.
 {my ($t, $zmm, $length) = @_;                                                  # Tree, zmm number, length variable
  @_ == 3 or confess "Three parameters";
  ref($length) or confess dump($length);
  $length->bIntoZ($zmm, $t->lengthOffset)                                       # Set the length field
 }

sub Nasm::X86::Tree::incLengthInKeys($$)                                        #P Increment the number of keys in a keys block or complain if such is not possible
 {my ($t, $K) = @_;                                                             # Tree, zmm number
  @_ == 2 or confess "Two parameters";
  my $l = $t->lengthOffset;                                                     # Offset of length bits
  PushR 15;
  ClearRegisters r15;
  bRegFromZmm r15, $K, $l;                                                      # Length
  Cmp r15, $t->length;
  IfLt
  Then
   {Inc r15;
    bRegIntoZmm r15, $K, $l;
   },
  Else
   {PrintErrTraceBack "Cannot increment length of block beyond ".$t->length;
   };
  PopR;
 }

sub Nasm::X86::Tree::decLengthInKeys($$)                                        #P Decrement the number of keys in a keys block or complain if such is not possible
 {my ($t, $K) = @_;                                                             # Tree, zmm number
  @_ == 2 or confess "Two parameters";
  my $l = $t->lengthOffset;                                                     # Offset of length bits
  PushR 15;
  ClearRegisters r15;
  bRegFromZmm r15, $K, $l;                                                      # Length
  Cmp r15, 0;
  IfGt
  Then
   {Dec r15;
    bRegIntoZmm r15, $K, $l;
   },
  Else
   {PrintErrTraceBack "Cannot decrement length of block below 0";
   };

  PopR;
 }

sub Nasm::X86::Tree::leafFromNodes($$)                                          #P Return a variable containing true if we are on a leaf.  We determine whether we are on a leaf by checking the offset of the first sub node.  If it is zero we are on a leaf otherwise not.
 {my ($tree, $zmm) = @_;                                                        # Tree descriptor, number of zmm containing node block
  @_ == 2 or confess "Two parameters";
  my $n = dFromZ $zmm, 0;                                                       # Get first node
  my $l = V leaf => 0;                                                          # Return a variable which is non zero if  this is a leaf
  If $n == 0, Then {$l->copy(1)};                                               # Leaf if the node is zero
  $l
 }

sub Nasm::X86::Tree::getLoop($$)                                                #P Return the value of the loop field as a variable.
 {my ($t, $zmm) = @_;                                                           # Tree descriptor, numbered zmm
  @_ == 2 or confess "Two parameters";
  dFromZ $zmm, $t->loop;                                                        # Get loop field as a variable
 }

sub Nasm::X86::Tree::putLoop($$$)                                               #P Set the value of the loop field from a variable.
 {my ($t, $value, $zmm) = @_;                                                   # Tree descriptor, variable containing offset of next loop entry, numbered zmm
  @_ == 3 or confess "Three parameters";
  $value->dIntoZ($zmm, $t->loop);                                               # Put loop field as a variable
 }

sub Nasm::X86::Tree::maskForFullKeyArea                                         #P Place a mask for the full key area in the numbered mask register
 {my ($tree, $maskRegister) = @_;                                               # Tree description, mask register
  my $m = registerNameFromNumber $maskRegister;
  ClearRegisters $m;                                                            # Zero register
  Knotq $m, $m;                                                                 # Invert to fill with ones
  Kshiftrw $m, $m, 2;                                                           # Mask with ones in the full key area
 }

sub Nasm::X86::Tree::maskForFullNodesArea                                       #P Place a mask for the full nodes area in the numbered mask register
 {my ($tree, $maskRegister) = @_;                                               # Tree description, mask register
  my $m = registerNameFromNumber $maskRegister;
  ClearRegisters $m;                                                            # Zero register
  Knotq $m, $m;                                                                 # Invert to fill with ones
  Kshiftrw $m, $m, 1;                                                           # Mask with ones in the full key area
 }

sub Nasm::X86::Tree::getBlock($$$$$)                                            #P Get the keys, data and child nodes for a tree node from the specified offset in the area for the tree.
 {my ($t, $offset, $K, $D, $N) = @_;                                            # Tree descriptor, offset of block as a variable, numbered zmm for keys, numbered data for keys, numbered zmm for nodes
  @_ == 5 or confess "Five parameters";
  my $a = $t->area;                                                             # Underlying area
  $a->getZmmBlock($offset, $K);                                                 # Get the keys block
  my $data = $t->getLoop(  $K);                                                 # Get the offset of the corresponding data block
  $a->getZmmBlock($data,   $D);                                                 # Get the data block
  my $node = $t->getLoop  ($D);                                                 # Get the offset of the corresponding node block
  $a->getZmmBlock($node,   $N);                                                 # Get the node block
 }

sub Nasm::X86::Tree::putBlock($$$$$)                                            #P Put a tree block held in three zmm registers back into the area holding the tree at the specified offset.
 {my ($t, $offset, $K, $D, $N) = @_;                                            # Tree descriptor, offset of block as a variable, numbered zmm for keys, numbered data for keys, numbered zmm for nodes
  @_ == 5 or confess "Five parameters";
  my $a    = $t->area;                                                          # Area for tree
  my $data = $t->getLoop(  $K);                                                 # Get the offset of the corresponding data block
  my $node = $t->getLoop(  $D);                                                 # Get the offset of the corresponding node block
  $a->putZmmBlock($offset, $K);                                                 # Put the keys block
  $a->putZmmBlock($data,   $D);                                                 # Put the data block
  $a->putZmmBlock($node,   $N);                                                 # Put the node block
 }

sub Nasm::X86::Tree::firstNode($$$$)                                            #P Return as a variable the last node block in the specified tree node held in a zmm
 {my ($tree, $K, $D, $N) = @_;                                                  # Tree definition, key zmm, data zmm, node zmm for a node block
  @_ == 4 or confess "Four parameters";

  dFromZ($N, 0)
 }

sub Nasm::X86::Tree::lastNode($$$$)                                             #P Return as a variable the last node block in the specified tree node held in a zmm
 {my ($tree, $K, $D, $N) = @_;                                                  # Tree definition, key zmm, data zmm, node zmm for a node block
  @_ == 4 or confess "Four parameters";

  dFromZ($N, $tree->lengthFromKeys($K) * $tree->width)
 }

sub Nasm::X86::Tree::relativeNode($$$$$)                                        #P Return as a variable a node offset relative (specified as ac constant) to another offset in the same node in the specified zmm
 {my ($tree, $offset, $relative, $K, $N) = @_;                                  # Tree definition, offset, relative location, key zmm, node zmm
  @_ == 5 or confess "Five parameters";

  abs($relative) == 1 or confess "Relative must be +1 or -1";

  my $l = $tree->lengthFromKeys($K);                                            # Length of block
  PushR $K, 7, 15;                                                              # Reuse keys for comparison value
  $offset->setReg(15);
  Vpbroadcastd zmm($K), r15d;                                                   # Load offset to test
  Vpcmpud k7, zmm($N, $K), $Vpcmp->eq;                                          # Check for nodes equal to offset
  Kmovq r15, k7;
  Tzcnt r15, r15;                                                               # Index of offset
  if ($relative < 0)
   {Cmp r15, 0;
    IfEq Then{PrintErrTraceBack "Cannot get offset before first offset"};
    Sub r15, 1;
   }
  if ($relative > 0)
   {Cmp r15, $tree->length;
    IfGt Then{PrintErrTraceBack "Cannot get offset beyond last offset"};
    Add r15, 1;
   }
  my $r = dFromZ $N, V(offset => r15) * $tree->width;                           # Select offset
  PopR;

  $r
 }

sub Nasm::X86::Tree::nextNode($$$$)                                             #P Return as a variable the next node block offset after the specified one in the specified zmm
 {my ($tree, $offset, $K, $N) = @_;                                             # Tree definition, offset, key zmm, node zmm
  @_ == 4 or confess "Four parameters";
  $tree->relativeNode($offset, +1, $K, $N);
 }

sub Nasm::X86::Tree::prevNode($$$$)                                             #P Return as a variable the previous node block offset after the specified one in the specified zmm
 {my ($tree, $offset, $K, $N) = @_;                                             # Tree definition, offset, key zmm, node zmm
  @_ == 4 or confess "Four parameters";
  $tree->relativeNode($offset, -1, $K, $N);
 }

sub Nasm::X86::Tree::indexNode($$$$)                                            #P Return, as a variable, the point mask obtained by testing the nodes in a block for specified offset. We have to supply the keys as well so that we can find the number of nodes. We need the number of nodes so that we only search the valid area not all possible node positions in the zmm.
 {my ($tree, $offset, $K, $N) = @_;                                             # Tree definition, key as a variable, zmm containing keys, comparison from B<Vpcmp>
  @_ == 4 or confess "Four parameters";

  my $A = $K == 17 ? 18 : 17;                                                   # The broadcast facility 1 to 16 does not seem to work reliably so we load an alternate zmm
  PushR rcx, 14, 15, 7, $A;                                                     # Registers

  $offset->setReg(14);                                                          # The offset we are looking for
  Vpbroadcastd zmm($A), r14d;                                                   # Load offset to test
  Vpcmpud k7, zmm($N, $A), $Vpcmp->eq;                                          # Check for nodes equal to offset
  my $l = $tree->lengthFromKeys($K);                                            # Current length of the keys block
  $l->setReg(rcx);                                                              # Create a mask of ones that matches the width of a key node in the current tree.
  Mov   r15, 2;                                                                 # A one in position two because the number of nodes is always one more than the number of keys
  Shl   r15, cl;                                                                # Position the one at end of nodes block
  Dec   r15;                                                                    # Reduce to fill block with ones
  Kmovq r14, k7;                                                                # Matching nodes
  And   r15, r14;                                                               # Matching nodes in mask area
  my $r = V index => r15;                                                       # Save result as a variable
  PopR;

  $r                                                                            # Point of key if non zero, else no match
 }

sub Nasm::X86::Tree::expand($$)                                                 #P Expand the node at the specified offset in the specified tree if it needs to be expanded and is not the root node (which cannot be expanded because it has no siblings to take substance from whereas as all other nodes do).  Set tree.found to the offset of the left sibling if the node at the specified offset was merged into it and freed else set tree.found to zero.
 {my ($tree, $offset) = @_;                                                     # Tree descriptor, offset of node block to expand
  @_ == 2 or confess "Two parameters";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    Block
     {my ($success) = @_;                                                       # Short circuit if ladders by jumping directly to the end after a successful push

      PushR 8..15, 22..31;

      my $t = $$s{tree};                                                        # Tree to search
      my $L = $$p{offset};                                                      # Offset of node to expand is currently regarded as left
      my $F = 31;
      my $PK = 30; my $PD = 29; my $PN = 28;
      my $LK = 27; my $LD = 26; my $LN = 25;
      my $RK = 24; my $RD = 23; my $RN = 22;

      $t->found->copy(0);                                                       # Assume the left node will not be freed by the expansion
      $t->firstFromMemory($F);                                                  # Load first block
      my $root = $t->rootFromFirst($F);                                         # Root node block offset
      If $root == 0 || $root == $L, Then {Jmp $success};                        # Empty tree or on root so nothing to do

      Block                                                                     # If not on the root and node has the minimum number of keys then either steal left or steal right or merge left or merge right
       {my ($end, $start) = @_;                                                 # Code with labels supplied
        $t->getBlock($L, $LK, $LD, $LN);                                        # Load node from memory
        my $ll = $t->lengthFromKeys($LK);                                       # Length of node
        If $ll > $t->lengthMin, Then {Jmp $end};                                # Has more than the bare minimum so does not need to be expanded

        my $P = $t->upFromData($LD);                                            # Parent offset
        $t->getBlock($P, $PK, $PD, $PN);                                        # Get the parent keys/data/nodes
        my $fn = $t->firstNode($PK, $PD, $PN);                                  # Parent first node
        my $ln = $t-> lastNode($PK, $PD, $PN);                                  # Parent last node

        my $R = V right => 0;                                                   # The node on the right
        my $plp = $t->indexNode($L, $PK, $PN);                                  # Position of the left node in the parent

        If $plp == 0,                                                           # Zero implies that the left child is not registered in its parent
        Then
         {PrintErrTraceBack "Cannot find left node in parent";
         };

        If $L == $ln,                                                           # If necessary step one to the let and record the fact that we did is that we can restart the search at the top
        Then                                                                    # Last child and needs merging
         {Vmovdqu64 zmm $RK, $LK;                                               # Copy the current left node into the right node
          Vmovdqu64 zmm $RD, $LD;
          Vmovdqu64 zmm $RN, $LN;
          $R->copy($L);                                                         # Left becomes right node because it is last
          my $l = $plp >> K(one => 1);                                          # The position of the previous node known to exist because we are currently on the last node
          $L->copy($l->dFromPointInZ($PN));                                     # Load previous sibling as new left keeping old left in right so that left and right now form a pair of siblings
          $t->getBlock($L, $LK, $LD, $LN);                                      # Load the new left
          $t->found->copy($L);                                                  # Show that we created a new left
         },
        Else
         {my $r = $plp << K(one => 1);                                          # The position of the node to tthe right known to exist because we are not currently on the last node
          $R->copy($r->dFromPointInZ($PN));                                     # Load next sibling as right
          $t->getBlock($R, $RK, $RD, $RN);                                      # Load the right sibling
         };

        my $lr = $t->lengthFromKeys($RK);                                       # Length of right
        If $lr == $t->lengthMin,
        Then                                                                    # Merge left and right into left as they are both at minimum size
         {$t->merge($PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN);               # Tree definition, parent keys zmm, data zmm, nodes zmm, left keys zmm, data zmm, nodes zmm.
          $t->freeBlock($R, $RK, $RD, $RN);                                     # The right is no longer required because it has been merged away

          my $lp = $t->lengthFromKeys($PK);                                     # New length of parent
          If $lp == 0,
          Then                                                                  # Root now empty
           {$t->rootIntoFirst($F, $L);                                          # Parent is now empty so the left block must be the new root
            $t->firstIntoMemory($F);                                            # Save first block with updated root
            $t->freeBlock($P, $PK, $PD, $PN);                                   # The parent is no longer required because the left ir the new root
           },
          Else                                                                  # Root not empty
           {$t->putBlock($P, $PK, $PD, $PN);                                    # Write parent back into memory
           };
         },
        Else                                                                    # Steal from right as it is too big to merge and so must have some excess that we can steal
         {$t->stealFromRight($PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN);      # Steal
          $t->putBlock($P, $PK, $PD, $PN);                                      # Save modified parent
          $t->putBlock($R, $RK, $RD, $RN);                                      # Save modified right
         };
        $t->putBlock($L, $LK, $LD, $LN);                                        # Save non minimum left

        If $t->leafFromNodes($LN) == 0,
        Then                                                                    # Not a leaf
         {PushR $RK, $RD, $RN;                                                  # Save these zmm even though we are not going to need them any more
          ($t->lengthFromKeys($LK) + 1)->for(sub                                # Reparent the children of the left hand side.  This is not efficient as we load all the children (if there are any) but it is effective.
           {my ($index, $start, $next, $end) = @_;
            my $R = dFromZ $LN, $index * $t->width;                             # Offset of node
            $t->getBlock  ($R, $RK, $RD, $RN);                                  # Get child of right node reusing the left hand set of registers as we no longer need them having written them to memory
            $t->upIntoData($L,      $RD);                                       # Parent for child of right hand side
            $t->putBlock  ($R, $RK, $RD, $RN);                                  # Save block into memory now that its parent pointer has been updated
           });
           PopR;
         };
       };  # Block
     }; # Block                                                                 # Find completed successfully
    PopR;
   } parameters=>[qw(offset)],
     structures=>{tree=>$tree},
     name => 'Nasm::X86::Tree::expand';

  $s->call(structures=>{tree => $tree}, parameters=>{offset => $offset});
 } # expand

sub Nasm::X86::Tree::replace($$$$)                                              #P Replace the key/data/subTree at the specified point in the specified zmm with the values found in the tree key/data/sub tree fields.
 {my ($tree, $point, $K, $D) = @_;                                              # Tree descriptor, point at which to extract, keys zmm, data zmm
  @_ == 4 or confess "Four parameters";

  $point->dIntoPointInZ($K, $tree->key);                                        # Key
  $point->dIntoPointInZ($D, $tree->data);                                       # Data at point

  $tree->setOrClearTreeBitToMatchContent($K, $point, $tree->subTree);           # Replace tree bit
 } # replace

sub Nasm::X86::Tree::overWriteKeyDataTreeInLeaf($$$$$$$)                        #P Over write an existing key/data/sub tree triple in a set of zmm registers and set the tree bit as indicated.
 {my ($tree, $point, $K, $D, $IK, $ID, $subTree) = @_;                          # Tree descriptor, point at which to overwrite formatted as a one in a sea of zeros, key, data, insert key, insert data, sub tree if tree.

  @_ == 7 or confess "Seven parameters";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    PushR 1..7, rdi;

    $$p{point}->setReg(rdi);                                                    # Load mask register showing point of insertion.
    Kmovq k7, rdi;                                                              # A sea of zeros with a one at the point of insertion

    $$p{key}  ->setReg(rdi); Vpbroadcastd zmmM($K, 7), edi;                     # Insert value at expansion point
    $$p{data} ->setReg(rdi); Vpbroadcastd zmmM($D, 7), edi;

    If $$p{subTree} > 0,                                                        # Set the inserted tree bit
    Then
     {Kmovq rdi, k7;
      $tree->setTreeBit ($K, rdi);
     },
    Else
     {Kmovq rdi, k7;
      $tree->clearTreeBit($K, rdi);
     };

    PopR;
   } name => "Nasm::X86::Tree::overWriteKeyDataTreeInLeaf($K, $D)",             # Different variants for different blocks of registers.
     structures => {tree=>$tree},
     parameters => [qw(point key data subTree)];

  $s->call(structures => {tree  => $tree},
           parameters => {key   => $IK, data => $ID,
                          point => $point, subTree => $subTree});
 }

#D2 Insert                                                                      # Insert a key into the tree.

sub Nasm::X86::Tree::indexXX($$$$)                                              #P Return, as a variable, the mask obtained by performing a specified comparison on the key area of a node against a specified key.
 {my ($tree, $key, $K, $cmp) = @_;                                              # Tree definition, key as a variable, zmm containing keys, comparison from B<Vpcmp>
  @_ == 4 or confess "Four parameters";

  my $A = $K == 17 ? 18 : 17;                                                   # The broadcast facility 1 to 16 does not seem to work reliably so we load an alternate zmm
  PushR rcx, r14, r15, k7, $A;                                                  # Registers

  $key->setReg(14);
  Vpbroadcastd zmm($A), r14d;                                                   # Load key to test
  Vpcmpud k7, zmm($K, $A), $cmp;                                                # Check keys from memory broadcast
  my $l = $tree->lengthFromKeys($K);                                            # Current length of the keys block
  $l->setReg(rcx);                                                              # Create a mask of ones that matches the width of a key node in the current tree.
  Mov   r15, 1;                                                                 # The one
  Shl   r15, cl;                                                                # Position the one at end of keys block
  Dec   r15;                                                                    # Reduce to fill block with ones
  Kmovq r14, k7;                                                                # Matching keys
  And   r15, r14;                                                               # Matching keys in mask area
  my $r = V index => r15;                                                       # Save result as a variable
  PopR;

  $r                                                                            # Point of key if non zero, else no match
 }

sub Nasm::X86::Tree::indexEq($$$)                                               #P Return the  position of a key in a zmm equal to the specified key as a point in a variable.
 {my ($tree, $key, $K) = @_;                                                    # Tree definition, key as a variable, zmm containing keys
  @_ == 3 or confess "Three parameters";

  $tree->indexXX($key, $K, $Vpcmp->eq);                                         # Check for equal keys from the broadcasted memory
 }

sub Nasm::X86::Tree::insertionPoint($$$)                                        #P Return the position at which a key should be inserted into a zmm as a point in a variable.
 {my ($tree, $key, $K) = @_;                                                    # Tree definition, key as a variable, zmm containing keys
  @_ == 3 or confess "Three parameters";

  $tree->indexXX($key, $K, $Vpcmp->le) + 1;                                     # Check for less than or equal keys
 }

sub Nasm::X86::Tree::insertKeyDataTreeIntoLeaf($$$$$$$$)                        #P Insert a new key/data/sub tree triple into a set of zmm registers if there is room, increment the length of the node and set the tree bit as indicated and increment the number of elements in the tree.
 {my ($tree, $point, $F, $K, $D, $IK, $ID, $subTree) = @_;                      # Tree descriptor, point at which to insert formatted as a one in a sea of zeros, first, key, data, insert key, insert data, sub tree if tree.

  @_ == 8 or confess "Eight parameters";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    my $t = $$s{tree};                                                          # Address tree

    PushR 4..8;

    my $point = $$p{point};                                                     # Point at which to insert
    $$p{point}->setReg(8);                                                      # Load mask register showing point of insertion.

    Kmovq k7, r8;                                                               # A sea of zeros with a one at the point of insertion

    $t->maskForFullKeyArea(6);                                                  # Mask for key area

    Kandnq  k4, k7, k6;                                                         # Mask for key area with a hole at the insertion point

    Vpexpandd zmmM($K, 4), zmm($K);                                             # Expand to make room for the value to be inserted
    Vpexpandd zmmM($D, 4), zmm($D);

    $$p{key}  ->setReg(8); Vpbroadcastd zmmM($K, 7), r8d;                       # Insert value at expansion point
    $$p{data} ->setReg(8); Vpbroadcastd zmmM($D, 7), r8d;

    $t->incLengthInKeys($K);                                                    # Increment the length of this node to include the inserted value

    $t->insertIntoTreeBits($K, 7, $$p{subTree});                                # Set the matching tree bit depending on whether we were supplied with a tree or a variable

    $t->incSizeInFirst($F);                                                     # Update number of elements in entire tree.

    PopR;
   } name => "Nasm::X86::Tree::insertKeyDataTreeIntoLeaf($F, $K, $D)",          # Different variants for different blocks of registers.
     structures => {tree=>$tree},
     parameters => [qw(point key data subTree)];

  $s->call(structures => {tree  => $tree},
           parameters => {key   => $IK, data => $ID,
                          point => $point, subTree => $subTree});
 }

sub Nasm::X86::Tree::splitNode($$)                                              #P Split a node if it it is full returning a variable that indicates whether a split occurred or not.
 {my ($tree, $offset) = @_;                                                     # Tree descriptor,  offset of block in area of tree as a variable
  @_ == 2 or confess 'Two parameters';

  my $PK = 31; my $PD = 30; my $PN = 29;                                        # Key, data, node blocks
  my $LK = 28; my $LD = 27; my $LN = 26;
  my $RK = 25; my $RD = 24; my $RN = 23;
  my $F  = 22;
                                                                                # First block of this tree
  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    Block
     {my ($success) = @_;                                                       # Short circuit if ladders by jumping directly to the end after a successful push

      my $t     = $$s{tree};                                                    # Tree
      my $area = $t->area;                                                      # Area

      PushR 22...31;
      ClearRegisters 22..31;                                                    # Otherwise we get left over junk

      my $offset = $$p{offset};                                                 # Offset of block in area
      my $split  = $$p{split};                                                  # Indicate whether we split or not
      $t->getBlock($offset, $LK, $LD, $LN);                                     # Load node as left

      my $length = $t->lengthFromKeys($LK);
      If $t->lengthFromKeys($LK) < $t->maxKeys,
      Then                                                                      # Only split full blocks
       {$split->copy(K split => 0);                                             # Split not required
        Jmp $success;
       };

      my $parent = $t->upFromData($LD);                                         # Parent of this block

      my $r = $t->allocBlock    ($RK, $RD, $RN);                                # Create a new right block
      If $parent > 0,
      Then                                                                      # Not the root node because it has a parent
       {$t->upIntoData      ($parent, $RD);                                     # Address existing parent from new right
        $t->getBlock        ($parent, $PK, $PD, $PN);                           # Load extant parent
        $t->splitNotRoot
                            ($r,      $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN);
        $t->putBlock        ($parent, $PK, $PD, $PN);
        $t->putBlock        ($offset, $LK, $LD, $LN);
       },
      Else                                                                      # Split the root node
       {my $p = $t->allocBlock       ($PK, $PD, $PN);                           # Create a new parent block
        $t->splitRoot   ($offset, $r, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN);
        $t->upIntoData      ($p,      $LD);                                     # Left  points up to new parent
        $t->upIntoData      ($p,      $RD);                                     # Right points up to new parent
        $t->putBlock        ($p,      $PK, $PD, $PN);
        $t->putBlock        ($offset, $LK, $LD, $LN);
        $t->putBlock        ($r,      $RK, $RD, $RN);

        $t->firstFromMemory ($F);                                               # Update new root of tree
        $t->rootIntoFirst   ($F, $p);
        $t->firstIntoMemory ($F);
       };

      $t->leafFromNodes($RN);                                                   # Whether the right block is a leaf
      If $t->leafFromNodes($RN) == 0,                                           # Not a leaf
      Then
       {(K(nodes => $t->lengthRight) + 1)->for(sub                              # Reparent the children of the right hand side now known not to be a leaf
         {my ($index, $start, $next, $end) = @_;
          my $n = dFromZ $RN, $index * $t->width;                               # Offset of node
          $t->getBlock  ($n, $LK, $LD, $LN);                                    # Get child of right node reusing the left hand set of registers as we no longer need them having written them to memory
          $t->upIntoData($r,      $LD);                                         # Parent for child of right hand side
          $t->putBlock  ($n, $LK, $LD, $LN);                                    # Save block into memory now that its parent pointer has been updated
         });
       };

      $t->putBlock        ($r,      $RK, $RD, $RN);                             # Save right block

     };                                                          # Insert completed successfully
    PopR;
   }  structures => {tree => $tree},
      parameters => [qw(offset split)],
      name       => 'Nasm::X86::Tree::splitNode';

  $s->call(structures => {tree   => $tree},
           parameters => {offset => $offset, split => my $p = V split => 1});

  $p                                                                            # Return a variable containing one if the node was split else zero.
 } # splitNode

sub Nasm::X86::Tree::splitNotRoot($$$$$$$$$$$)                                  #P Split a non root left node pushing its excess right and up.
 {my ($tree, $newRight, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN) = @_;      # Tree definition, variable offset in area of right node block, parent keys zmm, data zmm, nodes zmm, left keys zmm, data zmm, nodes zmm, right keys, data, node zmm
  @_ == 11 or confess "Eleven parameters required";

  my $w         = $tree->width;                                                 # Size of keys, data, nodes
  my $zw        = $tree->zWidthD;                                               # Number of dwords in a zmm
  my $zwn       = $tree->maxNodesZ;                                             # Maximum number of dwords that could be used for nodes in a zmm register.
  my $zwk       = $tree->maxKeysZ;                                              # Maxiumum number of dwords used for keys/data in a zmm
  my $lw        = $tree->maxKeys;                                               # Maximum number of keys in a node
  my $ll        = $tree->lengthLeft;                                            # Minimum node width on left
  my $lm        = $tree->lengthMiddle;                                          # Position of splitting key
  my $lr        = $tree->lengthRight;                                           # Minimum node on right
  my $lb        = $tree->lengthOffset;                                          # Position of length byte
  my $tb        = $tree->treeBits;                                              # Position of tree bits
  my $up        = $tree->up;                                                    # Position of up word in data
  my $transfer  = r8;                                                           # Transfer register
  my $transferD = r8d;                                                          # Transfer register as a dword
  my $transferW = r8w;                                                          # Transfer register as a  word
  my $work      = r9;                                                           # Work register as a dword

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Variable parameters, structure variables, structure copies, subroutine description
    PushR $transfer, $work, 1..7;

    my $SK = dFromZ $LK, $ll * $w;                                              # Splitting key
    my $SD = dFromZ $LD, $ll * $w;                                              # Data corresponding to splitting key

    my $mask = sub                                                              # Set k7 to a specified bit mask
     {my ($prefix, @onesAndZeroes) = @_;                                        # Prefix bits, alternating zeroes and ones
      LoadBitsIntoMaskRegister(7, $prefix, @onesAndZeroes);                     # Load k7 with mask
     };

    &$mask("00", $zwk);                                                         # Area to clear in keys and data preserving last qword
    Vmovdqu32    zmmM($RK, 7),  zmm($LK);
    Vmovdqu32    zmmM($RD, 7),  zmm($LD);

    &$mask("0",  $zwn);                                                         # Area to clear in nodes preserving last dword
    Vmovdqu32    zmmM($RN, 7),  zmm($LN);

    &$mask("00", $lw-$zwk,  $lr, -$ll-1);                                       # Compress right data/keys
    Vpcompressd  zmmM($RK, 7),  zmm($RK);
    Vpcompressd  zmmM($RD, 7),  zmm($RD);

    &$mask("0",  $lw-$zwk, $lr+1, -$lr-1);                                      # Compress right nodes
    Vpcompressd  zmmM($RN, 7),  zmm($RN);

    &$mask("11", $ll-$zwk, $ll);                                                # Clear left keys and data
    Vmovdqu32    zmmMZ($LK, 7), zmm($LK);
    Vmovdqu32    zmmMZ($LD, 7), zmm($LD);

    &$mask("1",  $ll-$zwk, $ll+1);                                              # Clear left nodes
    Vmovdqu32    zmmMZ($LN, 7), zmm($LN);

    &$mask("11", 2+$lr-$zw,  $lr);                                              # Clear right keys and data
    Vmovdqu32    zmmMZ($RK, 7), zmm($RK);
    Vmovdqu32    zmmMZ($RD, 7), zmm($RD);

    &$mask("1",  $lr-$zwk, $lr+1);                                              # Clear right nodes
    Vmovdqu32    zmmMZ($RN, 7), zmm($RN);

    my $t = $$s{tree};                                                          # Address tree

    &$mask("00", $zwk);                                                         # Area to clear in keys and data preserving last qword
    my $in = $t->insertionPoint($SK, $PK);                                      # The position at which the key would be inserted if this were a leaf
    $in->setReg($transfer);
    Kmovq k6, $transfer;                                                        # Mask shows insertion point
    Kandnq k5, k6, k7;                                                          # Mask shows expansion needed to make the insertion possible

    Vpexpandd zmmM($PK, 5), zmm($PK);                                           # Make room in parent keys and place the splitting key
    Vpexpandd zmmM($PD, 5), zmm($PD);                                           # Make room in parent data and place the data associated with the splitting key

    $SK->setReg($transfer);                                                     # Key to be inserted
    Vpbroadcastd zmmM($PK, 6), $transferD;                                      # Insert key

    $SD->setReg($transfer);                                                     # Data to be inserted
    Vpbroadcastd zmmM($PD, 6), $transferD;                                      # Insert data


    $in->setReg($transfer);                                                     # Next node up as we always expand to the right
    Shl $transfer, 1;
    Kmovq k4, $transfer;                                                        # Mask shows insertion point
    &$mask("0", $zwn);                                                          # Area to clear in keys and data preserving last qword
    Kandnq k3, k4, k7;                                                          # Mask shows expansion needed to make the insertion possible
    Vpexpandd zmmM($PN, 3), zmm($PN);                                           # Expand nodes

    $$p{newRight}->setReg($transfer);                                           # New right node to be inserted
    Vpbroadcastd zmmM($PN, 4), $transferD;                                      # Insert node

                                                                                # Lengths
    wRegFromZmm $work, $PK, $lb;                                                # Increment length of parent field
    Inc $work;
    wRegIntoZmm $work, $PK, $lb;

    Mov $work, $ll;                                                             # Lengths
    wRegIntoZmm $work, $LK, $lb;                                                # Left after split
    Mov $work, $lr;                                                             # Lengths
    wRegIntoZmm $work, $RK, $lb;                                                # Right after split

    &$mask("01", -$zwk);                                                        # Copy parent offset from left to right so that the new right node  still has the same parent
    Vmovdqu32 zmmM($RD, 7), zmm($LD);

    wRegFromZmm $transfer, $LK, $tb;                                            # Tree bits
    Mov $work, $transfer;
    And $work, (1 << $ll) - 1;
    wRegIntoZmm $work, $LK, $tb;                                                # Left after split

    Mov $work, $transfer;
    Shr $work, $lm;
    And $work, (1 << $lr) - 1;
    wRegIntoZmm $work, $RK, $tb;                                                # Right after split

    Mov $work, $transfer;                                                       # Insert splitting key tree bit into parent at the location indicated by k5
    Shr $work, $ll;
    And  $work, 1;                                                              # Tree bit to be inserted parent at the position indicated by a single 1 in k5 in parent
    wRegFromZmm $transfer, $PK, $tb;                                            # Tree bits from parent

    Cmp  $work, 0;                                                              # Are we inserting a zero into the tree bits?
    IfEq
    Then                                                                        # Inserting zero
     {InsertZeroIntoRegisterAtPoint k6, $transfer;                              # Insert a zero into transfer at the point indicated by k5
     },
    Else                                                                        # Inserting one
     {InsertOneIntoRegisterAtPoint k6, $transfer;                               # Insert a zero into transfer at the point indicated by k5
     };
    wRegIntoZmm $transfer, $PK, $tb;                                            # Save parent tree bits after split

    PopR;
   }
  structures => {tree => $tree},
  parameters => [qw(newRight)],
  name       => "Nasm::X86::Tree::splitNotRoot".
          "($lw, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN)";

  $s->call(
    structures => {tree => $tree},
    parameters => {newRight => $newRight});
 }
sub Nasm::X86::Tree::splitRoot($$$$$$$$$$$$)                                    #P Split a non root node into left and right nodes with the left half left in the left node and splitting key/data pushed into the parent node with the remainder pushed into the new right node
 {my ($tree, $nLeft, $nRight, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN) = @_;# Tree definition, variable offset in area of new left node block, variable offset in area of new right node block, parent keys zmm, data zmm, nodes zmm, left keys zmm, data zmm, nodes zmm, right keys, data , nodes zmm
  @_ == 12 or confess "Twelve parameters required";

  my $w         = $tree->width;                                                 # Size of keys, data, nodes
  my $zw        = $tree->zWidthD;                                               # Number of dwords in a zmm
  my $zwn       = $tree->maxNodesZ;                                             # Maximum number of dwords that could be used for nodes in a zmm register.
  my $zwk       = $tree->maxKeysZ;                                              # Maxiumum number of dwords used for keys/data in a zmm
  my $lw        = $tree->maxKeys;                                               # Maximum number of keys in a node
  my $ll        = $tree->lengthLeft;                                            # Minimum node width on left
  my $lm        = $tree->lengthMiddle;                                          # Position of splitting key
  my $lr        = $tree->lengthRight;                                           # Minimum node on right
  my $lb        = $tree->lengthOffset;                                          # Position of length byte
  my $tb        = $tree->treeBits;                                              # Position of tree bits
  my $transfer  = r8;                                                           # Transfer register
  my $transferD = r8d;                                                          # Transfer register as a dword
  my $transferW = r8w;                                                          # Transfer register as a  word

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Variable parameters, structure variables, structure copies, subroutine description

    my $mask = sub                                                              # Set k7 to a specified bit mask
     {my ($prefix, @onesAndZeroes) = @_;                                        # Prefix bits, alternating zeroes and ones
      LoadBitsIntoMaskRegister(7, $prefix, @onesAndZeroes);                     # Load k7 with mask
     };

    my $t = $$s{tree};                                                          # Address tree

    PushR $transfer, 6, 7;

    $t->maskForFullKeyArea(7);                                                  # Mask for keys area
    $t->maskForFullNodesArea(6);                                                # Mask for nodes area

    Mov $transfer, -1;
    Vpbroadcastd zmmM($PK, 7), $transferD;                                      # Force keys to be high so that insertion occurs before all of them

    Mov $transfer, 0;
    Vpbroadcastd zmmM($PD, 7), $transferD;                                      # Zero other keys and data
    Vpbroadcastd zmmM($RK, 7), $transferD;
    Vpbroadcastd zmmM($RD, 7), $transferD;

    Mov $transfer, 0;
    Vpbroadcastd zmmM($PN, 6), $transferD;
    Vpbroadcastd zmmM($RN, 6), $transferD;

    my $newRight = $$p{newRight};
    $t->splitNotRoot($newRight, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN);   # Split the root node as if it were a non root node

    $$p{newLeft} ->dIntoZ($PN, 0);                                              # Place first - left sub node into new root
    $$p{newRight}->dIntoZ($PN, 4);                                              # Place second - right sub node into new root

    Kshiftrw k7, k7, 1;                                                         # Reset parent keys/data outside of single key/data
    Kshiftlw k7, k7, 1;
    Mov $transfer, 0;
    Vpbroadcastd zmmM($PK, 7), $transferD;

    Mov $transfer, 1;                                                           # Lengths
    wRegIntoZmm $transfer, $PK, $lb;                                            # Left after split

    wRegFromZmm $transfer, $PK, $tb;                                            # Parent tree bits
    And $transfer, 1;
    wRegIntoZmm $transfer, $PK, $tb;

    PopR;
   }
  structures => {tree => $tree},
  parameters => [qw(newLeft newRight)],
  name       => "Nasm::X86::Tree::splitRoot".
          "($lw, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN)";

  $s->call
   (structures => {tree => $tree},
    parameters => {newLeft => $nLeft, newRight => $nRight});
 }

sub Nasm::X86::Tree::put($$$)                                                   # Put a variable key and data into a tree. The data could be a tree descriptor to place a sub tree into a tree at the indicated key.
 {my ($tree, $key, $data) = @_;                                                 # Tree definition, key as a variable, data as a variable or a tree descriptor
  @_ == 3 or confess "Three parameters";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    Block
     {my ($success) = @_;                                                       # End label

      PushR my ($F, $K, $D, $N) = reverse 28..31;

      my $t = $$s{tree};
      my $k = $$p{key};
      my $d = $$p{data};
      my $S = $$p{subTree};
      my $a = $t->area;

      my $start = SetLabel;                                                     # Start the descent through the tree

      $t->firstFromMemory($F);
      my $Q = $t->rootFromFirst($F);                                            # Start the descent at the root node

      If $Q == 0,                                                               # First entry as there is no root node.
      Then
       {my $block = $t->allocBlock($K, $D, $N);
        $k->dIntoZ                ($K, 0);
        $d->dIntoZ                ($D, 0);
        $t->incLengthInKeys       ($K);
        $t->setOrClearTreeBitToMatchContent($K, K(key => 1), $S);
        $t->putBlock($block,       $K, $D, $N);
        $t->rootIntoFirst         ($F, $block);
        $t->incSizeInFirst        ($F);
        $t->firstIntoMemory       ($F);                                         # First back into memory
        Jmp $success;
       };

      my $descend = SetLabel;                                                   # Descend to the next level

      $t->getBlock($Q, $K, $D, $N);                                             # Get the current block from memory

      my $eq = $t->indexEq($k, $K);                                             # Check for an equal key
      If $eq > 0,                                                               # Equal key found
      Then                                                                      # Overwrite the existing key/data
       {$t->overWriteKeyDataTreeInLeaf($eq, $K, $D, $k, $d, $S);
        $t->putBlock                  ($Q,  $K, $D, $N);
        Jmp $success;
       };

      my $split = $t->splitNode($Q);                                            # Split blocks that are full
      If $split > 0,
      Then
       {Jmp $start;                                                             # Restart the descent now that this block has been split
       };

      If $t->leafFromNodes($N) > 0,
      Then                                                                      # On a leaf
       {my $i = $t->insertionPoint($k, $K);                                     # Find insertion point
        $t->insertKeyDataTreeIntoLeaf($i, $F, $K, $D, $k, $d, $S);
        $t->putBlock                 ($Q, $K, $D, $N);
        $t->firstIntoMemory          ($F);                                      # First back into memory
        Jmp $success;
       };

      my $in = $t->insertionPoint($k, $K);                                      # The position at which the key would be inserted if this were a leaf
      my $next = $in->dFromPointInZ($N);                                        # The node to the left of the insertion point - this works because the insertion point can be upto one more than the maximum number of keys

      $Q->copy($next);                                                          # Get the offset of the next node - we are not on a leaf so there must be one
      Jmp $descend;                                                             # Descend to the next level
     };
    PopR;
   } name => "Nasm::X86::Tree::put",
     structures => {tree=>$tree},
     parameters => [qw(key data subTree)];

  if (ref($data) !~ m(Tree))                                                    # Whether we are a putting a sub tree
   {$s->call(structures => {tree    => $tree},                                  # Not a sub tree
             parameters => {key     => $key,
                            data    => $data,
                            subTree => K(zero => 0)});
   }
  else                                                                          # Sub tree
   {$s->call(structures => {tree    => $tree},
             parameters => {key     => $key,
                            data    => $data->first,
                            subTree => K(key => 1)});
   }
 }

#D2 Find                                                                        # Find a key in the tree. Trees have dword integer keys and so can act as arrays as well.

sub Nasm::X86::Tree::zero($)                                                    #P Zero the return fields of a tree descriptor
 {my ($tree) = @_;                                                              # Tree descriptor, key field to search for
  @_ == 1 or confess "One parameter";
  $tree->found  ->copy(0);                                                      # Key not found
  $tree->data   ->copy(0);                                                      # Data not yet found
  $tree->subTree->copy(0);                                                      # Not yet a sub tree
  $tree->offset ->copy(0);                                                      # Offset not known
  $tree                                                                         # Chaining
 }

sub Nasm::X86::Tree::find($$)                                                   # Find a key in a tree and tests whether the found data is a sub tree.  The results are held in the variables "found", "data", "subTree" addressed by the tree descriptor. The key just searched for is held in the key field of the tree descriptor. The point at which it was found is held in B<found> which will be zero if the key was not found.
 {my ($tree, $key) = @_;                                                        # Tree descriptor, key field to search for
  @_ == 2 or confess "Two parameters";
  ref($key) =~ m(Variable) or confess "Variable required";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    Block
     {my ($success) = @_;                                                       # Short circuit if ladders by jumping directly to the end after a successful push

      PushR my $F = 31, my $K = 30, my $D = 29, my $N = 28;

      my $t = $$s{tree}->zero;                                                  # Tree to search
      $t->key->copy(my $k = $$p{key});                                          # Copy in key so we know what was searched for

      $t->firstFromMemory      ($F);                                            # Load first block
      my $Q = $t->rootFromFirst($F);                                            # Start the search from the root
      If $Q == 0,
      Then                                                                      # Empty tree so we have not found the key
       {Jmp $success;                                                           # Return
       };

      K(loop=>99)->for(sub                                                      # Step down through tree
       {my ($index, $start, $next, $end) = @_;

        $t->getBlock($Q, $K, $D, $N);                                           # Get the keys/data/nodes

        my $eq = $t->indexEq($k, $K);                                           # The position of a key in a zmm equal to the specified key as a point in a variable.
        If $eq  > 0,                                                            # Result mask is non zero so we must have found the key
        Then
         {my $d = $eq->dFromPointInZ($D);                                       # Get the corresponding data
          $t->found ->copy($eq);                                                # Key found at this point
          $t->data  ->copy($d);                                                 # Data associated with the key
          $t->offset->copy($Q);                                                 # Offset of the containing block
          $t->subTree->copy($t->getTreeBit($K, $eq));                           # Get corresponding tree bit
          Jmp $success;                                                         # Return
         };

        If $t->leafFromNodes($N) > 0,
        Then                                                                    # Leaf so we cannot go further
         {Jmp $success;                                                         # Return
         };

        my $i = $t->insertionPoint($k, $K);                                     # The insertion point if we were inserting
        my $n = $i->dFromPointInZ($N);                                          # Get the corresponding data
        $Q->copy($n);                                                           # Corresponding node
       });
      PrintErrTraceBack "Stuck in find";                                        # We seem to be looping endlessly
     };                                                                         # Find completed successfully
    PopR;
   } parameters=>[qw(key)],
     structures=>{tree=>$tree},
     name => 'Nasm::X86::Tree::find';

  $s->call(structures=>{tree => $tree}, parameters=>{key => $key});
 } # find

sub Nasm::X86::Tree::findFirst($)                                               # Find the first element in a tree and set B<found>|B<key>|B<data>|B<subTree> to show the result
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess "One parameter";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    Block
     {my ($success) = @_;                                                       # Successfully completed

      my $t = $$s{tree};                                                        # Tree to search
         $t->zero;                                                              # Key not found

      PushR my $F = 31, my $K = 30, my $D = 29, my $N = 28;

      $t->firstFromMemory($F);                                                  # Update the size of the tree
      my $size = $t->sizeFromFirst($F);                                         # Size of tree

      If $size == 0,                                                            # Empty tree
      Then
       {Jmp $success
       };

      my $root = $t->rootFromFirst($F);                                         # Root of tree
      $t->getBlock($root, $K, $D, $N);                                          # Load root

      K(loop => 99)->for(sub                                                    # Step down through the tree a reasonable number of times
       {my ($i, $start, $next, $end) = @_;
        my $k = dFromZ($K, 0);
        my $d = dFromZ($D, 0);
        my $n = dFromZ($N, 0);
        my $b = $t->getTreeBit($K, K key => 1);

        If $t->leafFromNodes($N),                                               # Leaf node means we have arrived
        Then
         {$t->found  ->copy(1);
          $t->key    ->copy($k);
          $t->data   ->copy($d);
          $t->subTree->copy($b);
          Jmp $success
         };

        $t->getBlock($n, $K, $D, $N);
       });
      PrintErrTraceBack "Stuck looking for first";
     };                                                          # Find completed successfully
    PopR;
   } structures=>{tree=>$tree},
     name => "Nasm::X86::Tree::findFirst($$tree{length})";

  $s->call(structures=>{tree => $tree});
 } # findFirst

sub Nasm::X86::Tree::findLast($)                                                # Find the last key in a tree
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess "One parameter";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    Block
     {my ($success) = @_;                                                       # Successfully completed

      my $t = $$s{tree}->zero;                                                  # Tree to search

      PushR my $F = 31, my $K = 30, my $D = 29, my $N = 28;

      $t->firstFromMemory($F);                                                  # Update the size of the tree
      my $size = $t->sizeFromFirst($F);                                         # Size of tree

      If $size == 0,                                                            # Empty tree
      Then
       {Jmp $success
       };

      my $root = $t->rootFromFirst($F);                                         # Root of tree
      $t->getBlock($root, $K, $D, $N);                                          # Load root

      K(loop => 99)->for(sub                                                    # Step down through the tree a reasonable number of times
       {my ($i, $start, $next, $end) = @_;
        my $l = $t->lengthFromKeys($K);
        my $o  = ($l - 1) * $t->width;
        my $O  = ($l + 0) * $t->width;
        my $k = dFromZ($K, $o);
        my $d = dFromZ($D, $o);
        my $n = dFromZ($N, $O);
        my $b = $t->getTreeBit($K, $l);

        If $t->leafFromNodes($N),                                               # Leaf node means we have arrived
        Then
         {$t->found   ->copy(1);
          $t->key    ->copy($k);
          $t->data   ->copy($d);
          $t->subTree->copy($b);
          Jmp $success
         };

        $t->getBlock($n, $K, $D, $N);
       });
      PrintErrTraceBack "Stuck looking for last";
     };                                                          # Find completed successfully
    PopR;
   } structures=>{tree=>$tree},
     name => "Nasm::X86::Tree::findLast($$tree{length})";

  $s->call(structures=>{tree => $tree});
 } # findLast

sub Nasm::X86::Tree::findNext($$)                                               # Find the next key greater than the one specified.
 {my ($tree, $key) = @_;                                                        # Tree descriptor, key
  @_ == 2 or confess "Two parameters";
  ref($key) =~ m(Variable) or confess "Variable required";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    Block
     {my ($success) = @_;                                                       # Short circuit if ladders by jumping directly to the end after a successful push

      PushR my $F = 31, my $K = 30, my $D = 29, my $N = 28;
      my $t = $$s{tree}->zero;                                                  # Tree to search
      my $k = $$p{key};                                                         # Key to find
      $t->key->copy($k);                                                        # Copy in key so we know what was searched for

      $t->firstFromMemory      ($F);                                            # Load first block
      my $Q = $t->rootFromFirst($F);                                            # Start the search from the root
      If $Q == 0,
      Then                                                                      # Empty tree so we have successfully not found the key
       {Jmp $success;                                                           # Return
       };

      my $li = V(key => 0);                                                     # Offset of last not right tells us where to continue the search -
      my $lQ = V(key => 0);                                                     # Insertion point of last non right

      K(loop=>99)->for(sub                                                      # Step down through tree
       {my ($index, $start, $next, $end) = @_;

        $t->getBlock($Q, $K, $D, $N);                                           # Get the keys/data/nodes
        my $lp   = K(key => 1) << $t->lengthFromKeys($K);                       # Point to last node in nodes area
        my $i = $t->insertionPoint($k, $K);                                     # The insertion point
        If $t->leafFromNodes($N) > 0,
        Then                                                                    # On a leaf
         {If $i == $lp,
          Then                                                                  # Last in leaf so reposition on last not right
           {If $li == 0, Then {Jmp $success};                                   # Greater than all keys
            $t->getBlock($li, $K, $D, $N);
            $i->copy($lQ);
           };
          $t->found  ->copy($i);                                                # Key found at this point
          $t->key    ->copy($i->dFromPointInZ($K));                             # Save key
          $t->data   ->copy($i->dFromPointInZ($D));                             # Save data
          $t->subTree->copy($t->getTreeBit   ($K, $i));                         # Save sub tree
          $t->offset ->copy($Q);                                                # Save offset
          Jmp $success;                                                         # Return
         };

        my $n = $i->dFromPointInZ($N);                                          # Get the corresponding data
        If $i != $lp,
        Then                                                                    # Not descending through the last right
         {$li->copy($Q);
          $lQ->copy($i);
         };
        $Q->copy($n);                                                           # Corresponding node
       });
      PrintErrTraceBack "Stuck in find next";                                   # We seem to be looping endlessly
     };                                                          # Find completed successfully
    PopR;
   } parameters=>[qw(key)],
     structures=>{tree=>$tree},
     name => 'Nasm::X86::Tree::findNext';

  $s->call(structures=>{tree => $tree}, parameters=>{key => $key});
 } # findNext

sub Nasm::X86::Tree::findPrev($$)                                               # Find the previous key less than the one specified.
 {my ($tree, $key) = @_;                                                        # Tree descriptor, key
  @_ == 2 or confess "Two parameters";
  ref($key) =~ m(Variable) or confess "Variable required";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    Block
     {my ($success) = @_;                                                       # Short circuit if ladders by jumping directly to the end after a successful push

      PushR my $F = 31, my $K = 30, my $D = 29, my $N = 28;
      my $t = $$s{tree}->zero;                                                  # Tree to search
      my $k = $$p{key};                                                         # Key to find
      $t->key->copy($k);                                                        # Copy in key so we know what was searched for

      $t->firstFromMemory      ($F);                                            # Load first block
      my $Q = $t->rootFromFirst($F);                                            # Start the search from the root
      If $Q == 0, Then {Jmp $success};                                          # Empty tree so we have successfully not found the key

      my $li = V key => 0;                                                      # Offset of last not right tells us where to continue the search -
      my $lQ = V key => 0;                                                      # Insertion point of last non right

      K(loop => 99)->for(sub                                                    # Step down through tree
       {my ($index, $start, $next, $end) = @_;
        $t->getBlock($Q, $K, $D, $N);                                           # Get the keys/data/nodes
        my $i = $t->insertionPoint($k, $K);                                     # The insertion point
        If $i > 1,
        Then
         {my $j = $i >> K key => 1;
          If $j->dFromPointInZ($K) == $k,
          Then
           {$i->copy($j);
           };
         };

        If $t->leafFromNodes($N) > 0,
        Then                                                                    # On a leaf
         {If $i == 1,
          Then                                                                  # First in leaf so reposition on last not left
           {If $li == 0, Then {Jmp $success};                                   # Greater than all keys
            $t->getBlock($li, $K, $D, $N);
            $i->copy($lQ);
           };
          $i->copy($i >> K(one => 1));
          $t->found  ->copy($i);                                                # Key found at this point
          $t->key    ->copy($i->dFromPointInZ($K));                             # Save key
          $t->data   ->copy($i->dFromPointInZ($D));                             # Save data
          $t->subTree->copy($t->getTreeBit   ($K, $i));                         # Save sub tree
          $t->offset ->copy($Q);                                                # Save offset
          Jmp $success;                                                         # Return
         };

        my $n = $i->dFromPointInZ($N);                                          # Get the corresponding data
        If $i != 1,
        Then                                                                    # Not descending through the first left
         {$li->copy($Q);
          $lQ->copy($i);
         };
        $Q->copy($n);                                                           # Corresponding node
       });
      PrintErrTraceBack "Stuck in find prev";                                   # We seem to be looping endlessly
     };                                                                         # Find completed successfully
    PopR;
   } parameters=>[qw(key)],
     structures=>{tree=>$tree},
     name => 'Nasm::X86::Tree::findPrev';

  $s->call(structures=>{tree => $tree}, parameters=>{key => $key});
 } # findPrev

sub Nasm::X86::Tree::findAndReload($$)                                          #P Find a key in the specified tree and clone it is it is a sub tree.
 {my ($t, $key) = @_;                                                           # Tree descriptor, key as a dword
  @_ == 2 or confess "Two parameters";

  $t->find($key);                                                               # Find the key
  If $t->found > 0,                                                             # Make the found data the new  tree
  Then
   {$t->first->copy($t->data);                                                  # Copy the data variable to the first variable without checking whether it is valid
   };
 }

sub Nasm::X86::Tree::findSubTree($$)                                            # Find a key in the specified tree and create a sub tree from the data field if possible
 {my ($t, $key) = @_;                                                           # Tree descriptor, key as a dword
  @_ == 2 or confess "Two parameters";

  my $s = $t->describeTree;                                                     # The sub tree we are attempting to load
     $s->found->copy(0);                                                        # Assume we will not find the sub tree

  $t->find($key);                                                               # Find the key

  If AND(sub{$t->found > 0}, sub{$t->subTree > 0}),                             # Make the found data the new  tree
  Then
   {$s->first->copy($t->data);                                                  # Copy the data variable to the first variable without checking whether it is valid
    $s->found->copy(1);
   };
  $s
 }

sub Nasm::X86::Tree::leftOrRightMost($$$$)                                      #P Return the offset of the left most or right most node.
 {my ($tree, $dir, $node, $offset) = @_;                                        # Tree descriptor, direction: left = 0 or right = 1, start node,  offset of located node
  @_ == 4 or confess "Four parameters";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    Block
     {my ($success) = @_;                                                       # Short circuit if ladders by jumping directly to the end after a successful push

      my $t        = $$s{tree};                                                 # Tree
         $t->first->copy(my $F = $$p{node});                                    # First block
      my $area = $t->area;                                                      # Area
      PushR rax, 8, 9, 29..31;

      K(loopLimit=>9)->for(sub                                                  # Loop a reasonable number of times
       {my ($index, $start, $next, $end) = @_;
        $t->getBlock($F, 31, 30, 29);                                           # Get the first keys block
        my $n = dFromZ 29, 0;                                                   # Get the node block offset from the data block loop
        If $n == 0,
        Then                                                                    # Reached the end so return the containing block
         {$$p{offset}->copy($F);
          Jmp $success;
         };
        if ($dir == 0)                                                          # Left most
         {my $l = dFromZ 29, 0;                                                 # Get the left most node
          $F->copy($l);                                                         # Continue with the next level
         }
        else                                                                    # Right most
         {my $l = $t->lengthFromKeys(31);                                       # Length of the node
          my $r = dFromZ 31, $l;                                                # Get the right most child
          $F->copy($r);                                                         # Continue with the next level
         }
       });
      PrintErrStringNL "Stuck in LeftOrRightMost";
      Exit(1);
     };                                                          # Insert completed successfully
    PopR;
   } structures => {tree => $tree},
     parameters => [qw(node offset)],
     name       => $dir==0 ? "Nasm::X86::Tree::leftMost" :
                             "Nasm::X86::Tree::rightMost";

  $s->call(structures => {tree=>$tree},
           parameters => {node => $node, offset=>$offset});
 }

sub Nasm::X86::Tree::leftMost($$$)                                              #P Return the offset of the left most node from the specified node.
 {my ($t, $node, $offset) = @_;                                                 # Tree descriptor, start node, returned offset
  @_ == 3 or confess "Three parameters";
  $t->leftOrRightMost(0, $node, $offset)                                        # Return the left most node
 }

sub Nasm::X86::Tree::rightMost($$$)                                             #P Return the offset of the left most node from the specified node.
 {my ($t, $node, $offset) = @_;                                                 # Tree descriptor, start node, returned offset
  @_ == 3 or confess "Three parameters";
  $t->leftOrRightMost(1, $node, $offset)                                        # Return the right most node
 }

sub Nasm::X86::Tree::depth($$)                                                  # Return the depth of a node within a tree.
 {my ($tree, $node) = @_;                                                       # Tree descriptor, node
  @_ == 2 or confess "Two parameters required";
  PrintErrTraceBack "Rewrite me";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    Block
     {my ($success) = @_;                                                       # Short circuit if ladders by jumping directly to the end after a successful push

      my $t = $$s{tree};                                                        # Tree
      my $area = $tree->area;                                                   # Area
      my $N = $$p{node};                                                        # Starting node

      PushR 8, 9, 14, 15, 30, 31;
      my $tree = $N->clone('tree');                                             # Start at the specified node

      K(loop => 9)->for(sub                                                     # Step up through tree
       {my ($index, $start, $next, $end) = @_;
        $t->getKeysData($tree, 31, 30, r8, r9);                                 # Get the first node of the tree
        my $P = $t->getUpFromData(30);                                          # Parent
        If $P == 0,
        Then                                                                    # Empty tree so we have not found the key
         {$$p{depth}->copy($index+1);                                           # Key not found
          Jmp $success;                                                         # Return
         };
        $tree->copy($P);                                                        # Up to next level
       });
      PrintErrStringNL "Stuck in depth";                                        # We seem to be looping endlessly
      Exit(1);
     };                                                          # Insert completed successfully
    PopR;
   }  structures => {tree => $tree},
      parameters => [qw(node depth)],
      name       => 'Nasm::X86::Tree::depth';

  $s->call(structures => {tree => $tree->copyDescription},
           parameters => {node => $node, depth => my $d = V depth => 0});

  $d
 } # depth

#D2 Sub trees                                                                   # Construct trees of trees.

sub Nasm::X86::Tree::isTree($$$)                                                #P Set the Zero Flag to oppose the tree bit in the numbered zmm register holding the keys of a node to indicate whether the data element indicated by the specified register is an offset to a sub tree in the containing area or not.
{my ($t, $zmm, $point) = @_;                                                    # Tree descriptor, numbered zmm register holding the keys for a node in the tree, register showing point to test
 @_ == 3 or confess "Three parameters";

  my $z = registerNameFromNumber $zmm;                                          # Full name of zmm register
  my $o = $t->treeBits;                                                         # Bytes from tree bits to end of zmm
  my $w = $t->zWidth;                                                           # Size of zmm register
  Vmovdqu64    "[rsp-$w]", $z;                                                  # Write beyond stack
  Test $point, "[rsp-$w+$o]";                                                   # Test the tree bit under point
 } # isTree

sub Nasm::X86::Tree::getTreeBit($$$)                                            #P Get the tree bit from the numbered zmm at the specified point and return it in a variable as a one or a zero.
 {my ($t, $zmm, $point) = @_;                                                   # Tree descriptor, register showing point to test, numbered zmm register holding the keys for a node in the tree
  @_ == 3 or confess "Three parameters";

  $t->getTreeBits($zmm, rdi);                                                   # Tree bits
  $point->setReg(rsi);
  And rdi, rsi;                                                                 # Write beyond stack
  my $r = V treeBit => 0;
  Cmp di, 0;
  IfNe Then {$r->copy(1)};
  $r
 }

sub Nasm::X86::Tree::setOrClearTreeBit($$$$)                                    #P Set or clear the tree bit selected by the specified point in the numbered zmm register holding the keys of a node to indicate that the data element indicated by the specified register is an offset to a sub tree in the containing area.
 {my ($t, $set, $point, $zmm) = @_;                                             # Tree descriptor, set if true else clear, register holding point to set, numbered zmm register holding the keys for a node in the tree
  @_ == 4 or confess "Four parameters";
  #CheckGeneralPurposeRegister($point);
  my $z = registerNameFromNumber $zmm;                                          # Full name of zmm register
  my $o = $t->treeBits;                                                         # Tree bits to end of zmm
  my $r = registerNameFromNumber $point;
  PushR $z;                                                                     # Push onto stack so we can modify it
  if ($set)                                                                     # Set the indexed bit
   {And $point, $t->treeBitsMask;                                               # Mask tree bits to prevent operations outside the permitted area
    Or "[rsp+$o]", $point;                                                      # Set tree bit in zmm
   }
  else                                                                          # Clear the indexed bit
   {And $point, $t->treeBitsMask;                                               # Mask tree bits to prevent operations outside the permitted area
    Not $point;
    And "[rsp+$o]", $point;
   }
  PopR;                                                                         # Retrieve zmm
 } # setOrClearTree

sub Nasm::X86::Tree::setTreeBit($$$)                                            #P Set the tree bit in the numbered zmm register holding the keys of a node to indicate that the data element indexed by the specified register is an offset to a sub tree in the containing area.
 {my ($t, $zmm, $point) = @_;                                                   # Tree descriptor, numbered zmm register holding the keys for a node in the tree, register holding the point to clear
  @_ == 3 or confess "Three parameters";
  $t->setOrClearTreeBit(1, $point, $zmm);
 } # setTree

sub Nasm::X86::Tree::clearTreeBit($$$)                                          #P Clear the tree bit in the numbered zmm register holding the keys of a node to indicate that the data element indexed by the specified register is an offset to a sub tree in the containing area.
{my ($t, $zmm, $point) = @_;                                                    # Tree descriptor, numbered zmm register holding the keys for a node in the tree, register holding register holding the point to set
  @_ == 3 or confess "Three parameters";
  $t->setOrClearTreeBit(0, $point, $zmm);
 } # clearTree


sub Nasm::X86::Tree::setOrClearTreeBitToMatchContent($$$$)                      #P Set or clear the tree bit pointed to by the specified register depending on the content of the specified variable.
 {my ($t, $zmm, $point, $content) = @_;                                         # Tree descriptor, numbered keys zmm, register indicating point, content indicating zero or one
  @_ == 4 or confess "Four parameters";

  if (ref($point))                                                              # Point is a variable so we must put it in a register
   {PushR 15;
    $point->setReg(15);
    If $content > 0,                                                            # Content represents a tree
    Then
     {$t->setTreeBit($zmm, r15);
     },
    Else                                                                        # Content represents a variable
     {$t->clearTreeBit($zmm, r15);
     };
    PopR;
   }
  Else
   {If $content > 0,                                                            # Content represents a tree
    Then
     {$t->setTreeBit($zmm, $point);
     },
    Else                                                                        # Content represents a variable
     {$t->clearTreeBit($zmm, $point);
     };
   }
 }

sub Nasm::X86::Tree::getTreeBits($$$)                                           #P Load the tree bits from the numbered zmm into the specified register.
 {my ($t, $zmm, $register) = @_;                                                # Tree descriptor, numbered zmm, target register
  @_ == 3 or confess "Three parameters";
  wRegFromZmm $register, $zmm, $t->treeBits;
  And $register, $t->treeBitsMask;
 }

sub Nasm::X86::Tree::setTreeBits($$$)                                           #P Put the tree bits in the specified register into the numbered zmm.
 {my ($t, $zmm, $register) = @_;                                                # Tree descriptor, numbered zmm, target register
  @_ == 3 or confess "Three parameters";
  And $register, $t->treeBitsMask;
  wRegIntoZmm $register, $zmm, $t->treeBits;
 }

sub Nasm::X86::Tree::insertTreeBit($$$$)                                        #P Insert a zero or one into the tree bits field in the numbered zmm at the specified point moving the bits at and beyond point one position to the right.
 {my ($t, $onz, $zmm, $point) = @_;                                             # Tree descriptor, 0 - zero or 1 - one, numbered zmm, register indicating point
  @_ == 4 or confess "Four parameters";
  my $z = registerNameFromNumber $zmm;
  my $p = registerNameFromNumber $point;
  PushR my @save = my ($bits) = ChooseRegisters(1, $point);                     # Tree bits register
  $t->getTreeBits($zmm, $bits);                                                 # Get tree bits
  if ($onz)
   {InsertOneIntoRegisterAtPoint ($p, $bits);                                   # Insert a one into the tree bits at the indicated location
   }
  else
   {InsertZeroIntoRegisterAtPoint($p, $bits);                                   # Insert a zero into the tree bits at the indicated location
   }
  $t->setTreeBits($zmm, $bits);                                                 # Put tree bits
  PopR;
 }

sub Nasm::X86::Tree::insertZeroIntoTreeBits($$$)                                #P Insert a zero into the tree bits field in the numbered zmm at the specified point moving the bits at and beyond point one position to the right.
 {my ($t, $zmm, $point) = @_;                                                   # Tree descriptor, numbered zmm, register indicating point
  @_ == 3 or confess "3 parameters";
  $t->insertTreeBit(0, $zmm, $point);                                           # Insert a zero into the tree bits field in the numbered zmm at the specified point
 }

sub Nasm::X86::Tree::insertOneIntoTreeBits($$$)                                 #P Insert a one into the tree bits field in the numbered zmm at the specified point moving the bits at and beyond point one position to the right.
 {my ($t, $zmm, $point) = @_;                                                   # Tree descriptor, numbered zmm, register indicating point
  @_ == 3 or confess "Three parameters";
  $t->insertTreeBit(1, $zmm, $point);                                           # Insert a one into the tree bits field in the numbered zmm at the specified point
 }

sub Nasm::X86::Tree::insertIntoTreeBits($$$$)                                   #P Insert a one into the tree bits field in the numbered zmm at the specified point moving the bits at and beyond point one position to the right.
 {my ($t, $zmm, $point, $content) = @_;                                         # Tree descriptor, numbered zmm, register indicating point, bit to insert
  @_ == 4 or confess "Four parameters";

  if (ref($point))                                                              # Point is a variable so we must put into a register
   {PushR 15;
    $point->setReg(15);
    If $content > 0,                                                            # Content represents a one
    Then
     {$t->insertOneIntoTreeBits ($zmm, r15);
     },
    Else                                                                        # Content represents a zero
     {$t->insertZeroIntoTreeBits($zmm, r15);
     };
    PopR;
   }
  else
   {If $content > 0,                                                            # Content represents a one
    Then
     {$t->insertOneIntoTreeBits ($zmm, $point);
     },
    Else                                                                        # Content represents a zero
     {$t->insertZeroIntoTreeBits($zmm, $point);
     };
   }
 }

#D2 Delete                                                                      # Delete a key from the tree

sub Nasm::X86::Tree::extract($$$$$)                                             #P Extract the key/data/node and tree bit at the specified point from the block held in the specified zmm registers.
 {my ($tree, $point, $K, $D, $N) = @_;                                          # Tree descriptor, point at which to extract, keys zmm, data zmm, node zmm
  @_ == 5 or confess "Five parameters";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    my $t = $$s{tree};                                                          # Tree to search
    If $t->leafFromNodes($N) == 0,                                              # If the zero Flag is zero then this is not a leaf
    Then                                                                        # We can only perform this operation on a leaf
     {PrintErrTraceBack "Cannot extract from a non leaf node";
     };

    PushR 7, 15;

    my $q = $$p{point};                                                         # Point at which to extract
    $t->data->copy($q->dFromPointInZ($D));                                      # Data at point
    $t->subTree->copy($t->getTreeBit($K, $q));                                  # Sub tree or not a sub tree

    $q->setReg(15);                                                             # Create a compression mask to squeeze out the key/data
    Not r15;                                                                    # Invert point
    Mov rsi, r15;                                                               # Inverted point
    And rsi, $t->keyDataMask;                                                   # Mask for keys area
    Kmovq k7, rsi;
    Vpcompressd zmmM($K, 7), zmm($K);                                           # Compress out the key
    Vpcompressd zmmM($D, 7), zmm($D);                                           # Compress out the data

    PushR 6, 31;
    $t->getTreeBits($K, rsi);                                                   # Tree bits
    Kmovq k6, rsi;
    Vpmovm2d zmm(31), k6;                                                       # Broadcast the tree bits into a zmm
    Vpcompressd zmmM(31, 7), zmm(31);                                           # Compress out the tree bit in question
    Vpmovd2m k6, zmm(31);                                                       # Reform the tree bits minus the squeezed out bit
    Kmovq rsi, k6;                                                              # New tree bits
    $t->setTreeBits($K, rsi);                                                   # Reload tree bits
    PopR;

    Mov rsi, r15;                                                               # Inverted point
    And rsi, $t->nodeMask;                                                      # Mask for node area
    Kmovq k7, rsi;
    Vpcompressd zmmM($N, 7), zmm($N);                                           # Compress out the node

    $t->decLengthInKeys($K);                                                    # Reduce length by  one

    PopR;
   } parameters=>[qw(point)],
     structures=>{tree=>$tree},
     name => "Nasm::X86::Tree::extract($K, $D, $N, $$tree{length})";

  $s->call(structures=>{tree => $tree}, parameters=>{point => $point});
 } # extract

sub Nasm::X86::Tree::extractFirst($$$$)                                         #P Extract the first key/data and tree bit at the specified point from the block held in the specified zmm registers and place the extracted data/bit in tree data/subTree.
 {my ($tree, $K, $D, $N) = @_;                                                  # Tree descriptor, keys zmm, data zmm, node zmm
  @_ == 4 or confess "Four parameters";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    my $t = $$s{tree};                                                          # Tree to search
    $t->leafFromNodes($N);                                                      # Check for a leaf
    IfNe                                                                        # If the zero Flag is zero then this is not a leaf
    Then                                                                        # We can only perform this operation on a leaf
     {PrintErrTraceBack "Cannot extract first from a non leaf node";
     };

    $t->key ->copy(dFromZ($K, 0));                                              # Save corresponding key  into tree data field
    $t->data->copy(dFromZ($D, 0));                                              # Save corresponding data into tree data field

    PushR 7;
    Mov rsi, $t->keyDataMask;                                                   # Mask for keys area
    Sub rsi, 1;                                                                 # Mask for keys area with a zero in the first position
    Kmovq k7, rsi;
    Vpcompressd zmmM($K, 7), zmm($K);                                           # Compress out the key
    Vpcompressd zmmM($D, 7), zmm($D);                                           # Compress out the data

    $t->getTreeBits($K, rdi);                                                   # Tree bits
    Mov rsi, rdi;
    And rsi, 1;                                                                 # First tree bit
    $t->subTree->getReg(rsi);                                                   # Save tree bit
    Shr rdi, 1;                                                                 # Remove first tree bit
    $t->setTreeBits($K, rdi);                                                   # Reload tree bits

    $t->decLengthInKeys($K);                                                    # Reduce length by one

    PopR;
   } structures=>{tree=>$tree},
     name => "Nasm::X86::Tree::extractFirst($K, $D, $N, $$tree{length})";

  $s->call(structures=>{tree => $tree});
 } # extractFirst

sub Nasm::X86::Tree::mergeOrSteal($$)                                           #P Merge the block at the specified offset with its right sibling or steal from it. If there is no  right sibling then do the same thing but with the left sibling.  The supplied block must not be the root. The key we ae looking for must be in the tree key field.
 {my ($tree, $offset) = @_;                                                     # Tree descriptor, offset of non root block that might need to merge or steal
  @_ == 2 or confess "Two parameters";

  my $s = Subroutine
   {my ($parameters, $structures, $sub) = @_;                                   # Parameters, structures, subroutine definition

    my $t  = $$structures{tree};                                                # Tree to search
    my $F  = 31;
    my $PK = 30; my $PD = 29; my $PN = 28;
    my $LK = 27; my $LD = 26; my $LN = 25;
    my $RK = 24; my $RD = 23; my $RN = 22;

    PushR 22..31;

    my $l = $$parameters{offset}->clone("left");                                # Offset of left node that might need merging
    If $l == 0,
    Then
     {PrintErrTraceBack "Zero offset in mergeOrSteal";
     };
    $t->getBlock($l, $LK, $LD, $LN);                                            # Get the keys/data/nodes
    my $p = $t->upFromData($LD);                                                # Parent offset
    If $p == 0,
    Then
     {PrintErrTraceBack "Cannot mergeOrSteal the root";
     };

    my $ll = $t->lengthFromKeys($LK);                                           # Length of left
    If $ll == $t->lengthMin,                                                    # Need to merge or steal
    Then
     {$t->getBlock($p, $PK, $PD, $PN);                                          # Get the parent
      If $l != $t->lastNode($PK, $PD, $PN),
      Then                                                                      # Not the last node so we ca either steal or merge right
       {my $ll = $t->lengthFromKeys($LK);                                       # Length of left
        my $r = $t->nextNode($l, $PK, $PN);                                     # Right hand will be next sibling
        $t->getBlock($r, $RK, $RD, $RN);                                        # Get next sibling

        my $rl = $t->lengthFromKeys($RK);
        If $rl == $t->lengthMin,
        Then                                                                    # Merge left and right siblings because we now know they are both minimal
         {$t->merge($PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN);               # Tree definition, parent keys zmm, data zmm, nodes zmm, left keys zmm, data zmm, nodes zmm.
          If $t->lengthFromKeys($PK) == 0,
          Then                                                                  # We just merged in the root so make the left sibling the root
           {$t->firstFromMemory($F);
            $t->rootIntoFirst($F, $l);
            $t->firstIntoMemory($F);
            $t->upIntoData(K(zero => 0), $LD);                                  # Zero the up pointer for the root
            $t->freeBlock($p, $PK, $PD, $PN);                                   # Free parent as it is no longer needed
           },                                                                   # Else not required
          Else                                                                  # Steal from right sibling
           {$t->putBlock($p, $PK, $PD, $PN);                                    # Save modified parent
           };
          $t->freeBlock($r, $RK, $RD, $RN);                                     # Free right as it is no longer needed
         },
        Else                                                                    # Steal from right sibling
         {$t->stealFromRight($PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN);      # Steal
          $t->putBlock($p, $PK, $PD, $PN);                                      # Save modified parent
          $t->putBlock($r, $RK, $RD, $RN);                                      # Save modified right
         };
        $t->putBlock($l, $LK, $LD, $LN);                                        # Save non minimum left
        $$parameters{changed}->copy(1);                                         # Show that we changed the tree layout
       },

      Else                                                                      # Left sibling is last so we either merge the two nodes to eliminate the right node or steal from the left is that is not possible
       {my $r = $l;                                                             # The left sibling is last so we make it the right block
        $t->getBlock($r, $RK, $RD, $RN);                                        # Get the right keys/data/nodes
        my $l = $t->prevNode($r, $PK, $PN);                                     # Left block will be previous sibling
        $t->getBlock($l, $LK, $LD, $LN);                                        # Get the right keys/data/nodes
        my $ll = $t->lengthFromKeys($LK);                                       # Length of left
        If $ll == $t->lengthMin,                                                # Has the the bare minimum so must merge or steal
        Then
         {$t->merge($PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN);               # Tree definition, parent keys zmm, data zmm, nodes zmm, left keys zmm, data zmm, nodes zmm.
          If $t->lengthFromKeys($PK) == 0,
          Then                                                                  # We just merged in the root so make the left sibling the root
           {$t->firstFromMemory($F);
            $t->rootIntoFirst($F, $l);
            $t->firstIntoMemory($F);
            $t->upIntoData(K(zero => 0), $LD);                                  # Zero the up pointer for the root
            $t->freeBlock($p, $PK, $PD, $PN);                                   # Free parent as it is no longer needed
           },                                                                   # Else not required
          Else                                                                  # Steal from right sibling
           {$t->putBlock($p, $PK, $PD, $PN);                                    # Save modified parent
           };
           $t->freeBlock($r, $RK, $RD, $RN);                                    # Save modified right
         },
        Else                                                                    # Steal from right sibling
         {$t->stealFromLeft($PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN);       # Steal
          $t->putBlock($p, $PK, $PD, $PN);                                      # Save modified parent
          $t->putBlock($r, $RK, $RD, $RN);                                      # Save modified right
         };
        $t->putBlock($l, $LK, $LD, $LN);                                        # Save non minimum left
        $$parameters{changed}->copy(1);                                         # Show that we changed the tree layout
       };
     };
    PopR;
   } parameters=>[qw(offset changed)],
     structures=>{tree=>$tree},
     name => "Nasm::X86::Tree::mergeOrSteal($$tree{length})";

  $s->call(structures=>
   {tree       =>  $tree},
    parameters => {offset=> $offset, changed => my $changed = V changed => 0});

  $changed                                                                      # Whether we did a merge or steal
 } # mergeOrSteal

sub Nasm::X86::Tree::stealFromRight($$$$$$$$$$)                                 #P Steal one key from the node on the right where the current left node,parent node and right node are held in zmm registers and return one if the steal was performed, else zero.
 {my ($tree, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN) = @_;                 # Tree definition, parent keys zmm, data zmm, nodes zmm, left keys zmm, data zmm, nodes zmm, right keys, data, nodes zmm.
  @_ == 10 or confess "Ten parameters required";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Variable parameters, structure variables, structure copies, subroutine description
    my $t  = $$s{tree};
    my $ll = $t->lengthFromKeys($LK);
    my $lr = $t->lengthFromKeys($RK);

    PushR 7;

    $t->found->copy(0);                                                         # Assume we cannot steal

    Block                                                                       # Check that it is possible to steal key a from the node on the right
     {my ($end, $start) = @_;                                                   # Code with labels supplied
      If $ll != $t->lengthLeft,
      Then                                                                      # Left not minimal
       {PrintErrStringNL "Left not minimal";
        Jmp $end
       };
      If $lr == $t->lengthRight,                                                # Right minimal
      Then
       {PrintErrStringNL "Should merge not steal";
        Jmp $end
       };

      $t->found->copy(1);                                                       # Proceed with the steal

      my $pir = (K one => 1);                                                   # Point of right key to steal
      my $pil = $pir << ($ll - 1);                                              # Point of left key to receive key

      my $rk  = $pir->dFromPointInZ($RK);                                       # Right key to rotate left
      my $rd  = $pir->dFromPointInZ($RD);                                       # Right data to rotate left
      my $rn  = $pir->dFromPointInZ($RN);                                       # Right node to rotate left

      If $t->leafFromNodes($LN) == 0,
      Then                                                                      # Left is not a leaf so the right is not a leaf so we must upgrade first right child up pointer
       {PushR $LK, $LD, $LN, $RK, $RD, $RN;
        my $ln = dFromZ($LN, 0);                                                # First child of left
        $t->getBlock($ln, $LK, $LD, $LN);                                       # Left grand child
        $t->getBlock($rn, $RK, $RD, $RN);                                       # Right grand child
        my $lcu = $t->upFromData($LD);                                          # Offset of left block
        $t->upIntoData($lcu, $RD);                                              # Set up of right grand child to left block
        $t->putBlock($rn, $RK, $RD, $RN);
        PopR;
       };

      my $pip = $t->insertionPoint($rk, $PK);                                   # Point of parent key to insert
      my $pip1= $pip >> K(one=>1);                                              # Point of parent key to merge in
      my $pk  = $pip1->dFromPointInZ($PK);                                      # Parent key to rotate left
      my $pd  = $pip1->dFromPointInZ($PD);                                      # Parent data to rotate left

      my $pb  = $t->getTreeBit($PK, $pip);                                      # Parent tree bit
      my $rb  = $t->getTreeBit($RK, K one => 1);                                # First right tree bit
      $pip1->dIntoPointInZ($PK, $rk);                                           # Right key into parent
      $pip1->dIntoPointInZ($PD, $rd);                                           # Right data into parent
      $t->setOrClearTreeBitToMatchContent($PK, $pip, $rb);                      # Right tree bit into parent
      $pk->dIntoZ($LK, $t->middleOffset);                                       # Parent key into left
      $pd->dIntoZ($LD, $t->middleOffset);                                       # Parent data into left
      $rn->dIntoZ($LN, $t->rightOffset);                                        # Right node into left

      $t->insertIntoTreeBits($LK, K(position => 1 << $t->lengthLeft), $pb);     # Parent tree bit into left

      LoadConstantIntoMaskRegister                                              # Nodes area
       (7, createBitNumberFromAlternatingPattern '00', $t->maxKeysZ-1, -1);
      Vpcompressd zmmM($RK, 7), zmm($RK);                                       # Compress right keys one slot left
      Vpcompressd zmmM($RD, 7), zmm($RD);                                       # Compress right data one slot left

      LoadConstantIntoMaskRegister                                              # Nodes area
       (7, createBitNumberFromAlternatingPattern '0', $t->maxNodesZ-1, -1);
      Vpcompressd zmmM($RN, 7), zmm($RN);                                       # Compress right nodes one slot left

      $t->incLengthInKeys($LK);                                                 # Increment left hand length
      $t->decLengthInKeys($RK);                                                 # Decrement right hand
     };
    PopR;
   }
  name       =>
  "Nasm::X86::Tree::stealFromRight($$tree{length}, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN)",
  structures => {tree => $tree};

  $s->call(structures => {tree   => $tree});

  $tree                                                                         # Chain
 }

sub Nasm::X86::Tree::stealFromLeft($$$$$$$$$$)                                  #P Steal one key from the node on the left where the current left node,parent node and right node are held in zmm registers and return one if the steal was performed, else  zero.
 {my ($tree, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN) = @_;                 # Tree definition, parent keys zmm, data zmm, nodes zmm, left keys zmm, data zmm, nodes zmm, right keys, data, nodes zmm.
  @_ == 10 or confess "Ten parameters required";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Variable parameters, structure variables, structure copies, subroutine description
    my $t  = $$s{tree};
    my $ll = $t->lengthFromKeys($LK);
    my $lr = $t->lengthFromKeys($RK);

    PushR 7;

    $t->found->copy(0);                                                         # Assume we cannot steal

    Block                                                                       # Check that it is possible to steal a key from the node on the left
     {my ($end, $start) = @_;                                                   # Code with labels supplied
      If $lr != $t->lengthRight,  Then {Jmp $end};                              # Right not minimal
      If $ll == $t->lengthLeft,   Then {Jmp $end};                              # Left minimal

      $t->found->copy(1);                                                       # Proceed with the steal

      my $pir = K(one => 1);                                                    # Point of right key
      my $pil = $pir << ($ll - 1);                                              # Point of left key

      my $lk  = $pil->dFromPointInZ($LK);                                       # Left key to rotate right
      my $ld  = $pil->dFromPointInZ($LD);                                       # Left data to rotate right
      my $ln  = ($pil << K(key => 1))->dFromPointInZ($LN);                      # Left node to rotate right

      my $lb  = $t->getTreeBit($LK, $pil);                                      # Left tree bit to rotate right

      my $pip = $t->insertionPoint($lk, $PK);                                   # Point of parent key to merge in

      my $pk  = $pip->dFromPointInZ($PK);                                       # Parent key to rotate right
      my $pd  = $pip->dFromPointInZ($PD);                                       # Parent data to rotate right
      my $pb  = $t->getTreeBit($PK, $pip);                                      # Parent tree bit

      LoadConstantIntoMaskRegister                                              # Nodes area
       (7, createBitNumberFromAlternatingPattern '00', $t->maxKeysZ-1, -1);
      Vpexpandd zmmM($RK, 7), zmm($RK);                                         # Expand right keys one slot right
      Vpexpandd zmmM($RD, 7), zmm($RD);                                         # Expand right data one slot right

      LoadConstantIntoMaskRegister                                              # Nodes area
       (7, createBitNumberFromAlternatingPattern '0', $t->maxNodesZ-1, -1);
      Vpexpandd zmmM($RN, 7), zmm($RN);                                         # Expand right nodes one slot right

      $pip->dIntoPointInZ($PK, $lk);                                            # Left key into parent
      $pip->dIntoPointInZ($PD, $ld);                                            # Left data into parent
      $t->setOrClearTreeBitToMatchContent($PK, $pip, $lb);                      # Left tree bit into parent

      $pir->dIntoPointInZ($RK, $pk);                                            # Parent key into right
      $pir->dIntoPointInZ($RD, $pd);                                            # Parent data into right
      $pir->dIntoPointInZ($RN, $ln);                                            # Left node into right
      $t->insertIntoTreeBits($RK, $pir, $pb);                                   # Parent tree bit into right

      $t->decLengthInKeys($LK);                                                 # Decrement left hand
      $t->incLengthInKeys($RK);                                                 # Increment right hand

      If $t->leafFromNodes($RN) == 0,
      Then                                                                      # Right is not a leaf so we must upgrade the up pointer of the first child of right to match that of the second child of right
       {PushR $LK, $LD, $LN, $RK, $RD, $RN;
        my $r1 = dFromZ($RN, 0);                                                # First child of right
        my $r2 = dFromZ($RN, 0);                                                # Second child of right
        $t->getBlock($r1, $LK, $LD, $LN);                                       # Load first child of right
        $t->getBlock($r2, $RK, $RD, $RN);                                       # Load second child of right
        my $r2u = $t->upFromData($RD);                                          # Up from second child of right
        $t->upIntoData($r2u, $LD);                                              # Set first child up to second child up
        $t->putBlock($r1, $LK, $LD, $LN);
        PopR;
       };

     };
    PopR;
   }
  name       =>
  "Nasm::X86::Tree::stealFromLeft($$tree{length}, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN)",
  structures => {tree => $tree};

  $s->call(structures => {tree   => $tree});

  $tree                                                                         # Chain
 } # stealFromLeft

sub Nasm::X86::Tree::merge($$$$$$$$$$)                                          #P Merge a left and right node if they are at minimum size.
 {my ($tree, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN) = @_;                 # Tree definition, parent keys zmm, data zmm, nodes zmm, left keys zmm, data zmm, nodes zmm, right keys, data, nodes zmm.
  @_ == 10 or confess "Ten parameters required";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Variable parameters, structure variables, structure copies, subroutine description
    my $t  = $$s{tree};
    my $ll = $t->lengthFromKeys($LK);
    my $lr = $t->lengthFromKeys($RK);

    PushR 7, 14, 15;

    Block                                                                       # Check that it is possible to steal a key from the node on the left
     {my ($end, $start) = @_;                                                   # Code with labels supplied
      If $ll != $t->lengthLeft,  Then {Jmp $end};                               # Left not minimal
      If $lr != $t->lengthRight, Then {Jmp $end};                               # Right not minimal

      my $pil = K(one => 1);                                                    # Point of first left key
      my $lk  = $pil->dFromPointInZ($LK);                                       # First left key
      my $pip = $t->insertionPoint($lk, $PK);                                   # Point of parent key to merge in
      my $pk  = $pip->dFromPointInZ($PK);                                       # Parent key to merge
      my $pd  = $pip->dFromPointInZ($PD);                                       # Parent data to merge
      my $pn  = $pip->dFromPointInZ($PN);                                       # Parent node to merge
      my $pb  = $t->getTreeBit($PK, $pip);                                      # Parent tree bit

      my $m = K(one => 1) << K( shift => $t->lengthLeft);                       # Position of parent key in left
      $m->dIntoPointInZ($LK, $pk);                                              # Position parent key in left
      $m->dIntoPointInZ($LD, $pd);                                              # Position parent data in left
     #$m->dIntoPointInZ($LN, $pn);                                              # Position parent node in left - not needed because the left and right around the aprent lkey are the left and right node offsets - we should use this fact to update the children of the right node so that their up pointers point to the left node
      $t->insertIntoTreeBits($LK, $m, $pb);                                     # Tree bit for parent data
      LoadConstantIntoMaskRegister                                              # Keys/Data area
       (7, createBitNumberFromAlternatingPattern '00', $t->lengthRight,   -$t->lengthMiddle);
      Vpexpandd zmmM($LK, 7), zmm($RK);                                         # Expand right keys into left
      Vpexpandd zmmM($LD, 7), zmm($RD);                                         # Expand right data into left
      LoadConstantIntoMaskRegister                                              # Nodes area
       (7, createBitNumberFromAlternatingPattern '0',  $t->lengthRight+1, -$t->lengthMiddle);
      Vpexpandd zmmM($LN, 7), zmm($RN);                                         # Expand right data into left

      $pip->setReg(15);                                                         # Collapse mask for keys/data in parent
      Not r15;
      And r15, $t->treeBitsMask;
      Kmovq k7, r15;
      Vpcompressd zmmM($PK, 7), zmm($PK);                                       # Collapse parent keys
      Vpcompressd zmmM($PD, 7), zmm($PD);                                       # Collapse data keys

      my $one = K(one => 1);                                                    # Collapse mask for keys/data in parent
#     my $np = (!$pip << $one) >> $one;
      my $np = !$pip << $one;                                                   # Move the compression point up one to remove the matching node
      $np->setReg(14);
      Add r14, 1;                                                               # Fill hole left at position 0
      Kmovq k7, r14;                                                            # Node squeeze mask
      Vpcompressd zmmM($PN, 7), zmm($PN);                                       # Collapse nodes

      my $z = $PK == 31 ? 30: 31;                                               # Collapse parent tree bits
      PushR zmm $z;                                                             # Collapse parent tree bits
      $t->getTreeBits($PK, r15);                                                # Get tree bits
      Kmovq k7, r15;                                                            # Tree bits
      Vpmovm2d zmm($z), k7;                                                     # Broadcast the bits into a zmm
      $pip->setReg(15);                                                         # Parent insertion point
      Kmovq k7, r15;
      Knotq k7, k7;                                                             # Invert parent insertion point
      Vpcompressd zmmM($z, 7), zmm($z);                                         # Compress
      Vpmovd2m k7, zmm $z;                                                      # Recover bits
      Kmovq r15, k7;
      And r15, $t->treeBitsMask;                                                # Clear trailing bits beyond valid tree bits
      $t->setTreeBits($PK, r15);
      PopR;

      $t->getTreeBits($LK, r15);                                                # Append right tree bits to the Left tree bits
      $t->getTreeBits($RK, r14);                                                # Right tree bits
      my $sl = RegisterSize(r15) * $bitsInByte / 4 - $tree->lengthMiddle;       # Clear bits right of the lower left bits
      Shl r15w, $sl;
      Shr r15w, $sl;

      Shl r14, $tree->lengthMiddle;                                             # Move right tree bits into position
      Or  r15, r14;                                                             # And in left tree bits
      And r15, $t->treeBitsMask;                                                # Clear trailing bits beyond valid tree bits
      $t->setTreeBits($LK, r15);                                                # Set tree bits

      If $t->leafFromNodes($RN) == 0,
      Then                                                                      # Right is not a leaf so we must upgrade the up offset of its children to the up pointer of the first left child
       {PushR $LK, $LD, $LN;
        my $l1 = dFromZ($LN, 0);                                                # First child of left
        $t->getBlock($l1, $LK, $LD, $LN);                                       # Load first child of left
        my $l2u = $t->upFromData($LD);                                          # Offset of left block
        my $lr = 1 + $t->lengthFromKeys($RK);                                   # Number of right children
        $lr->for(sub                                                            # Each child of right
         {my ($i) = @_;
          my $r = dFromZ($RN, $i * $tree->width);                               # Offset of child
          $t->getBlock($r, $LK, $LD, $LN);                                      # Load child of right
          $t->upIntoData ($l2u, $LD);                                           # Set parent
          $t->putBlock($r, $LK, $LD, $LN);                                      # Write back into memory
         });
        PopR;
       };

      $t->decLengthInKeys($PK);                                                 # Parent now has one less
      $t->lengthIntoKeys($LK, K length => $t->length);                          # Left is now full

     };
    PopR;
   }
  name       =>
  "Nasm::X86::Tree::merge($$tree{length}, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN)",
  structures => {tree => $tree};

  $s->call(structures => {tree=> $tree});

  $tree                                                                         # Chain
 } # merge

sub Nasm::X86::Tree::deleteFirstKeyAndData($$$)                                 #P Delete the first element of a leaf mode returning its characteristics in the calling tree descriptor.
 {my ($tree, $K, $D) = @_;                                                      # Tree definition, keys zmm, data zmm
  @_ == 3 or confess "Three parameters";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Variable parameters, structure variables, structure copies, subroutine description
    my $t = $$s{tree};
    my $l = $t->lengthFromKeys($K);

    PushR 7, 14, 15;

    $t->found->copy(0);                                                         # Assume not found

    Block                                                                       # Check that it is possible to steal a key from the node on the left
     {my ($end, $start) = @_;                                                   # Code with labels supplied
      If $l == 0,  Then {Jmp $end};                                             # No elements left

      $t->found->copy(1);                                                       # Show first key and data have been found

      $t->key ->copy(dFromZ $K, 0);                                             # First key
      $t->data->copy(dFromZ $D, 0);                                             # First data
      $t->getTreeBits($K, r15);                                                 # First tree bit

      Mov r14, r15;
      Shr r14, 1;                                                               # Shift tree bits over by 1
      $t->setTreeBits($K, r14);                                                 # Save new tree bits
      And r15, 1;                                                               # Isolate first tree bit
      $t->subTree->copy(r15);                                                   # Save first tree bit

      my $m = (K(one => 1) << K(shift => $t->length)) - 2;                      # Compression mask to remove key/data
      $m->setReg(7);
      Vpcompressd zmmM($K, 7), zmm($K);                                         # Compress out first key
      Vpcompressd zmmM($D, 7), zmm($D);                                         # Compress out first data

      $t->decLengthInKeys($K);                                                  # Reduce length
     };
    PopR;
   }
  name       => "Nasm::X86::Tree::deleteFirstKeyAndData($K, $D)",
  structures => {tree => $tree};

  $s->call(structures => {tree => $tree});

  $tree                                                                         # Chain tree - actual data is in key, data,  subTree, found variables
 }

sub Nasm::X86::Tree::delete($$)                                                 # Find a key in a tree and delete it
 {my ($tree, $key) = @_;                                                        # Tree descriptor, key field to delete
  @_ == 2 or confess "Two parameters";
  ref($key) =~ m(Variable) or confess "Variable required";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    Block
     {my ($success) = @_;                                                       # Short circuit if ladders by jumping directly to the end after a successful push

      my $t = $$s{tree}->zero;                                                  # Tree to search
      my $k = $$p{key};                                                         # Key to find
      $t->key->copy($k);                                                        # Copy in key so we know what was searched for

      $t->find($k);                                                             # See if we can find the key
      If $t->found == 0, Then {Jmp $success};                                   # Key not present so we cannot delete

      PushR my $F = 31, my $K = 30, my $D = 29, my $N = 28;

      $t->firstFromMemory($F);                                                  # Update the size of the tree
      my $size = $t->sizeFromFirst($F);                                         # Size of tree
      $t->decSizeInFirst($F);
      $t->firstIntoMemory($F);

      K(loop => 99)->for(sub
       {my ($i, $startDescent, $next, $end) = @_;

        $t->firstFromMemory         ($F);                                       # Load first block
        my $root = $t->rootFromFirst($F);                                       # Start the search from the root to locate the  key to be deleted
        If $root == 0, Then{Jmp $success};                                      # Empty tree so we have not found the key and nothing needs to be done

        If $size == 1,                                                          # Delete the last element which must be the matching element
        Then
         {$t->rootIntoFirst($F, K z=>0);                                        # Empty the tree
          $t->firstIntoMemory($F);                                              # The position of the key in the root node
          Jmp $success
         };

        $t->getBlock($root, $K, $D, $N);                                        # Load root block
        If $t->leafFromNodes($N) > 0,                                           # Element must be in the root as the root is a leaf and we know the key can be found
        Then
         {my $eq = $t->indexEq($k, $K);                                         # Key must be in this leaf as we know it can be found and this is the last opportunity to find it
          $t->extract($eq, $K, $D, $N);                                         # Extract from root
          $t->putBlock($root, $K, $D, $N);
          Jmp $success
         };

        my $P = $root->clone('position');                                       # Position in tree
        K(loop => 99)->for(sub                                                  # Step down through tree looking for the key
         {my ($index, $start, $next, $end) = @_;
          my $eq = $t->indexEq($k, $K);                                         # The key might still be in the parent now known not be a leaf
          If $eq > 0,
          Then                                                                  # We have found the key so now we need to find the next leaf unless this node is in fact a leaf
           {my $pu = $t->upFromData($D);                                        # Parent offset
            If $pu > 0,
            Then                                                                # Cannot merge or steal on root
             {If $t->mergeOrSteal($P) > 0,                                      # Merge or steal if necessary
              Then                                                              # Restart entire process because we might have changed the position of the key being deleted by merging in its vicinity
               {Jmp $startDescent;
               };
             };

            If $t->leafFromNodes($N) > 0,                                       # We found the item in a leaf so it can be deleted immediately if there is enough
            Then
             {my $eq = $t->indexEq($k, $K);                                     # Key must be in this leaf as we know it can be found and this is the last opportunity to find it
              $t->extract($eq, $K, $D, $N);                                     # Remove from block
              $t->putBlock($P, $K, $D, $N);                                     # Save block
              Jmp $success;                                                     # Leaf removed
             };

            my $eq = $t->indexEq($k, $K);                                       # Location of key
            my $Q = ($eq << K(one=>1))->dFromPointInZ($N);                      # Go right to the next level down

            K(loop => 99)->for(sub                                              # Find the left most leaf
             {my ($index, $start, $next, $end) = @_;

              If $t->mergeOrSteal($Q) > 0,                                      # Merge or steal if necessary
              Then                                                              # Restart entire process because we might have changed the position of the key being deleted by merging in its vicinity
               {Jmp $startDescent;
               };
              $t->getBlock($Q, $K, $D, $N);                                     # Next block down
              If $t->leafFromNodes($N) > 0,                                     # We must hit a leaf eventually
              Then
               {$t->extractFirst($K, $D, $N);                                   # Remove from block
                $t->putBlock($Q, $K, $D, $N);                                   # Save block

                my $key     = $t->key->clone("key");                            # Record details of leaf
                my $data    = $t->data->clone("data");                          #
                my $subTree = $t->subTree->clone("data");                       #
                $t->find($k);                                                   # Find key we actually want to delete

                $t->key    ->copy($key);                                        # Reload
                $t->data   ->copy($data);
                $t->subTree->copy($subTree);

                my $l = $t->offset;                                             # Offset of block containing key

                $t->getBlock($l, $K, $D, $N);                                   # Block containing key
                $t->replace ($t->found,  $K, $D);                               # Replace key to delete with leaf
                $t->putBlock($l, $K, $D, $N);                                   # Save block
                Jmp $success;
               };

              my $i = $t->insertionPoint($k, $K);                               # The insertion point if we were inserting is the next node to visit
              $Q->copy($i->dFromPointInZ($N));                                  # Get the corresponding offset of the the next block down
             });
             Jmp $success;
           };

          my $i = $t->insertionPoint($k, $K);                                   # The insertion point if we were inserting is the next node to visit
          $P->copy($i->dFromPointInZ($N));                                      # Get the corresponding node

          $t->getBlock($P, $K, $D, $N);                                         # Get the next block

          my $l = $t->lengthFromKeys($K);                                       # Length of block

          If $l == $t->lengthMin,                                               # Has the the bare minimum so must be merged.
          Then
           {If $t->mergeOrSteal($P) > 0,                                        # Merge or steal if necessary
            Then                                                                # Restart entire process because we might have changed the position of the key being deleted by merging in its vicinity
             {Jmp $startDescent;
             };
           };
         });
       });
      PrintErrTraceBack "Stuck looking for leaf";
     };                                                          # Find completed successfully
    PopR;
   } parameters=>[qw(key)],
     structures=>{tree=>$tree},
     name => "Nasm::X86::Tree::delete($$tree{length})";

  $s->call(structures=>{tree => $tree}, parameters=>{key => $key});
 } # delete

sub Nasm::X86::Tree::clear($)                                                   # Delete everything in the tree recording the memory so liberated to the free chain for reuse by other trees.
 {my ($tree) = @_;                                                              # Tree
  @_ == 1 or confess "One parameter";

  my $s = Subroutine                                                            # Delete all the sub blocks of a block and then free the block as well
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    my $t = $$s{tree};                                                          # Tree
    my $area = $t->area;                                                        # Area

    PushR my $K = 31, my $D = 30, my $N = 29;

    Block                                                                       # Free sub blocks then free block
     {my ($end, $start) = @_;

      $t->getBlock($$p{offset}, $K, $D, $N);                                    # Load block

      If $t->leafFromNodes($N) == 0,
      Then                                                                      # Not a leaf so free the sub blocks
       {my $l = $t->lengthFromKeys($K);                                         # Number of nodes
        ($l+1)->for(sub                                                         # Free sub blocks
         {my ($i) = @_;
          $sub->call(parameters => {offset => dFromZ $N, $i * $t->width},       # Recurse
                     structures => {tree   => $t});
         });
       };

      $t->freeBlock($$p{offset}, $K, $D, $N);                                   # Free this block
     };

    PopR;
   } parameters => [qw(offset)],
     structures => {tree => $tree},
     name       => "Nasm::X86::Tree::clear";

  PushR my $F = 31;
  $tree->firstFromMemory($F);
  my $root = $tree->rootFromFirst($F);                                          # Root block if any

  If $root > 0,                                                                 # Non empty tree
  Then
   {$s->call(structures => {tree  => $tree}, parameters => {offset => $root});  # Free from root node
    $tree->rootIntoFirst($F, K root => 0);
    $tree->sizeIntoFirst($F, K size => 0);
    $tree->firstIntoMemory($F);
   };

  PopR;
 }

sub Nasm::X86::Tree::free($)                                                    # Free all the memory used by a tree
 {my ($tree) = @_;                                                              # Tree
  @_ == 1 or confess "One parameter";
  $tree->clear;                                                                 # Clear the tree
 }

#D2 Iteration                                                                   # Iterate through a tree non recursively

sub Nasm::X86::Tree::by($&)                                                     # Call the specified block with each element of the specified tree in ascending order.
 {my ($tree, $block) = @_;                                                      # Tree descriptor, block to execute
  @_ == 2 or confess "Two parameters required";

  $tree->findFirst;                                                             # First element
  my $end   = Label;                                                            # End of processing
  my $next  = Label;                                                            # Next iteration
  my $start = SetLabel;                                                         # Start of this iteration
  If $tree->found == 0, Then {Jmp $end};
  &$block($tree, $start, $next, $end);                                          # Perform the specified block
  SetLabel $next;
  $tree->findNext($tree->key);
  Jmp $start;
  SetLabel $end;
 }

sub Nasm::X86::Tree::yb($&)                                                     # Call the specified block with each element of the specified tree in descending order.
 {my ($tree, $block) = @_;                                                      # Tree descriptor, block to execute
  @_ == 2 or confess "Two parameters required";

  $tree->findLast;                                                              # Last element
  my $end   = Label;                                                            # End of processing
  my $prev  = Label;                                                            # Next iteration
  my $start = SetLabel;                                                         # Start of this iteration
  If $tree->found == 0, Then {Jmp $end};
  &$block($tree, $start, $prev, $end);                                          # Perform the specified block
  SetLabel $prev;
  $tree->findPrev($tree->key);
  Jmp $start;
  SetLabel $end;
 }

#D2 Push and Pop                                                                # Use a tree as a stack: Push elements on to a tree with the next available key; Pop the last element in a tree.

sub Nasm::X86::Tree::push($$)                                                   #P Push a data value onto a tree. If the data is a reference to a tree then the offset of the first block of the tree is pushed.
 {my ($tree, $data) = @_;                                                       # Tree descriptor, variable data
  @_ == 2 or confess "Two parameters";

  $tree->usage->{stack}++;                                                      # Being used as a stack

  $tree->findLast;                                                              # Last element
  If $tree->found == 0,
  Then                                                                          # Empty tree
   {$tree->put(K(key => 0), $data);                                             # First element in tree
   },
  Else                                                                          # Non empty tree
   {$tree->put($tree->key + 1, $data);                                          # Last element in tree
   };
 }

sub Nasm::X86::Tree::peek($$)                                                   # Peek at the element the specified distance back from the top of the stack and return its B<value> in data and found status in B<found> in the tree descriptor.
 {my ($tree, $back) = @_;                                                       # Tree descriptor, how far back to go with 1 being the top
  @_ == 2 or confess "Two parameters";
  ref($back) =~ m(Variable) or confess "Must be a variable, not: ", dump($back);

  $tree->usage->{stack} or confess "Tree not being used as a stack";            # Check usage

  $tree->found->copy(0);                                                        # Assume we will not be able to find the desired element

  my $size = $tree->size;                                                       # Size of the stack
  If $back <= $size,
  Then                                                                          # Requested element is available on the stack
   {$tree->find($size - $back);
   };
  $tree
 }

sub Nasm::X86::Tree::peekSubTree($)                                              # Pop the last value out of a tree and return a tree descriptor positioned on it with the first/found fields set.
 {my ($tree, $back) = @_;                                                       # Tree descriptor, how far back to go with 1 being the top
  @_ == 2 or confess "Two parameters";
  ref($back) =~ m(Variable) or confess "Must be a variable, not: ", dump($back);

  $tree->usage->{stack} or confess "Tree not being used as a stack";            # Check usage

  my $t = $tree->describeTree;                                                  # Create a tree descriptor
  $t->found->copy(0);                                                           # Mark tree as not set
  $tree->peek($back);                                                           # Requested element
  If $tree->found > 0,
  Then                                                                          # Found an element
   {If $tree->subTree > 0,
    Then                                                                        # Found a sub tree
     {$t->reposition($tree->data);                                              # Reposition on sub tree
      $t->found->copy(1);
     };
   };
  $t
 }

sub Nasm::X86::Tree::pop($)                                                     # Pop the last value out of a tree and return the key/data/subTree in the tree descriptor.
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess "One parameter";

  $tree->usage->{stack} or confess "Tree not being used as a stack";            # Check usage

  $tree->findLast;                                                              # Last element
  If $tree->found > 0,
  Then                                                                          # Empty tree
   {my $k = $tree->key    ->clone('key');
    my $d = $tree->data   ->clone('data');
    my $s = $tree->subTree->clone('subTree');
    $tree->delete($k);                                                          # Delete last key
    $tree->key    ->copy($k);                                                   # Retrieved key
    $tree->data   ->copy($d);                                                   # Retrieved data
    $tree->subTree->copy($s);                                                   # Retrieved sub tree indicator
    $tree->found  ->copy(1);                                                    # Indicate success
   };
 }

sub Nasm::X86::Tree::popSubTree($)                                              # Pop the last value out of a tree and return a tree descriptor positioned on it with the first/found fields set.
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess "One parameter";

  $tree->usage->{stack} or confess "Tree not being used as a stack";            # Check usage

  my $t = $tree->describeTree;                                                  # Create a tree descriptor
  $t->found->copy(0);                                                           # Mark tree as not set
  $tree->findLast;                                                              # Last element
  If $tree->found > 0,
  Then                                                                          # Found an element
   {If $tree->subTree > 0,
    Then                                                                        # Found a sub tree
     {$t->reposition($tree->data);                                              # Reposition on sub tree
      $tree->delete($tree->key);                                                # Remove subtree from stack
      $t->found->copy(1);
     };
   };
  $t
 }

sub Nasm::X86::Tree::get($$)                                                    # Retrieves the element at the specified zero based index in the stack.
 {my ($tree, $key) = @_;                                                        # Tree descriptor, zero based index
  @_ == 2 or confess "Two parameters";
  $tree->find($key);
 }

#D2 Trees as Strings                                                            # Use trees as strings of dwords.  The size of the tree is the length of the string. Each dword is consider as an indivisible unit. This arrangement allows the normal string operations of concatenation and substring to be performed easily.

sub Nasm::X86::Tree::appendAscii($$$)                                           # Append ascii bytes in memory to a tree acting as a string. The address and size of the source memory are specified via variables. TheEach byute should represent a valid ascii byte so that it can be considered, when left extended with 24 zero bits, as utf32.
 {my ($string, $address, $size) = @_;                                           # Tree descriptor of string to append to, variable address of memory to append from, variable size of memory
  @_ == 3 or confess "Three parameters";

  my $s = Subroutine
   {my ($parameters, $structures, $sub) = @_;
    PushR rax, 13, 14, 15;
    my $s = $$structures{string};
    $$parameters{address}->setReg(r13);
    $$parameters{size}   ->setReg(r14);
    ClearRegisters r15;
    For                                                                         # Clear memory
     {Mov al, "[r13+r15]";
      $s->push(V byte => rax);
     } r15, r14, 1;
    PopR;
   } structures=>{string=>$string},
     parameters=>[qw(address size)], name => 'Nasm::X86::Tree::m';

  $s->call(parameters=>{address => $address, size=>$size},
           structures=>{string=>$string});
 }

sub Nasm::X86::Tree::append($$)                                                 # Append the second source string to the first target string renumbering the keys of the source string to follow on from those of the target string.  A string can safely be appended to itself.
 {my ($string, $append) = @_;                                                   # Tree descriptor of string to append to, tree descriptor of string to append from
  @_ == 2 or confess "Two parameters";

  my $lt = $string->size;                                                       # Target string size
  my $ls = $append->size;                                                       # Source string size
  $ls->for(sub                                                                  # Look up each character
   {my ($i, $start, $next, $end) = @_;
    $string->get($i);
    $string->put($lt+$string->key, $string->data);
   });
  $string                                                                       # Chain from the target string
 }

sub Nasm::X86::Tree::clone($)                                                   # Clone a string.
 {my ($string) = @_;                                                            # Tree descriptor
  @_ == 1 or confess "One parameter";

  my $t = $string->area->CreateTree;                                            # Cloned copy
  $string->by(sub
   {$t->put($string->key, $string->data);
   });
  $t                                                                            # Chain from the target string
 }

sub Nasm::X86::Tree::substring($$$)                                             # Create the substring of the specified string between the specified start and end keys.
 {my ($string, $start, $finish) = @_;                                           # Tree descriptor of string to extract from, start key, end key
  @_ == 3 or confess "Three parameters";

  my $t = $string->area->CreateTree;                                            # Cloned copy
  If $start == $finish,
  Then                                                                          # Start and end are the same
   {$string->find($start);
    If $string->found > 0,
    Then
     {$t->put($string->key, $string->data);
     };
   },
  Ef {$start < $finish}
  Then                                                                          # Range of several keys
   {$string->find($finish);
    If $string->found > 0,
    Then                                                                        # Finish exists
     {$string->find($start);
      If $string->found > 0,
      Then                                                                      # Start exists
       {$string->size->for(sub                                                  # Each key in range
         {my ($i, $start, $next, $end) = @_;
          $t->put($string->key, $string->data);
          $string->findNext($string->key);
          If $string->key == $finish, Then {Jmp $end};                          # End of range
         });
       };
     };
   };
  $t                                                                            # Chain from the target string
 }

sub Nasm::X86::Tree::reverse($)                                                 # Create a clone of the sstring in reverse order
 {my ($string) = @_;                                                            # Tree descriptor of string
  @_ == 1 or confess "One parameter";

  my $t = $string->area->CreateTree;                                            # Cloned reversed copy
  my $l = $string->size;                                                        # Size of string
  $string->by(sub
   {$t->put($l - $string->key - 1, $string->data);
   });
  $t                                                                            # Chain from the target string
 }

#D3 Trees as sets                                                               # Trees of trees as sets

sub Nasm::X86::Tree::union($)                                                   # Given a tree of trees consider each sub tree as a set and form the union of all these sets as a new tree
 {my ($tree) = @_;                                                              # Tree descriptor for a tree of trees
  @_ == 1 or confess "One parameter";

  my $u = $tree->area->CreateTree;
  $tree->by(sub                                                                 # Each sub tree
   {my ($T) = @_;
    my $t = $tree->position($T->data);
    $t->by(sub                                                                  # Insert each element of each sub tree
     {my ($s) = @_;
      $u->put($s->key, $s->data);
     });
   });
  $u                                                                            # Union
 }

sub Nasm::X86::Tree::intersection($)                                            # Given a tree of trees consider each sub tree as a set and form the intersection of all these sets as a new tree
 {my ($tree) = @_;                                                              # Tree descriptor for a tree of trees
  @_ == 1 or confess "One parameter";

  my $i = $tree->area->CreateTree;                                              # Resulting intersection
  my $F = V smallest => -1;
  my $S = V size     => -1;

  $tree->by(sub                                                                 # Find smallest sub tree
   {my ($T, $start, $next) = @_;
    my $f = $T->data;
    my $t = $tree->position($f);
    my $s = $t->size;
    OrBlock                                                                     # Update size if no size seen yet or if the size is smaller
     {my ($pass) = @_;
      If $S == -1, Then {Jmp $pass};                                            # No size set yet
      If $S > $s,  Then {Jmp $pass};                                            # Smaller size
     }                                                                          # Do not attempt to put a comma here!
    Then                                                                        # Smallest so far
     {$S->copy($s);
      $F->copy($f);
     };
   });

  If $S > 0,                                                                    # The smallest set is not empty set so the intersection might not be empty either
  Then
   {$tree->findFirst;
    my $f = $tree->position($F);                                                # First tree (but the smallest sub tree would be better)

    $f->by(sub                                                                  # Insert each element of each sub tree
     {my ($t, undef, $nextElement) = @_;
      my $k = $t->key;

      $tree->by(sub                                                             # Each sub tree
       {my ($T, undef, $nextTree) = @_;
        If $F == $T->data, Then {Jmp $nextTree};                                # Skip the first tree

        my $t = $tree->position($T->data);
        $t->find($k);
        If $t->found == 0, Then {Jmp $nextElement};                             # Not found in this sub tree so it cannot be part of the intersection
       });
      $i->put($k, $k);
     });
   };

  $i                                                                            # Intersection
 }

#D3 Trees of strings                                                            # Trees of strings assign a unique number to a string so that given a string we can produce a unique number representing the string.  The inverse operation is much easier as we just have to look up a string by number in a tree.

sub Nasm::X86::Tree::putString($$)                                              # The last element of the string is the value, the preceding elements are the keys so such a string must have at least two elements. We create a string tree to index strings to values
 {my ($tree, $string) = @_;                                                     # Tree descriptor representing string tree, tree representing a string to be inserted into the string tree.
  @_ == 2 or confess "Two parameters";

  my $size = $string->size;                                                     # Tree size
  If $size > 1,                                                                 # Tree must be two or more
  Then
   {my $size1 = $size - 1;
    my $S = $tree->copyDescription;                                             # Create a new descriptor for the string tree
    my $s = V state => 1;                                                       # 1 - string found so far, 0 - inserting new string
    my $z = V count => 0;                                                       # Count of elements so that we can find the last element to be inserted
    my $l = V last  => 0;                                                       # Last key

    $string->by(sub                                                             # Insert latest tree
     {my ($t) = @_;
      $z++;
      If $z < $size1,                                                           # First elements are keys
      Then
       {If $s == 1,
        Then
         {$S->find($t->data);
          If $S->found == 0,
          Then                                                                  # Position on new element
           {$s->copy(0);
            my $T = $t->area->CreateTree;
            $S->put($t->data, $T);
            $S->first->copy($T->first);
           },
          Else
           {$S->first->copy($S->data);                                          # Position on found element
           };
         },
        Else
         {my $T = $t->area->CreateTree;
          $S->put($t->data, $T);
          $S->first->copy($T->first);
         };
       },
      Ef {$z == $size1}                                                         # Last key
      Then
       {$l->copy($t->data);
       },
      Else
       {$S->put($l, $t->data);
       };
     });
   };
 }

sub Nasm::X86::Tree::getString($$)                                              # Locate the tree in a string tree representing the specified string and return its data in B<found> and B<data>.
 {my ($tree, $string) = @_;                                                     # Tree descriptor representing string tree, tree representing a string to be inserted into the string tree.
  @_ == 2 or confess "Two parameters";
  ref($string) =~ m(\ANasm::X86::::Tree\Z);

  my $S = $tree->copyDescription;                                               # Create a new descriptor for the string tree

  Block
   {my ($end, $start) = @_;                                                     # End label
    $S->zero;                                                                   # Assume we will not find the string
    $S->subTree->copy(1);                                                       # We know we start with a string
    $string->by(sub                                                             # Insert latest tree
     {my ($s) = @_;
      If $S->subTree == 0, Then {Jmp $end};                                     # Confirm that we are searching a sub tree
      $S->find($s->data);                                                       # Try to find the next character of the string
      If $S->found   == 0, Then {Jmp $end};                                     # The string cannot be found
      $S->first->copy($S->data);
     });
   };

  $S                                                                            # The result is shown via a tree descriptor
 }

#D2 Print                                                                       # Print a tree

sub Nasm::X86::Tree::dumpWithWidth($$$$$$$)                                     #P Dump a tree and all its sub trees.
 {my ($tree, $title, $width, $margin, $first, $keyX, $dataX) = @_;              # Tree, title, width of offset field, the maximum width of the indented area, whether to print the offset of the tree, whether to print the key field in hex or decimal, whether to print the data field in hex or decimal
  @_ == 7 or confess "Seven parameters";

  PushR my $F = 31;

  my $s = Subroutine                                                            # Print a tree
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    my $t = $$s{tree};                                                          # Tree
    my $I = $$p{indentation};                                                   # Indentation to apply to the start of each new line

    PushR my $transfer = r8, my $treeBitsR = r10, my $treeBitsIndexR = r11,
          my $K = 30, my $D = 29, my $N = 28;

    Block                                                                       # Print each node in the tree
     {my ($end, $start) = @_;                                                   # Labels
      my $offset = $$p{offset};                                                 # Offset of node to print
      $t->getBlock($offset, $K, $D, $N);                                        # Load node
      $t->getTreeBits($K, $treeBitsR);                                          # Tree bits for this node
      my $l = $t->lengthFromKeys($K);                                           # Number of nodes

      my $root = $t->rootFromFirst($F);                                         # Root or not

      $I->outSpaces;
      PrintOutString "At: ";                                                    # Print position and length
      $offset->outRightInHex(K width => $width);
      (K(col => $margin) - $I)->outSpaces;
      PrintOutString "length: ";
      $l->outRightInDec(K width => $width);

      PrintOutString ",  data: ";                                               # Position of data block
      $t->getLoop($K)->outRightInHex(K width => $width);

      PrintOutString ",  nodes: ";                                              # Position of nodes block
      $t->getLoop($D)->outRightInHex(K width => $width);

      PrintOutString ",  first: ";                                              # First block of tree
      $t->getLoop($N)->outRightInHex(K width => $width);

      my $U = $t->upFromData($D);                                               # Up field determines root / parent / leaf

      If $root == $offset,
      Then
       {PrintOutString ", root";                                                # Root
       },
      Else
       {PrintOutString ",  up: ";                                               # Up
        $U->outRightInHex(K width => $width);
       };

      If dFromZ($N, 0) == 0,                                                    # Leaf or parent
      Then
       {PrintOutString ", leaf";
       },
      Else
       {PrintOutString ", parent";
       };

      $t->getTreeBits($K, $transfer);
      Cmp $transfer, 0;
      IfGt
      Then                                                                      # Identify the data elements which are sub trees
       {PrintOutString ",  trees: ";
        V(bits => $transfer)->outRightInBin(K width => $t->maxKeys);
       };
      PrintOutNL;

      $I->copy($I + 2);                                                         # Indent sub tree

      $I->outSpaces; PrintOutString "Index:";                                   # Indices
      $l->for(sub
       {my ($index, $start, $next, $end) = @_;
        PrintOutString ' ';
        $index->outRightInDec(K width => $width);
       });
      PrintOutNL;

      my $printKD = sub                                                         # Print keys or data or nodes
       {my ($name, $zmm, $nodes, $tb) = @_;                                     # Key or data or node, zmm containing key or data or node, print nodes if true, print tree bits if true
        $I->outSpaces; PrintOutString $name;                                    # Keys
        Mov $treeBitsIndexR, 1 if $tb;                                          # Check each tree bit position

        ($nodes ? $l + 1 : $l)->for(sub                                         # There is one more node than keys or data
         {my ($index, $start, $next, $end) = @_;
          my $i = $index * $t->width;                                           # Key or Data offset
          my $k = dFromZ $zmm, $i;                                              # Key or Data

          if (!$tb)                                                             # No tree bits
           {PrintOutString ' ';
            $k->outRightInHex(K width => $width);
           }
          else
           {Test $treeBitsR, $treeBitsIndexR;                                   # Check for a tree bit
            IfNz
            Then                                                                # This key indexes a sub tree
             {if ($first)                                                       # Print out the offset of the first block as used by the sub tree
               {($k >> K(four => 4))->outRightInHex(K width => $width);         # This field indicates the offset of the first block
               }
              else                                                              # This key indexes a sub tree and for a reason which I have no desire to call to mind, I once thought it necessary to print the offset of the first node rather than the first block.
               {PushR 31;
                $t->area->getZmmBlock($k, 31);
                my $r = $t->rootFromFirst($F) >> K(four => 4);
                PopR;
                $r->outRightInHex(K width => $width);
               }
              PrintOutString '*';
             },
            Else
             {PrintOutString ' ';
              if ($name =~ m(key))
               {$k->outRightInHex(K width => $width) if     $keyX;
                $k->outRightInDec(K width => $width) unless $keyX;
               }
              else
               {$k->outRightInHex(K width => $width) if     $dataX;
                $k->outRightInDec(K width => $width) unless $dataX;
               }
             };
           }
          Shl $treeBitsIndexR, 1 if $tb;                                        # Next tree bit position
         });
        PrintOutNL;
       };

      $printKD->('Keys :', $K, 0, 0);                                           # Print key
      $printKD->('Data :', $D, 0, 1);                                           # Print data
      If dFromZ($N, 0) > 0,                                                     # If the first node is not zero we are not on a leaf
      Then
       {$printKD->('Nodes:', $N, 1, 0);
       };

      Cmp $treeBitsR, 0;                                                        # Any tree bit sets?
      IfNe
      Then                                                                      # Tree bits present
       {Mov $treeBitsIndexR, 1;                                                 # Check each tree bit position
        PushR my $F = 31;                                                       # Load first block of sub tree
        K(loop => $t->maxKeys)->for(sub
         {my ($index, $start, $next, $end) = @_;
          Test $treeBitsR, $treeBitsIndexR;                                     # Check for a tree bit
          IfNz
          Then                                                                  # This key indexes a sub tree
           {my $i = $index * $t->width;                                         # Key/data offset
            my $d = dFromZ($D, $i);                                             # Data
            my $I = V(indentation => 0)->copy($I + 2 + 1);                      # Indent by one extra space to show separate sub tree rather than continuation of the existing tree and to make the at address line up with the address in data.

            my      $T = $t->position($d);
                    $T->firstFromMemory($F);                                    # First block for tree
            my $r = $T->rootFromFirst($F);

            if ($first)                                                         # The offset of the tree if requested
             {($I-2)->outSpaces;                                                # The word 'tree' is two letters longer than the word 'at'
              PrintOutString "Tree: ";
              $T->first->outRightInHexNL(K width => $width);
             }

            If $r == 0,                                                         # Empty tree
            Then
             {PrintOutStringNL "- empty";
             },
            Else
             {$sub->call(parameters => {indentation => $I, offset => $r},
                         structures => {tree        => $T});                    # Print sub tree referenced by data field
             };
           };
          Shl $treeBitsIndexR, 1;                                               # Next tree bit position
         });
        PopR;
       };

      If $l > 0,
      Then                                                                      # If the block only has one node it must be a leaf
       {($l+1)->for(sub                                                         # Print sub nodes
         {my ($index, $start, $next, $end) = @_;
          my $i = $index * $t->width;                                           # Key/Data offset
          my $d = dFromZ($N, $i);                                               # Sub nodes
          If $d > 0,                                                            # Print any sub nodes
          Then
           {my $I = V(indentation => 0)->copy($I + 2);
            $sub->call(parameters => {indentation => $I, offset=>$d},
                       structures => {tree        => $t});                      # Print sub tree referenced by data field
           };
         });
       };

      ($I - 2)->outSpaces; PrintOutStringNL "end";                              # Separate sub tree dumps

     };

    PopR;
   } parameters => [qw(indentation offset)],
     structures => {tree => $tree},
     name       => "Nasm::X86::Tree::dump_$width-$margin-$first";

  PrintOutStringNL $title;                                                      # Title of the piece so we do not lose it

  $tree->firstFromMemory($F);                                                   # First block for tree
  my $Q = $tree->rootFromFirst($F);

  If $Q == 0,                                                                   # Empty tree
  Then
   {PrintOutStringNL "- empty";
   },
  Else
   {$tree->first->outNL("Tree: ") if $first;
    $s->call(structures => {tree        => $tree},                              # Print root node
             parameters => {indentation => V(indentation => 0),
                            offset      => $Q});
   };

  PopR;
 }

sub Nasm::X86::Tree::dump($$)                                                   #P Dump a tree and all its sub trees.
 {my ($tree, $title) = @_;                                                      # Tree, title
  @_ == 2 or confess "Two parameters";
  $tree->dumpWithWidth($title, 4, 20, 0, 1, 0)
 }

sub Nasm::X86::Tree::dump8($$)                                                  #P Dump a tree and all its sub trees using 8 character fields for numbers.
 {my ($tree, $title) = @_;                                                      # Tree, title
  @_ == 2 or confess "Two parameters";
  $tree->dumpWithWidth($title, 8, 80, 1, 1, 0)
 }

sub Nasm::X86::Tree::dump8xx($$)                                                #P Dump a tree and all its sub trees using 8 character fields for numbers printing the keys and data in hexadeximal.
 {my ($tree, $title) = @_;                                                      # Tree, title
  @_ == 2 or confess "Two parameters";
  $tree->dumpWithWidth($title, 8, 80, 1, 1, 1)
 }

sub Nasm::X86::Tree::printInOrder($$)                                           # Print a tree in order
 {my ($tree, $title) = @_;                                                      # Tree, title
  @_ == 2 or confess "Two parameters";

  PushR my $F = 31;

  my $s = Subroutine                                                            # Print a tree
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    my $t = $$s{tree};                                                          # Tree
    my $area = $t->area;                                                        # Area

    PushR my $treeBitsR = r10, my $treeBitsIndexR = r11,
          my $K = 30, my $D = 29, my $N = 28;

    Block                                                                       # Print each node in the tree
     {my ($end, $start) = @_;                                                   # Labels
      my $offset = $$p{offset};                                                 # Offset of node to print
      $t->getBlock($offset, $K, $D, $N);                                        # Load node
      my $l = $t->lengthFromKeys($K);                                           # Number of nodes
      $l->for(sub                                                               # Print sub nodes
       {my ($index, $start, $next, $end) = @_;
        my $i = $index * $t->width;                                             # Key/Data?node offset
        my $k = dFromZ $K, $i;                                                  # Key
        my $d = dFromZ $D, $i;                                                  # Data
        my $n = dFromZ $N, $i;                                                  # Sub nodes
        If $n > 0,                                                              # Not a leaf
        Then
         {$sub->call(parameters => {offset => $n},                              # Recurse
                     structures => {tree   => $t});
         };
        $k->outRightInHex(K width => 4);                                        # Print key
       });

      If $l > 0,                                                                # Print final sub tree
      Then
       {my $o = $l * $t->width;                                                 # Final sub tree offset
        my $n = dFromZ $N, $l * $t->width;                                      # Final sub tree
        If $n > 0,                                                              # Not a leaf
        Then
         {$sub->call(parameters => {offset => $n},
                     structures => {tree   => $t});

         };
       };
     };
    PopR;
   } parameters => [qw(offset)],
     structures => {tree => $tree},
     name       => "Nasm::X86::Tree::printInOrder";

  PrintOutString $title;                                                        # Title of the piece so we do not lose it

  $tree->firstFromMemory($F);
  my $R = $tree->rootFromFirst($F);
  my $C = $tree->sizeFromFirst($F);

  If $R == 0,                                                                   # Empty tree
  Then
   {PrintOutStringNL "- empty";
   },
  Else
   {$C->outRightInDec(K width => 4);
    PrintOutString ": ";

     $s->call(structures => {tree  => $tree},                                   # Print root node
             parameters => {offset => $R});
    PrintOutNL;
   };

  PopR;
 }

sub Nasm::X86::Tree::outAsUtf8($)                                               # Print the data values of the specified string on stdout assuming each data value is a utf32 character and that the output device supports utf8
 {my ($string) = @_;                                                            # Tree descriptor of string
  @_ == 1 or confess "One parameter";

  $string->by(sub                                                               # Each character
   {my ($i, $start, $next, $end) = @_;
    PushR rax;
    $string->data->setReg(rax);
    convert_rax_from_utf32_to_utf8;
    PrintOutRaxAsText;
    PopR;
   });
  $string                                                                       # Chain from the target string
 }

sub Nasm::X86::Tree::outAsUtf8NL($)                                             # Print the data values of the specified string on stdout assuming each data value is a utf32 character and that the output device supports utf8. Follow the print with a new line character.
 {my ($string) = @_;                                                            # Tree descriptor of string
  @_ == 1 or confess "One parameter";
  $string->outAsUtf8;
  PrintOutNL;
  $string                                                                       # Chain from the target string
 }

if (1)                                                                          # Define operator overloading for trees
 {package Nasm::X86::Tree;
  use overload
#   '+'  => \&add,
#   '-'  => \&sub,
#   '*'  => \&times,
#   '/'  => \&divide,
#   '%'  => \&mod,
#  '=='  => \&eq,
#  '!='  => \&ne,
#  '>='  => \&ge,
#   '>'  => \&gt,
#  '<='  => \&le,
#  '<'   => \&lt,
#  '++'  => \&inc,
   '--'  => \&dec,
#  '""'  => \&str,
#  '&'   => \&and,                                                              # We use the zero flag as the bit returned by a Boolean operation so we cannot implement '&' or '|' which were previously in use because '&&' and '||' and "and" and "or" are all disallowed in Perl operator overloading.
#  '|'   => \&or,
   '+='  => \&plusAssign,
#  '-='  => \&minusAssign,
#  '='   => \&equals,
#  '<<'  => \&shiftLeft,
#  '>>'  => \&shiftRight,
#  '!'    => \&not,
   "fallback" => 1,
 }

sub Nasm::X86::Tree::plusAssign($$)                                             # Use plus to push an element to a tree being used as a stack
 {my ($tree, $data) = @_;                                                       # Tree being used as a stack, data to push

  !exists $tree->usage->{stack} and keys $tree->usage->%* and                   # Check that the tree is being used as a stack
    confess "Tree is not being used as a stack";
  ref($data) =~ m(Variable|Tree) or                                             # Check right operand on right
    confess "Need a tree or variable on the right";

  $tree->push($data);                                                           # Perform the push
  $tree                                                                         # The resulting tree
 }

sub Nasm::X86::Tree::dec($)                                                     # Pop from the tree if it is being used as  stack
 {my ($tree, $data) = @_;                                                       # Tree being used as a stack, data to push

  !exists $tree->usage->{stack} and keys $tree->usage->%* and                   # Check that the tree is being used as a stack
    confess "Tree is not being used as a stack";

  $tree->pop                                                                    # Perform the pop
 }

#D1 Assemble                                                                    # Assemble generated code

sub CallC($@)                                                                   # Call a C subroutine.
 {my ($sub, @parameters) = @_;                                                  # Name of the sub to call, parameters
  my @order = (rdi, rsi, rdx, rcx, r8, r9, r15);
  PushR @order;

  for my $i(keys @parameters)                                                   # Load parameters into designated registers
   {Mov $order[$i], $parameters[$i];
   }

  Push rax;                                                                     # Align stack on 16 bytes
  Mov rax, rsp;                                                                 # Move stack pointer
  Shl rax, 60;                                                                  # Get lowest nibble
  Shr rax, 60;
  IfEq                                                                          # If we are 16 byte aligned push two twos
  Then
   {Mov rax, 2; Push rax; Push rax;
   },
  Else                                                                          # If we are not 16 byte aligned push one one.
   {Mov rax, 1; Push rax;
   };

  if (ref($sub))                                                                # Where do we use this option?
   {Call $sub->start;
   }
  else                                                                          # Call named subroutine
   {Call $sub;
   }

  Pop r15;                                                                      # Decode and reset stack after 16 byte alignment
  Cmp r15, 2;                                                                   # Check for double push
  Pop r15;                                                                      # Single or double push
  IfEq Then {Pop r15};                                                          # Double push
  PopR @order;
 }

sub Extern(@)                                                                   # Name external references.
 {my (@externalReferences) = @_;                                                # External references
  push @extern, @_;
 }

sub Link(@)                                                                     # Libraries to link with.
 {my (@libraries) = @_;                                                         # External references
  push @link, @_;
 }

sub Start()                                                                     # Initialize the assembler.
 {@bss = @data = @rodata = %rodata = %rodatas = %subroutines = @text =
  @PushR = @extern = @link = @VariableStack = ();
# @RegistersAvailable = ({map {$_=>1} @GeneralPurposeRegisters});               # A stack of hashes of registers that are currently free and this can be used without pushing and popping them.
  SubroutineStartStack;                                                       # Number of variables at each lexical level
  $Labels = 0;
 }

sub Exit(;$)                                                                    # Exit with the specified return code or zero if no return code supplied.  Assemble() automatically adds a call to Exit(0) if the last operation in the program is not a call to Exit.
 {my ($c) = @_;                                                                 # Return code
  $c //= 0;
  my $s = Subroutine
   {Comment "Exit code: $c";
    PushR rax, rdi;
    Mov rdi, $c;
    Mov rax, 60;
    Syscall;
    PopR;
   } name => "Exit_$c";

  $s->call;
 }

my $LocateIntelEmulator;                                                        # Location of Intel Software Development Emulator

sub LocateIntelEmulator()                                                       #P Locate the Intel Software Development Emulator.
 {my @locations = qw(/var/isde/sde64 sde/sde64 ./sde64);                        # Locations at which we might find the emulator
  my $downloads = q(/home/phil/Downloads);                                      # Downloads folder

  return $LocateIntelEmulator if defined $LocateIntelEmulator;                  # Location has already been discovered

  for my $l(@locations)                                                         # Try each locations
   {return $LocateIntelEmulator = $l if -e $l;                                  # Found it - cache and return
   }

  if (qx(sde64 -version) =~ m(Intel.R. Software Development Emulator))          # Try path
   {return $LocateIntelEmulator = "sde64";
   }

  return undef unless -e $downloads;                                            # Skip local install if not developing
  my $install = <<END =~ s(\n) (  && )gsr =~ s(&&\s*\Z) ()sr;                   # Install sde
cd $downloads
curl https://software.intel.com/content/dam/develop/external/us/en/documents/downloads/sde-external-8.63.0-2021-01-18-lin.tar.bz2 > sde.tar.bz2
tar -xf sde.tar.bz2
sudo mkdir -p /var/isde/
sudo cp -r * /var/isde/
ls -ls /var/isde/
END

  say STDERR qx($install);                                                      # Execute install

  for my $l(@locations)                                                         # Retry install locations after install
   {return $LocateIntelEmulator = $l if -e $l;                                  # Found it - cache and return
   }
  undef                                                                         # Still not found - give up
 }

sub getInstructionCount()                                                       #P Get the number of instructions executed from the emulator mix file.
 {return 0 unless -e $sdeMixOut;
  my $s = readFile $sdeMixOut;
  if ($s =~ m(\*total\s*(\d+))) {return $1}
  confess;
 }

sub Optimize(%)                                                                 #P Perform code optimizations.
 {my (%options) = @_;                                                           # Options
  my %o = map {$_=>1} $options{optimize}->@*;
  if (1 or $o{if})                                                              # Optimize if statements by looking for the unnecessary reload of the just stored result
   {for my $i(1..@text-2)                                                       # Each line
     {my $t = $text[$i];
      if ($t =~ m(\A\s+push\s+(r\d+)\s*\Z)i)                                    # Push
       {my $R = $1;                                                             # Register being pushed
        my $s = $text[$i-1];                                                    # Previous line
        if ($s =~ m(\A\s+pop\s+$R\s*\Z)i)                                       # Matching push
         {my $r = $text[$i-2];
          if ($r =~ m(\A\s+mov\s+\[rbp-8\*\((\d+)\)],\s*$R\s*\Z)i)              # Save to variable
           {my $n = $1;                                                         # Variable number
            my $u = $text[$i+1];
            if ($u =~ m(\A\s+mov\s+$R,\s*\[rbp-8\*\($n\)]\s*\Z)i)               # Reload register
             {for my $j($i-1..$i+1)
               {$text[$j] = '; out '. $text[$j];
               }
             }
           }
         }
       }
     }
   }
 }

my $hasAvx512;

sub hasAvx512()                                                                 #P Check whether the current device has avx512 instructions or not
 {return $hasAvx512 if defined $hasAvx512;
  $hasAvx512 = qx(cat /proc/cpuinfo | grep avx512) =~ m(\S) ? 1 : 0;            # Cache avx512 result
 }

sub lineNumbersToSubNamesFromSource                                             # Create a hash mapping line numbers to subroutine definitions
 {my @s = readFile $0;                                                          # Read source file
  my %l;                                                                        # Mapping from line number to curent sub
  my $c;                                                                        # The current sub
  for my $i(keys @s)                                                            # Each line number
   {my $s = $s[$i];
    if ($s =~ m(\Asub ([^ \(]+)))
     {$c = $1 =~ s(\ANasm::X86::) ()r;                                          # Subroutine name  minus package name and parameters
     }
    if ($s =~ m(\A }))                                                          # End of sub
     {$c = undef;
     }
    $l{$i+1} = $c if $c;
   }
  %l
 }

sub locateRunTimeErrorInDebugTraceOutput                                        # Locate the traceback of the last known good position in the trace file before the error occurred
 {my @a = readFile q(sde-debugtrace-out.txt);                                   # Read trace file
  my $s = 0;                                                                    # Parse state
  my @p;                                                                        # Position in source file

  for my $a(reverse @a)                                                         # Read backwards
   {if (!$s)                                                                    # Looking for traceback start
     {if ($a =~ m(\AINS 0x[[:xdigit:]]{16}\s+MMX\s+movq\sr11,\s+mm0))
       {$s = 1;
       }
     }
    elsif ($s == 1)                                                             # In the traceback
     {if ($a =~ m(\AINS\s+0x[[:xdigit:]]{16}\s+BASE\s+mov r11, (0x[[:xdigit:]]+)))
       {unshift @p, eval $1;
        next;
       }
      last;                                                                     # Finished the scan of the tracebook
     }
   }

  push my @t, "TraceBack start: ", "_"x80;                                      # Write the traceback
  my %l = lineNumbersToSubNamesFromSource();
  for my $i(keys @p)
   {my $p =  $p[$i];
    push @t, sprintf "%6d %s called at $0 line %d", $p, pad($l{$p}//'.', 32), $p;
   }
  push @t, "_" x 80;
  my $t = join "\n", @t;
  say STDERR $t;                                                                # Print trace back so we can see it in geany messages
  owf("zzzTraceBack.txt", $t);                                                  # Place into a well known file
 }

sub fixMixOutput                                                                # Fix mix output so we know where the code comes from in the source file
 {my @a = readFile q(sde-mix-out.txt);                                          # Read mix output
  my %l = lineNumbersToSubNamesFromSource();

  for my $i(keys @a)                                                            # Each line of output
   {if ($a[$i] =~ m(\AXDIS\s+[[:xdigit:]]{16}:\s+BASE\s+[[:xdigit:]]+\s+mov\s+r11,\s+(0x[[:xdigit:]]+)))
     {my $l = eval($1)+1;
      $a[$i] = sprintf "    %s called at $0 line %d\n", $l{$l}//'', $l;
     }
   }
  owf q(sde-mix-out.txt), join "", @a;                                          # Update mix out
  say STDERR              join "", @a;                                          # Write mix out
 }

sub onGitHub                                                                    # Whether we are on GitHub or not
 {$ENV{GITHUB_REPOSITORY_OWNER}
 }

our $assembliesPerformed  = 0;                                                  # Number of assemblies performed
our $instructionsExecuted = 0;                                                  # Total number of instructions executed
our $totalBytesAssembled  = 0;                                                  # Total size of the output programs

sub Assemble(%)                                                                 # Assemble the generated code.
 {my (%options) = @_;                                                           # Options
  my $aStart = time;
  my $library    = $options{library};                                           # Create  the named library if supplied from the supplied assembler code
  my $list       = $options{list};                                              # Create and retain a listing file so we can see where a trace error occurs
  my $debug      = $options{debug}//0;                                          # Debug: 0 - none (minimal output), 1 - normal (debug output and confess of failure), 2 - failures (debug output and no confess on failure) .
  my $trace      = $options{trace}//0;                                          # Trace: 0 - none (minimal output), 1 - trace with sde64 and create a listing file to match
  my $keep       = $options{keep};                                              # Keep the executable
  my $mix        = $options{mix};                                               # Create mix output and fix with line number locations in source

  my $sourceFile = q(z.asm);                                                    # Source file
  my $execFile   = $keep // q(z);                                               # Executable file
  my $listFile   = q(z.txt);                                                    # Assembler listing
  my $objectFile = $library // q(z.o);                                          # Object file
  my $o1         = 'zzzOut.txt';                                                # Stdout from run
  my $o2         = 'zzzErr.txt';                                                # Stderr from run

  @PushR and confess "Mismatch PushR, PopR";                                    # Match PushR with PopR

  unlink $o1, $o2, $objectFile, $execFile, $listFile, $sourceFile;              # Remove output files

  Exit 0 unless $library or @text > 4 && $text[-4] =~ m(Exit code:);            # Exit with code 0 if an exit was not the last thing coded in a program but ignore for a library.

# Optimize(%options);                                                           # Perform any optimizations requested

  if (1)                                                                        # Concatenate source code
   {my $r = join "\n", map {s/\s+\Z//sr}   @rodata;
    my $d = join "\n", map {s/\s+\Z//sr}   @data;
    my $B = join "\n", map {s/\s+\Z//sr}   @bss;
    my $t = join "\n", map {s/\s+\Z//sr}   @text;
    my $x = join "\n", map {qq(extern $_)} @extern;
    my $N = $VariableStack[0];                                                  # Number of variables needed on the stack

    my $A = <<END;                                                              # Source code
bits 64
default rel
END

    $A .= <<END if $t and !$library;
global _start, main
  _start:
  main:
  Enter $N*8, 0
  $t
  Leave
END

    $A .= <<END if $t and $library;
  $t
END

    $A .= <<END if $r;
section .rodata
  $r
END
    $A .= <<END if $d;
section .data
  $d
END
    $A .= <<END if $B;
section .bss
  $B
  $d
END
    $A .= <<END if $x;
section .text
$x
END

    owf($sourceFile, $A);                                                       # Save source code to source file
   }

  if (!confirmHasCommandLineCommand(q(nasm)))                                   # Check for network assembler
   {my $f = fpf(currentDirectory, $sourceFile);
    say STDERR <<END;
Assember code written to the following file:

$f

I cannot compile this file because you do not have Nasm installed, see:

https://www.nasm.us/
END
    return;
   }

  my $avx512 = hasAvx512 ? 0 : exists $options{avx512} ? $options{avx512} : 1;  # Emulate if necessary
  my $sde      = LocateIntelEmulator;                                           # Locate the emulator
  my $run      = !$keep && !$library;                                           # Are we actually going to run the resulting code?

  if ($run and $avx512 and !$sde)                                               # Complain about the emulator if we are going to run and we have not suppressed the emulator and the emulator is not present
   {my $f = fpf(currentDirectory, $execFile);
    say STDERR <<END;
Executable written to the following file:

$f

I am going to run this without using the Intel emulator. Your program will
crash if it contains instructions not implemented on your computer.

You can get the Intel emulator from:

https://software.intel.com/content/dam/develop/external/us/en/documents/downloads/sde-external-8.63.0-2021-01-18-lin.tar.bz2

To avoid this message, use option(1) below to produce just an executable
without running it, or use the option(2) to run without the emulator:

(1) Assemble(keep=>"executable file name")

(2) Assemble(avx512=>0)
END
    $avx512 = 0;
   }

  if (my @emulatorFiles = searchDirectoryTreesForMatchingFiles(qw(. .txt)))     # Remove prior emulator output files
   {for my $f(@emulatorFiles)
     {unlink $f if $f =~ m(sde-mix-out);
     }
   }
  unlink qw(sde-ptr-check.out.txt sde-mix-out.txt sde-debugtrace-out.txt zzzTraceBack.txt);

  if (1)                                                                        # Assemble
   {my $I = @link ? $interpreter : '';                                          # Interpreter only required if calling C
    my $L = join " ",  map {qq(-l$_)} @link;                                    # List of libraries to link supplied via Link directive.
    my $e = $execFile;
    my $l = $trace ? qq(-l $listFile) : q();                                    # Create a list file if we are tracing because otherwise it it is difficult to know what we are tracing
    my $a = qq(nasm -O0 $l -o $objectFile $sourceFile);                         # Assembly options

    my $cmd  = $library
      ? qq($a -fbin)
      : qq($a -felf64 -g  && ld $I $L -o $e $objectFile && chmod 744 $e);

    qx($cmd);
#say STDERR $cmd; exit;
    confess "Assembly failed $?" if $?;                                         # Stop if assembly failed
   }

  my $aTime = time - $aStart;

  my $out  = $run ? "1>$o1" : '';
  my $err  = $run ? "2>$o2" : '';

  my $exec = sub                                                                # Execution string
   {my $m = $mix ? '-mix' : '';                                                 # Mix output option
    my $o = qq($sde $m -ptr-check);                                             # Emulator options
       $o = qq($sde $m -ptr-check -debugtrace -footprint) if $trace;            # Emulator options - tracing
    my $e = $execFile;

    my $E = $options{emulator};                                                 # Emulator required
    if ($E or $avx512 && !hasAvx512 or $trace)                                  # Command to execute program via the  emulator
     {return qq($o -- ./$e $err $out)
     }

    qq(./$e $err $out);                                                         # Command to execute program without the emulator
   }->();

  my $eStart = time;

  qx($exec) if $run;                                                            # Run unless suppressed by user or library
#say STDERR $exec;exit;
  my $er     = $?;                                                              # Execution result
  my $eTime  = time - $eStart;

  if ($run)                                                                     # Execution details
   {my $instructions       = getInstructionCount;                               # Instructions executed under emulator
    $instructionsExecuted += $instructions;                                     # Count instructions executed
    my $p = $assembliesPerformed++;                                             # Count assemblies
    my $n = $options{number};
    !$n or $n == $p or warn "Assembly $p versus number => $n";

    my $bytes = (fileSize($execFile)//9448) - 9448;                             # Estimate the size of the output program
    $totalBytesAssembled += $bytes;                                             # Estimate total of all programs assembled

    my (undef, $file, $line) = caller();                                        # Line in caller

    say STDERR sprintf("        %12s    %12s    %12s    %12s  %12s  %12s",      # Header if necessary
       "Clocks", "Bytes", "Total Clocks", "Total Bytes", "Run Time", "Assembler")
      if $assembliesPerformed % 100 == 1;

    say STDERR                                                                  # Rows
      sprintf("%4d    %12s    %12s    %12s    %12s  %12.6f  %12.2f  at $file line $line",
      $assembliesPerformed,
      (map {numberWithCommas $_} $instructions,         $bytes,
                                 $instructionsExecuted, $totalBytesAssembled),
                                 $eTime, $aTime);
   }

  if ($run and $debug == 0 and -e $o2)                                          # Print errors if not debugging
   {say STDERR readBinaryFile($o2);
   }

  if ($run and $debug == 1)                                                     # Print files if soft debugging or error
   {say STDERR readFile($o1) if -e $o1;
    say STDERR readFile($o2) if -e $o2;
   }

  fixMixOutput if $run and $mix;                                                # Fix mix output to show where code came from in the source file

  if ($run and $debug < 2 and -e $o2 and readFile($o2) =~ m(SDE ERROR:)s)       # Emulator detected an error
   {locateRunTimeErrorInDebugTraceOutput if $trace;                             # Locate the last known good position in the debug trace file, if it exists,  before the error occurred
    #confess "Stopping on SDE ERROR\n";
   }

# confess "Failed $er" if $debug < 2 and $er;                                   # Check that the run succeeded

  unlink $objectFile unless $library;                                           # Delete files
  unlink $execFile   unless $keep;                                              # Delete executable unless asked to keep it or its a library

  if (my $N = $options{countComments})                                          # Count the comments so we can see what code to put into subroutines
   {my %c; my %b;                                                               # The number of lines between the comments, the number of blocks
    my $s;
    for my $c(readFile $sourceFile)
     {if (!$s)
       {if ($c =~ m(;\s+CommentWithTraceBack\s+PushR))
         {$s = $c =~ s(Push) (Pop)r;
          $b{$s}++;
         }
       }
      elsif ($c eq $s)  {$s = undef}
      else              {$c{$s}++}
     }

    my @c;
    for my $c(keys %c)                                                          # Remove comments that do not appear often
     {push @c, [$c{$c}, $b{$c}, $c] if $c{$c} >= $N;
     }
    my @d = sort {$$b[0] <=> $$a[0]} @c;
    say STDERR formatTable(\@d, [qw(Lines Blocks Comment)]);                    # Print frequently appearing comments
   }

  Start;                                                                        # Clear work areas for next assembly

  if ($run and defined(my $e = $options{eq}))                                   # Diff results against expected
   {my $g = readFile($debug < 2 ? $o1 : $o2);
       $e =~ s(\s+#.*?\n) (\n)gs;                                               # Remove comments so we can annotate listings
    s(Subroutine trace back.*) ()s for $e, $g;                                  # Remove any trace back because the location of the subroutine in memory will vary
    if ($g ne $e)
     {my ($s, $G, $E) = stringsAreNotEqual($g, $e);
      if (length($s))
       {my $line = 1 + length($s =~ s([^\n])  ()gsr);
        my $char = 1 + length($s =~ s(\A.*\n) ()sr);
        say STDERR "Comparing wanted with got failed at line: $line, character: $char";
        say STDERR "Start:\n$s";
       }
      my $b1 = '+' x 80;
      my $b2 = '_' x 80;
      say STDERR "Want $b1\n", firstNChars($E, 80);
      say STDERR "Got  $b2\n", firstNChars($G, 80);
      say STDERR "Want: ", dump($e);
      say STDERR "Got : ", dump($g);

      if (onGitHub)                                                             # Dump output files that might show why the failure occurred
       {for my $f(qw(zzzOut.txt zzzErr.txt sde-mix-out.txt sde-debugtrace-out.txt zzzTraceBack.txt))
         {if (-e $f)                                                            # Dump the file if it exists
           {say STDERR qx(ls -la $f; cat $f);
           }
         }
       }
      confess "Test failed";# unless $onGitHub;                                 # Test failed unless we are debugging test failures
     }
    return 1;                                                                   # Test passed
   }

  return scalar(readFile($debug < 2 ? $o1 : $o2)) if $run;                      # Show stdout results unless stderr results requested
  $exec;                                                                        # Retained output
 }

sub totalBytesAssembled                                                         #P Total size in bytes of all files assembled during testing.
 {$totalBytesAssembled
 }

#d
#-------------------------------------------------------------------------------
# Export - eeee
#-------------------------------------------------------------------------------

if (0)                                                                          # Print exports
 {my @e = (@declarations);
  for my $a(readFile $0)
   {next unless $a =~ m(\Asub);
    next if     $a =~ m(#P);
    if ($a =~ m(\s+(.*?)\())
     {push @e, $1;
     }
   }
  say STDERR q/@EXPORT_OK    = qw(/.join(' ', sort @e).q/);/;
  exit;
 }

use Exporter qw(import);

use vars qw(@ISA @EXPORT @EXPORT_OK %EXPORT_TAGS);

@ISA          = qw(Exporter);
@EXPORT       = qw();
@EXPORT_OK    = qw(Add Align All8Structure AllocateMemory And AndBlock Andn Assemble Block Bswap Bt Btc Btr Bts Bzhi Call CallC CheckIfMaskRegisterNumber CheckIfMaskRegisterNumber CheckMaskRegister CheckMaskRegisterNumber CheckMaskRegisterNumber ChooseRegisters ClassifyInRange ClassifyWithInRange ClassifyWithInRangeAndSaveOffset ClassifyWithInRangeAndSaveWordOffset ClearMemory ClearRegisters ClearRegisters ClearZF CloseFile Cmova Cmovae Cmovb Cmovbe Cmovc Cmove Cmovg Cmovge Cmovl Cmovle Cmovna Cmovnae Cmovnb Cmp Comment Comment CommentWithTraceBack ConvertUtf8ToUtf32 CopyMemory Cpuid CreateArea CreateLibrary DComment DComment Db Dd Dec DescribeArea Div Dq Ds Dw Ef Else Enter Exit Extern Fail For ForEver ForIn Fork FreeMemory GetNextUtf8CharAsUtf32 GetPPid GetPid GetPidInHex GetUid Hash Idiv If IfC IfEq IfGe IfGt IfLe IfLt IfNc IfNe IfNs IfNz IfS IfZ Imul Imul3 Inc InsertOneIntoRegisterAtPoint InsertZeroIntoRegisterAtPoint Ja Jae Jb Jbe Jc Jcxz Je Jecxz Jg Jge Jl Jle Jmp Jna Jnae Jnb Jnbe Jnc Jne Jng Jnge Jnl Jnle Jno Jnp Jns Jnz Jo Jp Jpe Jpo Jrcxz Js Jz K Kaddb Kaddd Kaddq Kaddw Kandb Kandd Kandnb Kandnd Kandnq Kandnw Kandq Kandw Kmovb Kmovd Kmovq Kmovw Knotb Knotd Knotq Knotw Korb Kord Korq Kortestb Kortestd Kortestq Kortestw Korw Kshiftlb Kshiftld Kshiftlq Kshiftlw Kshiftrb Kshiftrd Kshiftrq Kshiftrw Ktestb Ktestd Ktestq Ktestw Kunpckb Kunpckd Kunpckq Kunpckw Kxnorb Kxnord Kxnorq Kxnorw Kxorb Kxord Kxorq Kxorw Lahf Lea Leave Link LoadBitsIntoMaskRegister LoadConstantIntoMaskRegister LoadRegFromMm LoadZmm Loop Lzcnt Mov Movd Movdqa Mulpd Nasm::X86::Area::CreateTree Nasm::X86::Area::allocZmmBlock Nasm::X86::Area::allocate Nasm::X86::Area::append Nasm::X86::Area::char Nasm::X86::Area::clear Nasm::X86::Area::dump Nasm::X86::Area::free Nasm::X86::Area::freeChainSpace Nasm::X86::Area::m Nasm::X86::Area::makeReadOnly Nasm::X86::Area::makeWriteable Nasm::X86::Area::nl Nasm::X86::Area::out Nasm::X86::Area::outNL Nasm::X86::Area::q Nasm::X86::Area::ql Nasm::X86::Area::read Nasm::X86::Area::size Nasm::X86::Area::used Nasm::X86::Area::write Nasm::X86::Area::z Nasm::X86::Structure::field Nasm::X86::StructureField::addr Nasm::X86::Sub::V Nasm::X86::Sub::call Nasm::X86::Sub::dispatch Nasm::X86::Sub::dispatchV Nasm::X86::Sub::via Nasm::X86::Subroutine::mapStructureVariables Nasm::X86::Subroutine::uploadStructureVariablesToNewStackFrame Nasm::X86::Tree::append Nasm::X86::Tree::by Nasm::X86::Tree::clear Nasm::X86::Tree::clone Nasm::X86::Tree::delete Nasm::X86::Tree::depth Nasm::X86::Tree::dump Nasm::X86::Tree::find Nasm::X86::Tree::findFirst Nasm::X86::Tree::findLast Nasm::X86::Tree::findNext Nasm::X86::Tree::findPrev Nasm::X86::Tree::findShortString Nasm::X86::Tree::free Nasm::X86::Tree::get Nasm::X86::Tree::insertShortString Nasm::X86::Tree::outAsUtf8 Nasm::X86::Tree::outAsUtf8NL Nasm::X86::Tree::pop Nasm::X86::Tree::printInOrder Nasm::X86::Tree::put Nasm::X86::Tree::reverse Nasm::X86::Tree::size Nasm::X86::Tree::substring Nasm::X86::Tree::yb Nasm::X86::Variable::add Nasm::X86::Variable::address Nasm::X86::Variable::allocateMemory Nasm::X86::Variable::and Nasm::X86::Variable::arithmetic Nasm::X86::Variable::assign Nasm::X86::Variable::bFromZ Nasm::X86::Variable::bIntoX Nasm::X86::Variable::bIntoZ Nasm::X86::Variable::boolean Nasm::X86::Variable::booleanC Nasm::X86::Variable::booleanZF Nasm::X86::Variable::call Nasm::X86::Variable::clearBit Nasm::X86::Variable::clearMaskBit Nasm::X86::Variable::clearMemory Nasm::X86::Variable::clone Nasm::X86::Variable::copy Nasm::X86::Variable::copyMemory Nasm::X86::Variable::copyRef Nasm::X86::Variable::copyZF Nasm::X86::Variable::copyZFInverted Nasm::X86::Variable::d Nasm::X86::Variable::dFromPointInZ Nasm::X86::Variable::dFromZ Nasm::X86::Variable::dIntoPointInZ Nasm::X86::Variable::dIntoX Nasm::X86::Variable::dIntoZ Nasm::X86::Variable::debug Nasm::X86::Variable::dec Nasm::X86::Variable::divide Nasm::X86::Variable::division Nasm::X86::Variable::eq Nasm::X86::Variable::equals Nasm::X86::Variable::err Nasm::X86::Variable::errCString Nasm::X86::Variable::errCStringNL Nasm::X86::Variable::errInDec Nasm::X86::Variable::errInDecNL Nasm::X86::Variable::errNL Nasm::X86::Variable::errRightInBin Nasm::X86::Variable::errRightInBinNL Nasm::X86::Variable::errRightInDec Nasm::X86::Variable::errRightInDecNL Nasm::X86::Variable::errRightInHex Nasm::X86::Variable::errRightInHexNL Nasm::X86::Variable::errSpaces Nasm::X86::Variable::for Nasm::X86::Variable::freeMemory Nasm::X86::Variable::ge Nasm::X86::Variable::getConst Nasm::X86::Variable::getReg Nasm::X86::Variable::gt Nasm::X86::Variable::inc Nasm::X86::Variable::incDec Nasm::X86::Variable::isRef Nasm::X86::Variable::le Nasm::X86::Variable::loadZmm Nasm::X86::Variable::lt Nasm::X86::Variable::max Nasm::X86::Variable::min Nasm::X86::Variable::minusAssign Nasm::X86::Variable::mod Nasm::X86::Variable::ne Nasm::X86::Variable::not Nasm::X86::Variable::or Nasm::X86::Variable::out Nasm::X86::Variable::outCString Nasm::X86::Variable::outCStringNL Nasm::X86::Variable::outInDec Nasm::X86::Variable::outInDecNL Nasm::X86::Variable::outNL Nasm::X86::Variable::outRightInBin Nasm::X86::Variable::outRightInBinNL Nasm::X86::Variable::outRightInDec Nasm::X86::Variable::outRightInDecNL Nasm::X86::Variable::outRightInHex Nasm::X86::Variable::outRightInHexNL Nasm::X86::Variable::outSpaces Nasm::X86::Variable::plusAssign Nasm::X86::Variable::printErrMemoryInHexNL Nasm::X86::Variable::printMemoryInHexNL Nasm::X86::Variable::printOutMemoryInHexNL Nasm::X86::Variable::putBwdqIntoMm Nasm::X86::Variable::putWIntoZmm Nasm::X86::Variable::qFromZ Nasm::X86::Variable::qIntoX Nasm::X86::Variable::qIntoZ Nasm::X86::Variable::rightInBin Nasm::X86::Variable::rightInDec Nasm::X86::Variable::rightInHex Nasm::X86::Variable::setBit Nasm::X86::Variable::setMask Nasm::X86::Variable::setMaskBit Nasm::X86::Variable::setMaskFirst Nasm::X86::Variable::setReg Nasm::X86::Variable::setZmm Nasm::X86::Variable::shiftLeft Nasm::X86::Variable::shiftRight Nasm::X86::Variable::spaces Nasm::X86::Variable::str Nasm::X86::Variable::sub Nasm::X86::Variable::times Nasm::X86::Variable::wFromZ Nasm::X86::Variable::wIntoX Nasm::X86::Library::load Neg Not OnSegv OpenRead OpenWrite Or OrBlock Pass Pextrb Pextrd Pextrq Pextrw Pinsrb Pinsrd Pinsrq Pinsrw Pop PopR PopR PopRR Popcnt Popfq PrintCString PrintCStringNL PrintErrNL PrintErrOneRegisterInHex PrintErrOneRegisterInHexNL PrintErrRaxInHex PrintErrRaxInHexNL PrintErrRaxRightInDec PrintErrRaxRightInDecNL PrintErrRax_InHex PrintErrRax_InHexNL PrintErrRegisterInHex PrintErrRegisterInHex PrintErrRightInBin PrintErrRightInBinNL PrintErrRightInHex PrintErrRightInHexNL PrintErrSpace PrintErrString PrintErrStringNL PrintErrStringNL PrintErrTraceBack PrintMemory PrintMemoryInHex PrintMemory_InHex PrintNL PrintOneRegisterInHex PrintOutNL PrintOutOneRegisterInHex PrintOutOneRegisterInHexNL PrintOutRaxInHex PrintOutRaxInHexNL PrintOutRaxRightInDec PrintOutRaxRightInDecNL PrintOutRax_InHex PrintOutRax_InHexNL PrintOutRegisterInHex PrintOutRegisterInHex PrintOutRightInBin PrintOutRightInBinNL PrintOutRightInHex PrintOutRightInHexNL PrintOutSpace PrintOutString PrintOutStringNL PrintOutStringNL PrintOutTraceBack PrintRaxAsChar PrintRaxAsText PrintRaxInDec PrintRaxInHex PrintRaxRightInDec PrintRax_InHex PrintRegisterInHex PrintRightInBin PrintRightInHex PrintSpace PrintString PrintString PrintStringNL PrintTraceBack Pslldq Psrldq Push PushR PushRR Pushfq R RComment RComment Rb Rd Rdtsc ReadChar ReadFile ReadInteger ReadLine ReadTimeStampCounter RegisterSize RestoreFirstFour RestoreFirstFourExceptRax RestoreFirstFourExceptRaxAndRdi RestoreFirstSeven RestoreFirstSevenExceptRax RestoreFirstSevenExceptRaxAndRdi Ret Rq Rs Rutf8 Rw Sal Sar SaveFirstFour SaveFirstSeven SaveRegIntoMm SetLabel SetMaskRegister SetZF Seta Setae Setb Setbe Setc Sete Setg Setge Setl Setle Setna Setnae Setnb Setnbe Setnc Setne Setng Setnge Setnl Setno Setnp Setns Setnz Seto Setp Setpe Setpo Sets Setz Shl Shr Start StatSize StringLength StringLength Structure Sub Subroutine Subroutine SubroutineStartStack Syscall Syscall Test Then Tzcnt V Vaddd Vaddpd Valignb Valignd Valignq Valignw Variable Vcvtudq2pd Vcvtudq2ps Vcvtuqq2pd Vdpps Vgetman
tps Vmovd Vmovdqa32 Vmovdqa64 Vmovdqu Vmovdqu32 Vmovdqu64 Vmovdqu8 Vmovq Vmulpd Vpaddb Vpaddd Vpaddq Vpaddw Vpandb Vpandd Vpandnb Vpandnd Vpandnq Vpandnw Vpandq Vpandw Vpbroadcastb Vpbroadcastd Vpbroadcastq Vpbroadcastw Vpcmpeqb Vpcmpeqd Vpcmpeqq Vpcmpeqw Vpcmpub Vpcmpud Vpcmpuq Vpcmpuw Vpcompressd Vpcompressq Vpexpandd Vpexpandq Vpextrb Vpextrd Vpextrq Vpextrw Vpinsrb Vpinsrd Vpinsrq Vpinsrw Vpmovb2m Vpmovd2m Vpmovm2b Vpmovm2d Vpmovm2q Vpmovm2w Vpmovq2m Vpmovw2m Vpmullb Vpmulld Vpmullq Vpmullw Vporb Vpord Vporq Vporvpcmpeqb Vporvpcmpeqd Vporvpcmpeqq Vporvpcmpeqw Vporw Vprolq Vpsubb Vpsubd Vpsubq Vpsubw Vptestb Vptestd Vptestq Vptestw Vpxorb Vpxord Vpxorq Vpxorw Vsqrtpd WaitPid Xchg Xor ah al ax bFromX bFromZ bRegFromZmm bRegIntoZmm bh bl bp bpl bx byteRegister ch checkZmmRegister cl copyStructureMinusVariables createBitNumberFromAlternatingPattern cs cx dFromX dFromZ dWordRegister dh di dil dl ds dx eax ebp ebx ecx edi edx es esi esp executeFileViaBash fs getBwdqFromMm gs k0 k1 k2 k3 k4 k5 k6 k7 mm0 mm1 mm2 mm3 mm4 mm5 mm6 mm7 qFromX qFromZ r10 r10b r10d r10l r10w r11 r11b r11d r11l r11w r12 r12b r12d r12l r12w r13 r13b r13d r13l r13w r14 r14b r14d r14l r14w r15 r15b r15d r15l r15w r8 r8b r8d r8l r8w r9 r9b r9d r9l r9w rax rbp rbx rcx rdi rdx registerNameFromNumber rflags rip rsi rsp si sil sp spl ss st0 st1 st2 st3 st4 st5 st6 st7 unlinkFile wFromX wFromZ wRegFromZmm wRegIntoZmm wordRegister xmm xmm0 xmm1 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 xmm16 xmm17 xmm18 xmm19 xmm2 xmm20 xmm21 xmm22 xmm23 xmm24 xmm25 xmm26 xmm27 xmm28 xmm29 xmm3 xmm30 xmm31 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 ymm ymm0 ymm1 ymm10 ymm11 ymm12 ymm13 ymm14 ymm15 ymm16 ymm17 ymm18 ymm19 ymm2 ymm20 ymm21 ymm22 ymm23 ymm24 ymm25 ymm26 ymm27 ymm28 ymm29 ymm3 ymm30 ymm31 ymm4 ymm5 ymm6 ymm7 ymm8 ymm9 zmm zmm0 zmm1 zmm10 zmm11 zmm12 zmm13 zmm14 zmm15 zmm16 zmm17 zmm18 zmm19 zmm2 zmm20 zmm21 zmm22 zmm23 zmm24 zmm25 zmm26 zmm27 zmm28 zmm29 zmm3 zmm30 zmm31 zmm4 zmm5 zmm6 zmm7 zmm8 zmm9 zmmM zmmMZ);%EXPORT_TAGS  = (all => [@EXPORT, @EXPORT_OK]);

# podDocumentation
=pod

=encoding utf-8

=head1 Name

Nasm::X86 - Generate X86 assembler code using Perl as a macro pre-processor.

=head1 Synopsis

Write and execute B<x64> B<Avx512> assembler code from L<perl> using L<perl> as a
macro assembler.  The generated code can be run under the Intel emulator to
obtain execution trace and instruction counts.

=head2 Examples

=head3 Avx512 instructions

Use B<Avx512> instructions to perform B<64> comparisons in parallel.

  my $P = "2F";                                                                 # Value to test for
  my $l = Rb 0;  Rb $_ for 1..RegisterSize zmm0;                                # 0..63
  Vmovdqu8 zmm0, "[$l]";                                                        # Load data to test
  PrintOutRegisterInHex zmm0;

  Mov rax, "0x$P";                                                              # Broadcast the value to be tested
  Vpbroadcastb zmm1, rax;
  PrintOutRegisterInHex zmm1;

  for my $c(0..7)                                                               # Each possible test
   {my $m = "k$c";
    Vpcmpub $m, zmm1, zmm0, $c;
    PrintOutRegisterInHex $m;
   }

  Kmovq rax, k0;                                                                # Count the number of trailing zeros in k0
  Tzcnt rax, rax;
  PrintOutRegisterInHex rax;

  is_deeply Assemble, <<END;                                                    # Assemble and test
  zmm0: 3F3E 3D3C 3B3A 3938   3736 3534 3332 3130   2F2E 2D2C 2B2A 2928   2726 2524 2322 2120   1F1E 1D1C 1B1A 1918   1716 1514 1312 1110   0F0E 0D0C 0B0A 0908   0706 0504 0302 0100
  zmm1: 2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F   2F2F 2F2F 2F2F 2F2F
    k0: 0000 8000 0000 0000
    k1: FFFF 0000 0000 0000
    k2: FFFF 8000 0000 0000
    k3: 0000 0000 0000 0000
    k4: FFFF 7FFF FFFF FFFF
    k5: 0000 FFFF FFFF FFFF
    k6: 0000 7FFF FFFF FFFF
    k7: FFFF FFFF FFFF FFFF
   rax: 0000 0000 0000 002F
END

With the print statements removed, the Intel Emulator indicates that 26
instructions were executed:

  CALL_NEAR                                                              1
  ENTER                                                                  2
  JMP                                                                    1
  KMOVQ                                                                  1
  MOV                                                                    5
  POP                                                                    1
  PUSH                                                                   3
  SYSCALL                                                                1
  TZCNT                                                                  1
  VMOVDQU8                                                               1
  VPBROADCASTB                                                           1
  VPCMPUB                                                                8

  *total                                                                26

=head3 Create a library

Create a library with three subroutines in it and save the library to a file:

  my $library = CreateLibrary          # Library definition
   (subroutines =>                     # Sub routines in libray
     {inc => sub {Inc rax},            # Increment rax
      dup => sub {Shl rax, 1},         # Double rax
      put => sub {PrintOutRaxInDecNL}, # Print rax in decimal
     },
    file => q(library),
   );

Reload the library and call its subroutines from a separate assembly:

  my ($dup, $inc, $put) = $library->load; # Load the library into variables

  Mov rax, 1; &$put;
  &$inc;      &$put;                      # Use the subroutines from the library
  &$dup;      &$put;
  &$dup;      &$put;
  &$inc;      &$put;

  ok Assemble eq => <<END;
1
2
4
8
9
END

=head3 Read and write characters

Read a line of characters from stdin and print them out on stdout:

  my $e = q(readChar);

  ForEver
   {my ($start, $end) = @_;
    ReadChar;
    Cmp rax, 0xa;
    Jle $end;
    PrintOutRaxAsChar;
    PrintOutRaxAsChar;
   };
  PrintOutNL;

  Assemble keep => $e;

  is_deeply qx(echo "ABCDCBA" | ./$e), <<END;
AABBCCDDCCBBAA
END

=head3 Write unicode characters

Generate and write some unicode utf8 characters:

  V( loop => 16)->for(sub
   {my ($index, $start, $next, $end) = @_;
    $index->setReg(rax);
    Add rax, 0xb0;   Shl rax, 16;
    Mov  ax, 0x9d9d; Shl rax, 8;
    Mov  al, 0xf0;
    PrintOutRaxAsText;
   });
  PrintOutNL;

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
𝝰𝝱𝝲𝝳𝝴𝝵𝝶𝝷𝝸𝝹𝝺𝝻𝝼𝝽𝝾𝝿
END

=head3 Read a file

Read this file:

  ReadFile(V(file, Rs($0)), (my $s = V(size)), my $a = V(address));             # Read file
  $a->setReg(rax);                                                              # Address of file in memory
  $s->setReg(rdi);                                                              # Length  of file in memory
  PrintOutMemory;                                                               # Print contents of memory to stdout

  my $r = Assemble(1 => (my $f = temporaryFile));                               # Assemble and execute
  ok fileMd5Sum($f) eq fileMd5Sum($0);                                          # Output contains this file


=head3 Call functions in Libc

Call B<C> functions by naming them as external and including their library:

  my $format = Rs "Hello %s\n";
  my $data   = Rs "World";

  Extern qw(printf exit malloc strcpy); Link 'c';

  CallC 'malloc', length($format)+1;
  Mov r15, rax;
  CallC 'strcpy', r15, $format;
  CallC 'printf', r15, $data;
  CallC 'exit', 0;

  ok Assemble eq => <<END;
Hello World
END

=head3 Print numbers in decimal from assembly code using nasm and perl:

Debug your programs with powerful print statements:

  Mov rax, 0x2a;
  PrintOutRaxInDecNL;

  ok Assemble eq => <<END;
42
END

=head3 Process management

Start a child process and wait for it, printing out the process identifiers of
each process involved:

   Fork;                                     # Fork

   Test rax,rax;
   IfNz                                      # Parent
   Then
    {Mov rbx, rax;
     WaitPid;
     GetPid;                                 # Pid of parent as seen in parent
     Mov rcx,rax;
     PrintOutRegisterInHex rax, rbx, rcx;
    },
   Else                                      # Child
    {Mov r8,rax;
     GetPid;                                 # Child pid as seen in child
     Mov r9,rax;
     GetPPid;                                # Parent pid as seen in child
     Mov r10,rax;
     PrintOutRegisterInHex r8, r9, r10;
    };

   my $r = Assemble;

 #    r8: 0000 0000 0000 0000   #1 Return from fork as seen by child
 #    r9: 0000 0000 0003 0C63   #2 Pid of child
 #   r10: 0000 0000 0003 0C60   #3 Pid of parent from child
 #   rax: 0000 0000 0003 0C63   #4 Return from fork as seen by parent
 #   rbx: 0000 0000 0003 0C63   #5 Wait for child pid result
 #   rcx: 0000 0000 0003 0C60   #6 Pid of parent

=head3 Dynamic area

Arenas are resizeable, relocatable blocks of memory that hold other dynamic
data structures. Arenas can be transferred between processes and relocated as
needed as all addressing is relative to the start of the block of memory
containing each area.

Create two dynamic arenas, add some content to them, write each area to
stdout:

  my $a = CreateArea;

  my $b = CreateArea;
  $a->q('aa');
  $b->q('bb');
  $a->q('AA');
  $b->q('BB');
  $a->q('aa');
  $b->q('bb');

  $a->out;
  $b->out;

  PrintOutNL;

  is_deeply Assemble, <<END;
aaAAaabbBBbb
END

=head4 Dynamic string held in an area

Create a dynamic string within an area and add some content to it:

  my $s = Rb(0..255);
  my $A = CreateArea;
  my $S = $A->CreateString;

  $S->append(V(source, $s), K(size, 256));
  $S->len->outNL;
  $S->clear;

  $S->append(V(source, $s), K(size,  16));
  $S->len->outNL;
  $S->dump;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
size: 0000 0000 0000 0100
size: 0000 0000 0000 0010
string Dump
Offset: 0000 0000 0000 0018   Length: 0000 0000 0000 0010
 zmm31: 0000 0018 0000 0018   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 000F   0E0D 0C0B 0A09 0807   0605 0403 0201 0010

END

=head4 Dynamic array held in an area

Create a dynamic array within an area, push some content on to it then pop it
off again:

  my $N = 15;
  my $A = CreateArea;
  my $a = $A->CreateArray;

  $a->push(V(element, $_)) for 1..$N;

  K(loop, $N)->for(sub
   {my ($start, $end, $next) = @_;
    my $l = $a->size;
    If $l == 0, Then {Jmp $end};
    $a->pop(my $e = V(element));
    $e->outNL;
   });

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
element: 0000 0000 0000 000F
element: 0000 0000 0000 000E
element: 0000 0000 0000 000D
element: 0000 0000 0000 000C
element: 0000 0000 0000 000B
element: 0000 0000 0000 000A
element: 0000 0000 0000 0009
element: 0000 0000 0000 0008
element: 0000 0000 0000 0007
element: 0000 0000 0000 0006
element: 0000 0000 0000 0005
element: 0000 0000 0000 0004
element: 0000 0000 0000 0003
element: 0000 0000 0000 0002
element: 0000 0000 0000 0001
END

=head4 Create a multi way tree in an area using SIMD instructions

Create a multiway tree as in L<Tree::Multi> using B<Avx512> instructions and
iterate through it:

  my $N = 12;
  my $b = CreateArea;                   # Resizable memory block
  my $t = $b->CreateTree;        # Multi way tree in memory block

  K(count, $N)->for(sub                      # Add some entries to the tree
   {my ($index, $start, $next, $end) = @_;
    my $k = $index + 1;
    $t->insert($k,      $k + 0x100);
    $t->insert($k + $N, $k + 0x200);
   });

  $t->by(sub                                  # Iterate through the tree
   {my ($iter, $end) = @_;
    $iter->key ->out('key: ');
    $iter->data->out(' data: ');
    $iter->tree->depth($iter->node, my $D = V(depth));

    $t->find($iter->key);
    $t->found->out(' found: '); $t->data->out(' data: '); $D->outNL(' depth: ');
   });

  $t->find(K(key, 0xffff));  $t->found->outNL('Found: ');  # Find some entries
  $t->find(K(key, 0xd));     $t->found->outNL('Found: ');

  If ($t->found,
  Then
   {$t->data->outNL("Data : ");
   });

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
key: 0000 0000 0000 0001 data: 0000 0000 0000 0101 found: 0000 0000 0000 0001 data: 0000 0000 0000 0101 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0002 data: 0000 0000 0000 0102 found: 0000 0000 0000 0001 data: 0000 0000 0000 0102 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0003 data: 0000 0000 0000 0103 found: 0000 0000 0000 0001 data: 0000 0000 0000 0103 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0004 data: 0000 0000 0000 0104 found: 0000 0000 0000 0001 data: 0000 0000 0000 0104 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0005 data: 0000 0000 0000 0105 found: 0000 0000 0000 0001 data: 0000 0000 0000 0105 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0006 data: 0000 0000 0000 0106 found: 0000 0000 0000 0001 data: 0000 0000 0000 0106 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0007 data: 0000 0000 0000 0107 found: 0000 0000 0000 0001 data: 0000 0000 0000 0107 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0008 data: 0000 0000 0000 0108 found: 0000 0000 0000 0001 data: 0000 0000 0000 0108 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0009 data: 0000 0000 0000 0109 found: 0000 0000 0000 0001 data: 0000 0000 0000 0109 depth: 0000 0000 0000 0002
key: 0000 0000 0000 000A data: 0000 0000 0000 010A found: 0000 0000 0000 0001 data: 0000 0000 0000 010A depth: 0000 0000 0000 0002
key: 0000 0000 0000 000B data: 0000 0000 0000 010B found: 0000 0000 0000 0001 data: 0000 0000 0000 010B depth: 0000 0000 0000 0002
key: 0000 0000 0000 000C data: 0000 0000 0000 010C found: 0000 0000 0000 0001 data: 0000 0000 0000 010C depth: 0000 0000 0000 0002
key: 0000 0000 0000 000D data: 0000 0000 0000 0201 found: 0000 0000 0000 0001 data: 0000 0000 0000 0201 depth: 0000 0000 0000 0001
key: 0000 0000 0000 000E data: 0000 0000 0000 0202 found: 0000 0000 0000 0001 data: 0000 0000 0000 0202 depth: 0000 0000 0000 0002
key: 0000 0000 0000 000F data: 0000 0000 0000 0203 found: 0000 0000 0000 0001 data: 0000 0000 0000 0203 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0010 data: 0000 0000 0000 0204 found: 0000 0000 0000 0001 data: 0000 0000 0000 0204 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0011 data: 0000 0000 0000 0205 found: 0000 0000 0000 0001 data: 0000 0000 0000 0205 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0012 data: 0000 0000 0000 0206 found: 0000 0000 0000 0001 data: 0000 0000 0000 0206 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0013 data: 0000 0000 0000 0207 found: 0000 0000 0000 0001 data: 0000 0000 0000 0207 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0014 data: 0000 0000 0000 0208 found: 0000 0000 0000 0001 data: 0000 0000 0000 0208 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0015 data: 0000 0000 0000 0209 found: 0000 0000 0000 0001 data: 0000 0000 0000 0209 depth: 0000 0000 0000 0002
key: 0000 0000 0000 0016 data: 0000 0000 0000 020A found: 0000 0000 0000 0001 data: 0000 0000 0000 020A depth: 0000 0000 0000 0002
key: 0000 0000 0000 0017 data: 0000 0000 0000 020B found: 0000 0000 0000 0001 data: 0000 0000 0000 020B depth: 0000 0000 0000 0002
key: 0000 0000 0000 0018 data: 0000 0000 0000 020C found: 0000 0000 0000 0001 data: 0000 0000 0000 020C depth: 0000 0000 0000 0002
Found: 0000 0000 0000 0000
Found: 0000 0000 0000 0001
Data : 0000 0000 0000 0201
END

=head4 Quarks held in an area

Quarks replace unique strings with unique numbers and in doing so unite all
that is best and brightest in dynamic trees, arrays, strings and short
strings, all written in X86 assembler, all generated by Perl:

  my $N = 5;
  my $a = CreateArea;                      # Area containing quarks
  my $Q = $a->CreateQuarks;                 # Quarks

  my $s = CreateShortString(0);             # Short string used to load and unload quarks
  my $d = Rb(1..63);

  for my $i(1..$N)                          # Load a set of quarks
   {my $j = $i - 1;
    $s->load(K(address, $d), K(size, 4+$i));
    my $q = $Q->quarkFromShortString($s);
    $q->outNL("New quark    $j: ");         # New quark, new number
   }
  PrintOutNL;

  for my $i(reverse 1..$N)                  # Reload a set of quarks
   {my $j = $i - 1;
    $s->load(K(address, $d), K(size, 4+$i));
    my $q = $Q->quarkFromShortString($s);
    $q->outNL("Old quark    $j: ");         # Old quark, old number
   }
  PrintOutNL;

  for my $i(1..$N)                          # Dump quarks
   {my $j = $i - 1;
     $s->clear;
    $Q->shortStringFromQuark(K(quark, $j), $s);
    PrintOutString "Quark string $j: ";
    PrintOutRegisterInHex xmm0;
   }

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
  New quark    0: 0000 0000 0000 0000
  New quark    1: 0000 0000 0000 0001
  New quark    2: 0000 0000 0000 0002
  New quark    3: 0000 0000 0000 0003
  New quark    4: 0000 0000 0000 0004

  Old quark    4: 0000 0000 0000 0004
  Old quark    3: 0000 0000 0000 0003
  Old quark    2: 0000 0000 0000 0002
  Old quark    1: 0000 0000 0000 0001
  Old quark    0: 0000 0000 0000 0000

  Quark string 0:   xmm0: 0000 0000 0000 0000   0000 0504 0302 0105
  Quark string 1:   xmm0: 0000 0000 0000 0000   0006 0504 0302 0106
  Quark string 2:   xmm0: 0000 0000 0000 0000   0706 0504 0302 0107
  Quark string 3:   xmm0: 0000 0000 0000 0008   0706 0504 0302 0108
  Quark string 4:   xmm0: 0000 0000 0000 0908   0706 0504 0302 0109
  END

=head3 Recursion with stack and parameter tracing

Call a subroutine recursively and get a trace back showing the procedure calls
and parameters passed to each call. Parameters are passed by reference not
value.

  my $d = V depth => 3;                                                         # Create a variable on the stack

  my $s = Subroutine33
   {my ($p, $s) = @_;                                                           # Parameters, subroutine descriptor
    PrintOutTraceBack;

    my $d = $$p{depth}->copy($$p{depth} - 1);                                   # Modify the variable referenced by the parameter

    If ($d > 0,
    Then
     {$s->call($d);                                                             # Recurse
     });

    PrintOutTraceBack;
   } [qw(depth)], name => 'ref';

  $s->call($d);                                                                 # Call the subroutine

  ok Assemble(debug => 0, eq => <<END, avx512=>0);

  Subroutine trace back, depth:  1
  0000 0000 0000 0003    ref


  Subroutine trace back, depth:  2
  0000 0000 0000 0002    ref
  0000 0000 0000 0002    ref


  Subroutine trace back, depth:  3
  0000 0000 0000 0001    ref
  0000 0000 0000 0001    ref
  0000 0000 0000 0001    ref


  Subroutine trace back, depth:  3
  0000 0000 0000 0000    ref
  0000 0000 0000 0000    ref
  0000 0000 0000 0000    ref


  Subroutine trace back, depth:  2
  0000 0000 0000 0000    ref
  0000 0000 0000 0000    ref


  Subroutine trace back, depth:  1
  0000 0000 0000 0000    ref

  END

=head2 Installation

The Intel Software Development Emulator will be required if you do not have a
computer with the avx512 instruction set and wish to execute code containing
these instructions. For details see:

L<https://software.intel.com/content/dam/develop/external/us/en/documents/downloads/sde-external-8.63.0-2021-01-18-lin.tar.bz2>


The Networkwide Assembler is required to assemble the code produced  For full
details see:

L<https://github.com/philiprbrenan/Nasm::X86/blob/main/.github/workflows/main.yml>

=head2 Execution Options

The L</Assemble(%)> function takes the keywords described below to
control assembly and execution of the assembled code:

L</Assemble(%)> runs the generated program after a successful assembly
unless the B<keep> option is specified. The output on B<stdout> is captured in
file B<zzzOut.txt> and that on B<stderr> is captured in file B<zzzErr.txt>.

The amount of output displayed is controlled by the B<debug> keyword.

The B<eq> keyword can be used to test that the output by the run.

The output produced by the program execution is returned as the result of the
L</Assemble(%)> function.

=head3 Keep

To produce a named executable without running it, specify:

 keep=>"executable file name"

=head3 Library

To produce a shared library file:

 library=>"library.so"

=head3 Emulator

To run the executable produced by L</Assemble(%)> without the Intel
emulator, which is used by default if it is present, specify:

 avx512=>0

=head3 eq

The B<eq> keyword supplies the expected output from the execution of the
assembled program.  If the expected output is not obtained on B<stdout> then we
confess and stop further testing. Output on B<stderr> is ignored for test
purposes.

The point at which the wanted output diverges from the output actually got is
displayed to assist debugging as in:

  Comparing wanted with got failed at line: 4, character: 22
  Start:
      k7: 0000 0000 0000 0001
      k6: 0000 0000 0000 0003
      k5: 0000 0000 0000 0007
      k4: 0000 0000 000
  Want ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
  1 0002
      k3: 0000 0000 0000 0006
      k2: 0000 0000 0000 000E
      k1: 0000 0000
  Got  ________________________________________________________________________________
  0 0002
      k3: 0000 0000 0000 0006
      k2: 0000 0000 0000 000E
      k1: 0000 0000


=head3 Debug

The debug keyword controls how much output is printed after each assemble and
run.

  debug => 0

produces no output unless the B<eq> keyword was specified and the actual output
fails to match the expected output. If such a test fails we L<Carp::confess>.

  debug => 1

shows all the output produces and conducts the test specified by the B<eq> is
present. If the test fails we L<Carp::confess>.

  debug => 2

shows all the output produces and conducts the test specified by the B<eq> is
present. If the test fails we continue rather than calling L<Carp::confess>.

=head1 Description

Generate X86 assembler code using Perl as a macro pre-processor.

=head1 Copyright

Copyright (c) 2016-2021 Philip R Brenan.

This module is free software. It may be used, redistributed and/or modified
under the same terms as Perl itself.

=cut

# Tests and documentation

sub test
 {my $p = __PACKAGE__;
  binmode($_, ":utf8") for *STDOUT, *STDERR;
  return if eval "eof(${p}::DATA)";
  my $s = eval "join('', <${p}::DATA>)";
  $@ and die $@;
  eval $s;
  $@ and die $@;
  1
 }

test unless caller;

1;
# podDocumentation
#__DATA__
use Time::HiRes qw(time);
use Test::Most;

bail_on_fail unless onGitHub;

my $localTest = ((caller(1))[0]//'Nasm::X86') eq "Nasm::X86";                   # Local testing mode
my $homeTest  = -e q(/home/phil/);                                              # Testing on a local machine

Test::More->builder->output("/dev/null") if $localTest;                         # Reduce number of confirmation messages during testing

if ($^O =~ m(bsd|linux|cygwin)i)                                                # Supported systems
 {if (confirmHasCommandLineCommand(q(nasm)) and LocateIntelEmulator){}          # Network assembler and Intel Software Development emulator
  else
   {plan skip_all => qq(Nasm or Intel 64 emulator not available);
   }
 }
else
 {plan skip_all => qq(Not supported on: $^O);
 }

my $start = time;                                                               # Tests

eval {goto latest} if !caller(0);# and !onGitHub;                               # Go to latest test if specified

#latest:
if (1) {                                                                        #TPrintOutStringNL #TPrintErrStringNL #TAssemble
  PrintOutStringNL "Hello World";
  PrintOutStringNL "Hello\nWorld";
  PrintErrStringNL "Hello World";

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
Hello World
Hello
World
END
 }

#latest:
if (1) {                                                                        #TPrintOutRaxInHexNL
  my $s = Rb(0..255);

  Vmovdqu64 xmm1, "[$s]";
  PrintOutRegisterInHex xmm1;
  PrintOutRegisterInHex xmm1;

  Vmovdqu64 ymm1, "[$s]";
  PrintOutRegisterInHex ymm1;
  PrintOutRegisterInHex ymm1;

  Vmovdqu64 zmm1, "[$s]";
  PrintOutRegisterInHex zmm1;
  PrintOutRegisterInHex zmm1;

  ok Assemble avx512=>1, debug=>0, eq =><<END;
  xmm1: .F.E .D.C .B.A .9.8  .7.6 .5.4 .3.2 .1..
  xmm1: .F.E .D.C .B.A .9.8  .7.6 .5.4 .3.2 .1..
  ymm1: 1F1E 1D1C 1B1A 1918  1716 1514 1312 1110 - .F.E .D.C .B.A .9.8  .7.6 .5.4 .3.2 .1..
  ymm1: 1F1E 1D1C 1B1A 1918  1716 1514 1312 1110 - .F.E .D.C .B.A .9.8  .7.6 .5.4 .3.2 .1..
  zmm1: 3F3E 3D3C 3B3A 3938  3736 3534 3332 3130 - 2F2E 2D2C 2B2A 2928  2726 2524 2322 2120 + 1F1E 1D1C 1B1A 1918  1716 1514 1312 1110 - .F.E .D.C .B.A .9.8  .7.6 .5.4 .3.2 .1..
  zmm1: 3F3E 3D3C 3B3A 3938  3736 3534 3332 3130 - 2F2E 2D2C 2B2A 2928  2726 2524 2322 2120 + 1F1E 1D1C 1B1A 1918  1716 1514 1312 1110 - .F.E .D.C .B.A .9.8  .7.6 .5.4 .3.2 .1..
END
 }

#latest:;
if (1) {                                                                        #TMov #TComment #TRs #TPrintOutMemory #TExit
  Comment "Print a string from memory";
  my $s = "Hello World";
  Mov rax, Rs($s);
  Mov rdi, length $s;
  PrintOutMemory;
  Exit(0);

  ok Assemble(avx512=>0) =~ m(Hello World);
 }

#latest:;
if (1) {                                                                        #TPrintOutMemoryNL #TStringLength
  my $s = Rs("Hello World\n\nHello Skye");
  my $l = StringLength(my $t = V string => $s);
  $t->setReg(rax);
  $l->setReg(rdi);
  PrintOutMemoryNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
Hello World

Hello Skye
END
 }

#latest:;
if (1) {                                                                        #TPrintOutRaxInHex #TPrintOutNL #TPrintOutString
  my $q = Rs('abababab');
  Mov(rax, "[$q]");
  PrintOutString "rax: ";
  PrintOutRaxInHex;
  PrintOutNL;
  Xor rax, rax;
  PrintOutString "rax: ";
  PrintOutRaxInHex;
  PrintOutNL;

  ok Assemble(avx512=>0, eq=><<END)
rax: 6261 6261 6261 6261
rax: .... .... .... ....
END
 }

#latest:;
if (1) {                                                                        #TPrintOutRegistersInHex #TRs
  my $q = Rs('abababab');
  Mov r10, 0x10;
  Mov r11, 0x11;
  Mov r12, 0x12;
  Mov r13, 0x13;
  Mov r14, 0x14;
  Mov r15, 0x15;
  Mov  r8, 0x08;
  Mov  r9, 0x09;
  Mov rax, 1;
  Mov rbx, 2;
  Mov rcx, 3;
  Mov rdi, 4;
  Mov rdx, 5;
  Mov rsi, 6;
  PrintOutRegistersInHex;

  my $r = Assemble(avx512=>0, eq=><<END, debug=>0);
rfl: .... .... .... .2.2
r10: .... .... .... ..10
r11: .... .... .... .2.2
r12: .... .... .... ..12
r13: .... .... .... ..13
r14: .... .... .... ..14
r15: .... .... .... ..15
 r8: .... .... .... ...8
 r9: .... .... .... ...9
rax: .... .... .... ...1
rbx: .... .... .... ...2
rcx: .... .... ..40 18E1
rdi: .... .... .... ...4
rdx: .... .... .... ...5
rsi: .... .... .... ...6
END
 }

#latest:;
if (1) {                                                                        #TDs TRs
  my $q = Rs('a'..'z');
  Mov rax, Ds('0'x64);                                                          # Output area
  Vmovdqu32(xmm0, "[$q]");                                                      # Load
  Vprolq   (xmm0,   xmm0, 32);                                                  # Rotate double words in quad words
  Vmovdqu32("[rax]", xmm0);                                                     # Save
  Mov rdi, 16;
  PrintOutMemoryNL;

  ok Assemble(avx512=>1, eq=><<END)
efghabcdmnopijkl
END
 }

#latest:;
if (1) {
  my $q = Rs(('a'..'p')x2);
  Mov rax, Ds('0'x64);
  Vmovdqu32(ymm0, "[$q]");
  Vprolq   (ymm0,   ymm0, 32);
  Vmovdqu32("[rax]", ymm0);
  Mov rdi, 32;
  PrintOutMemoryNL;

  ok Assemble(avx512=>1, eq=><<END)
efghabcdmnopijklefghabcdmnopijkl
END
 }

#latest:;
if (1) {
  my $q = Rs my $s = join '', ('a'..'p')x4;                                     # Sample string
  Mov rax, Ds('0'x128);

  Vmovdqu64 zmm0, "[$q]";                                                       # Load zmm0 with sample string
  Vprolq    zmm1, zmm0, 32;                                                     # Rotate left 32 bits in lanes
  Vmovdqu64 "[rax]", zmm1;                                                      # Save results

  Mov rdi, length $s;                                                           # Print results
  PrintOutMemoryNL;

  is_deeply "$s\n", <<END;                                                      # Initial string
abcdefghijklmnopabcdefghijklmnopabcdefghijklmnopabcdefghijklmnop
END

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
efghabcdmnopijklefghabcdmnopijklefghabcdmnopijklefghabcdmnopijkl
END
 }

#latest:
if (1) {
  my $q = Rb(0..255);
  Vmovdqu8 xmm0, "[$q]";
  Vmovdqu8 xmm1, "[$q+16]";
  Vmovdqu8 xmm2, "[$q+32]";
  Vmovdqu8 xmm3, "[$q+48]";
  PrintOutRegisterInHex xmm0, xmm1,  xmm2, xmm3;

  Vmovdqu8 ymm0, "[$q]";
  Vmovdqu8 ymm1, "[$q+16]";
  Vmovdqu8 ymm2, "[$q+32]";
  Vmovdqu8 ymm3, "[$q+48]";
  PrintOutRegisterInHex ymm0, ymm1, ymm2, ymm3;

  Vmovdqu8 zmm0, "[$q]";
  Vmovdqu8 zmm1, "[$q+16]";
  Vmovdqu8 zmm2, "[$q+32]";
  Vmovdqu8 zmm3, "[$q+48]";
  PrintOutRegisterInHex zmm0, zmm1, zmm2, zmm3;

  ok Assemble(avx512=>1, eq=><<END);
  xmm0: .F.E .D.C .B.A .9.8  .7.6 .5.4 .3.2 .1..
  xmm1: 1F1E 1D1C 1B1A 1918  1716 1514 1312 1110
  xmm2: 2F2E 2D2C 2B2A 2928  2726 2524 2322 2120
  xmm3: 3F3E 3D3C 3B3A 3938  3736 3534 3332 3130
  ymm0: 1F1E 1D1C 1B1A 1918  1716 1514 1312 1110 - .F.E .D.C .B.A .9.8  .7.6 .5.4 .3.2 .1..
  ymm1: 2F2E 2D2C 2B2A 2928  2726 2524 2322 2120 - 1F1E 1D1C 1B1A 1918  1716 1514 1312 1110
  ymm2: 3F3E 3D3C 3B3A 3938  3736 3534 3332 3130 - 2F2E 2D2C 2B2A 2928  2726 2524 2322 2120
  ymm3: 4F4E 4D4C 4B4A 4948  4746 4544 4342 4140 - 3F3E 3D3C 3B3A 3938  3736 3534 3332 3130
  zmm0: 3F3E 3D3C 3B3A 3938  3736 3534 3332 3130 - 2F2E 2D2C 2B2A 2928  2726 2524 2322 2120 + 1F1E 1D1C 1B1A 1918  1716 1514 1312 1110 - .F.E .D.C .B.A .9.8  .7.6 .5.4 .3.2 .1..
  zmm1: 4F4E 4D4C 4B4A 4948  4746 4544 4342 4140 - 3F3E 3D3C 3B3A 3938  3736 3534 3332 3130 + 2F2E 2D2C 2B2A 2928  2726 2524 2322 2120 - 1F1E 1D1C 1B1A 1918  1716 1514 1312 1110
  zmm2: 5F5E 5D5C 5B5A 5958  5756 5554 5352 5150 - 4F4E 4D4C 4B4A 4948  4746 4544 4342 4140 + 3F3E 3D3C 3B3A 3938  3736 3534 3332 3130 - 2F2E 2D2C 2B2A 2928  2726 2524 2322 2120
  zmm3: 6F6E 6D6C 6B6A 6968  6766 6564 6362 6160 - 5F5E 5D5C 5B5A 5958  5756 5554 5352 5150 + 4F4E 4D4C 4B4A 4948  4746 4544 4342 4140 - 3F3E 3D3C 3B3A 3938  3736 3534 3332 3130
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Variable::copyZF #TNasm::X86::Variable::copyZFInverted
  Mov r15, 1;
  my $z = V(zf => undef);
  Cmp r15, 1; $z->copyZF;         $z->outNL;
  Cmp r15, 2; $z->copyZF;         $z->outNL;
  Cmp r15, 1; $z->copyZFInverted; $z->outNL;
  Cmp r15, 2; $z->copyZFInverted; $z->outNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
zf: .... .... .... ...1
zf: .... .... .... ....
zf: .... .... .... ....
zf: .... .... .... ...1
END
 }

#latest:
if (1) {                                                                        #TPrintOutRightInHexNL
  my $N = K number => 0x12345678;

  for my $i(reverse 1..16)
   {PrintOutRightInHexNL($N, K width => $i);
   }
  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>1);
        12345678
       12345678
      12345678
     12345678
    12345678
   12345678
  12345678
 12345678
12345678
2345678
345678
45678
5678
678
78
8
END
 }

#latest:
if (1) {                                                                        #TPrintOutRightInBinNL
  K(count => 64)->for(sub
   {my ($index, $start, $next, $end) = @_;
    PrintOutRightInBinNL K(number => 0x99), K(max => 64) - $index;
   });
  ok Assemble(debug => 0, eq => <<END, avx512=>0);
                                                        10011001
                                                       10011001
                                                      10011001
                                                     10011001
                                                    10011001
                                                   10011001
                                                  10011001
                                                 10011001
                                                10011001
                                               10011001
                                              10011001
                                             10011001
                                            10011001
                                           10011001
                                          10011001
                                         10011001
                                        10011001
                                       10011001
                                      10011001
                                     10011001
                                    10011001
                                   10011001
                                  10011001
                                 10011001
                                10011001
                               10011001
                              10011001
                             10011001
                            10011001
                           10011001
                          10011001
                         10011001
                        10011001
                       10011001
                      10011001
                     10011001
                    10011001
                   10011001
                  10011001
                 10011001
                10011001
               10011001
              10011001
             10011001
            10011001
           10011001
          10011001
         10011001
        10011001
       10011001
      10011001
     10011001
    10011001
   10011001
  10011001
 10011001
10011001
0011001
011001
11001
1001
001
01
1
END
 }

#latest:
if (1) {                                                                        #TAllocateMemory #TFreeMemory
  my $N = K size => 2048;
  my $q = Rs('a'..'p');
  my $address = AllocateMemory $N;

  Vmovdqu8 xmm0, "[$q]";
  $address->setReg(rax);
  Vmovdqu8 "[rax]", xmm0;
  Mov rdi, 16;
  PrintOutMemory;
  PrintOutNL;

  FreeMemory $address, $N;

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
abcdefghijklmnop
END
 }

#latest:
if (1) {                                                                        #addressAndLengthOfConstantStringAsVariables
  my ($t, $l) = addressAndLengthOfConstantStringAsVariables("Hello World");
  $t->printOutMemoryNL($l);

  ok Assemble eq => <<END, avx512=>1;
Hello World
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Variable::allocateMemory #TNasm::X86::Variable::freeMemory
  my $N = K size => 2048;
  my $q = Rs('a'..'p');
  my $address = $N->allocateMemory;

  Vmovdqu8 xmm0, "[$q]";
  $address->setReg(rax);
  Vmovdqu8 "[rax]", xmm0;
  Mov rdi, 16;
  PrintOutMemory;
  PrintOutNL;

  $address->freeMemory($N);

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
abcdefghijklmnop
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Variable::outNL
  my $a = V a => 0x1111;
  $a->outNL('');
  $a->outRightInBinNL(K width => 16);
  $a->outRightInDecNL(K width => 16);
  $a->outRightInHexNL(K width => 16);
  ok Assemble(debug => 0, eq => <<END, avx512=>1);
.... .... .... 1111
   1000100010001
            4369
            1111
END
 }

#latest:
if (1) {                                                                        #TReadTimeStampCounter
  for(1..10)
   {ReadTimeStampCounter;
    PrintOutRegisterInHex rax;
   }

  my @s = split /\n/, Assemble(avx512=>0);
  my @S = sort @s;
  is_deeply \@s, \@S;
 }

#latest:
if (1) {                                                                        #TIf
  my $c = K(one => 1);
  If ($c == 0,
  Then
   {PrintOutStringNL "1 == 0";
   },
  Else
   {PrintOutStringNL "1 != 0";
   });

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
1 != 0
END
 }

if (1) {                                                                        #TIfNz
  Mov rax, 0;
  Test rax,rax;
  IfNz
  Then
   {PrintOutRegisterInHex rax;
   },
  Else
   {PrintOutRegisterInHex rbx;
   };
  Mov rax, 1;
  Test rax,rax;
  IfNz
  Then
   {PrintOutRegisterInHex rcx;
   },
  Else
   {PrintOutRegisterInHex rdx;
   };

  ok Assemble(avx512=>0) =~ m(rbx.*rcx)s;
 }

if (1) {                                                                        #TFork #TGetPid #TGetPPid #TWaitPid
  Fork;                                                                         # Fork

  Test rax,rax;
  IfNz                                                                          # Parent
  Then
   {Mov rbx, rax;
    WaitPid;
    GetPid;                                                                     # Pid of parent as seen in parent
    Mov rcx,rax;
    PrintOutRegisterInHex rax, rbx, rcx;
   },
  Else                                                                          # Child
   {Mov r8,rax;
    GetPid;                                                                     # Child pid as seen in child
    Mov r9,rax;
    GetPPid;                                                                    # Parent pid as seen in child
    Mov r10,rax;
    PrintOutRegisterInHex r8, r9, r10;
   };

  my $r = Assemble(avx512=>0);

#    r8: 0000 0000 0000 0000   #1 Return from fork as seen by child
#    r9: 0000 0000 0003 0C63   #2 Pid of child
#   r10: 0000 0000 0003 0C60   #3 Pid of parent from child
#   rax: 0000 0000 0003 0C63   #4 Return from fork as seen by parent
#   rbx: 0000 0000 0003 0C63   #5 Wait for child pid result
#   rcx: 0000 0000 0003 0C60   #6 Pid of parent

  if ($r =~ m(r8:( 0000){4}.*r9:(.*)\s{5,}r10:(.*)\s{5,}rax:(.*)\s{5,}rbx:(.*)\s{5,}rcx:(.*)\s{2,})s)
   {ok $2 eq $4;
    ok $2 eq $5;
    ok $3 eq $6;
    ok $2 gt $6;
   }
 }

if ($homeTest) {                                                                #TGetUid
  GetUid;                                                                       # Userid
  PrintOutRegisterInHex rax;

  my $r = Assemble(avx512=>0);
  ok $r =~ m(3E8);
 }

if (1) {                                                                        #TStatSize
  Mov rax, Rs($0);                                                              # File to stat
  StatSize;                                                                     # Stat the file
  PrintOutRegisterInHex rax;

  my $r = Assemble(avx512=>0) =~ s( ) ()gsr;
  if ($r =~ m(rax:([0-9a-f]{16}))is)                                            # Compare file size obtained with that from fileSize()
   {is_deeply $1, sprintf("%016X", fileSize($0));
   }
 }

if (1) {                                                                        #TOpenRead #TCloseFile #TOpenWrite
  Mov rax, Rs($0);                                                              # File to read
  OpenRead;                                                                     # Open file
  PrintOutRegisterInHex rax;
  CloseFile;                                                                    # Close file
  PrintOutRegisterInHex rax;

  Mov rax, Rs(my $f = "zzzTemporaryFile.txt");                                  # File to write
  OpenWrite;                                                                    # Open file
  CloseFile;                                                                    # Close file

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
   rax: .... .... .... ...3
   rax: .... .... .... ....
END
  ok -e $f;                                                                     # Created file
  unlink $f;
 }

if (1) {                                                                        #TFor
  For
   {my ($start, $end, $next) = @_;
    Cmp rax, 3;
    Jge $end;
    PrintOutRegisterInHex rax;
   } rax, 16, 1;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
   rax: .... .... .... ....
   rax: .... .... .... ...1
   rax: .... .... .... ...2
END
 }

if (1) {                                                                        #TAndBlock #TFail
  Mov rax, 1; Mov rdx, 2;
  AndBlock
   {my ($fail, $end, $start) = @_;
    Cmp rax, 1;
    Jne $fail;
    Cmp rdx, 2;
    Jne $fail;
    PrintOutStringNL "Pass";
   }
  Fail
   {my ($end, $fail, $start) = @_;
    PrintOutStringNL "Fail";
   };

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
Pass
END
 }

if (1) {                                                                        #TOrBlock #TPass
  Mov rax, 1;
  OrBlock
   {my ($pass, $end, $start) = @_;
    Cmp rax, 1;
    Je  $pass;
    Cmp rax, 2;
    Je  $pass;
    PrintOutStringNL "Fail";
   }
  Pass
   {my ($end, $pass, $start) = @_;
    PrintOutStringNL "Pass";
   };

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
Pass
END
 }

if (1) {                                                                        #TPrintOutRaxInReverseInHex #TPrintOutMemoryInHex
  Mov rax, 0x07654321;
  Shl rax, 32;
  Or  rax, 0x07654321;
  PushR rax;

  PrintOutRaxInHex;
  PrintOutNL;
  PrintOutRaxInReverseInHex;
  PrintOutNL;

  Mov rax, rsp;
  Mov rdi, 8;
  PrintOutMemoryInHex;
  PrintOutNL;
  PopR rax;

  Mov rax, 4096;
  PushR rax;
  Mov rax, rsp;
  Mov rdi, 8;
  PrintOutMemoryInHex;
  PrintOutNL;
  PopR rax;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
.765 4321 .765 4321
2143 65.7 2143 65.7
2143 65.7 2143 65.7
..10 .... .... ....
END
 }

if (1) {                                                                        #TPushR #TPopR
  Mov rax, 0x11111111;
  Mov rbx, 0x22222222;
  PushR my @save = (rax, rbx);
  Mov rax, 0x33333333;
  PopR;
  PrintOutRegisterInHex rax;
  PrintOutRegisterInHex rbx;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
   rax: .... .... 1111 1111
   rbx: .... .... 2222 2222
END
 }

#latest:;
if (1) {                                                                        #TClearMemory
  K(loop => 8+1)->for(sub
   {my ($index, $start, $next, $end) = @_;
    $index->setReg(15);
    Push r15;
   });

  Mov rax, rsp;
  Mov rdi, 8*9;
  PrintOutMemory_InHexNL;
  ClearMemory(V(address => rax), K(size => 8*9));
  PrintOutMemory_InHexNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
.8__ ____ ____ ____  .7__ ____ ____ ____  .6__ ____ ____ ____  .5__ ____ ____ ____  .4__ ____ ____ ____  .3__ ____ ____ ____  .2__ ____ ____ ____  .1__ ____ ____ ____  ____ ____ ____ ____
____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
END
 }

#latest:;
if (1) {                                                                        #TAllocateMemory #TFreeMemory #TClearMemory
  my $N = K size => 4096;                                                       # Size of the initial allocation which should be one or more pages

  my $A = AllocateMemory $N;

  ClearMemory($A, $N);

  $A->setReg(rax);
  Mov rdi, 128;
  PrintOutMemory_InHexNL;

  FreeMemory $A, $N;

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
END
 }

#latest:;
if (1) {
  Mov rax, 0x44332211;
  PrintOutRegisterInHex rax;

  my $s = Subroutine
   {PrintOutRegisterInHex rax;
    Inc rax;
    PrintOutRegisterInHex rax;
   } name => "printIncPrint";

  $s->call;

  PrintOutRegisterInHex rax;

  my $r = Assemble(avx512=>0, eq=><<END);
   rax: .... .... 4433 2211
   rax: .... .... 4433 2211
   rax: .... .... 4433 2212
   rax: .... .... 4433 2212
END
 }

#latest:;
if (!$homeTest) {                                                               #TReadFile #TPrintMemory
  my $file = V(file => Rs $0);
  my ($address, $size) = ReadFile $file;                                        # Read file into memory
  $address->setReg(rax);                                                        # Address of file in memory
  $size   ->setReg(rdi);                                                        # Length  of file in memory
  PrintOutMemory;                                                               # Print contents of memory to stdout

  my $r = Assemble(avx512=>0);                                                  # Assemble and execute
  ok stringMd5Sum($r) eq fileMd5Sum($0);                                        # Output contains this file
 }

#latest:;
if (1) {                                                                        #TCreateArea #TArea::clear #TArea::outNL #TArea::copy #TArea::nl
  my $a = CreateArea;
  $a->q('aa');
  $a->outNL;
  ok Assemble(debug => 0, eq => <<END, avx512=>0);
aa
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Area::print
  my $a = CreateArea;
  my $z = $a->allocZmmBlock;
  LoadZmm 31, (ord('a')) x 64;
  $a->putZmmBlock($z, 31);
  $a->printOut($z, K length => 3);

  ok Assemble eq => <<END, avx512=>1;
aaa
END
 }

#latest:
if (1) {                                                                        #TArea::dump
  my $a = CreateArea;
  my $b = CreateArea;
  $a->q("aaaa");
  $a->dump("aaaaa");
  $b->q("bbbb");
  $b->dump("bbbb");

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
aaaaa
Area     Size:     4096    Used:       68
.... .... .... .... | __10 ____ ____ ____  44__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | 6161 6161 ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
bbbb
Area     Size:     4096    Used:       68
.... .... .... .... | __10 ____ ____ ____  44__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | 6262 6262 ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
END
 }

if (1) {                                                                        #TCreateArea #TArea::clear #TArea::out #TArea::copy #TArea::nl
  my $a = CreateArea;
  my $b = CreateArea;
  $a->q('aa');
  $b->q('bb');
  $a->out;
  PrintOutNL;
  $b->out;
  PrintOutNL;
  ok Assemble(debug => 0, eq => <<END, avx512=>0);
aa
bb
END
 }

if (1) {                                                                        #TCreateArea #TArea::clear #TArea::out #TArea::copy #TArea::nl
  my $a = CreateArea;
  my $b = CreateArea;
  $a->q('aa');
  $a->q('AA');
  $a->out;
  PrintOutNL;
  ok Assemble(debug => 0, eq => <<END, avx512=>0);
aaAA
END
 }

if (1) {                                                                        #TCreateArea #TArea::clear #TArea::out #TArea::copy #TArea::nl
  my $a = CreateArea;
  my $b = CreateArea;
  $a->q('aa');
  $b->q('bb');
  $a->q('AA');
  $b->q('BB');
  $a->q('aa');
  $b->q('bb');
  $a->out;
  $b->out;
  PrintOutNL;
  ok Assemble(debug => 0, eq => <<END, avx512=>0);
aaAAaabbBBbb
END
 }

#latest:
if (1) {                                                                        #TCreateArea #TArea::length  #TArea::clear #TArea::out #TArea::copy #TArea::nl
  my $a = CreateArea;
  $a->q('ab');
  my $b = CreateArea;
  $b->append($a);
  $b->append($a);
  $a->append($b);
  $b->append($a);
  $a->append($b);
  $b->append($a);
  $b->append($a);
  $b->append($a);
  $b->append($a);


  $a->out;   PrintOutNL;
  $b->out;   PrintOutNL;
  my $sa = $a->used; $sa->outNL;
  my $sb = $b->used; $sb->outNL;
  $a->clear;
  my $sA = $a->used; $sA->outNL;
  my $sB = $b->used; $sB->outNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
abababababababab
ababababababababababababababababababababababababababababababababababababab
area used up: .... .... .... ..10
area used up: .... .... .... ..4A
area used up: .... .... .... ....
area used up: .... .... .... ..4A
END
 }


if (1) {                                                                        # Mask register instructions #TClearRegisters
  Mov rax,1;
  Kmovq k0,  rax;
  Kaddb k0,  k0, k0;
  Kaddb k0,  k0, k0;
  Kaddb k0,  k0, k0;
  Kmovq rax, k0;
  PushR k0;
  ClearRegisters k0;
  Kmovq k1, k0;
  PopR  k0;
  PrintOutRegisterInHex k0;
  PrintOutRegisterInHex k1;

  ok Assemble(avx512 => 1, eq => <<END)
    k0: .... .... .... ...8
    k1: .... .... .... ....
END
 }

if (1) {                                                                        # Count leading zeros
  Mov   rax, 8;                                                                 # Append a constant to the area
  Lzcnt rax, rax;                                                               # New line
  PrintOutRegisterInHex rax;

  Mov   rax, 8;                                                                 # Append a constant to the area
  Tzcnt rax, rax;                                                               # New line
  PrintOutRegisterInHex rax;

  ok Assemble(avx512 => 1, eq => <<END)
   rax: .... .... .... ..3C
   rax: .... .... .... ...3
END
 }

#latest:;
if (1) {                                                                        #TArea::nl
  my $s = CreateArea;
  $s->q("A");
  $s->nl;
  $s->q("B");
  $s->out;
  PrintOutNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
A
B
END
 }

#latest:;
if (!$homeTest) {                                                               # Print this file - slow -  #TArea::read #TArea::z #TArea::q
  my $s = CreateArea;                                                           # Create a string
  $s->read(K file => Rs($0));
  $s->out;

  my $r = Assemble(emulator => 0);
  is_deeply stringMd5Sum($r), fileMd5Sum($0);                                   # Output contains this file
 }

#latest:;
if (1) {                                                                        # Print rdi in hex into an area #TGetPidInHex
  GetPidInHex;
  Mov r15, rax;

  GetPidInHex;
  Cmp r15, rax;
  IfEq Then {PrintOutStringNL "Same"}, Else {PrintOutStringNL "Diff"};

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
Same
END
 }

#latest:;
if ($homeTest) {                                                                # Execute the content of an area #TexecuteFileViaBash #TArea::write #TArea::out #TunlinkFile #TArea::ql
  my $s = CreateArea;                                                           # Create a string
  $s->ql(<<END);                                                                # Write code to execute
#!/usr/bin/bash
whoami
END
  $s->write         (my $f = V('file', Rs("zzz.sh")));                          # Write code to a file
  executeFileViaBash($f);                                                       # Execute the file
  unlinkFile        ($f);                                                       # Delete the file

  my $u = qx(whoami); chomp($u);
  ok Assemble(debug => 0, eq => <<END, avx512=>0);
phil
END
 }

#latest:;
if (!hasAvx512) {                                                               # Make an area readonly - but we need the emulator to test this
  my $s = CreateArea;                                                           # Create an area
  $s->q("Hello");                                                               # Write code to area
  $s->makeReadOnly;                                                             # Make area read only
  $s->q(" World");                                                              # Try to write to area

  ok Assemble(debug=>2, emulator=>1) =~ m(SDE ERROR: DEREFERENCING BAD MEMORY POINTER.*mov byte ptr .rax.rdx.1., r8b);
 }

#latest:;
if (1) {                                                                        # Make a read only area writable  #TArea::makeReadOnly #TArea::makeWriteable
  my $s = CreateArea;                                                           # Create an area
  $s->q("Hello");                                                               # Write data to area
  $s->makeReadOnly;                                                             # Make area read only - tested above
  $s->makeWriteable;                                                            # Make area writable again
  $s->q(" World");                                                              # Try to write to area
  $s->outNL;

  ok Assemble(avx512=>0, eq => <<END);
Hello World
END
 }

#latest:;
if (1) {                                                                        # Allocate some space in area #TArea::allocate
  my $s = CreateArea;                                                           # Create an area
  my $o1 = $s->allocate(K size => 0x20);                                        # Allocate space wanted
  my $o2 = $s->allocate(K size => 0x30);
  my $o3 = $s->allocate(K size => 0x10);
  $o1->outNL;
  $o2->outNL;
  $o3->outNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
offset: .... .... .... ..40
offset: .... .... .... ..60
offset: .... .... .... ..90
END
 }

#latest:;
if (1) {                                                                        #TNasm::X86::Area::checkYggdrasilCreated #TNasm::X86::Area::establishYggdrasil
  my $A = CreateArea;
  my $t = $A->checkYggdrasilCreated;
     $t->found->outNL;
  my $y = $A->establishYggdrasil;
  my $T = $A->checkYggdrasilCreated;
     $T->found->outNL;
  ok Assemble(debug => 0, eq => <<END, avx512=>1);
found: .... .... .... ....
found: .... .... .... ...1
END
 }

# It is one of the happiest characteristics of this glorious country that official utterances are invariably regarded as unanswerable

#latest:;
if (1) {                                                                        #TPrintOutZF #TSetZF #TClearZF #TIfC #TIfNc #TIfZ #IfNz
  SetZF;
  PrintOutZF;
  ClearZF;
  PrintOutZF;
  SetZF;
  PrintOutZF;
  SetZF;
  PrintOutZF;
  ClearZF;
  PrintOutZF;

  SetZF;
  IfZ  Then {PrintOutStringNL "Zero"},     Else {PrintOutStringNL "NOT zero"};
  ClearZF;
  IfNz Then {PrintOutStringNL "NOT zero"}, Else {PrintOutStringNL "Zero"};

  Mov r15, 5;
  Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};
  Shr r15, 1; IfC  Then {PrintOutStringNL "Carry"}   , Else {PrintOutStringNL "NO carry"};
  Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};
  Shr r15, 1; IfNc Then {PrintOutStringNL "NO carry"}, Else {PrintOutStringNL "Carry"};

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
ZF=1
ZF=0
ZF=1
ZF=1
ZF=0
Zero
NOT zero
Carry
NO carry
Carry
NO carry
END
 }

#latest:;
if (1) {                                                                        #TSetLabel #TRegisterSize #TSaveFirstFour #TSaveFirstSeven #TRestoreFirstFour #TRestoreFirstSeven #TRestoreFirstFourExceptRax #TRestoreFirstSevenExceptRax #TRestoreFirstFourExceptRaxAndRdi #TRestoreFirstSevenExceptRaxAndRdi #TReverseBytesInRax
  Mov rax, 1;
  Mov rdi, 1;
  SaveFirstFour;
  Mov rax, 2;
  Mov rdi, 2;
  SaveFirstSeven;
  Mov rax, 3;
  Mov rdi, 4;
  PrintOutRegisterInHex rax, rdi;
  RestoreFirstSeven;
  PrintOutRegisterInHex rax, rdi;
  RestoreFirstFour;
  PrintOutRegisterInHex rax, rdi;

  SaveFirstFour;
  Mov rax, 2;
  Mov rdi, 2;
  SaveFirstSeven;
  Mov rax, 3;
  Mov rdi, 4;
  PrintOutRegisterInHex rax, rdi;
  RestoreFirstSevenExceptRax;
  PrintOutRegisterInHex rax, rdi;
  RestoreFirstFourExceptRax;
  PrintOutRegisterInHex rax, rdi;

  SaveFirstFour;
  Mov rax, 2;
  Mov rdi, 2;
  SaveFirstSeven;
  Mov rax, 3;
  Mov rdi, 4;
  PrintOutRegisterInHex rax, rdi;

  Bswap rax;
  PrintOutRegisterInHex rax;

  my $l = Label;
  Jmp $l;
  SetLabel $l;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
   rax: .... .... .... ...3
   rdi: .... .... .... ...4
   rax: .... .... .... ...2
   rdi: .... .... .... ...2
   rax: .... .... .... ...1
   rdi: .... .... .... ...1
   rax: .... .... .... ...3
   rdi: .... .... .... ...4
   rax: .... .... .... ...3
   rdi: .... .... .... ...2
   rax: .... .... .... ...3
   rdi: .... .... .... ...1
   rax: .... .... .... ...3
   rdi: .... .... .... ...4
   rax: .3.. .... .... ....
END

  ok 8 == RegisterSize rax;
 }

#latest:
if (1) {                                                                        #TRb #TRd #TRq #TRw #TDb #TDd #TDq #TDw #TCopyMemory
  my $s = Rb 0; Rb 1; Rw 2; Rd 3;  Rq 4;
  my $t = Db 0; Db 1; Dw 2; Dd 3;  Dq 4;

  Vmovdqu8 xmm0, "[$s]";
  Vmovdqu8 xmm1, "[$t]";
  PrintOutRegisterInHex xmm0;
  PrintOutRegisterInHex xmm1;
  Sub rsp, 16;

  Mov rax, rsp;                                                                 # Copy memory, the target is addressed by rax, the length is in rdi, the source is addressed by rsi
  Mov rdi, 16;
  Mov rsi, $s;
  CopyMemory(V(source => rsi), V(target => rax), V size => rdi);
  PrintOutMemory_InHexNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
  xmm0: .... .... .... ...4  .... ...3 ...2 .1..
  xmm1: .... .... .... ...4  .... ...3 ...2 .1..
__.1 .2__ .3__ ____  .4__ ____ ____ ____
END
 }

#latest:
if (1) {
  my $a = V(a => 1);
  my $b = V(b => 2);
  my $c = $a + $b;
  Mov r15, 22;
  $a->getReg(r15);
  $b->copy($a);
  $b = $b + 1;
  $b->setReg(14);
  $a->outNL;
  $b->outNL;
  $c->outNL;
  PrintOutRegisterInHex r14, r15;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
a: .... .... .... ..16
(b add 1): .... .... .... ..17
(a add b): .... .... .... ...3
   r14: .... .... .... ..17
   r15: .... .... .... ..16
END
 }

#latest:
if (1) {                                                                        #TV #TK #TG #TNasm::X86::Variable::copy
  my $s = Subroutine
   {my ($p) = @_;
    $$p{v}->copy($$p{v} + $$p{k} + $$p{g} + 1);
   } name => 'add', parameters=>[qw(v k g)];

  my $v = V(v => 1);
  my $k = K(k => 2);
  my $g = V(g => 3);
  $s->call(parameters=>{v=>$v, k=>$k, g=>$g});
  $v->outNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
v: .... .... .... ...7
END
 }

#latest:
if (1) {                                                                        #TV #TK #TG #TNasm::X86::Variable::copy
  my $g = V g => 0;
  my $s = Subroutine
   {my ($p) = @_;
    $$p{g}->copy(K value => 1);
   } name => 'ref2', parameters=>[qw(g)];

  my $t = Subroutine
   {my ($p) = @_;
    $s->call(parameters=>{g=>$$p{g}});
   } name => 'ref', parameters=>[qw(g)];

  $t->call(parameters=>{g=>$g});
  $g->outNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
g: .... .... .... ...1
END
 }

#latest:
if (1) {                                                                        #TSubroutine
  my $g = V g => 3;
  my $s = Subroutine
   {my ($p, $s, $sub) = @_;
    my $g = $$p{g};
    $g->copy($g - 1);
    $g->outNL;
    If ($g > 0,
    Then
     {$sub->call(parameters=>{g => $g});
     });
   } parameters=>[qw(g)], name => 'ref';

  $s->call(parameters=>{g => $g});

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
g: .... .... .... ...2
g: .... .... .... ...1
g: .... .... .... ....
END
 }

#latest:
if (0) {                                                                        #TPrintOutTraceBack
  my $d = V depth => 3;                                                         # Create a variable on the stack

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine descriptor

    my $d = $$p{depth}->copy($$p{depth} - 1);                                   # Modify the variable referenced by the parameter

    If $d > 0,
    Then
     {$sub->call(parameters => {depth => $d});                                  # Recurse
     };

    #PrintOutTraceBack 'AAAA';
   } parameters =>[qw(depth)], name => 'ref';

  $s->call(parameters=>{depth => V depth => 0});

  ok Assemble(debug => 0, eq => <<END, avx512=>0);

Subroutine trace back, depth:  3
0000 0000 0000 0001    ref
0000 0000 0000 0001    ref
0000 0000 0000 0001    ref
END
 }

#latest:
if (0) {                                                                        #TSubroutine
  my $g = V g, 2;
  my $u = Subroutine33
   {my ($p, $s) = @_;
    $$p{g}->copy(K gg, 1);
    PrintOutTraceBack '';
   } [qw(g)], name => 'uuuu';
  my $t = Subroutine33
   {my ($p, $s) = @_;
    $u->call($$p{g});
   } [qw(g)], name => 'tttt';
  my $s = Subroutine33
   {my ($p, $s) = @_;
    $t->call($$p{g});
   } [qw(g)], name => 'ssss';

  $g->outNL;
  $s->call($g);
  $g->outNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
Subroutine trace back, depth:  3
0000 0000 0000 0002    uuuu
0000 0000 0000 0002    tttt
0000 0000 0000 0002    ssss
END
 }

#latest:
if (0) {                                                                        #TSubroutine
  my $r = V r, 2;

  my $u = Subroutine33
   {my ($p, $s) = @_;
    $$p{u}->copy(K gg, 1);
    PrintOutTraceBack '';
   } [qw(u)], name => 'uuuu';

  my $t = Subroutine33
   {my ($p, $s) = @_;
    $u->call(u => $$p{t});
   } [qw(t)], name => 'tttt';

  my $s = Subroutine33
   {my ($p, $s) = @_;
   $t->call(t => $$p{s});
   } [qw(s)], name => 'ssss';

  $r->outNL;
  $s->call(s=>$r);
  $r->outNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
r: 0000 0000 0000 0002

Subroutine trace back, depth:  3
0000 0000 0000 0002    uuuu
0000 0000 0000 0002    tttt
0000 0000 0000 0002    ssss


Subroutine trace back, depth:  3
0000 0000 0000 0001    uuuu
0000 0000 0000 0001    tttt
0000 0000 0000 0001    ssss

r: 0000 0000 0000 0001
END
 }

#latest:;
if (1) {                                                                        #TAllocateMemory #TPrintOutMemoryInHexNL #TCopyMemory
  my $N = 256;
  my $s = Rb 0..$N-1;
  my $a = AllocateMemory K size => $N;
  CopyMemory(V(source => $s), $a, K(size => $N));

  my $b = AllocateMemory K size => $N;
  CopyMemory($a, $b, K size => $N);

  $b->setReg(rax);
  Mov rdi, $N;
  PrintOutMemory_InHexNL;

  ok Assemble(debug=>0, eq => <<END, avx512=>0);
__.1 .2.3 .4.5 .6.7  .8.9 .A.B .C.D .E.F  1011 1213 1415 1617  1819 1A1B 1C1D 1E1F  2021 2223 2425 2627  2829 2A2B 2C2D 2E2F  3031 3233 3435 3637  3839 3A3B 3C3D 3E3F  4041 4243 4445 4647  4849 4A4B 4C4D 4E4F  5051 5253 5455 5657  5859 5A5B 5C5D 5E5F  6061 6263 6465 6667  6869 6A6B 6C6D 6E6F  7071 7273 7475 7677  7879 7A7B 7C7D 7E7F  8081 8283 8485 8687  8889 8A8B 8C8D 8E8F  9091 9293 9495 9697  9899 9A9B 9C9D 9E9F  A0A1 A2A3 A4A5 A6A7  A8A9 AAAB ACAD AEAF  B0B1 B2B3 B4B5 B6B7  B8B9 BABB BCBD BEBF  C0C1 C2C3 C4C5 C6C7  C8C9 CACB CCCD CECF  D0D1 D2D3 D4D5 D6D7  D8D9 DADB DCDD DEDF  E0E1 E2E3 E4E5 E6E7  E8E9 EAEB ECED EEEF  F0F1 F2F3 F4F5 F6F7  F8F9 FAFB FCFD FEFF
END
 }

if (1) {                                                                        # Variable length shift
  Mov rax, -1;
  Mov cl, 30;
  Shl rax, cl;
  Kmovq k0, rax;
  PrintOutRegisterInHex k0;

  ok Assemble(avx512=>1, eq=><<END);
    k0: FFFF FFFF C0.. ....
END
 }

#latest:;
if (1) {                                                                        # Expand
  ClearRegisters rax;
  Bts rax, 14;
  Not rax;
  PrintOutRegisterInHex rax;
  Kmovq k1, rax;
  PrintOutRegisterInHex k1;

  Mov rax, 1;
  Vpbroadcastb zmm0, rax;
  PrintOutRegisterInHex zmm0;

  Vpexpandd "zmm1{k1}", zmm0;
  PrintOutRegisterInHex zmm1;

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
   rax: FFFF FFFF FFFF BFFF
    k1: FFFF FFFF FFFF BFFF
  zmm0: .1.1 .1.1 .1.1 .1.1  .1.1 .1.1 .1.1 .1.1 - .1.1 .1.1 .1.1 .1.1  .1.1 .1.1 .1.1 .1.1 + .1.1 .1.1 .1.1 .1.1  .1.1 .1.1 .1.1 .1.1 - .1.1 .1.1 .1.1 .1.1  .1.1 .1.1 .1.1 .1.1
  zmm1: .1.1 .1.1 .... ....  .1.1 .1.1 .1.1 .1.1 - .1.1 .1.1 .1.1 .1.1  .1.1 .1.1 .1.1 .1.1 + .1.1 .1.1 .1.1 .1.1  .1.1 .1.1 .1.1 .1.1 - .1.1 .1.1 .1.1 .1.1  .1.1 .1.1 .1.1 .1.1
END
 }

#latest:;
if (1) {
  my $P = "2F";                                                                 # Value to test for
  my $l = Rb 0;  Rb $_ for 1..RegisterSize zmm0;                                # The numbers 0..63
  Vmovdqu8 zmm0, "[$l]";                                                        # Load data to test
  PrintOutRegisterInHex zmm0;
  PrintOutRegisterInHex zmm0;

  Mov rax, "0x$P";                                                              # Broadcast the value to be tested
  Vpbroadcastb zmm1, rax;
  PrintOutRegisterInHex zmm1;

  for my $c(0..7)                                                               # Each possible test
   {my $m = "k$c";
    Vpcmpub $m, zmm1, zmm0, $c;
    PrintOutRegisterInHex $m;
   }

  Kmovq rax, k0;                                                                # Count the number of trailing zeros in k0
  Tzcnt rax, rax;

  PrintOutRegisterInHex rax;

  ok Assemble(avx512=>1, eq=><<END);
  zmm0: 3F3E 3D3C 3B3A 3938  3736 3534 3332 3130 - 2F2E 2D2C 2B2A 2928  2726 2524 2322 2120 + 1F1E 1D1C 1B1A 1918  1716 1514 1312 1110 - .F.E .D.C .B.A .9.8  .7.6 .5.4 .3.2 .1..
  zmm0: 3F3E 3D3C 3B3A 3938  3736 3534 3332 3130 - 2F2E 2D2C 2B2A 2928  2726 2524 2322 2120 + 1F1E 1D1C 1B1A 1918  1716 1514 1312 1110 - .F.E .D.C .B.A .9.8  .7.6 .5.4 .3.2 .1..
  zmm1: 2F2F 2F2F 2F2F 2F2F  2F2F 2F2F 2F2F 2F2F - 2F2F 2F2F 2F2F 2F2F  2F2F 2F2F 2F2F 2F2F + 2F2F 2F2F 2F2F 2F2F  2F2F 2F2F 2F2F 2F2F - 2F2F 2F2F 2F2F 2F2F  2F2F 2F2F 2F2F 2F2F
    k0: .... 80.. .... ....
    k1: FFFF .... .... ....
    k2: FFFF 80.. .... ....
    k3: .... .... .... ....
    k4: FFFF 7FFF FFFF FFFF
    k5: .... FFFF FFFF FFFF
    k6: .... 7FFF FFFF FFFF
    k7: FFFF FFFF FFFF FFFF
   rax: .... .... .... ..2F
END
#   0 eq    1 lt    2 le    4 ne    5 ge    6 gt   comparisons
 }

#latest:;
if (1) {
  my $P = "2F";                                                                 # Value to test for
  my $l = Rb 0;  Rb $_ for 1..RegisterSize zmm0;                                # The numbers 0..63
  Vmovdqu8 zmm0, "[$l]";                                                        # Load data to test

  Mov rax, "0x$P";                                                              # Broadcast the value to be tested
  Vpbroadcastb zmm1, rax;

  for my $c(0..7)                                                               # Each possible test
   {my $m = "k$c";
    Vpcmpub $m, zmm1, zmm0, $c;
   }

  Kmovq rax, k0;                                                                # Count the number of trailing zeros in k0
  Tzcnt rax, rax;
  PrintOutRegisterInHex rax;

  Kmovq rax, k0;                                                                # Count the number of leading zeros in k0
  Lzcnt rax, rax;
  PrintOutRegisterInHex rax;

  ok Assemble(avx512=>1, eq=><<END);
   rax: .... .... .... ..2F
   rax: .... .... .... ..10
END
 }

#latest:;
if (1) {                                                                        #TStringLength
  StringLength(V string => Rs("abcd"))->outNL;
  Assemble(debug => 0, eq => <<END, avx512=>0);
size: .... .... .... ...4
END
 }

#latest:;
if (0) {                                                                        # Hash a string #THash
  Mov rax, "[rbp+24]";                                                          # Address of string as parameter
  StringLength(V string => rax)->setReg(rdi);                                   # Length of string to hash
  Hash();                                                                       # Hash string

  PrintOutRegisterInHex r15;

  my $e = Assemble keep => 'hash';                                              # Assemble to the specified file name
  say STDERR qx($e "");
  say STDERR qx($e "a");
  ok qx($e "")  =~ m(r15: 0000 3F80 0000 3F80);                                 # Test well known hashes
  ok qx($e "a") =~ m(r15: 0000 3F80 C000 45B2);

  if (0)                                                                        # Hash various strings
   {my %r; my %f; my $count = 0;
    my $N = RegisterSize zmm0;

    if (1)                                                                      # Fixed blocks
     {for my $l(qw(a ab abc abcd), 'a a', 'a  a')
       {for my $i(1..$N)
         {my $t = $l x $i;
          last if $N < length $t;
          my $s = substr($t.(' ' x $N), 0, $N);
          next if $f{$s}++;
          my $r = qx($e "$s");
          say STDERR "$count  $r";
          if ($r =~ m(^.*r15:\s*(.*)$)m)
           {push $r{$1}->@*, $s;
            ++$count;
           }
         }
       }
     }

    if (1)                                                                      # Variable blocks
     {for my $l(qw(a ab abc abcd), '', 'a a', 'a  a')
       {for my $i(1..$N)
         {my $t = $l x $i;
          next if $f{$t}++;
          my $r = qx($e "$t");
          say STDERR "$count  $r";
          if ($r =~ m(^.*r15:\s*(.*)$)m)
           {push $r{$1}->@*, $t;
            ++$count;
           }
         }
       }
     }
    for my $r(keys %r)
     {delete $r{$r} if $r{$r}->@* < 2;
     }

    say STDERR dump(\%r);
    say STDERR "Keys hashed: ", $count;
    confess "Duplicates : ",  scalar keys(%r);
   }

  unlink 'hash';
 }

if (1) {                                                                        #TIfEq #TIfNe #TIfLe #TIfLt #TIfGe #TIfGt
  my $cmp = sub
   {my ($a, $b) = @_;

    for my $op(qw(eq ne lt le gt ge))
     {Mov rax, $a;
      Cmp rax, $b;
      my $Op = ucfirst $op;
      eval qq(If$Op Then {PrintOutStringNL("$a $op $b")}, Else {PrintOutStringNL("$a NOT $op $b")});
      $@ and confess $@;
     }
   };
  &$cmp(1,1);
  &$cmp(1,2);
  &$cmp(3,2);
  Assemble(debug => 0, eq => <<END, avx512=>0);
1 eq 1
1 NOT ne 1
1 NOT lt 1
1 le 1
1 NOT gt 1
1 ge 1
1 NOT eq 2
1 ne 2
1 lt 2
1 le 2
1 NOT gt 2
1 NOT ge 2
3 NOT eq 2
3 ne 2
3 NOT lt 2
3 NOT le 2
3 gt 2
3 ge 2
END
 }

if (1) {                                                                        #TSetMaskRegister
  Mov rax, 8;
  Mov rsi, -1;
  Inc rsi; SetMaskRegister(0, rax, rsi); PrintOutRegisterInHex k0;
  Inc rsi; SetMaskRegister(1, rax, rsi); PrintOutRegisterInHex k1;
  Inc rsi; SetMaskRegister(2, rax, rsi); PrintOutRegisterInHex k2;
  Inc rsi; SetMaskRegister(3, rax, rsi); PrintOutRegisterInHex k3;
  Inc rsi; SetMaskRegister(4, rax, rsi); PrintOutRegisterInHex k4;
  Inc rsi; SetMaskRegister(5, rax, rsi); PrintOutRegisterInHex k5;
  Inc rsi; SetMaskRegister(6, rax, rsi); PrintOutRegisterInHex k6;
  Inc rsi; SetMaskRegister(7, rax, rsi); PrintOutRegisterInHex k7;

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
    k0: .... .... .... ....
    k1: .... .... .... .1..
    k2: .... .... .... .3..
    k3: .... .... .... .7..
    k4: .... .... .... .F..
    k5: .... .... .... 1F..
    k6: .... .... .... 3F..
    k7: .... .... .... 7F..
END
 }

#latest:;
if (1) {                                                                        #TNasm::X86::Variable::dump  #TNasm::X86::Variable::print #TThen #TElse #TV #TK
  my $a = V(a => 3);  $a->outNL;
  my $b = K(b => 2);  $b->outNL;
  my $c = $a +  $b; $c->outNL;
  my $d = $c -  $a; $d->outNL;
  my $g = $a *  $b; $g->outNL;
  my $h = $g /  $b; $h->outNL;
  my $i = $a %  $b; $i->outNL;

  If ($a == 3,
  Then
   {PrintOutStringNL "a == 3"
   },
  Else
   {PrintOutStringNL "a != 3"
   });

  ++$a; $a->outNL;
  --$a; $a->outNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
a: .... .... .... ...3
b: .... .... .... ...2
(a add b): .... .... .... ...5
((a add b) sub a): .... .... .... ...2
(a times b): .... .... .... ...6
((a times b) / b): .... .... .... ...3
(a % b): .... .... .... ...1
a == 3
a: .... .... .... ...4
a: .... .... .... ...3
END
 }

#latest:;
if (1) {                                                                        #TNasm::X86::Variable::for
  V(limit => 10)->for(sub
   {my ($i, $start, $next, $end) = @_;
    $i->outNL;
   });

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
index: .... .... .... ....
index: .... .... .... ...1
index: .... .... .... ...2
index: .... .... .... ...3
index: .... .... .... ...4
index: .... .... .... ...5
index: .... .... .... ...6
index: .... .... .... ...7
index: .... .... .... ...8
index: .... .... .... ...9
END
 }

#latest:;
if (1) {                                                                        #TNasm::X86::Variable::min #TNasm::X86::Variable::max
  my $a = V("a", 1);
  my $b = V("b", 2);
  my $c = $a->min($b);
  my $d = $a->max($b);
  $a->outNL;
  $b->outNL;
  $c->outNL;
  $d->outNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
a: .... .... .... ...1
b: .... .... .... ...2
min: .... .... .... ...1
max: .... .... .... ...2
END
 }

#latest:;
if (1) {                                                                        #TNasm::X86::Variable::setMask
  my $start  = V("Start",  7);
  my $length = V("Length", 3);
  $start->setMask($length, k7);
  PrintOutRegisterInHex k7;

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
    k7: .... .... .... .380
END
 }

#latest:;
if (1) {                                                                        #TNasm::X86::Variable::setZmm
  my $s = Rb(0..128);
  my $source = V(Source=> $s);

  if (1)                                                                        # First block
   {$source->setZmm(0, K(key => 7), K length => 3);
   }

  if (1)                                                                        # Second block
   {$source->setZmm(0, K(key => 33), K key => 12);
   }

  PrintOutRegisterInHex zmm0;

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
  zmm0: .... .... .... ....  .... .... .... .... - .... ...B .A.9 .8.7  .6.5 .4.3 .2.1 .... + .... .... .... ....  .... .... .... .... - .... .... .... .2.1  .... .... .... ....
END
 }

#latest:;
if (1) {                                                                        #TLoadZmm #Tzmm
  LoadZmm 0, 0..63;
  PrintOutRegisterInHex zmm 0;

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
  zmm0: 3F3E 3D3C 3B3A 3938  3736 3534 3332 3130 - 2F2E 2D2C 2B2A 2928  2726 2524 2322 2120 + 1F1E 1D1C 1B1A 1918  1716 1514 1312 1110 - .F.E .D.C .B.A .9.8  .7.6 .5.4 .3.2 .1..
END
 }

#latest:;
if (1) {                                                                        #TgetDFromZmm #TNasm::X86::Variable::dIntoZ
  my $s = Rb(0..8);
  my $c = V("Content",   "[$s]");
     $c->bIntoZ     (0, 4);
     $c->putWIntoZmm(0, 6);
     $c->dIntoZ(0, 10);
     $c->qIntoZ(0, 16);
  PrintOutRegisterInHex zmm0;
  bFromZ(0, 12)->outNL;
  wFromZ(0, 12)->outNL;
  dFromZ(0, 12)->outNL;
  qFromZ(0, 12)->outNL;

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
  zmm0: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .7.6 .5.4 .3.2 .1.. - .... .3.2 .1.. ....  .1.. .... .... ....
b at offset 12 in zmm0: .... .... .... ...2
w at offset 12 in zmm0: .... .... .... .3.2
d at offset 12 in zmm0: .... .... .... .3.2
q at offset 12 in zmm0: .3.2 .1.. .... .3.2
END
 }

#latest:;
if (1) {                                                                        #TNasm::X86::Area::used #TNasm::X86::Area::clear #TNasm::X86::Area::size  #TNasm::X86::Area::free
  my $a = CreateArea;

  $a->q("a" x 255);
  $a->used->outNL;
  $a->size->outNL;
  $a->dump('A');
  $a->clear;
  $a->used->outNL;
  $a->size->outNL;
  $a->dump('B');

  $a->q("a" x 4095);
  $a->used->outNL;
  $a->size->outNL;
  $a->dump('C');
  $a->clear;
  $a->used->outNL;
  $a->size->outNL;
  $a->dump('D');

  $a->free;

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
area used up: .... .... .... ..FF
size of area: .... .... .... 10..
A
Area     Size:     4096    Used:      319
.... .... .... .... | __10 ____ ____ ____  3F.1 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | 6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161
.... .... .... ..80 | 6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161
.... .... .... ..C0 | 6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161
area used up: .... .... .... ....
size of area: .... .... .... 10..
B
Area     Size:     4096    Used:       64
.... .... .... .... | __10 ____ ____ ____  40__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | 6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161
.... .... .... ..80 | 6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161
.... .... .... ..C0 | 6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161
area used up: .... .... .... .FFF
size of area: .... .... .... 20..
C
Area     Size:     8192    Used:     4159
.... .... .... .... | __20 ____ ____ ____  3F10 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | 6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161
.... .... .... ..80 | 6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161
.... .... .... ..C0 | 6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161
area used up: .... .... .... ....
size of area: .... .... .... 20..
D
Area     Size:     8192    Used:       64
.... .... .... .... | __20 ____ ____ ____  40__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | 6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161
.... .... .... ..80 | 6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161
.... .... .... ..C0 | 6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161  6161 6161 6161 6161
END
 }

#latest:;
if (1) {                                                                        #TNasm::X86::Variable::setMask
  my $z = V('zero', 0);
  my $o = V('one',  1);
  my $t = V('two',  2);
  $z->setMask($o,       k7); PrintOutRegisterInHex k7;
  $z->setMask($t,       k6); PrintOutRegisterInHex k6;
  $z->setMask($o+$t,    k5); PrintOutRegisterInHex k5;
  $o->setMask($o,       k4); PrintOutRegisterInHex k4;
  $o->setMask($t,       k3); PrintOutRegisterInHex k3;
  $o->setMask($o+$t,    k2); PrintOutRegisterInHex k2;

  $t->setMask($o,       k1); PrintOutRegisterInHex k1;
  $t->setMask($t,       k0); PrintOutRegisterInHex k0;

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
    k7: .... .... .... ...1
    k6: .... .... .... ...3
    k5: .... .... .... ...7
    k4: .... .... .... ...2
    k3: .... .... .... ...6
    k2: .... .... .... ...E
    k1: .... .... .... ...4
    k0: .... .... .... ...C
END
 }

#latest:
if (1) {                                                                        #TExtern #TLink #TCallC
  my $format = Rs "Hello %s\n";
  my $data   = Rs "World";

  Extern qw(printf exit malloc strcpy); Link 'c';

  CallC 'malloc', length($format)+1;
  Mov r15, rax;
  CallC 'strcpy', r15, $format;
  CallC 'printf', r15, $data;
  CallC 'exit', 0;

  ok Assemble avx512=>0, eq => <<END;
Hello World
END
 }

#latest:
if (1) {
  my $a = Rb((reverse 0..16)x16);
  my $b = Rb((        0..16)x16);
  Mov rax, $a;  Vmovdqu8 zmm0, "[rax]";
  Mov rax, $b;  Vmovdqu8 zmm1, "[rax]";
  Vpcmpeqb k0, zmm0, zmm1;

  Kmovq rax, k0; Popcnt rax, rax;
  PrintOutRegisterInHex zmm0, zmm1, k0, rax;

  ok Assemble avx512=>1, eq => <<END;
  zmm0: .4.5 .6.7 .8.9 .A.B  .C.D .E.F 10.. .1.2 - .3.4 .5.6 .7.8 .9.A  .B.C .D.E .F10 ...1 + .2.3 .4.5 .6.7 .8.9  .A.B .C.D .E.F 10.. - .1.2 .3.4 .5.6 .7.8  .9.A .B.C .D.E .F10
  zmm1: .C.B .A.9 .8.7 .6.5  .4.3 .2.1 ..10 .F.E - .D.C .B.A .9.8 .7.6  .5.4 .3.2 .1.. 10.F + .E.D .C.B .A.9 .8.7  .6.5 .4.3 .2.1 ..10 - .F.E .D.C .B.A .9.8  .7.6 .5.4 .3.2 .1..
    k0: .8.. .4.. .2.. .1..
   rax: .... .... .... ...4
END
 }

#latest:
if (1) {                                                                        #TConvertUtf8ToUtf32
  my ($out, $size, $fail);

  my $Chars = Rb(0x24, 0xc2, 0xa2, 0xc9, 0x91, 0xE2, 0x82, 0xAC, 0xF0, 0x90, 0x8D, 0x88);
  my $chars = V(chars => $Chars);

 ($out, $size, $fail) = GetNextUtf8CharAsUtf32 $chars+0;                        # Dollar               UTF-8 Encoding: 0x24                UTF-32 Encoding: 0x00000024
  $out->out('out1 : ');
  $size->outNL(' size : ');

 ($out, $size, $fail) = GetNextUtf8CharAsUtf32 $chars+1;                        # Cents                UTF-8 Encoding: 0xC2 0xA2           UTF-32 Encoding: 0x000000a2
  $out->out('out2 : ');     $size->outNL(' size : ');

 ($out, $size, $fail) = GetNextUtf8CharAsUtf32 $chars+3;                        # Alpha                UTF-8 Encoding: 0xC9 0x91           UTF-32 Encoding: 0x00000251
  $out->out('out3 : ');     $size->outNL(' size : ');

 ($out, $size, $fail) = GetNextUtf8CharAsUtf32 $chars+5;                        # Euro                 UTF-8 Encoding: 0xE2 0x82 0xAC      UTF-32 Encoding: 0x000020AC
  $out->out('out4 : ');     $size->outNL(' size : ');

 ($out, $size, $fail) = GetNextUtf8CharAsUtf32 $chars+8;                        # Gothic Letter Hwair  UTF-8 Encoding  0xF0 0x90 0x8D 0x88 UTF-32 Encoding: 0x00010348
  $out->out('out5 : ');     $size->outNL(' size : ');

  my $statement = qq(𝖺\n 𝑎𝑠𝑠𝑖𝑔𝑛 【【𝖻 𝐩𝐥𝐮𝐬 𝖼】】\nAAAAAAAA);                        # A sample sentence to parse

  my $s = K(statement => Rutf8($statement));
  my $l = StringLength $s;

  my $address = AllocateMemory $l;                                              # Allocate enough memory for a copy of the string
  CopyMemory($s, $address, $l);

 ($out, $size, $fail) = GetNextUtf8CharAsUtf32 $address;
  $out->out('outA : ');     $size->outNL(' size : ');

 ($out, $size, $fail) = GetNextUtf8CharAsUtf32 $address+4;
  $out->out('outB : ');     $size->outNL(' size : ');

 ($out, $size, $fail) = GetNextUtf8CharAsUtf32 $address+5;
  $out->out('outC : ');     $size->outNL(' size : ');

 ($out, $size, $fail) = GetNextUtf8CharAsUtf32 $address+30;
  $out->out('outD : ');     $size->outNL(' size : ');

 ($out, $size, $fail) = GetNextUtf8CharAsUtf32 $address+35;
  $out->out('outE : ');     $size->outNL(' size : ');

  $address->printOutMemoryInHexNL($l);

  ok Assemble(debug => 0, eq => <<END, avx512=>0);
out1 : .... .... .... ..24 size : .... .... .... ...1
out2 : .... .... .... ..A2 size : .... .... .... ...2
out3 : .... .... .... .251 size : .... .... .... ...2
out4 : .... .... .... 20AC size : .... .... .... ...3
out5 : .... .... ...1 .348 size : .... .... .... ...4
outA : .... .... ...1 D5BA size : .... .... .... ...4
outB : .... .... .... ...A size : .... .... .... ...1
outC : .... .... .... ..20 size : .... .... .... ...1
outD : .... .... .... ..20 size : .... .... .... ...1
outE : .... .... .... ..10 size : .... .... .... ...2
F09D 96BA .A20 F09D  918E F09D 91A0 F09D  91A0 F09D 9196 F09D  9194 F09D 919B 20E3  8090 E380 90F0 9D96  BB20 F09D 90A9 F09D  90A5 F09D 90AE F09D  90AC 20F0 9D96 BCE3  8091 E380 91.A 4141  4141 4141 4141 ....
END
 }

#latest:
if (1) {                                                                        #TLoadBitsIntoMaskRegister
  for (0..7)
   {ClearRegisters "k$_";
    K($_,$_)->setMaskBit("k$_");
    PrintOutRegisterInHex "k$_";
   }

  ClearRegisters k7;
  LoadBitsIntoMaskRegister(7, '1010', -4, +4, -2, +2, -1, +1, -1, +1);
  PrintOutRegisterInHex "k7";

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
    k0: .... .... .... ...1
    k1: .... .... .... ...2
    k2: .... .... .... ...4
    k3: .... .... .... ...8
    k4: .... .... .... ..10
    k5: .... .... .... ..20
    k6: .... .... .... ..40
    k7: .... .... .... ..80
    k7: .... .... ...A .F35
END
 }

#latest:
if (1) {                                                                        #TInsertZeroIntoRegisterAtPoint #TInsertOneIntoRegisterAtPoint
  Mov r15, 0x100;                                                               # Given a register with a single one in it indicating the desired position,
  Mov r14, 0xFFDC;                                                              # Insert a zero into the register at that position shifting the bits above that position up left one to make space for the new zero.
  Mov r13, 0xF03F;
  PrintOutRegisterInHex         r14, r15;
  InsertZeroIntoRegisterAtPoint r15, r14;
  PrintOutRegisterInHex r14;
  Or r14, r15;                                                                  # Replace the inserted zero with a one
  PrintOutRegisterInHex r14;
  InsertOneIntoRegisterAtPoint r15, r13;
  PrintOutRegisterInHex r13;
  ok Assemble(debug => 0, eq => <<END, avx512=>0);
   r14: .... .... .... FFDC
   r15: .... .... .... .1..
   r14: .... .... ...1 FEDC
   r14: .... .... ...1 FFDC
   r13: .... .... ...1 E13F
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::setOrClearTreeBits
  my $b = CreateArea;
  my $t = $b->CreateTree;

  Mov r15, 8;
  $t->setTreeBit  (31, r15); PrintOutRegisterInHex 31;
  $t->isTree      (31, r15); PrintOutZF;

  Mov r15, 16;
  $t->isTree      (31, r15); PrintOutZF;
  $t->setTreeBit  (31, r15); PrintOutRegisterInHex 31;
  $t->clearTreeBit(31, r15); PrintOutRegisterInHex 31;
  $t->isTree      (31, r15); PrintOutZF;

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
 zmm31: .... .... ...8 ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
ZF=0
ZF=1
 zmm31: .... .... ..18 ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
 zmm31: .... .... ...8 ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
ZF=0
END
 }

#latest:
if (1) {                                                                        # Print empty tree
  my $b = CreateArea;
  my $t = $b->CreateTree;
  $t->dump("AAAA");

  ok Assemble(debug => 0, eq => <<END, avx512=>1);
AAAA
- empty
END
 }

#latest:
if (0) {                                                                        # An example of using sigaction in x86 and x64 assembler code.  Linux on x86 requires not only a signal handler but a signal trampoline.  The following code shows how to set up a signal and its associated trampoline using sigaction or rt_sigaction.
  my $end   = Label;
  Jmp $end;                                                                     # Jump over subroutine definition
  my $start = SetLabel;
  Enter 0, 0;                                                                   # Inline code of signal handler
  Mov r15, rbp;                                                                 # Preserve the new stack frame
  Mov rbp, "[rbp]";                                                             # Restore our last stack frame
  PrintOutTraceBack '';                                                         # Print our trace back
  Mov rbp, r15;                                                                 # Restore supplied stack frame
  Exit(0);                                                                      # Exit so we do not trampoline. Exit with code zero to show that the program is functioning correctly, else L<Assemble> will report an error.
  Leave;
  Ret;
  SetLabel $end;

  Mov r15, 0;                                                                   # Push sufficient zeros onto the stack to make a struct sigaction as described in: https://www.man7.org/linux/man-pages/man2/sigaction.2.html
  Push r15 for 1..16;

  Mov r15, $start;                                                              # Actual signal handler
  Mov "[rsp]", r15;                                                             # Show as signal handler
  Mov "[rsp+0x10]", r15;                                                        # Add as trampoline as well - which is fine because we exit in the handler so this will never be called
  Mov r15, 0x4000000;                                                           # Mask to show we have a trampoline which is, apparently, required on x86
  Mov "[rsp+0x8]", r15;                                                         # Confirm we have a trampoline

  Mov rax, 13;                                                                  # Sigaction from "kill -l"
  Mov rdi, 11;                                                                  # Confirmed SIGSEGV = 11 from kill -l and tracing with sde64
  Mov rsi, rsp;                                                                 # Sigaction structure on stack
  Mov rdx, 0;                                                                   # Confirmed by trace
  Mov r10, 8;                                                                   # Found by tracing "signal.c" with sde64 it is the width of the signal set and mask. "signal.c" is reproduced below.
  Syscall;
  Add rsp, 128;

  my $s = Subroutine                                                            # Subroutine that will cause an error to occur to force a trace back to be printed
   {Mov r15, 0;
    Mov r15, "[r15]";                                                           # Try to read an unmapped memory location
   } [qw(in)], name => 'sub that causes a segv';                                # The name that will appear in the trace back

  $s->call(K(in, 42));

  ok Assemble(debug => 0, keep2 => 'signal', avx512=>0, eq => <<END, avx512=>0);# Cannot use the emulator because it does not understand signals

Subroutine trace back, depth:  1
0000 0000 0000 002A    sub that causes a segv

END

# /var/isde/sde64 -mix -ptr-check -debugtrace -- ./signal
##include <stdlib.h>
##include <stdio.h>
##include <signal.h>
##include <string.h>
##include <unistd.h>
#
#void handle_sigint(int sig)
# {exit(sig);
# }
#
#int main(void)
# {struct sigaction s;
#  memset(&s, 0, sizeof(s));
#  s.sa_sigaction = (void *)handle_sigint;
#
#  long a = 0xabcdef;
#  sigaction(SIGSEGV, &s, 0);
#  long *c = 0; *c = a;
# }
#
# gcc -finput-charset=UTF-8 -fmax-errors=7 -rdynamic -Wall -Wextra -Wno-unused-function -o signal signal.c  && /var/isde/sde64 -mix -ptr-check -debugtrace  -- ./signal; echo $?;
 }

#latest:
if (0) {                                                                        #TOnSegv
  OnSegv();                                                                     # Request a trace back followed by exit on a segv signal.

  my $t = Subroutine                                                            # Subroutine that will cause an error to occur to force a trace back to be printed
   {Mov r15, 0;
    Mov r15, "[r15]";                                                           # Try to read an unmapped memory location
   } [qw(in)], name => 'sub that causes a segv';                                # The name that will appear in the trace back

  $t->call(K(in, 42));

  ok Assemble(debug => 0, keep2 => 'signal', avx512=>0, eq => <<END, avx512=>0);# Cannot use the emulator because it does not understand signals

Subroutine trace back, depth:  1
0000 0000 0000 002A    sub that causes a segv

END
 }

#latest:
if (1) {                                                                        # R11 being disturbed by syscall 1
  Push 0x0a61;                                                                  # A followed by new line on the stack
  Mov  rax, rsp;
  Mov  rdx, 2;                                                                  # Length of string
  Mov  rsi, rsp;                                                                # Address of string
  Mov  rax, 1;                                                                  # Write
  Mov  rdi, 1;                                                                  # File descriptor
  Syscall;
  Pushfq;
  Pop rax;
  PrintOutRegisterInHex rax, r11;
  ok Assemble(debug => 0, keep2=>'z', emulator => 0, eq => <<END, avx512=>0);
a
   rax: .... .... .... .2.2
   r11: .... .... .... .212
END
 }

#latest:
if (0) {                                                                        # Print the utf8 string corresponding to a lexical item
  PushR zmm0, zmm1, rax, 14, 15;
  Sub rsp, RegisterSize xmm0;;
  Mov "dword[rsp+0*4]", 0x0600001A;
  Mov "dword[rsp+1*4]", 0x0600001B;
  Mov "dword[rsp+2*4]", 0x05000001;
  Mov "dword[rsp+3*4]", 0x0600001B;
  Vmovdqu8 zmm0, "[rsp]";
  Add rsp, RegisterSize zmm0;

  Pextrw rax,  xmm0, 1;                                                         # Extract lexical type of first element
  Vpbroadcastw zmm1, ax;                                                        # Broadcast
  Vpcmpeqw k0, zmm0, zmm1;                                                      # Check extent of first lexical item up to 16
  Shr rax, 8;                                                                   # Lexical type in lowest byte

  Mov r15, 0x55555555;                                                          # Set odd positions to one where we know the match will fail
  Kmovq k1, r15;
  Korq k2, k0, k1;                                                              # Fill in odd positions

  Kmovq r15, k2;
  Not r15;                                                                      # Swap zeroes and ones
  Tzcnt r14, r15;                                                               # Trailing zero count is a factor two too big
  Shr r14, 1;                                                                   # Normalized count of number of characters int name

  Mov r15, 0xffff;                                                              # Zero out lexical type
  Vpbroadcastd zmm1, r15d;                                                      # Broadcast
  Vpandd zmm1, zmm0, zmm1;                                                      # Remove lexical type to leave index into alphabet

  Cmp rax, 6;                                                                   # Test for variable
  IfEq
  Then
   {my $va = Rutf8 "\x{1D5D4}\x{1D5D5}\x{1D5D6}\x{1D5D7}\x{1D5D8}\x{1D5D9}\x{1D5DA}\x{1D5DB}\x{1D5DC}\x{1D5DD}\x{1D5DE}\x{1D5DF}\x{1D5E0}\x{1D5E1}\x{1D5E2}\x{1D5E3}\x{1D5E4}\x{1D5E5}\x{1D5E6}\x{1D5E7}\x{1D5E8}\x{1D5E9}\x{1D5EA}\x{1D5EB}\x{1D5EC}\x{1D5ED}\x{1D5EE}\x{1D5EF}\x{1D5F0}\x{1D5F1}\x{1D5F2}\x{1D5F3}\x{1D5F4}\x{1D5F5}\x{1D5F6}\x{1D5F7}\x{1D5F8}\x{1D5F9}\x{1D5FA}\x{1D5FB}\x{1D5FC}\x{1D5FD}\x{1D5FE}\x{1D5FF}\x{1D600}\x{1D601}\x{1D602}\x{1D603}\x{1D604}\x{1D605}\x{1D606}\x{1D607}\x{1D756}\x{1D757}\x{1D758}\x{1D759}\x{1D75A}\x{1D75B}\x{1D75C}\x{1D75D}\x{1D75E}\x{1D75F}\x{1D760}\x{1D761}\x{1D762}\x{1D763}\x{1D764}\x{1D765}\x{1D766}\x{1D767}\x{1D768}\x{1D769}\x{1D76A}\x{1D76B}\x{1D76C}\x{1D76D}\x{1D76E}\x{1D76F}\x{1D770}\x{1D771}\x{1D772}\x{1D773}\x{1D774}\x{1D775}\x{1D776}\x{1D777}\x{1D778}\x{1D779}\x{1D77A}\x{1D77B}\x{1D77C}\x{1D77D}\x{1D77E}\x{1D77F}\x{1D780}\x{1D781}\x{1D782}\x{1D783}\x{1D784}\x{1D785}\x{1D786}\x{1D787}\x{1D788}\x{1D789}\x{1D78A}\x{1D78B}\x{1D78C}\x{1D78D}\x{1D78E}\x{1D78F}";
    V(loop => r14)->for(sub                                                     # Write each letter out from its position on the stack
     {my ($index, $start, $next, $end) = @_;                                    # Execute body
      $index->setReg(14);                                                       # Index stack
      ClearRegisters r15;
      Mov r15b, "[rsp+4*r14]";                                                  # Load alphabet offset from stack
      Shl r15, 2;                                                               # Each letter is 4 bytes wide in utf8
      Mov r14, $va;                                                             # Alphabet address
      Mov r14d, "[r14+r15]";                                                    # Alphabet letter as utf8
      PushR 14;                                                                 # Utf8 is on the stack and it is 4 bytes wide
      Mov rax, rsp;
      Mov rdi, 4;
      PrintOutMemory;                                                           # Print letter from stack
      PopR;
     });
    PrintOutNL;
   };

  PopR;

  ok Assemble(avx512=>1, debug => 0, eq => "𝗮𝗯\n");
 }

#latest:
if (1) {                                                                        #TNasm::X86::Variable::outCStringNL
  my $s = Rutf8 '𝝰𝝱𝝲𝝳';
  V(address => $s)->outCStringNL;

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
𝝰𝝱𝝲𝝳
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Variable::printOutMemoryInHexNL
  my $u = Rd(ord('𝝰'), ord('𝝱'), ord('𝝲'), ord('𝝳'));
  Mov rax, $u;
  my $address = V address=>rax;
  $address->printOutMemoryInHexNL(K size => 16);

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
70D7 .1.. 71D7 .1..  72D7 .1.. 73D7 .1..
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Variable::printOutMemoryInHexNL
  my $v = V var => 2;

  If  $v == 0, Then {Mov rax, 0},
  Ef {$v == 1} Then {Mov rax, 1},
  Ef {$v == 2} Then {Mov rax, 2},
               Else {Mov rax, 3};
  PrintOutRegisterInHex rax;
  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
   rax: .... .... .... ...2
END
 }

#latest:
if (1) {                                                                        #TloadRegFromMm #TsaveRegIntoMm
  Mov rax, 1; SaveRegIntoMm(zmm0, 0, rax);
  Mov rax, 2; SaveRegIntoMm(zmm0, 1, rax);
  Mov rax, 3; SaveRegIntoMm(zmm0, 2, rax);
  Mov rax, 4; SaveRegIntoMm(zmm0, 3, rax);

  LoadRegFromMm(zmm0, 0, r15);
  LoadRegFromMm(zmm0, 1, r14);
  LoadRegFromMm(zmm0, 2, r13);
  LoadRegFromMm(zmm0, 3, r12);

  PrintOutRegisterInHex ymm0, r15, r14, r13, r12;
  ok Assemble(debug => 0, trace => 1, eq => <<END, avx512=>1);
  ymm0: .... .... .... ...4  .... .... .... ...3 - .... .... .... ...2  .... .... .... ...1
   r15: .... .... .... ...1
   r14: .... .... .... ...2
   r13: .... .... .... ...3
   r12: .... .... .... ...4
END
 }

#latest:
if (1) {                                                                        #TNasm::Variable::copy  #TNasm::Variable::copyRef
  my $a = V('a', 1);
  my $r = R('r')->copyRef($a);
  my $R = R('R')->copyRef($r);

  $a->outNL;
  $r->outNL;
  $R->outNL;

  $a->copy(2);

  $a->outNL;
  $r->outNL;
  $R->outNL;

  $r->copy(3);

  $a->outNL;
  $r->outNL;
  $R->outNL;

  $R->copy(4);

  $a->outNL;
  $r->outNL;
  $R->outNL;

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
a: .... .... .... ...1
r: .... .... .... ...1
R: .... .... .... ...1
a: .... .... .... ...2
r: .... .... .... ...2
R: .... .... .... ...2
a: .... .... .... ...3
r: .... .... .... ...3
R: .... .... .... ...3
a: .... .... .... ...4
r: .... .... .... ...4
R: .... .... .... ...4
END
 }

#latest:
if (1) {                                                                        # Register expressions in parameter lists
  my $s = Subroutine
   {my ($p) = @_;
    $$p{p}->outNL;
   } parameters=>[qw(p)], name => 'test';

  $s->call(parameters=>{p => K key => 221});
  $s->call(parameters=>{p => V key => 222});
  Mov r15, 0xcc;
  $s->call(parameters=>{p => V(key => r15)});

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
p: .... .... .... ..DD
p: .... .... .... ..DE
p: .... .... .... ..CC
END
 }

#latest:
if (0) {                                                                        #TNasm::X86::Sub::dispatch
  my $p = Subroutine                                                            # Prototype subroutine to establish parameter list
   {} [qw(p)], name => 'prototype';

  my $a = Subroutine                                                            # Subroutine we are actually going to call
   {$p->variables->{p}->outNL;
   } [], name => 'actual', with => $p;

  my $d = Subroutine                                                            # Dispatcher
   {my ($p, $s) = @_;
    $a->dispatch;
    PrintOutStringNL "This should NOT happen!";
   } [], name => 'dispatch', with => $p;

  $d->call(p => 0xcc);
  PrintOutStringNL "This should happen!";

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
p: 0000 0000 0000 00CC
This should happen!
END
 }

#latest:
if (0) {                                                                        #TNasm::X86::Sub::dispatchV
  my $s = Subroutine                                                            # Containing sub
   {my ($parameters, $sub) = @_;

    my $p = Subroutine                                                          # Prototype subroutine with cascading parameter lists
     {} [qw(q)], with => $sub, name => 'prototype';

    my $a = Subroutine                                                          # Subroutine we are actually going to call with extended parameter list
     {$p->variables->{p}->outNL;
      $p->variables->{q}->outNL;
     } [], name => 'actual', with => $p;

    my $d = Subroutine                                                          # Dispatcher
     {my ($p, $s) = @_;
      $a->dispatchV($a->V);
      PrintOutStringNL "This should NOT happen!";
     } [], name => 'dispatch', with => $p;

    $d->call(q => 0xdd) ;                                                       # Extend cascading parameter list
   } [qw(p)], name => 'outer';

  $s->call(p => 0xcc);                                                          # Start cascading parameter list
  PrintOutStringNL "This should happen!";

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
p: 0000 0000 0000 00CC
q: 0000 0000 0000 00DD
This should happen!
END
 }

if (1) {                                                                        #TNasm::X86::CreateQuarks #TNasm::X86::Quarks::put
  my $a = CreateArea;
  my ($s, $l) = addressAndLengthOfConstantStringAsVariables("01234567");

  my $q = $a->CreateQuarks;
  $q->put($s, $l-$l+$_)        for 0..7;
  $q->put($s, $l-$l+$_)->outNL for 0..7;

  ok Assemble(debug => 0, mix => 0, eq => <<END, avx512=>1);
size of tree: .... .... .... ....
size of tree: .... .... .... ...1
size of tree: .... .... .... ...2
size of tree: .... .... .... ...3
size of tree: .... .... .... ...4
size of tree: .... .... .... ...5
size of tree: .... .... .... ...6
size of tree: .... .... .... ...7
END
 }

#latest:
if (0) {                                                                        #TNasm::X86::CreateQuarks #TNasm::X86::Quarks::put #TNasm::X86::Quarks::putSub #TNasm::X86::Quarks::dump #TNasm::X86::Quarks::subFromQuarkViaQuarks #TNasm::X86::Quarks::subFromQuarkNumber #TNasm::X86::Quarks::subFromShortString #TNasm::X86::Quarks::callSubFromShortString
  my $s = Subroutine33
   {my ($p, $s) = @_;
    PrintOutString "SSSS";
    $$p{p}->setReg(15);
    PrintOutRegisterInHex r15;
   } [qw(p)], name => 'ssss';

  my $t = Subroutine33
   {my ($p, $s) = @_;
    PrintOutString "TTTT";
    $$p{p}->setReg(15);
    PrintOutRegisterInHex r15;
   } [], name => 'tttt', with => $s;

  my $A = CreateArea;

  my $Q  = $A->CreateQuarks;
           $Q->put('aaaa');
           $Q->put('bbbb');
  my $Qs = $Q->put('ssss');
  my $Qt = $Q->put('tttt');

  my $q  = $A->CreateQuarks;
  my $qs = $q->putSub('ssss', $s);
  my $qt = $q->putSub('tttt', $t);

  PrintOutStringNL "Quarks";   $Q->dump;
  PrintOutStringNL "Subs";     $q->dump;

  $q->subFromQuarkViaQuarks($Q, $Qs)->outNL;
  $q->subFromQuarkViaQuarks($Q, $Qt)->outNL;
  $q->subFromQuarkNumber($qs)->outNL;
  $q->subFromQuarkNumber($qt)->outNL;

  my $cs = $q->subFromQuarkNumber($qs);
  $s->via($cs, p => 1);
  my $ct = $q->subFromQuarkNumber($qt);
  $s->via($ct, p => 2);

  $q->callSubFromQuarkNumber   (    $s, $qs, p => 0x11);
  $q->callSubFromQuarkNumber   (    $s, $qt, p => 0x22);
  $q->callSubFromQuarkViaQuarks($Q, $s, $Qs, p => 0x111);
  $q->callSubFromQuarkViaQuarks($Q, $s, $Qt, p => 0x222);

  if (1)
   {my $s = CreateShortString(0);
       $s->loadConstantString("ssss");
    $q->subFromShortString($s)->outNL;
   }

  if (1)
   {my $s = CreateShortString(0);
       $s->loadConstantString("ssss");
    $q->callSubFromShortString($t, $s, p => 3);
   }

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
Quarks
Quark : 0000 0000 0000 0000 => 0000 0000 0000 00D8 == 0000 00D8 0000 00D8   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0061 6161 6104
Quark : 0000 0000 0000 0001 => 0000 0000 0000 0198 == 0000 0198 0000 0198   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0062 6262 6204
Quark : 0000 0000 0000 0002 => 0000 0000 0000 01D8 == 0000 01D8 0000 01D8   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0073 7373 7304
Quark : 0000 0000 0000 0003 => 0000 0000 0000 0218 == 0000 0218 0000 0218   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0074 7474 7404
Subs
Quark : 0000 0000 0000 0000 => 0000 0000 0000 0318 == 0000 0318 0000 0318   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0073 7373 7300   0000 0000 4010 090C
Quark : 0000 0000 0000 0001 => 0000 0000 0000 03D8 == 0000 03D8 0000 03D8   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0000 0000 0000   0000 0074 7474 7400   0000 0000 4013 870C
sub: 0000 0000 0040 1009
sub: 0000 0000 0040 1387
sub: 0000 0000 0040 1009
sub: 0000 0000 0040 1387
SSSS   r15: 0000 0000 0000 0001
TTTT   r15: 0000 0000 0000 0002
SSSS   r15: 0000 0000 0000 0011
TTTT   r15: 0000 0000 0000 0022
SSSS   r15: 0000 0000 0000 0111
TTTT   r15: 0000 0000 0000 0222
sub: 0000 0000 0040 1009
SSSS   r15: 0000 0000 0000 0003
END
 }

#latest:
if (11) {                                                                       #TNasm::X86::Variable::clone
  my $a = V('a', 1);
  my $b = $a->clone('a');

  $_->outNL for $a, $b;

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
a: .... .... .... ...1
a: .... .... .... ...1
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::ClassifyWithInRangeAndSaveWordOffset Nasm::X86::Variable::loadZmm
  my $l = V('low',   Rd(2, 7, (0) x 14));
  my $h = V('high' , Rd(3, 9, (0) x 14));
  my $o = V('off',   Rd(2, 5, (0) x 14));
  my $u = V('utf32', Dd(2, 3, 7, 8, 9, (0) x 11));


  $l->loadZmm(0);
  $h->loadZmm(1);
  $o->loadZmm(2);

  ClassifyWithInRangeAndSaveWordOffset($u, V('size', 5), V('classification', 7));
  $u->loadZmm(3);

  PrintOutRegisterInHex zmm 0..3;

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>1);
  zmm0: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... ...7 .... ...2
  zmm1: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... ...9 .... ...3
  zmm2: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... ...5 .... ...2
  zmm3: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .7.. ...4 - .7.. ...3 .7.. ...2  .7.. ...1 .7.. ....
END
 }

#latest:
if (1) {                                                                        #TPrintOutRaxInDecNL #TPrintOutRaxRightInDec
  my $w = V width => 12;

  Mov rax, 0;
  PrintOutRaxRightInDecNL $w;

  Mov rax, 0x2a;
  PrintOutRaxRightInDecNL $w;

  Mov rax, 1;
  PrintOutRaxRightInDecNL $w;

  Mov rax, 255;
  PrintOutRaxRightInDecNL $w;

  Mov rax, 123456;
  PrintOutRaxRightInDecNL $w;

  Mov rax, 1234567890;
  PrintOutRaxRightInDecNL $w;

  Mov rax, 0x2;
  Shl rax, 16;
  Mov rdx, 0xdfdc;
  Or rax, rdx;
  Shl rax, 16;
  Mov rdx, 0x1c35;
  Or rax, rdx;
  PrintOutRaxRightInDecNL $w;

# 1C BE99 1A14
  Mov rax, 0x1c;
  Shl rax, 16;
  Mov rdx, 0xbe99;
  Or rax, rdx;
  Shl rax, 16;
  Mov rdx, 0x1a14;
  Or rax, rdx;
  PrintOutRaxInDecNL;

# 2 EE33 3961
  Mov rax, 0x2;
  Shl rax, 16;
  Mov rdx, 0xee33;
  Or rax, rdx;
  Shl rax, 16;
  Mov rdx, 0x3961;
  Or rax, rdx;
  PrintOutRaxRightInDecNL $w;

  ok Assemble avx512=>0, eq => <<END;
           0
          42
           1
         255
      123456
  1234567890
 12345678901
123456789012
 12586269025
END
 }

#latest:
if (0) {                                                                        #TNasm::X86::Variable::call Create a library file and call the code in the library file.
  my $l = "aaa.so";
  Mov rax, 0x12345678;
  Ret;

  ok Assemble library => $l;                                                    # Create the library file
  ok -e $l;

  my ($address, $size) = ReadFile $l;                                           # Read library file into memory

  Mov rax, 0;
  PrintOutRaxInHexNL;

  $address->call;                                                               # Call code in memory loaded from library file

  PrintOutRaxInHexNL;                                                           # Print value set in library

  ok Assemble avx512=>1, eq =><<END;
.... .... .... ....
.... .... 1234 5678
END
  unlink $l;
 }

#latest:
if (0) {
  unlink my $l = "aaa.so";

  PrintOutRaxInDecNL;
  Ret;
  ok Assemble library => $l;                                                    # Create the library file

  my ($address, $size) = ReadFile $l;                                           # Read library file into memory

  Mov rax, 42;
  $address->call;                                                               # Call code in memory loaded from library file

  ok Assemble avx512=>1, eq =><<END;
42
END
  unlink $l;
 }

#latest:
if (0) {
  unlink my $l = "aaa.so";

  PrintOutRaxInHexNL;
  Ret;
  ok Assemble library => $l;                                                    # Create the library file

  my ($address, $size) = ReadFile $l;                                           # Read library file into memory

  Mov rax, 42;
  $address->call;                                                               # Call code in memory loaded from library file

  ok Assemble avx512=>1, eq =><<END;
.... .... .... ..2A
END
  unlink $l;
 }

#latest:
if (0) {
  unlink my $l = "aaa.so";
  my $N = 11;
  V(n => $N)->for(sub
   {my ($index, $start, $next, $end) = @_;
    $index->outNL;
    Inc rax;
   });
  Ret;
  ok Assemble library => $l;                                                    # Create the library file

  my ($address, $size) = ReadFile $l;                                           # Read library file into memory
  Mov rax, 0;
  $address->call;                                                               # Call code in memory loaded from library file
  PrintOutRaxInDecNL;

  ok Assemble avx512=>1, eq => <<END;
index: .... .... .... ....
index: .... .... .... ...1
index: .... .... .... ...2
index: .... .... .... ...3
index: .... .... .... ...4
index: .... .... .... ...5
index: .... .... .... ...6
index: .... .... .... ...7
index: .... .... .... ...8
index: .... .... .... ...9
index: .... .... .... ...A
11
END
  unlink $l;
 }

#latest:
if (0) {
  unlink my $l = "aaa.so";
  my $N = 21;
  my $q = Rq($N);
  Mov rax, "[$q]";
  Ret;
  ok Assemble library => $l;                                                    # Create the library file


  my ($address, $size) = ReadFile $l;                                           # Read library file into memory
  Mov rax, 0;
  $address->call;                                                               # Call code in memory loaded from library file
  PrintOutRaxInDecNL;

  ok Assemble avx512=>1, eq => <<END;
$N
END
  unlink $l;
 }

#latest:
if (0) {
  unlink my $l = "library";                                                     # The name of the file containing the library

  my @s = qw(inc dup put);                                                      # Subroutine names
  my %s = map
   {my $l = Label;                                                              # Start label for subroutine
    my  $o = "qword[rsp-".(($_+1) * RegisterSize rax)."]";                      # Position of subroutine on stack
    Mov $o, $l.'-$$';                                                           # Put offset of subroutine on stack
    Add $o, r15;                                                                # The library must be called via r15 to convert the offset to the address of each subroutine

    $s[$_] => genHash("Nasm::X86::Library::Subroutine",                         # Subroutine definitions
      number  => $_ + 1,                                                        # Number of subroutine from 1
      label   => $l,                                                            # Label of subroutine
      name    => $s[$_],                                                        # Name of subroutine
      call    => undef,                                                         # Perl subroutine to call assembler subroutine
   )} keys @s;

  Ret;

  sub Nasm::X86::Library::Subroutine::gen($$)                                   # Write the code of a subroutine
   {my ($sub, $code) = @_;                                                      # Subroutine definition, asssociated code as a sub
    SetLabel $sub->label;                                                       # Start label
    &$code;                                                                     # Code of subroutine
    Ret;                                                                        # Return from sub routine
   }

  $s{inc}->gen(sub {Inc rax});                                                  # Increment rax
  $s{dup}->gen(sub {Shl rax, 1});                                               # Double rax
  $s{put}->gen(sub {PrintOutRaxInDecNL});                                       # Print rax in decimal

  ok Assemble library => $l;                                                    # Create the library file

  my ($address, $size) = ReadFile $l;                                           # Read library file into memory
  $address->call(r15);                                                          # Load addresses of subroutines onto stack

  for my $s(@s{@s})                                                             # Each subroutine
   {Mov r15, "[rsp-".(($s->number + 1) * RegisterSize rax)."]";                 # Address of subroutine in this process
    $s->call = V $s->name => r15;                                               # Address of subroutine in this process from stack as a variable
   }
  my ($inc, $dup, $put) = map {my $c = $_->call; sub {$c->call}} @s{@s};        # Call subroutine via variable - perl bug because $_ by  itself is not enough

   Mov rax, 1; &$put;
#  &$inc;      &$put;                                                           # Use the subroutines from the library
#  &$dup;      &$put;
#  &$dup;      &$put;
#  &$inc;      &$put;

  ok Assemble eq => <<END, avx512=>0;
1
2
4
8
9
END
  unlink $l;
 }

#latest:
if (1) {                                                                        #TreadChar #TPrintOutRaxAsChar
  my $e = q(readChar);

  ForEver
   {my ($start, $end) = @_;
    ReadChar;
    Cmp rax, 0xa;
    Jle $end;
    PrintOutRaxAsChar;
    PrintOutRaxAsChar;
   };
  PrintOutNL;

  Assemble keep => $e;

  is_deeply qx(echo "ABCDCBA" | ./$e), <<END;
AABBCCDDCCBBAA
END
  unlink $e;
 }

#latest:
if (1) {                                                                        #TPrintOutRaxAsTextNL
  my $t = Rs('abcdefghi');
  Mov rax, $t;
  Mov rax, "[rax]";
  PrintOutRaxAsTextNL;
  ok Assemble eq => <<END, avx512=>0;
abcdefgh
END
}

#latest:
if (1) {                                                                        #TNasm::X86::Variable::outCStringNL #TNasm::X86::Variable::outInDecNL;
  my $e = q(parameters);

  (V string => "[rbp+8]")->outInDecNL;
  (V string => "[rbp+16]")->outCStringNL;
  (V string => "[rbp+24]")->outCStringNL;
  (V string => "[rbp+32]")->outCStringNL;
  (V string => "[rbp+40]")->outCStringNL;
  (V string => "[rbp+48]")->outInDecNL;

  (V string => "[rbp+8]")->for(sub
   {my ($index, $start, $next, $end) = @_;
    $index->setReg(rax);
    Inc rax;
    PrintOutRaxInDec;
    Inc rax;
    PrintOutString " : ";
    Shl rax, 3;
    (V string => "[rbp+rax]")->outCStringNL;
   });

  Assemble keep => $e;

  is_deeply scalar(qx(./$e AaAaAaAaAa BbCcDdEe 123456789)), <<END;
string: 4
./parameters
AaAaAaAaAa
BbCcDdEe
123456789
string: 0
1 : ./parameters
2 : AaAaAaAaAa
3 : BbCcDdEe
4 : 123456789
END

  unlink $e;
 }

#latest:
if (1) {                                                                        #TPrintOutRaxAsTextNL
  V( loop => 16)->for(sub
   {my ($index, $start, $next, $end) = @_;
    $index->setReg(rax);
    Add rax, 0xb0;   Shl rax, 16;
    Mov  ax, 0x9d9d; Shl rax, 8;
    Mov  al, 0xf0;
    PrintOutRaxAsText;
   });
  PrintOutNL;

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
𝝰𝝱𝝲𝝳𝝴𝝵𝝶𝝷𝝸𝝹𝝺𝝻𝝼𝝽𝝾𝝿
END
 }

#latest:
if (1) {                                                                        #TPrintOutRaxRightInDec #TPrintOutRaxRightInDecNL
  Mov rax, 0x2a;
  PrintOutRaxRightInDec   V width=> 4;
  Shl rax, 1;
  PrintOutRaxRightInDecNL V width=> 6;

  ok Assemble eq => <<END, avx512=>0;
  42    84
END
 }

#latest:
if (1) {                                                                        # Fibonacci numbers
  my $N = 11;                                                                   # The number of Fibonacci numbers to generate
  Mov r13, 0;                                                                   # First  Fibonacci number
  Mov r14, 1;                                                                   # Second Fibonacci
  PrintOutStringNL " i   Fibonacci";                                            # The title of the piece

  V(N => $N)->for(sub                                                           # Generate each Fibonacci number by adding the two previous ones together
   {my ($index, $start, $next, $end) = @_;
    $index->outRightInDec(V(width => 2));                                       # Index
    Mov rax, r13;
    PrintOutRaxRightInDecNL V width => 12;                                      # Fibonacci number at this index

    Mov r15, r14;                                                               # Next number is the sum of the two previous ones
    Add r15, r13;

    Mov r13, r14;                                                               # Move up
    Mov r14, r15;
   });

  ok Assemble eq => <<END, avx512=>0;
 i   Fibonacci
 0           0
 1           1
 2           1
 3           2
 4           3
 5           5
 6           8
 7          13
 8          21
 9          34
10          55
END
 }

#latest:
if (1) {                                                                        #TReadLine
  my $e = q(readLine);
  my $f = writeTempFile("hello\nworld\n");

  ReadLine;
  PrintOutRaxAsTextNL;
  ReadLine;
  PrintOutRaxAsTextNL;

  Assemble keep => $e;

  is_deeply scalar(qx(./$e < $f)), <<END;
hello
world
END
  unlink $f;
}

#latest:
if (1) {                                                                        #TReadInteger
  my $e = q(readInteger);
  my $f = writeTempFile("11\n22\n");

  ReadInteger;
  Shl rax, 1;
  PrintOutRaxInDecNL;
  ReadInteger;
  Shl rax, 1;
  PrintOutRaxInDecNL;

  Assemble keep => $e;

  is_deeply scalar(qx(./$e < $f)), <<END;
22
44
END

  unlink $e, $f;
 }

#latest:
if (1) {                                                                        #TSubroutine2
  package InnerStructure
   {use Data::Table::Text qw(:all);
    sub new($)                                                                  # Create a new structure
     {my ($value) = @_;                                                         # Value for structure variable
      describe(value => Nasm::X86::V(var => $value))
     };
    sub describe(%)                                                             # Describe the components of a structure
     {my (%options) = @_;                                                       # Options
      genHash(__PACKAGE__,
        value => $options{value},
       );
     }
   }

  package OuterStructure
   {use Data::Table::Text qw(:all);
    sub new($$)                                                                 # Create a new structure
     {my ($valueOuter, $valueInner) = @_;                                       # Value for structure variable
      describe
       (value => Nasm::X86::V(var => $valueOuter),
        inner => InnerStructure::new($valueInner),
       )
     };
    sub describe(%)                                                             # Describe the components of a structure
     {my (%options) = @_;                                                       # Options
      genHash(__PACKAGE__,
        value => $options{value},
        inner => $options{inner},
       );
     }
   }

  my $t = OuterStructure::new(42, 4);

  my $s = Subroutine
   {my ($parameters, $structures, $sub) = @_;                                   # Variable parameters, structure variables, structure copies, subroutine description

    $$structures{test}->value->setReg(rax);
    Mov r15, 84;
    $$structures{test}->value->getReg(r15);
    Mov r15, 8;
    $$structures{test}->inner->value->getReg(r15);

    $$parameters{p}->setReg(rdx);
   } parameters=>[qw(p)], structures => {test => $t}, name => 'test';

  my $T = OuterStructure::new(42, 4);
  my $V = V parameter => 21;

  $s->call(parameters=>{p => $V}, structures=>{test => $T});

  PrintOutRaxInDecNL;
  Mov rax, rdx;
  PrintOutRaxInDecNL;
  $t->value->outInDecNL;
  $t->inner->value->outInDecNL;
  $T->value->outInDecNL;
  $T->inner->value->outInDecNL;
  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
42
21
var: 42
var: 4
var: 84
var: 8
END
 }

#latest:
if (1) {
  my $s = Subroutine                                                            #TSubroutine2
   {my ($p, $s, $sub) = @_;                                                     # Variable parameters, structure variables, structure copies, subroutine description
    $$s{var}->setReg(rax);
    Dec rax;
    $$s{var}->getReg(rax);
   } structures => {var => my $v = V var => 42}, name => 'test';

  $v->outNL;

  $s->call(structures => {var => my $V = V var => 2});
  $V->outNL;

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
var: .... .... .... ..2A
var: .... .... .... ...1
END
 }

#latest:
if (1) {
  my $N = 256;
  my $t = V struct => 33;

  my $s = Subroutine                                                            #TSubroutine
   {my ($p, $s, $sub) = @_;                                                     # Variable parameters, structure variables, structure copies, subroutine description
    SaveFirstFour;
    my $v = V var => 0;
    $v->copy($$p{i});
    $$p{o}->copy($v);
    $$p{O}->copy($$s{struct});
    $$s{struct}->copy($$s{struct} + 1);

    my $M = AllocateMemory K size => $N;                                        # Allocate memory and save its location in a variable
    $$p{M}->copy($M);
    $M->setReg(rax);
    Mov "qword[rax]", -1;
    FreeMemory $M, K size => $N;                                                # Free memory
    RestoreFirstFour;
   } structures => {struct => $t}, parameters => [qw(i o O M)], name => 'test';

  $s->call(parameters => {i => (my $i = K i => 22),
                          o => (my $o = V o =>  0),
                          O => (my $O = V O =>  0),
                          M => (my $M = V M =>  0)},
           structures => {struct => $t});
  $i->outInDecNL;
  $o->outInDecNL;
  $O->outInDecNL;
  $t->outInDecNL;

  ok Assemble(debug => 0, trace => 0, eq => <<END, avx512=>0);
i: 22
o: 22
O: 33
struct: 34
END
 }

#latest:
if (1) {                                                                        # Split a left node held in zmm28..zmm26 with its parent in zmm31..zmm29 pushing to the right zmm25..zmm23
  my $newRight = K newRight => 0x9119;                                          # Offset of new right block
  my $tree = DescribeTree(length => 3);                                         # Test with a narrow tree
  my ($RN, $RD, $RK, $LN, $LD, $LK, $PN, $PD, $PK) = 23..31;                    # Zmm names
  my $transfer = r8;

  for my $test(0..13)                                                           # Test each key position
   {PrintOutStringNL "Test $test";

    K(PK => Rd(map {($_<<28) +0x9999999} 1..15, 0))->loadZmm($PK);
    K(PD => Rd(map {($_<<28) +0x7777777} 1..15, 0))->loadZmm($PD);
    K(PN => Rd(map {($_<<28) +0x8888888} 1..15, 0))->loadZmm($PN);

    K(LK => Rd(map {($_<<28) +0x6666666} $test..15, 0..($test-1)))->loadZmm($LK);
    K(LD => Rd(map {($_<<28) +0x4444444} $test..15, 0..($test-1)))->loadZmm($LD);
    K(LN => Rd(map {($_<<28) +0x5555555} 0..15))->loadZmm($LN);

    K(RK => Rd(map {($_<<28) +0x3333333} 0..15))->loadZmm($RK);
    K(RD => Rd(map {($_<<28) +0x1111111} 0..15))->loadZmm($RD);
    K(RN => Rd(map {($_<<28) +0x2222222} 0..15))->loadZmm($RN);

    Mov $transfer, 0;                                                           # Test set of tree bits
    wRegIntoZmm $transfer, $PK, $tree->treeBits;

    Mov $transfer, 1;                                                           # Test set of parent length
    wRegIntoZmm $transfer, $PK, $tree->lengthOffset;

    Mov $transfer, 0b11011101;                                                  # Test set of tree bits in node being split
    wRegIntoZmm $transfer, $LK, $tree->treeBits;

    $tree->splitNotRoot($newRight, reverse 23..31);

    PrintOutStringNL "Parent";
    PrintOutRegisterInHex zmm reverse 29..31;

    PrintOutStringNL "Left";
    PrintOutRegisterInHex zmm reverse 26..28;

    PrintOutStringNL "Right";
    PrintOutRegisterInHex zmm reverse 23..25;
   }

  ok Assemble eq => <<END, avx512=>1;
Test 0
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  1999 9999 1666 6666
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  1777 7777 1444 4444
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 2888 8888  .... 9119 1888 8888
Left
 zmm28: F666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .666 6666
 zmm27: F444 4444 E444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 2666 6666
 zmm24: F111 1111 E444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 2444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
Test 1
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  2666 6666 1999 9999
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  2444 4444 1777 7777
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 .... 9119  2888 8888 1888 8888
Left
 zmm28: .666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 1666 6666
 zmm27: .444 4444 F444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 1444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 3666 6666
 zmm24: F111 1111 F444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 3444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
Test 2
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  3666 6666 1999 9999
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  3444 4444 1777 7777
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 .... 9119  2888 8888 1888 8888
Left
 zmm28: 1666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 2666 6666
 zmm27: 1444 4444 .444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 2444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 4666 6666
 zmm24: F111 1111 .444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 4444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
Test 3
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  4666 6666 1999 9999
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  4444 4444 1777 7777
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 .... 9119  2888 8888 1888 8888
Left
 zmm28: 2666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 3666 6666
 zmm27: 2444 4444 1444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 3444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 5666 6666
 zmm24: F111 1111 1444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 5444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
Test 4
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  5666 6666 1999 9999
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  5444 4444 1777 7777
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 .... 9119  2888 8888 1888 8888
Left
 zmm28: 3666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 4666 6666
 zmm27: 3444 4444 2444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 4444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 6666 6666
 zmm24: F111 1111 2444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 6444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
Test 5
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  6666 6666 1999 9999
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  6444 4444 1777 7777
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 .... 9119  2888 8888 1888 8888
Left
 zmm28: 4666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 5666 6666
 zmm27: 4444 4444 3444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 5444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 7666 6666
 zmm24: F111 1111 3444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 7444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
Test 6
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  7666 6666 1999 9999
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  7444 4444 1777 7777
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 .... 9119  2888 8888 1888 8888
Left
 zmm28: 5666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 6666 6666
 zmm27: 5444 4444 4444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 6444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 8666 6666
 zmm24: F111 1111 4444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 8444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
Test 7
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  8666 6666 1999 9999
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  8444 4444 1777 7777
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 .... 9119  2888 8888 1888 8888
Left
 zmm28: 6666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 7666 6666
 zmm27: 6444 4444 5444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 7444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 9666 6666
 zmm24: F111 1111 5444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 9444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
Test 8
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  9666 6666 1999 9999
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  9444 4444 1777 7777
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 .... 9119  2888 8888 1888 8888
Left
 zmm28: 7666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 8666 6666
 zmm27: 7444 4444 6444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 8444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... A666 6666
 zmm24: F111 1111 6444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... A444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
Test 9
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  A666 6666 1999 9999
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  A444 4444 1777 7777
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 .... 9119  2888 8888 1888 8888
Left
 zmm28: 8666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 9666 6666
 zmm27: 8444 4444 7444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 9444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... B666 6666
 zmm24: F111 1111 7444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... B444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
Test 10
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  B666 6666 1999 9999
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  B444 4444 1777 7777
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 .... 9119  2888 8888 1888 8888
Left
 zmm28: 9666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... A666 6666
 zmm27: 9444 4444 8444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... A444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... C666 6666
 zmm24: F111 1111 8444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... C444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
Test 11
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  C666 6666 1999 9999
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  C444 4444 1777 7777
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 .... 9119  2888 8888 1888 8888
Left
 zmm28: A666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... B666 6666
 zmm27: A444 4444 9444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... B444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... D666 6666
 zmm24: F111 1111 9444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... D444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
Test 12
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  D666 6666 1999 9999
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  D444 4444 1777 7777
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 .... 9119  2888 8888 1888 8888
Left
 zmm28: B666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... C666 6666
 zmm27: B444 4444 A444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... C444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... E666 6666
 zmm24: F111 1111 A444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... E444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
Test 13
Parent
 zmm31: .999 9999 .... ...2  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  E666 6666 1999 9999
 zmm30: .777 7777 F777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  E444 4444 1777 7777
 zmm29: .888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 .... 9119  2888 8888 1888 8888
Left
 zmm28: C666 6666 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... D666 6666
 zmm27: C444 4444 B444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... D444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  1555 5555 .555 5555
Right
 zmm25: F333 3333 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... F666 6666
 zmm24: F111 1111 B444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... F444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  3555 5555 2555 5555
END
 }

#latest:
if (1) {                                                                        # Split a root node held in zmm28..zmm26 into a parent in zmm31..zmm29 and a right node held in zmm25..zmm23
  my $newLeft   = K newLeft  => 0x9119;                                         # Offset of new left  block
  my $newRight  = K newRight => 0x9229;                                         # Offset of new right block
  my $tree      = DescribeTree(length => 7);                                    # Tree definition

  my $transfer  = r8;                                                           # Transfer register
  my ($RN, $RD, $RK, $LN, $LD, $LK, $PN, $PD, $PK) = 23..31;                    # Zmm names

  K(PK => Rd(map {($_<<28) +0x9999999} 0..15))->loadZmm($PK);
  K(PD => Rd(map {($_<<28) +0x7777777} 0..15))->loadZmm($PD);
  K(PN => Rd(map {($_<<28) +0x8888888} 0..15))->loadZmm($PN);

  K(LK => Rd(map {($_<<28) +0x6666666} 0..15))->loadZmm($LK);
  K(LD => Rd(map {($_<<28) +0x4444444} 0..15))->loadZmm($LD);
  K(LN => Rd(map {($_<<28) +0x5555555} 0..15))->loadZmm($LN);

  K(RK => Rd(map {($_<<28) +0x3333333} 0..15))->loadZmm($RK);
  K(RD => Rd(map {($_<<28) +0x1111111} 0..15))->loadZmm($RD);
  K(RN => Rd(map {($_<<28) +0x2222222} 0..15))->loadZmm($RN);

  Mov $transfer, 0b11011101;                                                    # Test set of tree bits
  wRegIntoZmm $transfer, $LK, $tree->treeBits;

  Mov $transfer, 7;                                                             # Test set of length in left keys
  wRegIntoZmm $transfer, $LK, $tree->lengthOffset;
  PrintOutStringNL "Initial Parent";
  PrintOutRegisterInHex zmm reverse 29..31;

  PrintOutStringNL "Initial Left";
  PrintOutRegisterInHex zmm reverse 26..28;

  PrintOutStringNL "Initial Right";
  PrintOutRegisterInHex zmm reverse 23..25;

  $tree->splitRoot($newLeft, $newRight, reverse 23..31);

  PrintOutStringNL "Final Parent";
  PrintOutRegisterInHex zmm reverse 29..31;

  PrintOutStringNL "Final Left";
  PrintOutRegisterInHex zmm reverse 26..28;

  PrintOutStringNL "Final Right";
  PrintOutRegisterInHex zmm reverse 23..25;

  ok Assemble eq => <<END, avx512=>1;
Initial Parent
 zmm31: F999 9999 E999 9999  D999 9999 C999 9999 - B999 9999 A999 9999  9999 9999 8999 9999 + 7999 9999 6999 9999  5999 9999 4999 9999 - 3999 9999 2999 9999  1999 9999 .999 9999
 zmm30: F777 7777 E777 7777  D777 7777 C777 7777 - B777 7777 A777 7777  9777 7777 8777 7777 + 7777 7777 6777 7777  5777 7777 4777 7777 - 3777 7777 2777 7777  1777 7777 .777 7777
 zmm29: F888 8888 E888 8888  D888 8888 C888 8888 - B888 8888 A888 8888  9888 8888 8888 8888 + 7888 8888 6888 8888  5888 8888 4888 8888 - 3888 8888 2888 8888  1888 8888 .888 8888
Initial Left
 zmm28: F666 6666 ..DD ...7  D666 6666 C666 6666 - B666 6666 A666 6666  9666 6666 8666 6666 + 7666 6666 6666 6666  5666 6666 4666 6666 - 3666 6666 2666 6666  1666 6666 .666 6666
 zmm27: F444 4444 E444 4444  D444 4444 C444 4444 - B444 4444 A444 4444  9444 4444 8444 4444 + 7444 4444 6444 4444  5444 4444 4444 4444 - 3444 4444 2444 4444  1444 4444 .444 4444
 zmm26: F555 5555 E555 5555  D555 5555 C555 5555 - B555 5555 A555 5555  9555 5555 8555 5555 + 7555 5555 6555 5555  5555 5555 4555 5555 - 3555 5555 2555 5555  1555 5555 .555 5555
Initial Right
 zmm25: F333 3333 E333 3333  D333 3333 C333 3333 - B333 3333 A333 3333  9333 3333 8333 3333 + 7333 3333 6333 3333  5333 3333 4333 3333 - 3333 3333 2333 3333  1333 3333 .333 3333
 zmm24: F111 1111 E111 1111  D111 1111 C111 1111 - B111 1111 A111 1111  9111 1111 8111 1111 + 7111 1111 6111 1111  5111 1111 4111 1111 - 3111 1111 2111 1111  1111 1111 .111 1111
 zmm23: F222 2222 E222 2222  D222 2222 C222 2222 - B222 2222 A222 2222  9222 2222 8222 2222 + 7222 2222 6222 2222  5222 2222 4222 2222 - 3222 2222 2222 2222  1222 2222 .222 2222
Final Parent
 zmm31: F999 9999 ...1 ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 3666 6666
 zmm30: F777 7777 E777 7777  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... 3444 4444
 zmm29: F888 8888 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... 9229 .... 9119
Final Left
 zmm28: F666 6666 ...5 ...3  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... 2666 6666  1666 6666 .666 6666
 zmm27: F444 4444 E444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... 2444 4444  1444 4444 .444 4444
 zmm26: F555 5555 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - 3555 5555 2555 5555  1555 5555 .555 5555
Final Right
 zmm25: F333 3333 ...5 ...3  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... 6666 6666  5666 6666 4666 6666
 zmm24: F111 1111 E444 4444  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... 6444 4444  5444 4444 4444 4444
 zmm23: F222 2222 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - 7555 5555 6555 5555  5555 5555 4555 5555
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::setTree  #TNasm::X86::Tree::clearTree #TNasm::X86::Tree::insertZeroIntoTreeBits #TNasm::X86::Tree::insertOneIntoTreeBits #TNasm::X86::Tree::getTreeBits #TNasm::X86::Tree::setTreeBits #TNasm::X86::Tree::isTree

  my $t = DescribeTree;
  Mov r8, 0b100; $t->setTreeBit(31, r8);              PrintOutRegisterInHex 31;
  Mov r8, 0b010; $t->setTreeBit(31, r8);              PrintOutRegisterInHex 31;
  Mov r8, 0b001; $t->setTreeBit(31, r8);              PrintOutRegisterInHex 31;
  Mov r8, 0b010; $t->clearTreeBit(31, r8);            PrintOutRegisterInHex 31;

                                                     $t->getTreeBits(31, r8); V(TreeBits => r8)->outRightInBinNL(K width => 16);
  Mov r8, 0b010; $t->insertZeroIntoTreeBits(31, r8); $t->getTreeBits(31, r8); V(TreeBits => r8)->outRightInBinNL(K width => 16);
  Mov r8, 0b010; $t->insertOneIntoTreeBits (31, r8); $t->getTreeBits(31, r8); V(TreeBits => r8)->outRightInBinNL(K width => 16);

  $t->getTreeBits(31, r8);
  V(TreeBits => r8)->outRightInHexNL(K width => 4);
  PrintOutRegisterInHex 31;

  Mov r8, 1; $t->isTree(31, r8); PrintOutZF;
  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;
  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;
  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;

  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;
  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;
  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;
  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;

  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;
  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;
  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;
  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;

  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;
  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;
  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;
  Shl r8, 1; $t->isTree(31, r8); PrintOutZF;

  Not r8; $t->setTreeBits(31, r8); PrintOutRegisterInHex 31;

  ok Assemble eq => <<END, avx512=>1;
 zmm31: .... .... ...4 ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
 zmm31: .... .... ...6 ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
 zmm31: .... .... ...7 ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
 zmm31: .... .... ...5 ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
             101
            1001
           10011
  13
 zmm31: .... .... ..13 ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
ZF=0
ZF=0
ZF=1
ZF=1
ZF=0
ZF=1
ZF=1
ZF=1
ZF=1
ZF=1
ZF=1
ZF=1
ZF=1
ZF=1
ZF=1
ZF=1
 zmm31: .... .... 3FFF ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::allocBlock #TNasm::X86::Tree::putBlock #TNasm::X86::Tree::getBlock #TNasm::X86::Tree::root
  my $a = CreateArea;
  my $t = $a->CreateTree;
  my $b = $t->allocBlock(31, 30, 29);
  K(data => 0x33)->dIntoZ(31, 4);
  $t->lengthIntoKeys(31, K length =>0x9);
  $t->putBlock($b, 31, 30, 29);
  $t->getBlock($b, 25, 24, 23);
  PrintOutRegisterInHex 25;
  $t->lengthFromKeys(25)->outNL;


  $t->firstFromMemory(28);
  $t->incSizeInFirst (28);
  $t->rootIntoFirst  (28, K value => 0x2222);
  $t->root           (28, K value => 0x2222);  PrintOutZF;
  $t->root           (28, K value => 0x2221);  PrintOutZF;
  $t->root           (28, K value => 0x2222);  PrintOutZF;
  $t->firstIntoMemory(28);

  $t->first->outNL;
  $b->outNL;
  $a->dump("1111");
  PrintOutRegisterInHex 31, 30, 29, 28;

  If $t->leafFromNodes(29) > 0, Then {PrintOutStringNL "29 Leaf"}, Else {PrintOutStringNL "29 Branch"};
  If $t->leafFromNodes(28) > 0, Then {PrintOutStringNL "28 Leaf"}, Else {PrintOutStringNL "28 Branch"};


  ok Assemble eq => <<END, avx512=>1;
 zmm25: .... ..C0 .... ...9  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... ..33 .... ....
b at offset 56 in zmm25: .... .... .... ...9
ZF=1
ZF=0
ZF=1
first: .... .... .... ..40
address: .... .... .... ..80
1111
Area     Size:     4096    Used:      320
.... .... .... .... | __10 ____ ____ ____  40.1 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | 2222 ____ ____ ____  .1__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | ____ ____ 33__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .9__ ____ C0__ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ __.1 ____
 zmm31: .... ..C0 .... ...9  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... ..33 .... ....
 zmm30: .... .1.. .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
 zmm29: .... ..40 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
 zmm28: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ...1  .... .... .... 2222
29 Leaf
28 Branch
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::indexEq
  my $tree = DescribeTree(length => 7);

  my $K = 31;

  K(K => Rd(0..15))->loadZmm($K);
  $tree->lengthIntoKeys($K, K length => 13);

  K(loop => 16)->for(sub
   {my ($index, $start, $next, $end) = @_;
    my $f = $tree->indexEq ($index, $K);
    $index->outRightInDec(K width =>  2);
    $f    ->outRightInBin(K width => 14);
    PrintOutStringNL " |"
   });

  ok Assemble eq => <<END, avx512=>1;
 0             1 |
 1            10 |
 2           100 |
 3          1000 |
 4         10000 |
 5        100000 |
 6       1000000 |
 7      10000000 |
 8     100000000 |
 9    1000000000 |
10   10000000000 |
11  100000000000 |
12 1000000000000 |
13               |
14               |
15               |
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::insertionPoint
  my $tree = DescribeTree(length => 7);

  my $K = 31;

  K(K => Rd(map {2*$_} 1..16))->loadZmm($K);
  $tree->lengthIntoKeys($K, K length => 13);

  K(loop => 32)->for(sub
   {my ($index, $start, $next, $end) = @_;
    my $f = $tree->insertionPoint($index, $K);
    $index->outRightInDec(K width =>  2);
    $f    ->outRightInBin(K width => 16);
    PrintOutStringNL " |"
   });

  ok Assemble eq => <<END, avx512=>1;
 0               1 |
 1               1 |
 2              10 |
 3              10 |
 4             100 |
 5             100 |
 6            1000 |
 7            1000 |
 8           10000 |
 9           10000 |
10          100000 |
11          100000 |
12         1000000 |
13         1000000 |
14        10000000 |
15        10000000 |
16       100000000 |
17       100000000 |
18      1000000000 |
19      1000000000 |
20     10000000000 |
21     10000000000 |
22    100000000000 |
23    100000000000 |
24   1000000000000 |
25   1000000000000 |
26  10000000000000 |
27  10000000000000 |
28  10000000000000 |
29  10000000000000 |
30  10000000000000 |
31  10000000000000 |
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Variable::dFromPointInZ
  my $tree = DescribeTree(length => 7);

  my $K = 31;

  K(K => Rd(0..15))->loadZmm($K);

  PrintOutRegisterInHex zmm $K;
  K( offset => 1 << 5)->dFromPointInZ($K)->outNL;

  ok Assemble eq => <<END, avx512=>1;
 zmm31: .... ...F .... ...E  .... ...D .... ...C - .... ...B .... ...A  .... ...9 .... ...8 + .... ...7 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
d: .... .... .... ...5
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::indexEq
  my $tree = DescribeTree();
  $tree->maskForFullKeyArea(7);                                                 # Mask for full key area
  PrintOutRegisterInHex k7;
  $tree->maskForFullNodesArea(7);                                               # Mask for full nodes area
  PrintOutRegisterInHex k7;
  ok Assemble eq => <<END, avx512=>1;
    k7: .... .... .... 3FFF
    k7: .... .... .... 7FFF
END
 }

#latest:
if (1) {                                                                        # Perform the insertion
  my $tree = DescribeTree();

  my $F = 31; my $K  = 30; my $D = 29;
  my $IK = K insert  => 0x44;
  my $ID = K insert  => 0x55;
  my $tb = K treebit => 1;                                                      # Value to insert, tree bit to insert

  K(K => Rd(0..15))->loadZmm($_) for $F, $K, $D;                                # First, keys, data
  $tree->lengthIntoKeys($K, K length => 5);                                     # Set a length
  Mov rdi, 0x3FF0;                                                              # Initial tree bits
  $tree->setTreeBits(31, rdi);                                                  # Save tree bits

  my $point = K point => 1<<3;                                                  # Show insertion point

  PrintOutStringNL "Start";
  PrintOutRegisterInHex $F, $K, $D;

  $tree->insertKeyDataTreeIntoLeaf($point, $F, $K, $D, $IK, $ID, K subTree => 1);

  PrintOutStringNL "Inserted";
  PrintOutRegisterInHex $F, $K, $D;

  $tree->overWriteKeyDataTreeInLeaf($point, $K, $D, $ID, $IK, K subTree => 0);

  PrintOutStringNL "Overwritten";
  PrintOutRegisterInHex $F, $K, $D;

  ok Assemble eq => <<END, avx512=>1;                                           # Once we know the insertion point we can add the key/data/subTree triple, increase the length and update the tree bits
Start
 zmm31: .... ...F 3FF0 ...E  .... ...D .... ...C - .... ...B .... ...A  .... ...9 .... ...8 + .... ...7 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
 zmm30: .... ...F .... ...5  .... ...D .... ...C - .... ...B .... ...A  .... ...9 .... ...8 + .... ...7 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
 zmm29: .... ...F .... ...E  .... ...D .... ...C - .... ...B .... ...A  .... ...9 .... ...8 + .... ...7 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
Inserted
 zmm31: .... ...F 3FF0 ...E  .... ...D .... ...C - .... ...B .... ...A  .... ...9 .... ...8 + .... ...7 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...3  .... ...1 .... ....
 zmm30: .... ...F ...8 ...6  .... ...C .... ...B - .... ...A .... ...9  .... ...8 .... ...7 + .... ...6 .... ...5  .... ...4 .... ...3 - .... ..44 .... ...2  .... ...1 .... ....
 zmm29: .... ...F .... ...E  .... ...C .... ...B - .... ...A .... ...9  .... ...8 .... ...7 + .... ...6 .... ...5  .... ...4 .... ...3 - .... ..55 .... ...2  .... ...1 .... ....
Overwritten
 zmm31: .... ...F 3FF0 ...E  .... ...D .... ...C - .... ...B .... ...A  .... ...9 .... ...8 + .... ...7 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...3  .... ...1 .... ....
 zmm30: .... ...F .... ...6  .... ...C .... ...B - .... ...A .... ...9  .... ...8 .... ...7 + .... ...6 .... ...5  .... ...4 .... ...3 - .... ..55 .... ...2  .... ...1 .... ....
 zmm29: .... ...F .... ...E  .... ...C .... ...B - .... ...A .... ...9  .... ...8 .... ...7 + .... ...6 .... ...5  .... ...4 .... ...3 - .... ..44 .... ...2  .... ...1 .... ....
END
 }

#latest:
if (1) {
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);

  $a->dump("0000", K depth => 6);
  $t->dump("0000");

  $t->put(K(key=>1), K(data=>0x11));
  $a->dump("1111", K depth => 6);
  $t->dump("1111");

  $t->put(K(key=>2), K(data=>0x22));
  $a->dump("2222", K depth => 6);
  $t->dump("2222");

  $t->put(K(key=>3), K(data=>0x33));
  $a->dump("3333", K depth => 6);
  $t->dump("3333");

  $t->splitNode(K offset => 0x80);
  $a->dump("4444", K depth => 11);
  $t->dump("4444");

  ok Assemble eq => <<END, avx512=>1;
0000
Area     Size:     4096    Used:      128
.... .... .... .... | __10 ____ ____ ____  80__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... .1.. | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... .140 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
0000
- empty
1111
Area     Size:     4096    Used:      320
.... .... .... .... | __10 ____ ____ ____  40.1 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | 80__ ____ ____ ____  .1__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | .1__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ C0__ ____
.... .... .... ..C0 | 11__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ __.1 ____
.... .... .... .1.. | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .140 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
1111
At:   80                    length:    1,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0
  Keys :    1
  Data :   17
end
2222
Area     Size:     4096    Used:      320
.... .... .... .... | __10 ____ ____ ____  40.1 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | 80__ ____ ____ ____  .2__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | .1__ ____ .2__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .2__ ____ C0__ ____
.... .... .... ..C0 | 11__ ____ 22__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ __.1 ____
.... .... .... .1.. | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .140 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
2222
At:   80                    length:    2,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0    1
  Keys :    1    2
  Data :   17   34
end
3333
Area     Size:     4096    Used:      320
.... .... .... .... | __10 ____ ____ ____  40.1 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | 80__ ____ ____ ____  .3__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | .1__ ____ .2__ ____  .3__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .3__ ____ C0__ ____
.... .... .... ..C0 | 11__ ____ 22__ ____  33__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ __.1 ____
.... .... .... .1.. | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .140 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
3333
At:   80                    length:    3,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0    1    2
  Keys :    1    2    3
  Data :   17   34   51
end
4444
Area     Size:     4096    Used:      704
.... .... .... .... | __10 ____ ____ ____  C0.2 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | __.2 ____ ____ ____  .3__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | .1__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ C0__ ____
.... .... .... ..C0 | 11__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ __.1 ____
.... .... .... .1.. | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .140 | .3__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ 80.1 ____
.... .... .... .180 | 33__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ C0.1 ____
.... .... .... .1C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .2.. | .2__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ 40.2 ____
.... .... .... .240 | 22__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 80.2 ____
.... .... .... .280 | 80__ ____ 40.1 ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
4444
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :   34
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :   17
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    3
      Data :   51
    end
end
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::put
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);

  $t->put(K(key=>1), K(data=>0x11));
  $t->put(K(key=>2), K(data=>0x22));
  $t->put(K(key=>3), K(data=>0x33));
  $t->put(K(key=>4), K(data=>0x44));
  $a->dump("4444", K depth => 11);
  $t->dump("4444");

  ok Assemble eq => <<END, avx512=>1;
4444
Area     Size:     4096    Used:      704
.... .... .... .... | __10 ____ ____ ____  C0.2 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | __.2 ____ ____ ____  .4__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | .1__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ C0__ ____
.... .... .... ..C0 | 11__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ __.1 ____
.... .... .... .1.. | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .140 | .3__ ____ .4__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .2__ ____ 80.1 ____
.... .... .... .180 | 33__ ____ 44__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ C0.1 ____
.... .... .... .1C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .2.. | .2__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ 40.2 ____
.... .... .... .240 | 22__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 80.2 ____
.... .... .... .280 | 80__ ____ 40.1 ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
4444
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :   34
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :   17
    end
    At:  140                length:    2,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    3    4
      Data :   51   68
    end
end
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::put
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);

  $t->put(K(key=>1), K(data=>0x11));
  $t->put(K(key=>2), K(data=>0x22));
  $t->put(K(key=>3), K(data=>0x33));
  $t->put(K(key=>4), K(data=>0x44));
  $t->put(K(key=>5), K(data=>0x55));
  $a->dump("5555",   K depth => 11);

  ok Assemble eq => <<END, avx512=>1;
5555
Area     Size:     4096    Used:      704
.... .... .... .... | __10 ____ ____ ____  C0.2 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | __.2 ____ ____ ____  .5__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | .1__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ C0__ ____
.... .... .... ..C0 | 11__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ __.1 ____
.... .... .... .1.. | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .140 | .3__ ____ .4__ ____  .5__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .3__ ____ 80.1 ____
.... .... .... .180 | 33__ ____ 44__ ____  55__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ C0.1 ____
.... .... .... .1C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .2.. | .2__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ 40.2 ____
.... .... .... .240 | 22__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 80.2 ____
.... .... .... .280 | 80__ ____ 40.1 ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::put
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);

  $t->put(K(key=>1), K(data=>0x11));
  $t->put(K(key=>2), K(data=>0x22));
  $t->put(K(key=>3), K(data=>0x33));
  $t->put(K(key=>4), K(data=>0x44));
  $t->put(K(key=>5), K(data=>0x55));
  $t->splitNode(K split => 0x140);
  $a->dump("6666",   K depth => 14);

  ok Assemble eq => <<END, avx512=>1;
6666
Area     Size:     4096    Used:      896
.... .... .... .... | __10 ____ ____ ____  80.3 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | __.2 ____ ____ ____  .5__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | .1__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ C0__ ____
.... .... .... ..C0 | 11__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ __.1 ____
.... .... .... .1.. | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .140 | .3__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ 80.1 ____
.... .... .... .180 | 33__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ C0.1 ____
.... .... .... .1C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .2.. | .2__ ____ .4__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .2__ ____ 40.2 ____
.... .... .... .240 | 22__ ____ 44__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 80.2 ____
.... .... .... .280 | 80__ ____ 40.1 ____  C0.2 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .2C0 | .5__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ __.3 ____
.... .... .... .3.. | 55__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ 40.3 ____
.... .... .... .340 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::put
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);

  $t->put(K(key=>1), K(data=>0x11));
  $t->put(K(key=>2), K(data=>0x22));
  $t->put(K(key=>3), K(data=>0x33));
  $t->put(K(key=>4), K(data=>0x44));
  $t->put(K(key=>5), K(data=>0x55));
  $t->put(K(key=>6), K(data=>0x66));
  $a->dump("6666",   K depth => 14);

  ok Assemble eq => <<END, avx512=>1;
6666
Area     Size:     4096    Used:      896
.... .... .... .... | __10 ____ ____ ____  80.3 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | __.2 ____ ____ ____  .6__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | .1__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ C0__ ____
.... .... .... ..C0 | 11__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ __.1 ____
.... .... .... .1.. | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .140 | .3__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ 80.1 ____
.... .... .... .180 | 33__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ C0.1 ____
.... .... .... .1C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .2.. | .2__ ____ .4__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .2__ ____ 40.2 ____
.... .... .... .240 | 22__ ____ 44__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 80.2 ____
.... .... .... .280 | 80__ ____ 40.1 ____  C0.2 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .2C0 | .5__ ____ .6__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .2__ ____ __.3 ____
.... .... .... .3.. | 55__ ____ 66__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ 40.3 ____
.... .... .... .340 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::put
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);

  $t->put(K(key=>1), K(data=>0x11));
  $t->put(K(key=>2), K(data=>0x22));
  $t->put(K(key=>3), K(data=>0x33));
  $t->put(K(key=>4), K(data=>0x44));
  $t->put(K(key=>5), K(data=>0x55));
  $t->put(K(key=>6), K(data=>0x66));
  $t->put(K(key=>7), K(data=>0x77));
  $a->dump("7777",   K depth => 14);

  ok Assemble eq => <<END, avx512=>1;
7777
Area     Size:     4096    Used:      896
.... .... .... .... | __10 ____ ____ ____  80.3 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | __.2 ____ ____ ____  .7__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | .1__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ C0__ ____
.... .... .... ..C0 | 11__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ __.1 ____
.... .... .... .1.. | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .140 | .3__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ 80.1 ____
.... .... .... .180 | 33__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ C0.1 ____
.... .... .... .1C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .2.. | .2__ ____ .4__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .2__ ____ 40.2 ____
.... .... .... .240 | 22__ ____ 44__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 80.2 ____
.... .... .... .280 | 80__ ____ 40.1 ____  C0.2 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .2C0 | .5__ ____ .6__ ____  .7__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .3__ ____ __.3 ____
.... .... .... .3.. | 55__ ____ 66__ ____  77__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ 40.3 ____
.... .... .... .340 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::put
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);

  $t->put(K(key=>1), K(data=>0x11));
  $t->put(K(key=>2), K(data=>0x22));
  $t->put(K(key=>3), K(data=>0x33));
  $t->put(K(key=>4), K(data=>0x44));
  $t->put(K(key=>5), K(data=>0x55));
  $t->put(K(key=>6), K(data=>0x66));
  $t->put(K(key=>7), K(data=>0x77));
  $t->put(K(key=>8), K(data=>0x88));
  $t->dump("8888");

  ok Assemble eq => <<END, avx512=>1;
8888
At:  500                    length:    1,  data:  540,  nodes:  580,  first:   40, root, parent
  Index:    0
  Keys :    4
  Data :   68
  Nodes:  200  440
    At:  200                length:    1,  data:  240,  nodes:  280,  first:   40,  up:  500, parent
      Index:    0
      Keys :    2
      Data :   34
      Nodes:   80  140
        At:   80            length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
          Index:    0
          Keys :    1
          Data :   17
        end
        At:  140            length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
          Index:    0
          Keys :    3
          Data :   51
        end
    end
    At:  440                length:    1,  data:  480,  nodes:  4C0,  first:   40,  up:  500, parent
      Index:    0
      Keys :    6
      Data :  102
      Nodes:  2C0  380
        At:  2C0            length:    1,  data:  300,  nodes:  340,  first:   40,  up:  440, leaf
          Index:    0
          Keys :    5
          Data :   85
        end
        At:  380            length:    2,  data:  3C0,  nodes:  400,  first:   40,  up:  440, leaf
          Index:    0    1
          Keys :    7    8
          Data :  119  136
        end
    end
end
END
 }

#latest:
if (1) {
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);

  $t->put(K(key=>2), K(data=>0x22));
  $t->put(K(key=>1), K(data=>0x11));
  $t->dump("2222");

  ok Assemble eq => <<END, avx512=>1;
2222
At:   80                    length:    2,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0    1
  Keys :    1    2
  Data :   17   34
end
END
 }

#latest:
if (1) {
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);

  $t->put(K(key=>8), K(data=>0x88));
  $t->put(K(key=>7), K(data=>0x77));
  $t->put(K(key=>6), K(data=>0x66));
  $t->put(K(key=>5), K(data=>0x55));
  $t->put(K(key=>4), K(data=>0x44));
  $t->put(K(key=>3), K(data=>0x33));
  $t->put(K(key=>2), K(data=>0x22));
  $t->put(K(key=>1), K(data=>0x11));
  $t->dump("8888");

  ok Assemble eq => <<END, avx512=>1;
8888
At:  500                    length:    1,  data:  540,  nodes:  580,  first:   40, root, parent
  Index:    0
  Keys :    5
  Data :   85
  Nodes:  200  440
    At:  200                length:    1,  data:  240,  nodes:  280,  first:   40,  up:  500, parent
      Index:    0
      Keys :    3
      Data :   51
      Nodes:   80  380
        At:   80            length:    2,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
          Index:    0    1
          Keys :    1    2
          Data :   17   34
        end
        At:  380            length:    1,  data:  3C0,  nodes:  400,  first:   40,  up:  200, leaf
          Index:    0
          Keys :    4
          Data :   68
        end
    end
    At:  440                length:    1,  data:  480,  nodes:  4C0,  first:   40,  up:  500, parent
      Index:    0
      Keys :    7
      Data :  119
      Nodes:  2C0  140
        At:  2C0            length:    1,  data:  300,  nodes:  340,  first:   40,  up:  440, leaf
          Index:    0
          Keys :    6
          Data :  102
        end
        At:  140            length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  440, leaf
          Index:    0
          Keys :    8
          Data :  136
        end
    end
end
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::put #TNasm::X86::Tree::find
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K count => 128;

  $N->for(sub
   {my ($index, $start, $next, $end) = @_;
    my $l = $N-$index;
    $t->put($l, $l * 2);
    my $h = $N+$index;
    $t->put($h, $h * 2);
   });
  $t->put(K(zero=>0), K(zero=>0));
  $t->printInOrder("AAAA");

  PrintOutStringNL 'Indx   Found  Offset  Double   Found  Offset    Quad   Found  Offset    Octo   Found  Offset     *16   Found  Offset     *32   Found  Offset     *64   Found  Offset    *128   Found  Offset    *256   Found  Offset    *512';
  $N->for(sub
   {my ($index, $start, $next, $end) = @_;
    my $i = $index;
    my $j = $i * 2;
    my $k = $j * 2;
    my $l = $k * 2;
    my $m = $l * 2;
    my $n = $m * 2;
    my $o = $n * 2;
    my $p = $o * 2;
    my $q = $p * 2;
    $t->find($i); $i->outRightInDec(K width => 4); $t->found->outRightInBin(K width => 8); $t->offset->outRightInHex(K width => 8);  $t->data->outRightInDec  (K width => 8);
    $t->find($j);                                  $t->found->outRightInBin(K width => 8); $t->offset->outRightInHex(K width => 8);  $t->data->outRightInDec  (K width => 8);
    $t->find($k);                                  $t->found->outRightInBin(K width => 8); $t->offset->outRightInHex(K width => 8);  $t->data->outRightInDec  (K width => 8);
    $t->find($l);                                  $t->found->outRightInBin(K width => 8); $t->offset->outRightInHex(K width => 8);  $t->data->outRightInDec  (K width => 8);
    $t->find($m);                                  $t->found->outRightInBin(K width => 8); $t->offset->outRightInHex(K width => 8);  $t->data->outRightInDec  (K width => 8);
    $t->find($n);                                  $t->found->outRightInBin(K width => 8); $t->offset->outRightInHex(K width => 8);  $t->data->outRightInDec  (K width => 8);
    $t->find($o);                                  $t->found->outRightInBin(K width => 8); $t->offset->outRightInHex(K width => 8);  $t->data->outRightInDec  (K width => 8);
    $t->find($p);                                  $t->found->outRightInBin(K width => 8); $t->offset->outRightInHex(K width => 8);  $t->data->outRightInDec  (K width => 8);
    $t->find($q);                                  $t->found->outRightInBin(K width => 8); $t->offset->outRightInHex(K width => 8);  $t->data->outRightInDecNL(K width => 8);
   });

  ok Assemble eq => <<END, avx512=>1;
AAAA 256:    0   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A  3B  3C  3D  3E  3F  40  41  42  43  44  45  46  47  48  49  4A  4B  4C  4D  4E  4F  50  51  52  53  54  55  56  57  58  59  5A  5B  5C  5D  5E  5F  60  61  62  63  64  65  66  67  68  69  6A  6B  6C  6D  6E  6F  70  71  72  73  74  75  76  77  78  79  7A  7B  7C  7D  7E  7F  80  81  82  83  84  85  86  87  88  89  8A  8B  8C  8D  8E  8F  90  91  92  93  94  95  96  97  98  99  9A  9B  9C  9D  9E  9F  A0  A1  A2  A3  A4  A5  A6  A7  A8  A9  AA  AB  AC  AD  AE  AF  B0  B1  B2  B3  B4  B5  B6  B7  B8  B9  BA  BB  BC  BD  BE  BF  C0  C1  C2  C3  C4  C5  C6  C7  C8  C9  CA  CB  CC  CD  CE  CF  D0  D1  D2  D3  D4  D5  D6  D7  D8  D9  DA  DB  DC  DD  DE  DF  E0  E1  E2  E3  E4  E5  E6  E7  E8  E9  EA  EB  EC  ED  EE  EF  F0  F1  F2  F3  F4  F5  F6  F7  F8  F9  FA  FB  FC  FD  FE  FF
Indx   Found  Offset  Double   Found  Offset    Quad   Found  Offset    Octo   Found  Offset     *16   Found  Offset     *32   Found  Offset     *64   Found  Offset    *128   Found  Offset    *256   Found  Offset    *512
   0       1      80       0       1      80       0       1      80       0       1      80       0       1      80       0       1      80       0       1      80       0       1      80       0       1      80       0
   1      10      80       2       1     200       4       1     500       8       1     B00      16       1    1700      32       1    2F00      64       1    5F00     128      10    5F00     256               0       0
   2       1     200       4       1     500       8       1     B00      16       1    1700      32       1    2F00      64       1    5F00     128      10    5F00     256               0       0               0       0
   3       1    B540       6       1    B600      12       1    B6C0      24       1    B780      48       1    B840      96       1    B900     192      10    5E40     384               0       0               0       0
   4       1     500       8       1     B00      16       1    1700      32       1    2F00      64       1    5F00     128      10    5F00     256               0       0               0       0               0       0
   5       1    B3C0      10       1    B180      20       1    AC40      40       1    A100      80       1    89C0     160       1    5E40     320               0       0               0       0               0       0
   6       1    B600      12       1    B6C0      24       1    B780      48       1    B840      96       1    B900     192      10    5E40     384               0       0               0       0               0       0
   7       1    B0C0      14       1    AB80      28       1    A040      56       1    8900     112       1    59C0     224      10    8D80     448               0       0               0       0               0       0
   8       1     B00      16       1    1700      32       1    2F00      64       1    5F00     128      10    5F00     256               0       0               0       0               0       0               0       0
   9       1    AF40      18       1    A700      36       1    95C0      72       1    7280     144       1    2E40     288               0       0               0       0               0       0               0       0
  10       1    B180      20       1    AC40      40       1    A100      80       1    89C0     160       1    5E40     320               0       0               0       0               0       0               0       0
  11       1    AAC0      22       1    9F80      44       1    8840      88       1    5900     176       1    5D80     352               0       0               0       0               0       0               0       0
  12       1    B6C0      24       1    B780      48       1    B840      96       1    B900     192      10    5E40     384               0       0               0       0               0       0               0       0
  13       1    A940      26       1    9B00      52       1    7DC0     104       1    4280     208       1    8D80     416               0       0               0       0               0       0               0       0
  14       1    AB80      28       1    A040      56       1    8900     112       1    59C0     224      10    8D80     448               0       0               0       0               0       0               0       0
  15       1    A640      30       1    9500      60       1    71C0     120       1    2A80     240      10    A400     480               0       0               0       0               0       0               0       0
  16       1    1700      32       1    2F00      64       1    5F00     128      10    5F00     256               0       0               0       0               0       0               0       0               0       0
  17       1    A4C0      34       1    9080      68       1    6740     136       1    1640     272               0       0               0       0               0       0               0       0               0       0
  18       1    A700      36       1    95C0      72       1    7280     144       1    2E40     288               0       0               0       0               0       0               0       0               0       0
  19       1    9EC0      38       1    8780      76       1    5840     152       1    2D80     304               0       0               0       0               0       0               0       0               0       0
  20       1    AC40      40       1    A100      80       1    89C0     160       1    5E40     320               0       0               0       0               0       0               0       0               0       0
  21       1    9D40      42       1    8300      84       1    4DC0     168       1    4580     336               0       0               0       0               0       0               0       0               0       0
  22       1    9F80      44       1    8840      88       1    5900     176       1    5D80     352               0       0               0       0               0       0               0       0               0       0
  23       1    9A40      46       1    7D00      92       1    41C0     184       1    5CC0     368               0       0               0       0               0       0               0       0               0       0
  24       1    B780      48       1    B840      96       1    B900     192      10    5E40     384               0       0               0       0               0       0               0       0               0       0
  25       1    98C0      50       1    7880     100       1    3740     200       1    7580     400               0       0               0       0               0       0               0       0               0       0
  26       1    9B00      52       1    7DC0     104       1    4280     208       1    8D80     416               0       0               0       0               0       0               0       0               0       0
  27       1    9440      54       1    7100     108       1    29C0     216       1    8CC0     432               0       0               0       0               0       0               0       0               0       0
  28       1    A040      56       1    8900     112       1    59C0     224      10    8D80     448               0       0               0       0               0       0               0       0               0       0
  29       1    92C0      58       1    6C80     116       1    1F40     232       1    A400     464               0       0               0       0               0       0               0       0               0       0
  30       1    9500      60       1    71C0     120       1    2A80     240      10    A400     480               0       0               0       0               0       0               0       0               0       0
  31       1    8FC0      62       1    6680     124       1    1340     248      10    AE80     496               0       0               0       0               0       0               0       0               0       0
  32       1    2F00      64       1    5F00     128      10    5F00     256               0       0               0       0               0       0               0       0               0       0               0       0
  33       1    8E40      66       1    6200     132       1     A40     264               0       0               0       0               0       0               0       0               0       0               0       0
  34       1    9080      68       1    6740     136       1    1640     272               0       0               0       0               0       0               0       0               0       0               0       0
  35       1    86C0      70       1    5780     140       1    1580     280               0       0               0       0               0       0               0       0               0       0               0       0
  36       1    95C0      72       1    7280     144       1    2E40     288               0       0               0       0               0       0               0       0               0       0               0       0
  37       1    8540      74       1    5300     148       1    2180     296               0       0               0       0               0       0               0       0               0       0               0       0
  38       1    8780      76       1    5840     152       1    2D80     304               0       0               0       0               0       0               0       0               0       0               0       0
  39       1    8240      78       1    4D00     156       1    2CC0     312               0       0               0       0               0       0               0       0               0       0               0       0
  40       1    A100      80       1    89C0     160       1    5E40     320               0       0               0       0               0       0               0       0               0       0               0       0
  41       1    80C0      82       1    4880     164       1    3980     328               0       0               0       0               0       0               0       0               0       0               0       0
  42       1    8300      84       1    4DC0     168       1    4580     336               0       0               0       0               0       0               0       0               0       0               0       0
  43       1    7C40      86       1    4100     172       1    44C0     344               0       0               0       0               0       0               0       0               0       0               0       0
  44       1    8840      88       1    5900     176       1    5D80     352               0       0               0       0               0       0               0       0               0       0               0       0
  45       1    7AC0      90       1    3C80     180       1    5000     360               0       0               0       0               0       0               0       0               0       0               0       0
  46       1    7D00      92       1    41C0     184       1    5CC0     368               0       0               0       0               0       0               0       0               0       0               0       0
  47       1    77C0      94       1    3680     188       1    5C00     376               0       0               0       0               0       0               0       0               0       0               0       0
  48       1    B840      96       1    B900     192      10    5E40     384               0       0               0       0               0       0               0       0               0       0               0       0
  49       1    7640      98       1    3200     196       1    6980     392               0       0               0       0               0       0               0       0               0       0               0       0
  50       1    7880     100       1    3740     200       1    7580     400               0       0               0       0               0       0               0       0               0       0               0       0
  51       1    7040     102       1    2900     204       1    74C0     408               0       0               0       0               0       0               0       0               0       0               0       0
  52       1    7DC0     104       1    4280     208       1    8D80     416               0       0               0       0               0       0               0       0               0       0               0       0
  53       1    6EC0     106       1    2480     212       1    8000     424               0       0               0       0               0       0               0       0               0       0               0       0
  54       1    7100     108       1    29C0     216       1    8CC0     432               0       0               0       0               0       0               0       0               0       0               0       0
  55       1    6BC0     110       1    1E80     220       1    8C00     440               0       0               0       0               0       0               0       0               0       0               0       0
  56       1    8900     112       1    59C0     224      10    8D80     448               0       0               0       0               0       0               0       0               0       0               0       0
  57       1    6A40     114       1    1A00     228       1    9800     456               0       0               0       0               0       0               0       0               0       0               0       0
  58       1    6C80     116       1    1F40     232       1    A400     464               0       0               0       0               0       0               0       0               0       0               0       0
  59       1    65C0     118       1    1280     236       1    A340     472               0       0               0       0               0       0               0       0               0       0               0       0
  60       1    71C0     120       1    2A80     240      10    A400     480               0       0               0       0               0       0               0       0               0       0               0       0
  61       1    6440     122       1     E00     244       1    AE80     488               0       0               0       0               0       0               0       0               0       0               0       0
  62       1    6680     124       1    1340     248      10    AE80     496               0       0               0       0               0       0               0       0               0       0               0       0
  63       1    6140     126       1     800     252      10    B300     504               0       0               0       0               0       0               0       0               0       0               0       0
  64       1    5F00     128      10    5F00     256               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  65       1    5FC0     130       1     440     260               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  66       1    6200     132       1     A40     264               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  67       1    56C0     134       1     980     268               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  68       1    6740     136       1    1640     272               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  69       1    5540     138       1     F80     276               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  70       1    5780     140       1    1580     280               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  71       1    5240     142       1    14C0     284               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  72       1    7280     144       1    2E40     288               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  73       1    50C0     146       1    1B80     292               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  74       1    5300     148       1    2180     296               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  75       1    4C40     150       1    20C0     300               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  76       1    5840     152       1    2D80     304               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  77       1    4AC0     154       1    2600     308               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  78       1    4D00     156       1    2CC0     312               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  79       1    47C0     158       1    2C00     316               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  80       1    89C0     160       1    5E40     320               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  81       1    4640     162       1    3380     324               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  82       1    4880     164       1    3980     328               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  83       1    4040     166       1    38C0     332               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  84       1    4DC0     168       1    4580     336               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  85       1    3EC0     170       1    3E00     340               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  86       1    4100     172       1    44C0     344               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  87       1    3BC0     174       1    4400     348               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  88       1    5900     176       1    5D80     352               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  89       1    3A40     178       1    4A00     356               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  90       1    3C80     180       1    5000     360               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  91       1    35C0     182       1    4F40     364               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  92       1    41C0     184       1    5CC0     368               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  93       1    3440     186       1    5480     372               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  94       1    3680     188       1    5C00     376               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  95       1    3140     190       1    5B40     380               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  96       1    B900     192      10    5E40     384               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  97       1    2FC0     194       1    6380     388               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  98       1    3200     196       1    6980     392               0       0               0       0               0       0               0       0               0       0               0       0               0       0
  99       1    2840     198       1    68C0     396               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 100       1    3740     200       1    7580     400               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 101       1    26C0     202       1    6E00     404               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 102       1    2900     204       1    74C0     408               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 103       1    23C0     206       1    7400     412               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 104       1    4280     208       1    8D80     416               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 105       1    2240     210       1    7A00     420               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 106       1    2480     212       1    8000     424               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 107       1    1DC0     214       1    7F40     428               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 108       1    29C0     216       1    8CC0     432               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 109       1    1C40     218       1    8480     436               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 110       1    1E80     220       1    8C00     440               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 111       1    1940     222       1    8B40     444               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 112       1    59C0     224      10    8D80     448               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 113       1    17C0     226       1    9200     452               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 114       1    1A00     228       1    9800     456               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 115       1    11C0     230       1    9740     460               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 116       1    1F40     232       1    A400     464               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 117       1    1040     234       1    9C80     468               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 118       1    1280     236       1    A340     472               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 119       1     D40     238       1    A280     476               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 120       1    2A80     240      10    A400     480               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 121       1     BC0     242       1    A880     484               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 122       1     E00     244       1    AE80     488               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 123       1     740     246       1    ADC0     492               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 124       1    1340     248      10    AE80     496               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 125       1     5C0     250       1    B300     500               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 126       1     800     252      10    B300     504               0       0               0       0               0       0               0       0               0       0               0       0               0       0
 127       1     2C0     254      10    B480     508               0       0               0       0               0       0               0       0               0       0               0       0               0       0
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::printInOrder
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K count => 128;

  $N->for(sub
   {my ($index, $start, $next, $end) = @_;
    my $l0 = ($N-$index) / 2;
    my $l1 = ($N+$index) / 2;
    my $h0 =  $N-$index;
    my $h1 =  $N+$index;
    $t->put($l0, $l0 * 2);
    $t->put($h1, $h1 * 2);
    $t->put($l1, $l1 * 2);
    $t->put($h0, $h0 * 2);
   });
  $t->printInOrder("AAAA");

  ok Assemble eq => <<END, avx512=>1;
AAAA 256:    0   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A  3B  3C  3D  3E  3F  40  41  42  43  44  45  46  47  48  49  4A  4B  4C  4D  4E  4F  50  51  52  53  54  55  56  57  58  59  5A  5B  5C  5D  5E  5F  60  61  62  63  64  65  66  67  68  69  6A  6B  6C  6D  6E  6F  70  71  72  73  74  75  76  77  78  79  7A  7B  7C  7D  7E  7F  80  81  82  83  84  85  86  87  88  89  8A  8B  8C  8D  8E  8F  90  91  92  93  94  95  96  97  98  99  9A  9B  9C  9D  9E  9F  A0  A1  A2  A3  A4  A5  A6  A7  A8  A9  AA  AB  AC  AD  AE  AF  B0  B1  B2  B3  B4  B5  B6  B7  B8  B9  BA  BB  BC  BD  BE  BF  C0  C1  C2  C3  C4  C5  C6  C7  C8  C9  CA  CB  CC  CD  CE  CF  D0  D1  D2  D3  D4  D5  D6  D7  D8  D9  DA  DB  DC  DD  DE  DF  E0  E1  E2  E3  E4  E5  E6  E7  E8  E9  EA  EB  EC  ED  EE  EF  F0  F1  F2  F3  F4  F5  F6  F7  F8  F9  FA  FB  FC  FD  FE  FF
END
 }

#latest:
if (1) {
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K count => 128;

  $N->for(sub
   {my ($index, $start, $next, $end) = @_;
    my $l00 = ($N-$index) / 4;
    my $l01 = ($N+$index) / 4;
    my $h00 =  $N-$index  / 2;
    my $h01 =  $N+$index  / 2;
    my $l10 = ($N-$index) / 4 * 3;
    my $l11 = ($N+$index) / 4 * 3;
    my $h10 =  $N-$index ;
    my $h11 =  $N+$index ;
    $t->put($l00, $l00 * 2);
    $t->put($h01, $h01 * 2);
    $t->put($l01, $l01 * 2);
    $t->put($h00, $h00 * 2);
    $t->put($l10, $l10 * 2);
    $t->put($h11, $h11 * 2);
    $t->put($l11, $l11 * 2);
    $t->put($h10, $h10 * 2);
   });
  $t->printInOrder("AAAA");

  ok Assemble eq => <<END, avx512=>1;
AAAA 256:    0   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A  3B  3C  3D  3E  3F  40  41  42  43  44  45  46  47  48  49  4A  4B  4C  4D  4E  4F  50  51  52  53  54  55  56  57  58  59  5A  5B  5C  5D  5E  5F  60  61  62  63  64  65  66  67  68  69  6A  6B  6C  6D  6E  6F  70  71  72  73  74  75  76  77  78  79  7A  7B  7C  7D  7E  7F  80  81  82  83  84  85  86  87  88  89  8A  8B  8C  8D  8E  8F  90  91  92  93  94  95  96  97  98  99  9A  9B  9C  9D  9E  9F  A0  A1  A2  A3  A4  A5  A6  A7  A8  A9  AA  AB  AC  AD  AE  AF  B0  B1  B2  B3  B4  B5  B6  B7  B8  B9  BA  BB  BC  BD  BE  BF  C0  C1  C2  C3  C4  C5  C6  C7  C8  C9  CA  CB  CC  CD  CE  CF  D0  D1  D2  D3  D4  D5  D6  D7  D8  D9  DA  DB  DC  DD  DE  DF  E0  E1  E2  E3  E4  E5  E6  E7  E8  E9  EA  EB  EC  ED  EE  EF  F0  F1  F2  F3  F4  F5  F6  F7  F8  F9  FA  FB  FC  FD  FE  FF
END
 }

#latest:
if (1) {
  my $N = 13;
  my $a = CreateArea;
  my $t = $a->CreateTree(length => $N);

  my ($K, $D) = (31, 30);

  K(K => Rd( 1..16))->loadZmm($K);
  K(D => Rd(17..32))->loadZmm($D);

  $t->lengthIntoKeys($K, K length => $t->length);

  Mov r15, 0b11001100110011;
  $t->setTreeBits($K, r15);

  PrintOutStringNL "Start";
  PrintOutRegisterInHex $K, $D;

  K(loop => $N)->for(sub
   {my ($index) = @_;                                                           # Parameters
    $t->deleteFirstKeyAndData($K, $D);

    PrintOutNL;
    $index->outNL;
    PrintOutNL;
    PrintOutRegisterInHex $K, $D;
    PrintOutNL;
    $t->key    ->out("k: ", "   "); $t->data->out("d: ", "   ");
    $t->subTree->out("s: ", "   "); $t->found->outNL;
   });

  ok Assemble eq => <<END, avx512=>1;
Start
 zmm31: .... ..10 3333 ...D  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1C .... ..1B  .... ..1A .... ..19 + .... ..18 .... ..17  .... ..16 .... ..15 - .... ..14 .... ..13  .... ..12 .... ..11

index: .... .... .... ....

 zmm31: .... ..10 1999 ...C  .... ...E .... ...D - .... ...D .... ...C  .... ...B .... ...A + .... ...9 .... ...8  .... ...7 .... ...6 - .... ...5 .... ...4  .... ...3 .... ...2
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1D .... ..1C  .... ..1B .... ..1A + .... ..19 .... ..18  .... ..17 .... ..16 - .... ..15 .... ..14  .... ..13 .... ..12

k: .... .... .... ...1   d: .... .... .... ..11   s: .... .... .... ...1   found: .... .... .... ...1

index: .... .... .... ...1

 zmm31: .... ..10 .CCC ...B  .... ...E .... ...D - .... ...D .... ...D  .... ...C .... ...B + .... ...A .... ...9  .... ...8 .... ...7 - .... ...6 .... ...5  .... ...4 .... ...3
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1D .... ..1D  .... ..1C .... ..1B + .... ..1A .... ..19  .... ..18 .... ..17 - .... ..16 .... ..15  .... ..14 .... ..13

k: .... .... .... ...2   d: .... .... .... ..12   s: .... .... .... ...1   found: .... .... .... ...1

index: .... .... .... ...2

 zmm31: .... ..10 .666 ...A  .... ...E .... ...D - .... ...D .... ...D  .... ...D .... ...C + .... ...B .... ...A  .... ...9 .... ...8 - .... ...7 .... ...6  .... ...5 .... ...4
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1C + .... ..1B .... ..1A  .... ..19 .... ..18 - .... ..17 .... ..16  .... ..15 .... ..14

k: .... .... .... ...3   d: .... .... .... ..13   s: .... .... .... ....   found: .... .... .... ...1

index: .... .... .... ...3

 zmm31: .... ..10 .333 ...9  .... ...E .... ...D - .... ...D .... ...D  .... ...D .... ...D + .... ...C .... ...B  .... ...A .... ...9 - .... ...8 .... ...7  .... ...6 .... ...5
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1D + .... ..1C .... ..1B  .... ..1A .... ..19 - .... ..18 .... ..17  .... ..16 .... ..15

k: .... .... .... ...4   d: .... .... .... ..14   s: .... .... .... ....   found: .... .... .... ...1

index: .... .... .... ...4

 zmm31: .... ..10 .199 ...8  .... ...E .... ...D - .... ...D .... ...D  .... ...D .... ...D + .... ...D .... ...C  .... ...B .... ...A - .... ...9 .... ...8  .... ...7 .... ...6
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1D + .... ..1D .... ..1C  .... ..1B .... ..1A - .... ..19 .... ..18  .... ..17 .... ..16

k: .... .... .... ...5   d: .... .... .... ..15   s: .... .... .... ...1   found: .... .... .... ...1

index: .... .... .... ...5

 zmm31: .... ..10 ..CC ...7  .... ...E .... ...D - .... ...D .... ...D  .... ...D .... ...D + .... ...D .... ...D  .... ...C .... ...B - .... ...A .... ...9  .... ...8 .... ...7
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1D + .... ..1D .... ..1D  .... ..1C .... ..1B - .... ..1A .... ..19  .... ..18 .... ..17

k: .... .... .... ...6   d: .... .... .... ..16   s: .... .... .... ...1   found: .... .... .... ...1

index: .... .... .... ...6

 zmm31: .... ..10 ..66 ...6  .... ...E .... ...D - .... ...D .... ...D  .... ...D .... ...D + .... ...D .... ...D  .... ...D .... ...C - .... ...B .... ...A  .... ...9 .... ...8
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1D + .... ..1D .... ..1D  .... ..1D .... ..1C - .... ..1B .... ..1A  .... ..19 .... ..18

k: .... .... .... ...7   d: .... .... .... ..17   s: .... .... .... ....   found: .... .... .... ...1

index: .... .... .... ...7

 zmm31: .... ..10 ..33 ...5  .... ...E .... ...D - .... ...D .... ...D  .... ...D .... ...D + .... ...D .... ...D  .... ...D .... ...D - .... ...C .... ...B  .... ...A .... ...9
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1D + .... ..1D .... ..1D  .... ..1D .... ..1D - .... ..1C .... ..1B  .... ..1A .... ..19

k: .... .... .... ...8   d: .... .... .... ..18   s: .... .... .... ....   found: .... .... .... ...1

index: .... .... .... ...8

 zmm31: .... ..10 ..19 ...4  .... ...E .... ...D - .... ...D .... ...D  .... ...D .... ...D + .... ...D .... ...D  .... ...D .... ...D - .... ...D .... ...C  .... ...B .... ...A
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1D + .... ..1D .... ..1D  .... ..1D .... ..1D - .... ..1D .... ..1C  .... ..1B .... ..1A

k: .... .... .... ...9   d: .... .... .... ..19   s: .... .... .... ...1   found: .... .... .... ...1

index: .... .... .... ...9

 zmm31: .... ..10 ...C ...3  .... ...E .... ...D - .... ...D .... ...D  .... ...D .... ...D + .... ...D .... ...D  .... ...D .... ...D - .... ...D .... ...D  .... ...C .... ...B
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1D + .... ..1D .... ..1D  .... ..1D .... ..1D - .... ..1D .... ..1D  .... ..1C .... ..1B

k: .... .... .... ...A   d: .... .... .... ..1A   s: .... .... .... ...1   found: .... .... .... ...1

index: .... .... .... ...A

 zmm31: .... ..10 ...6 ...2  .... ...E .... ...D - .... ...D .... ...D  .... ...D .... ...D + .... ...D .... ...D  .... ...D .... ...D - .... ...D .... ...D  .... ...D .... ...C
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1D + .... ..1D .... ..1D  .... ..1D .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1C

k: .... .... .... ...B   d: .... .... .... ..1B   s: .... .... .... ....   found: .... .... .... ...1

index: .... .... .... ...B

 zmm31: .... ..10 ...3 ...1  .... ...E .... ...D - .... ...D .... ...D  .... ...D .... ...D + .... ...D .... ...D  .... ...D .... ...D - .... ...D .... ...D  .... ...D .... ...D
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1D + .... ..1D .... ..1D  .... ..1D .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1D

k: .... .... .... ...C   d: .... .... .... ..1C   s: .... .... .... ....   found: .... .... .... ...1

index: .... .... .... ...C

 zmm31: .... ..10 ...1 ....  .... ...E .... ...D - .... ...D .... ...D  .... ...D .... ...D + .... ...D .... ...D  .... ...D .... ...D - .... ...D .... ...D  .... ...D .... ...D
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1D + .... ..1D .... ..1D  .... ..1D .... ..1D - .... ..1D .... ..1D  .... ..1D .... ..1D

k: .... .... .... ...D   d: .... .... .... ..1D   s: .... .... .... ...1   found: .... .... .... ...1
END
 }

#latest:
if (1) {                                                                        #Nasm::X86::Variable::shiftLeft #Nasm::X86::Variable::shiftRight
  K(loop=>16)->for(sub
   {my ($index, $start, $next, $end) = @_;
   (K(one => 1)     << $index)->outRightInBinNL(K width => 16);
   (K(one => 1<<15) >> $index)->outRightInBinNL(K width => 16);
   });

  ok Assemble eq => <<END, avx512=>1;
               1
1000000000000000
              10
 100000000000000
             100
  10000000000000
            1000
   1000000000000
           10000
    100000000000
          100000
     10000000000
         1000000
      1000000000
        10000000
       100000000
       100000000
        10000000
      1000000000
         1000000
     10000000000
          100000
    100000000000
           10000
   1000000000000
            1000
  10000000000000
             100
 100000000000000
              10
1000000000000000
               1
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::firstNode #TNasm::X86::Tree::lastNode
  my $L = 13;
  my $a = CreateArea;
  my $t = $a->CreateTree(length => $L);

  my ($K, $D, $N) = (31, 30, 29);

  K(K => Rd( 1..16))->loadZmm($K);
  K(K => Rd( 1..16))->loadZmm($N);

  $t->lengthIntoKeys($K, K length => $t->length);

  PrintOutRegisterInHex 31, 29;
  my $f = $t->firstNode($K, $D, $N);
  my $l = $t-> lastNode($K, $D, $N);
  $f->outNL;
  $l->outNL;

  ok Assemble eq => <<END, avx512=>1;
 zmm31: .... ..10 .... ...D  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
 zmm29: .... ..10 .... ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
d at offset 0 in zmm29: .... .... .... ...1
d at offset (b at offset 56 in zmm31 times 4) in zmm29: .... .... .... ...E
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::firstNode #TNasm::X86::Tree::lastNode
  my $L = 13;
  my $a = CreateArea;
  my $t = $a->CreateTree(length => $L);

  my ($K, $D, $N) = (31, 30, 29);

  K(K => Rd( 1..16))->loadZmm($K);
  K(K => Rd( 1..16))->loadZmm($N);

  $t->lengthIntoKeys($K, K length => $t->length);

  PrintOutRegisterInHex 31, 29;
  my $f = $t->firstNode($K, $D, $N);
  my $l = $t-> lastNode($K, $D, $N);
  $f->outNL;
  $l->outNL;

  ok Assemble eq => <<END, avx512=>1;
 zmm31: .... ..10 .... ...D  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
 zmm29: .... ..10 .... ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
d at offset 0 in zmm29: .... .... .... ...1
d at offset (b at offset 56 in zmm31 times 4) in zmm29: .... .... .... ...E
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::expand
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);

  my ($PK, $PD, $PN) = (31, 30, 29);
  my ($LK, $LD, $LN) = (28, 27, 26);
  my ($RK, $RD, $RN) = (25, 24, 23);
  my ($lK, $lD, $lN) = (22, 21, 20);
  my ($rK, $rD, $rN) = (19, 18, 17);
  my $F = 16;

  my $P  = $t->allocBlock($PK, $PD, $PN);
  my $L  = $t->allocBlock($LK, $LD, $LN);
  my $R  = $t->allocBlock($RK, $RD, $RN);
  my $l  = $t->allocBlock($lK, $lD, $lN);
  my $r  = $t->allocBlock($rK, $rD, $rN);

  $t->lengthIntoKeys($PK, K length => 1);
  $t->lengthIntoKeys($LK, K length => 1);
  $t->lengthIntoKeys($RK, K length => 1);

  K(key=>1)->dIntoZ($LK, 0);  K(key=>1)->dIntoZ($LD, 0);
  K(key=>2)->dIntoZ($PK, 0);  K(key=>2)->dIntoZ($PD, 0);
  K(key=>3)->dIntoZ($RK, 0);  K(key=>3)->dIntoZ($RD, 0);

  $L->dIntoZ($PN, 0);
  $R->dIntoZ($PN, 4);
  $l->dIntoZ($LN, 0); $l->dIntoZ($LN, 4);
  $r->dIntoZ($RN, 0); $r->dIntoZ($RN, 4);

  $t->upIntoData($P, $LD);
  $t->upIntoData($P, $RD);
  $t->upIntoData($L, $lD);
  $t->upIntoData($R, $rD);

  $t->firstFromMemory($F);
  $t->rootIntoFirst($F, $P);
  $t->sizeIntoFirst($F, K size => 3);

  $t->firstIntoMemory($F);
  $t->putBlock($P, $PK, $PD, $PN);
  $t->putBlock($L, $LK, $LD, $LN);
  $t->putBlock($R, $RK, $RD, $RN);
  $t->putBlock($l, $lK, $lD, $lN);
  $t->putBlock($r, $rK, $rD, $rN);

  PrintOutStringNL "Start";
  PrintOutRegisterInHex reverse $F..$PK;

  $t->expand($L);

  $t->firstFromMemory($F);
# $t->getBlock($P, $PK, $PD, $PN);
  $t->getBlock($L, $LK, $LD, $LN);
# $t->getBlock($R, $RK, $RD, $RN);

  PrintOutStringNL "Finish";
  PrintOutRegisterInHex reverse $LN..$LK;

  PrintOutStringNL "Children";
  PrintOutRegisterInHex reverse $LN..$LK;

  ok Assemble eq => <<END, avx512=>1;
Start
 zmm31: .... ..C0 .... ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ...2
 zmm30: .... .1.. .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ...2
 zmm29: .... ..40 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .2.. .... .140
 zmm28: .... .180 .... ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ...1
 zmm27: .... .1C0 .... ..80  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ...1
 zmm26: .... ..40 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .2C0 .... .2C0
 zmm25: .... .240 .... ...1  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ...3
 zmm24: .... .280 .... ..80  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ...3
 zmm23: .... ..40 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .380 .... .380
 zmm22: .... .3.. .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
 zmm21: .... .340 .... .140  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
 zmm20: .... ..40 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
 zmm19: .... .3C0 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
 zmm18: .... .4.. .... .2..  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
 zmm17: .... ..40 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
 zmm16: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ...3  .... .... .... ..80
Finish
 zmm28: .... .180 .... ...3  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ...3  .... ...2 .... ...1
 zmm27: .... .1C0 .... ..80  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ...3  .... ...2 .... ...1
 zmm26: .... ..40 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .380 .... .380  .... .2C0 .... .2C0
Children
 zmm28: .... .180 .... ...3  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ...3  .... ...2 .... ...1
 zmm27: .... .1C0 .... ..80  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ...3  .... ...2 .... ...1
 zmm26: .... ..40 .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .380 .... .380  .... .2C0 .... .2C0
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::replace
  my ($K, $D) = (31, 30);

  K(K => Rd(reverse 1..16))->loadZmm($K);
  K(K => Rd(reverse 1..16))->loadZmm($D);
  PrintOutStringNL "Start";
  PrintOutRegisterInHex $K, $D;

  my $a = CreateArea;
  my $t = $a->CreateTree(length => 13);

  K(loop => 14)->for(sub
   {my ($index, $start, $next, $end) = @_;

    $t->key    ->copy($index);
    $t->data   ->copy($index * 2);
    $t->subTree->copy($index % 2);

    $t->replace(K(one=>1)<<$index, $K, $D);

    $index->outNL;
    PrintOutRegisterInHex $K, $D;
   });

  ok Assemble eq => <<END, avx512=>1;
Start
 zmm31: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...B .... ...C - .... ...D .... ...E  .... ...F .... ..10
 zmm30: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...B .... ...C - .... ...D .... ...E  .... ...F .... ..10
index: .... .... .... ....
 zmm31: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...B .... ...C - .... ...D .... ...E  .... ...F .... ....
 zmm30: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...B .... ...C - .... ...D .... ...E  .... ...F .... ....
index: .... .... .... ...1
 zmm31: .... ...1 ...2 ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...B .... ...C - .... ...D .... ...E  .... ...1 .... ....
 zmm30: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...B .... ...C - .... ...D .... ...E  .... ...2 .... ....
index: .... .... .... ...2
 zmm31: .... ...1 ...2 ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...B .... ...C - .... ...D .... ...2  .... ...1 .... ....
 zmm30: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...B .... ...C - .... ...D .... ...4  .... ...2 .... ....
index: .... .... .... ...3
 zmm31: .... ...1 ...A ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...B .... ...C - .... ...3 .... ...2  .... ...1 .... ....
 zmm30: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...B .... ...C - .... ...6 .... ...4  .... ...2 .... ....
index: .... .... .... ...4
 zmm31: .... ...1 ...A ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...B .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
 zmm30: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...B .... ...8 - .... ...6 .... ...4  .... ...2 .... ....
index: .... .... .... ...5
 zmm31: .... ...1 ..2A ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...5 .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
 zmm30: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...A  .... ...A .... ...8 - .... ...6 .... ...4  .... ...2 .... ....
index: .... .... .... ...6
 zmm31: .... ...1 ..2A ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
 zmm30: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...9 .... ...C  .... ...A .... ...8 - .... ...6 .... ...4  .... ...2 .... ....
index: .... .... .... ...7
 zmm31: .... ...1 ..AA ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...7 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
 zmm30: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...E .... ...C  .... ...A .... ...8 - .... ...6 .... ...4  .... ...2 .... ....
index: .... .... .... ...8
 zmm31: .... ...1 ..AA ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ...8 + .... ...7 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
 zmm30: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...7 .... ..10 + .... ...E .... ...C  .... ...A .... ...8 - .... ...6 .... ...4  .... ...2 .... ....
index: .... .... .... ...9
 zmm31: .... ...1 .2AA ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ...9 .... ...8 + .... ...7 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
 zmm30: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ...6  .... ..12 .... ..10 + .... ...E .... ...C  .... ...A .... ...8 - .... ...6 .... ...4  .... ...2 .... ....
index: .... .... .... ...A
 zmm31: .... ...1 .2AA ...2  .... ...3 .... ...4 - .... ...5 .... ...A  .... ...9 .... ...8 + .... ...7 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
 zmm30: .... ...1 .... ...2  .... ...3 .... ...4 - .... ...5 .... ..14  .... ..12 .... ..10 + .... ...E .... ...C  .... ...A .... ...8 - .... ...6 .... ...4  .... ...2 .... ....
index: .... .... .... ...B
 zmm31: .... ...1 .AAA ...2  .... ...3 .... ...4 - .... ...B .... ...A  .... ...9 .... ...8 + .... ...7 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
 zmm30: .... ...1 .... ...2  .... ...3 .... ...4 - .... ..16 .... ..14  .... ..12 .... ..10 + .... ...E .... ...C  .... ...A .... ...8 - .... ...6 .... ...4  .... ...2 .... ....
index: .... .... .... ...C
 zmm31: .... ...1 .AAA ...2  .... ...3 .... ...C - .... ...B .... ...A  .... ...9 .... ...8 + .... ...7 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
 zmm30: .... ...1 .... ...2  .... ...3 .... ..18 - .... ..16 .... ..14  .... ..12 .... ..10 + .... ...E .... ...C  .... ...A .... ...8 - .... ...6 .... ...4  .... ...2 .... ....
index: .... .... .... ...D
 zmm31: .... ...1 2AAA ...2  .... ...D .... ...C - .... ...B .... ...A  .... ...9 .... ...8 + .... ...7 .... ...6  .... ...5 .... ...4 - .... ...3 .... ...2  .... ...1 .... ....
 zmm30: .... ...1 .... ...2  .... ..1A .... ..18 - .... ..16 .... ..14  .... ..12 .... ..10 + .... ...E .... ...C  .... ...A .... ...8 - .... ...6 .... ...4  .... ...2 .... ....
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::extractFirst
  my ($K, $D, $N) = (31, 30, 29);

  K(K => Rd( 1..16))       ->loadZmm($K);
  K(K => Rd( 1..16))       ->loadZmm($D);
  K(K => Rd(map {0} 1..16))->loadZmm($N);

  my $a = CreateArea;
  my $t = $a->CreateTree(length => 13);

  my $p = K(one => 1) << K three => 3;
  Mov r15, 0xAAAA;
  $t->setTreeBits($K, r15);

  PrintOutStringNL "Start";
  PrintOutRegisterInHex 31, 30, 29;

  K(n=>4)->for(sub
   {my ($index, $start, $next, $end) = @_;

    $t->extractFirst($K, $D, $N);

    PrintOutStringNL "-------------";
    $index->outNL;
    PrintOutRegisterInHex 31, 30, 29;

    $t->data->outNL;
    $t->subTree->outNL;
    $t->lengthFromKeys($K)->outNL;
   });

  ok Assemble eq => <<END, avx512=>1;
Start
 zmm31: .... ..10 2AAA ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
 zmm30: .... ..10 .... ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
 zmm29: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
-------------
index: .... .... .... ....
 zmm31: .... ..10 1555 ...E  .... ...E .... ...E - .... ...D .... ...C  .... ...B .... ...A + .... ...9 .... ...8  .... ...7 .... ...6 - .... ...5 .... ...4  .... ...3 .... ...2
 zmm30: .... ..10 .... ...F  .... ...E .... ...E - .... ...D .... ...C  .... ...B .... ...A + .... ...9 .... ...8  .... ...7 .... ...6 - .... ...5 .... ...4  .... ...3 .... ...2
 zmm29: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
data: .... .... .... ...1
subTree: .... .... .... ....
b at offset 56 in zmm31: .... .... .... ...E
-------------
index: .... .... .... ...1
 zmm31: .... ..10 .AAA ...D  .... ...E .... ...E - .... ...E .... ...D  .... ...C .... ...B + .... ...A .... ...9  .... ...8 .... ...7 - .... ...6 .... ...5  .... ...4 .... ...3
 zmm30: .... ..10 .... ...F  .... ...E .... ...E - .... ...E .... ...D  .... ...C .... ...B + .... ...A .... ...9  .... ...8 .... ...7 - .... ...6 .... ...5  .... ...4 .... ...3
 zmm29: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
data: .... .... .... ...2
subTree: .... .... .... ...1
b at offset 56 in zmm31: .... .... .... ...D
-------------
index: .... .... .... ...2
 zmm31: .... ..10 .555 ...C  .... ...E .... ...E - .... ...E .... ...E  .... ...D .... ...C + .... ...B .... ...A  .... ...9 .... ...8 - .... ...7 .... ...6  .... ...5 .... ...4
 zmm30: .... ..10 .... ...F  .... ...E .... ...E - .... ...E .... ...E  .... ...D .... ...C + .... ...B .... ...A  .... ...9 .... ...8 - .... ...7 .... ...6  .... ...5 .... ...4
 zmm29: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
data: .... .... .... ...3
subTree: .... .... .... ....
b at offset 56 in zmm31: .... .... .... ...C
-------------
index: .... .... .... ...3
 zmm31: .... ..10 .2AA ...B  .... ...E .... ...E - .... ...E .... ...E  .... ...E .... ...D + .... ...C .... ...B  .... ...A .... ...9 - .... ...8 .... ...7  .... ...6 .... ...5
 zmm30: .... ..10 .... ...F  .... ...E .... ...E - .... ...E .... ...E  .... ...E .... ...D + .... ...C .... ...B  .... ...A .... ...9 - .... ...8 .... ...7  .... ...6 .... ...5
 zmm29: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
data: .... .... .... ...4
subTree: .... .... .... ...1
b at offset 56 in zmm31: .... .... .... ...B
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::extract
  my ($K, $D, $N) = (31, 30, 29);

  K(K => Rd( 1..16))->loadZmm($K);
  K(K => Rd( 1..16))->loadZmm($D);
  K(K => Rd(map {0} 1..16))->loadZmm($N);

  my $a = CreateArea;
  my $t = $a->CreateTree(length => 13);

  my $p = K(one => 1) << K three => 3;
  Mov r15, 0xAAAA;
  $t->setTreeBits($K, r15);

  PrintOutStringNL "Start";
  PrintOutRegisterInHex 31, 30, 29;

  $t->extract($p, $K, $D, $N);

  PrintOutStringNL "Finish";
  PrintOutRegisterInHex 31, 30, 29;

  ok Assemble eq => <<END, avx512=>1;
Start
 zmm31: .... ..10 2AAA ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
 zmm30: .... ..10 .... ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
 zmm29: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
Finish
 zmm31: .... ..10 2AAA ...E  .... ...E .... ...E - .... ...D .... ...C  .... ...B .... ...A + .... ...9 .... ...8  .... ...7 .... ...6 - .... ...5 .... ...3  .... ...2 .... ...1
 zmm30: .... ..10 .... ...F  .... ...E .... ...E - .... ...D .... ...C  .... ...B .... ...A + .... ...9 .... ...8  .... ...7 .... ...6 - .... ...5 .... ...3  .... ...2 .... ...1
 zmm29: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::mergeOrSteal
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  $t->put(   K(k=>1), K(d=>11));
  $t->put(   K(k=>2), K(d=>22));
  $t->put(   K(k=>3), K(d=>33));
  $t->put(   K(k=>4), K(d=>44));
  $t->put(   K(k=>5), K(d=>55));
  $t->put(   K(k=>6), K(d=>56));

  $t->getBlock(K(o=>0x2C0), 31, 30, 29);
  $t->lengthIntoKeys(31, K 1 => 1);
  $t->putBlock(K(o=>0x2C0), 31, 30, 29);
  $t->dump("6");

  $t->key->copy(K k => 4);
  $t->mergeOrSteal(K o => 0x140);
  $t->dump("5");

  ok Assemble eq => <<END, avx512=>1;
6
At:  200                    length:    2,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0    1
  Keys :    2    4
  Data :   22   44
  Nodes:   80  140  2C0
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :   11
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    3
      Data :   33
    end
    At:  2C0                length:    1,  data:  300,  nodes:  340,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    5
      Data :   55
    end
end
5
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :   22
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :   11
    end
    At:  140                length:    3,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0    1    2
      Keys :    3    4    5
      Data :   33   44   55
    end
end
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::nextNode #TNasm::X86::Tree::prevNode
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 13);

  K(loop => 66)->for(sub
   {my ($index, $start, $next, $end) = @_;
    $t->put($index, 2 * $index);
   });
  $t->getBlock(K(offset=>0x200), 31, 30, 29);
  $t->nextNode(K(offset=>0x440), 31, 29)->outRightInHexNL(K width => 3);
  $t->prevNode(K(offset=>0x440), 31, 29)->outRightInHexNL(K width => 3);

  ok Assemble eq => <<END, avx512=>1;
500
380
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::mergeOrSteal
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  $t->put(   K(k=>1), K(d=>11));
  $t->put(   K(k=>2), K(d=>22));
  $t->put(   K(k=>3), K(d=>33));
  $t->put(   K(k=>4), K(d=>44));
  $t->put(   K(k=>5), K(d=>55));
  $t->put(   K(k=>6), K(d=>56));

  $t->getBlock(K(o=>0x2C0), 31, 30, 29);
  $t->lengthIntoKeys(31, K 1 => 1);
  $t->putBlock(K(o=>0x2C0), 31, 30, 29);
  $t->dump("6");

  $t->key->copy(K k => 4);
  $t->mergeOrSteal(K o => 0x140);
  $t->dump("5");

  ok Assemble eq => <<END, avx512=>1;
6
At:  200                    length:    2,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0    1
  Keys :    2    4
  Data :   22   44
  Nodes:   80  140  2C0
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :   11
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    3
      Data :   33
    end
    At:  2C0                length:    1,  data:  300,  nodes:  340,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    5
      Data :   55
    end
end
5
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :   22
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :   11
    end
    At:  140                length:    3,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0    1    2
      Keys :    3    4    5
      Data :   33   44   55
    end
end
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::mergeOrSteal
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  $t->put(   K(k=>1), K(d=>11));
  $t->put(   K(k=>2), K(d=>22));
  $t->put(   K(k=>3), K(d=>33));
  $t->put(   K(k=>4), K(d=>44));
  $t->put(   K(k=>5), K(d=>55));
  $t->put(   K(k=>6), K(d=>56));

  $t->getBlock(K(o=>0x2C0), 31, 30, 29);
  $t->lengthIntoKeys(31, K 1 => 1);
  $t->putBlock(K(o=>0x2C0), 31, 30, 29);
  $t->dump("6");

  $t->key->copy(K k => 2);
  $t->mergeOrSteal(K o => 0x80);
  $t->dump("5");

  ok Assemble eq => <<END, avx512=>1;
6
At:  200                    length:    2,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0    1
  Keys :    2    4
  Data :   22   44
  Nodes:   80  140  2C0
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :   11
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    3
      Data :   33
    end
    At:  2C0                length:    1,  data:  300,  nodes:  340,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    5
      Data :   55
    end
end
5
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    4
  Data :   44
  Nodes:   80  2C0
    At:   80                length:    3,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0    1    2
      Keys :    1    2    3
      Data :   11   22   33
    end
    At:  2C0                length:    1,  data:  300,  nodes:  340,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    5
      Data :   55
    end
end
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::findFirst
  my $N = K(key => 32);
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);

  $N->for(sub
   {my ($i, $start, $next, $end) = @_;
    $t->put($i, $i);
   });

  $N->for(sub
   {my ($i, $start, $next, $end) = @_;
    $t->put($N + $i, $N + $i);
    $t->findFirst;

    If $t->key != $i,
    Then
     {PrintOutTraceBack "Reverse queue first failed at: "; $i->outNL;
     };
    $t->delete($i);
    If $t->size != $N,
    Then
     {PrintOutTraceBack "Reverse queue size failed at: "; $i->outNL;
     };
    $t->printInOrder("A");
   });

  ok Assemble eq => <<END, avx512=>1;
A  32:    1   2   3   4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20
A  32:    2   3   4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21
A  32:    3   4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22
A  32:    4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23
A  32:    5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24
A  32:    6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25
A  32:    7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26
A  32:    8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27
A  32:    9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28
A  32:    A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29
A  32:    B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A
A  32:    C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B
A  32:    D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C
A  32:    E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D
A  32:    F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E
A  32:   10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F
A  32:   11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30
A  32:   12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31
A  32:   13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32
A  32:   14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33
A  32:   15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34
A  32:   16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35
A  32:   17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36
A  32:   18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37
A  32:   19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38
A  32:   1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39
A  32:   1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A
A  32:   1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A  3B
A  32:   1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A  3B  3C
A  32:   1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A  3B  3C  3D
A  32:   1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A  3B  3C  3D  3E
A  32:   20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A  3B  3C  3D  3E  3F
END
 }


#latest:
if (1) {                                                                        #TNasm::X86::Tree::findLast
  my $N = K(key => 32);
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);

  $N->for(sub
   {my ($i, $start, $next, $end) = @_;
    $t->put($N + $i, $N + $i);
   });

  $N->for(sub
   {my ($i, $start, $next, $end) = @_;
    $t->put($N - $i, $N - $i);
    $t->findLast;
    $t->delete($t->key);
    If $t->size != $N - 1,
    Then
     {PrintOutTraceBack "Queued size failed at: "; $i->outNL;
     };
    $t->printInOrder("A");
   });

  ok Assemble eq => <<END, avx512=>1;
A  31:   20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A  3B  3C  3D  3E
A  31:   1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A  3B  3C  3D
A  31:   1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A  3B  3C
A  31:   1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A  3B
A  31:   1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39  3A
A  31:   1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38  39
A  31:   1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37  38
A  31:   19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36  37
A  31:   18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35  36
A  31:   17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34  35
A  31:   16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33  34
A  31:   15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32  33
A  31:   14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31  32
A  31:   13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30  31
A  31:   12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F  30
A  31:   11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E  2F
A  31:   10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D  2E
A  31:    F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C  2D
A  31:    E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B  2C
A  31:    D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A  2B
A  31:    C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29  2A
A  31:    B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28  29
A  31:    A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27  28
A  31:    9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26  27
A  31:    8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25  26
A  31:    7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24  25
A  31:    6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23  24
A  31:    5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23
A  31:    4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22
A  31:    3   4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21
A  31:    2   3   4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20
A  31:    1   2   3   4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $i2 = V  k => 2; $t->put($i2, $i2);
  my $i3 = V  k => 3; $t->put($i3, $i3);
  my $i4 = V  k => 4; $t->put($i4, $i4);
  my $i1 = V  k => 1; $t->put($i1, $i1);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("4"); $t->delete($i4);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("X"); $t->printInOrder("X");

  ok Assemble eq => <<END, avx512=>1;
   4
4
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    3
  Data :    3
  Nodes:   80  140
    At:   80                length:    2,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    1    2
      Data :    1    2
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    4
      Data :    4
    end
end
   3
X
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :    2
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :    1
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    3
      Data :    3
    end
end
X   3:    1   2   3
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $i20 = V  k => 20; $t->put($i20, $i20);
  my $i30 = V  k => 30; $t->put($i30, $i30);
  my $i40 = V  k => 40; $t->put($i40, $i40);
  my $i10 = V  k => 10; $t->put($i10, $i10);
  my $i31 = V  k => 31; $t->put($i31, $i31);
  my $i32 = V  k => 32; $t->put($i32, $i32);
  my $i33 = V  k => 33; $t->put($i33, $i33);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("33"); $t->delete($i33);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("40"); $t->delete($i40);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("X"); $t->printInOrder("X");

  ok Assemble eq => <<END, avx512=>1;
   7
33
At:  200                    length:    2,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0    1
  Keys :   1E   20
  Data :   30   32
  Nodes:   80  140  2C0
    At:   80                length:    2,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    A   14
      Data :   10   20
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :   1F
      Data :   31
    end
    At:  2C0                length:    2,  data:  300,  nodes:  340,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :   21   28
      Data :   33   40
    end
end
   6
40
At:  200                    length:    2,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0    1
  Keys :   1E   20
  Data :   30   32
  Nodes:   80  140  2C0
    At:   80                length:    2,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    A   14
      Data :   10   20
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :   1F
      Data :   31
    end
    At:  2C0                length:    1,  data:  300,  nodes:  340,  first:   40,  up:  200, leaf
      Index:    0
      Keys :   28
      Data :   40
    end
end
   5
X
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :   1E
  Data :   30
  Nodes:   80  140
    At:   80                length:    2,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    A   14
      Data :   10   20
    end
    At:  140                length:    2,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :   1F   20
      Data :   31   32
    end
end
X   5:    A  14  1E  1F  20
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $i1 = V  k =>  0; $t->put($i1, $i1);
  my $i2 = V  k => 11; $t->put($i2, $i2);
  my $i3 = V  k => 13; $t->put($i3, $i3);
  my $i4 = V  k => 15; $t->put($i4, $i4);
  $t->size->outRightInDecNL(K width => 4);
  $t->dump("1");
  $a->dump("AAA", K blocks => 12);
  $t->delete($i2);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("X"); $t->printInOrder("X");

  ok Assemble eq => <<END, avx512=>1;
   4
1
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    B
  Data :   11
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    0
      Data :    0
    end
    At:  140                length:    2,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    D    F
      Data :   13   15
    end
end
AAA
Area     Size:     4096    Used:      704
.... .... .... .... | __10 ____ ____ ____  C0.2 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | __.2 ____ ____ ____  .4__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ C0__ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ __.1 ____
.... .... .... .1.. | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .140 | .D__ ____ .F__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .2__ ____ 80.1 ____
.... .... .... .180 | .D__ ____ .F__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ C0.1 ____
.... .... .... .1C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .2.. | .B__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ 40.2 ____
.... .... .... .240 | .B__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 80.2 ____
.... .... .... .280 | 80__ ____ 40.1 ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .2C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
   3
X
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    D
  Data :   13
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    0
      Data :    0
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    F
      Data :   15
    end
end
X   3:    0   D   F
END
 }


#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $i1 = V  k => 1; $t->put($i1, $i1);
  my $i2 = V  k => 2; $t->put($i2, $i2);
  my $i3 = V  k => 3; $t->put($i3, $i3);
  my $i4 = V  k => 4; $t->put($i4, $i4);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("1"); $a->dump("AAA", K blocks => 12); $t->delete($i1);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("X"); $t->printInOrder("X");

  ok Assemble eq => <<END, avx512=>1;
   4
1
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :    2
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :    1
    end
    At:  140                length:    2,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    3    4
      Data :    3    4
    end
end
AAA
Area     Size:     4096    Used:      704
.... .... .... .... | __10 ____ ____ ____  C0.2 ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | __.2 ____ ____ ____  .4__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | .1__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ C0__ ____
.... .... .... ..C0 | .1__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ __.1 ____
.... .... .... .1.. | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .140 | .3__ ____ .4__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .2__ ____ 80.1 ____
.... .... .... .180 | .3__ ____ .4__ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  __.2 ____ C0.1 ____
.... .... .... .1C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .2.. | .2__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  .1__ ____ 40.2 ____
.... .... .... .240 | .2__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 80.2 ____
.... .... .... .280 | 80__ ____ 40.1 ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ 40__ ____
.... .... .... .2C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
   3
X
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    3
  Data :    3
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    2
      Data :    2
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    4
      Data :    4
    end
end
X   3:    2   3   4
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $i1 = V  k => 1; $t->put($i1, $i1);
  my $i2 = V  k => 2; $t->put($i2, $i2);
  my $i3 = V  k => 3; $t->put($i3, $i3);
  my $i4 = V  k => 4; $t->put($i4, $i4);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("2"); $t->delete($i2);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("X"); $t->printInOrder("X");

  ok Assemble eq => <<END, avx512=>1;
   4
2
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :    2
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :    1
    end
    At:  140                length:    2,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    3    4
      Data :    3    4
    end
end
   3
X
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    3
  Data :    3
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :    1
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    4
      Data :    4
    end
end
X   3:    1   3   4
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $i1 = V  k => 1; $t->put($i1, $i1);
  my $i2 = V  k => 2; $t->put($i2, $i2);
  my $i3 = V  k => 3; $t->put($i3, $i3);
  my $i4 = V  k => 4; $t->put($i4, $i4);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("3"); $t->delete($i3);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("X"); $t->printInOrder("X");

  ok Assemble eq => <<END, avx512=>1;
   4
3
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :    2
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :    1
    end
    At:  140                length:    2,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    3    4
      Data :    3    4
    end
end
   3
X
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :    2
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :    1
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    4
      Data :    4
    end
end
X   3:    1   2   4
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $i1 = V  k => 1; $t->put($i1, $i1);
  my $i2 = V  k => 2; $t->put($i2, $i2);
  my $i3 = V  k => 3; $t->put($i3, $i3);
  my $i4 = V  k => 4; $t->put($i4, $i4);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("4"); $t->delete($i4);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("X"); $t->printInOrder("X");

  ok Assemble eq => <<END, avx512=>1;
   4
4
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :    2
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :    1
    end
    At:  140                length:    2,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    3    4
      Data :    3    4
    end
end
   3
X
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :    2
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :    1
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    3
      Data :    3
    end
end
X   3:    1   2   3
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $i2 = V  k => 2; $t->put($i2, $i2);
  my $i1 = V  k => 1; $t->put($i1, $i1);
  my $i3 = V  k => 3; $t->put($i3, $i3);
  my $i4 = V  k => 4; $t->put($i4, $i4);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("0"); $t->delete($i2);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("2"); $t->delete($i3);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("3"); $t->delete($i4);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("4"); $t->delete($i1);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("1");

  ok Assemble eq => <<END, avx512=>1;
   4
0
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :    2
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :    1
    end
    At:  140                length:    2,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    3    4
      Data :    3    4
    end
end
   3
2
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    3
  Data :    3
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :    1
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    4
      Data :    4
    end
end
   2
3
At:   80                    length:    2,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0    1
  Keys :    1    4
  Data :    1    4
end
   1
4
At:   80                    length:    1,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0
  Keys :    1
  Data :    1
end
   0
1
- empty
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  $t->put(   K(k=>1), K(d=>11));
  $t->put(   K(k=>2), K(d=>22));
  $t->put(   K(k=>3), K(d=>33));
  $t->delete(K k=>1);  $t->dump("1");
  $t->delete(K k=>3);  $t->dump("3");
  $t->delete(K k=>2);  $t->dump("2");
  ok Assemble eq => <<END, avx512=>1;
1
At:   80                    length:    2,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0    1
  Keys :    2    3
  Data :   22   33
end
3
At:   80                    length:    1,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0
  Keys :    2
  Data :   22
end
2
- empty
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  $t->put(   K(k=>1), K(d=>11));
  $t->put(   K(k=>2), K(d=>22));
  $t->put(   K(k=>3), K(d=>33));
  $t->put(   K(k=>4), K(d=>44));
  $t->dump("0");
  $t->delete(K k=>1);
  $t->dump("1");
  $t->delete(K k=>2);
  $t->dump("2");
  $t->delete(K k=>3);
  $t->dump("3");
  $t->delete(K k=>4);
  $t->dump("4");
  ok Assemble eq => <<END, avx512=>1;
0
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :   22
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :   11
    end
    At:  140                length:    2,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    3    4
      Data :   33   44
    end
end
1
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    3
  Data :   33
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    2
      Data :   22
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    4
      Data :   44
    end
end
2
At:   80                    length:    2,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0    1
  Keys :    3    4
  Data :   33   44
end
3
At:   80                    length:    1,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0
  Keys :    4
  Data :   44
end
4
- empty
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  $t->put(   K(k=>1), K(d=>11));
  $t->put(   K(k=>2), K(d=>22));
  $t->put(   K(k=>3), K(d=>33));
  $t->put(   K(k=>4), K(d=>44));
  $t->dump("0");
  $t->delete(K k=>3);
  $t->dump("3");
  $t->delete(K k=>4);
  $t->dump("4");
  $t->delete(K k=>2);
  $t->dump("2");
  $t->delete(K k=>1);
  $t->dump("1");
  ok Assemble eq => <<END, avx512=>1;
0
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :   22
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :   11
    end
    At:  140                length:    2,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    3    4
      Data :   33   44
    end
end
3
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    2
  Data :   22
  Nodes:   80  140
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    1
      Data :   11
    end
    At:  140                length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    4
      Data :   44
    end
end
4
At:   80                    length:    2,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0    1
  Keys :    1    2
  Data :   11   22
end
2
At:   80                    length:    1,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0
  Keys :    1
  Data :   11
end
1
- empty
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $i1 = V  k => 1; $t->put($i1, $i1);
  my $i2 = V  k => 2; $t->put($i2, $i2);
  my $i3 = V  k => 3; $t->put($i3, $i3);
  my $i4 = V  k => 4; $t->put($i4, $i4);
  my $i5 = V  k => 5; $t->put($i5, $i5);
  my $i6 = V  k => 6; $t->put($i6, $i6);
  my $i7 = V  k => 7; $t->put($i7, $i7);
  my $i8 = V  k => 8; $t->put($i8, $i8);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("1"); $t->delete($i1);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("2"); $t->delete($i2);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("3"); $t->delete($i3);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("4"); $t->delete($i4);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("5"); $t->delete($i5);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("6"); $t->delete($i6);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("7"); $t->delete($i7);
  $t->size->outRightInDecNL(K width => 4);  $t->dump("8"); $t->delete($i8);
  $t->size->outRightInDecNL(K width => 4);
  $t->dump("X");

  ok Assemble eq => <<END, avx512=>1;
   8
1
At:  500                    length:    1,  data:  540,  nodes:  580,  first:   40, root, parent
  Index:    0
  Keys :    4
  Data :    4
  Nodes:  200  440
    At:  200                length:    1,  data:  240,  nodes:  280,  first:   40,  up:  500, parent
      Index:    0
      Keys :    2
      Data :    2
      Nodes:   80  140
        At:   80            length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
          Index:    0
          Keys :    1
          Data :    1
        end
        At:  140            length:    1,  data:  180,  nodes:  1C0,  first:   40,  up:  200, leaf
          Index:    0
          Keys :    3
          Data :    3
        end
    end
    At:  440                length:    1,  data:  480,  nodes:  4C0,  first:   40,  up:  500, parent
      Index:    0
      Keys :    6
      Data :    6
      Nodes:  2C0  380
        At:  2C0            length:    1,  data:  300,  nodes:  340,  first:   40,  up:  440, leaf
          Index:    0
          Keys :    5
          Data :    5
        end
        At:  380            length:    2,  data:  3C0,  nodes:  400,  first:   40,  up:  440, leaf
          Index:    0    1
          Keys :    7    8
          Data :    7    8
        end
    end
end
   7
2
At:  200                    length:    2,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0    1
  Keys :    4    6
  Data :    4    6
  Nodes:   80  2C0  380
    At:   80                length:    2,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    2    3
      Data :    2    3
    end
    At:  2C0                length:    1,  data:  300,  nodes:  340,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    5
      Data :    5
    end
    At:  380                length:    2,  data:  3C0,  nodes:  400,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    7    8
      Data :    7    8
    end
end
   6
3
At:  200                    length:    2,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0    1
  Keys :    4    6
  Data :    4    6
  Nodes:   80  2C0  380
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    3
      Data :    3
    end
    At:  2C0                length:    1,  data:  300,  nodes:  340,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    5
      Data :    5
    end
    At:  380                length:    2,  data:  3C0,  nodes:  400,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    7    8
      Data :    7    8
    end
end
   5
4
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    6
  Data :    6
  Nodes:   80  380
    At:   80                length:    2,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    4    5
      Data :    4    5
    end
    At:  380                length:    2,  data:  3C0,  nodes:  400,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    7    8
      Data :    7    8
    end
end
   4
5
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    6
  Data :    6
  Nodes:   80  380
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    5
      Data :    5
    end
    At:  380                length:    2,  data:  3C0,  nodes:  400,  first:   40,  up:  200, leaf
      Index:    0    1
      Keys :    7    8
      Data :    7    8
    end
end
   3
6
At:  200                    length:    1,  data:  240,  nodes:  280,  first:   40, root, parent
  Index:    0
  Keys :    7
  Data :    7
  Nodes:   80  380
    At:   80                length:    1,  data:   C0,  nodes:  100,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    6
      Data :    6
    end
    At:  380                length:    1,  data:  3C0,  nodes:  400,  first:   40,  up:  200, leaf
      Index:    0
      Keys :    8
      Data :    8
    end
end
   2
7
At:   80                    length:    2,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0    1
  Keys :    7    8
  Data :    7    8
end
   1
8
At:   80                    length:    1,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0
  Keys :    8
  Data :    8
end
   0
X
- empty
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K loop => 20;
  $N->for(sub                                                                   # Load tree
   {my ($i) = @_;
    $t->put($i, $i);
   });
  $t->size->outNL;        $t->printInOrder("AA");
  $t->delete(K k =>  0);  $t->printInOrder(" 0");
  $t->delete(K k =>  9);  $t->printInOrder(" 9");
  $t->delete(K k =>  1);  $t->printInOrder(" 1");
  $t->delete(K k =>  8);  $t->printInOrder(" 8");
  $t->delete(K k =>  2);  $t->printInOrder(" 2");
  $t->delete(K k =>  7);  $t->printInOrder(" 7");
  $t->delete(K k =>  3);  $t->printInOrder(" 3");
  $t->delete(K k =>  6);  $t->printInOrder(" 6");
  $t->delete(K k =>  4);  $t->printInOrder(" 4");
  $t->delete(K k =>  5);  $t->printInOrder(" 5");
  $t->delete(K k => 10);  $t->printInOrder("10");
  $t->delete(K k => 19);  $t->printInOrder("19");
  $t->delete(K k => 11);  $t->printInOrder("11");
  $t->delete(K k => 18);  $t->printInOrder("18");
  $t->delete(K k => 12);  $t->printInOrder("12");
  $t->delete(K k => 17);  $t->printInOrder("17");
  $t->delete(K k => 13);  $t->printInOrder("13");
  $t->delete(K k => 16);  $t->printInOrder("16");
  $t->delete(K k => 14);  $t->printInOrder("14");
  $t->delete(K k => 15);  $t->printInOrder("15");

  ok Assemble eq => <<END, avx512=>1;
size of tree: .... .... .... ..14
AA  20:    0   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13
 0  19:    1   2   3   4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13
 9  18:    1   2   3   4   5   6   7   8   A   B   C   D   E   F  10  11  12  13
 1  17:    2   3   4   5   6   7   8   A   B   C   D   E   F  10  11  12  13
 8  16:    2   3   4   5   6   7   A   B   C   D   E   F  10  11  12  13
 2  15:    3   4   5   6   7   A   B   C   D   E   F  10  11  12  13
 7  14:    3   4   5   6   A   B   C   D   E   F  10  11  12  13
 3  13:    4   5   6   A   B   C   D   E   F  10  11  12  13
 6  12:    4   5   A   B   C   D   E   F  10  11  12  13
 4  11:    5   A   B   C   D   E   F  10  11  12  13
 5  10:    A   B   C   D   E   F  10  11  12  13
10   9:    B   C   D   E   F  10  11  12  13
19   8:    B   C   D   E   F  10  11  12
11   7:    C   D   E   F  10  11  12
18   6:    C   D   E   F  10  11
12   5:    D   E   F  10  11
17   4:    D   E   F  10
13   3:    E   F  10
16   2:    E   F
14   1:    F
15- empty
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K loop => 16;
  $N->for(sub
   {my ($i) = @_;
    $t->put($i, $i);
   });
  $t->printInOrder(" 0"); $t->delete(K k =>  0);
  $t->printInOrder(" 2"); $t->delete(K k =>  2);
  $t->printInOrder(" 4"); $t->delete(K k =>  4);
  $t->printInOrder(" 6"); $t->delete(K k =>  6);
  $t->printInOrder(" 8"); $t->delete(K k =>  8);
  $t->printInOrder("10"); $t->delete(K k => 10);
  $t->printInOrder("12"); $t->delete(K k => 12);
  $t->printInOrder("14"); $t->delete(K k => 14);
  $t->printInOrder(" 1"); $t->delete(K k =>  1);
  $t->printInOrder(" 3"); $t->delete(K k =>  3);
  $t->printInOrder(" 5"); $t->delete(K k =>  5);
  $t->printInOrder(" 7"); $t->delete(K k =>  7);
  $t->printInOrder(" 9"); $t->delete(K k =>  9);
  $t->printInOrder("11"); $t->delete(K k => 11);
  $t->printInOrder("13"); $t->delete(K k => 13);
  $t->printInOrder("15"); $t->delete(K k => 15);
  $t->printInOrder("XX");

  ok Assemble eq => <<END, avx512=>1;
 0  16:    0   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
 2  15:    1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
 4  14:    1   3   4   5   6   7   8   9   A   B   C   D   E   F
 6  13:    1   3   5   6   7   8   9   A   B   C   D   E   F
 8  12:    1   3   5   7   8   9   A   B   C   D   E   F
10  11:    1   3   5   7   9   A   B   C   D   E   F
12  10:    1   3   5   7   9   B   C   D   E   F
14   9:    1   3   5   7   9   B   D   E   F
 1   8:    1   3   5   7   9   B   D   F
 3   7:    3   5   7   9   B   D   F
 5   6:    5   7   9   B   D   F
 7   5:    7   9   B   D   F
 9   4:    9   B   D   F
11   3:    B   D   F
13   2:    D   F
15   1:    F
XX- empty
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K max => 8;

  $N->for(sub                                                                   # Load tree
   {my ($i) = @_;
    $t->put(         $i,     2 *        $i);
    $t->put(2 * $N - $i - 1, 2 * ($N -  $i));
   });
#  $t->printInOrder("Full");

  ($N-1)->for(sub                                                               # Delete elements
   {my ($i) = @_;
    my $n1 = ($N + $i)->clone("1111"); my $n2 = ($N - $i - 1)->clone("2222");

    $n1->outNL;
    $t->delete($n1);
    $t->printInOrder("1111");

    $n2->outNL;
    $t->delete($n2);
    $t->printInOrder("2222");
   });
  $t->dump("Two:");
  $t->size->outRightInDecNL(K width => 4);

  ok Assemble eq => <<END, avx512=>1;
1111: .... .... .... ...8
1111  15:    0   1   2   3   4   5   6   7   9   A   B   C   D   E   F
2222: .... .... .... ...7
2222  14:    0   1   2   3   4   5   6   9   A   B   C   D   E   F
1111: .... .... .... ...9
1111  13:    0   1   2   3   4   5   6   A   B   C   D   E   F
2222: .... .... .... ...6
2222  12:    0   1   2   3   4   5   A   B   C   D   E   F
1111: .... .... .... ...A
1111  11:    0   1   2   3   4   5   B   C   D   E   F
2222: .... .... .... ...5
2222  10:    0   1   2   3   4   B   C   D   E   F
1111: .... .... .... ...B
1111   9:    0   1   2   3   4   C   D   E   F
2222: .... .... .... ...4
2222   8:    0   1   2   3   C   D   E   F
1111: .... .... .... ...C
1111   7:    0   1   2   3   D   E   F
2222: .... .... .... ...3
2222   6:    0   1   2   D   E   F
1111: .... .... .... ...D
1111   5:    0   1   2   E   F
2222: .... .... .... ...2
2222   4:    0   1   E   F
1111: .... .... .... ...E
1111   3:    0   1   F
2222: .... .... .... ...1
2222   2:    0   F
Two:
At:   80                    length:    2,  data:   C0,  nodes:  100,  first:   40, root, leaf
  Index:    0    1
  Keys :    0    F
  Data :    0   16
end
   2
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K max => 100;

  $N->for(sub                                                                   # Load tree
   {my ($index, $start, $next, $end) = @_;
    $t->put($index, 2 * $index);
    If $t->size != $index + 1,
    Then
     {PrintOutStringNL "SSSS"; $index->outNL; Exit(0);
     };
   });

  $N->for(sub                                                                   # Check elements
   {my ($i) = @_;
    $t->find($i);
    If $t->found == 0,
    Then
     {PrintOutStringNL "AAAA"; $i->outNL; Exit(0);
     };
   });

  $N->for(sub                                                                   # Delete elements
   {my ($i) = @_;
    $t->delete($i);

    If $t->size != $N - $i - 1,
    Then
     {PrintOutStringNL "TTTT"; $i->outNL; Exit(0);
     };

    $N->for(sub                                                                 # Check elements
     {my ($j) = @_;
      $t->find($j);
      If $t->found == 0,
      Then
       {If $j > $i,
        Then
         {PrintOutStringNL "BBBBB"; $j->outNL; Exit(0);                         # Not deleted yet so it should be findable
         };
       },
      Else
       {If $j <= $i,
        Then
         {PrintOutStringNL "CCCCC"; $j->outNL; Exit(0);                         # Deleted so should not be findable
         };
       };
     });
   });

  ok Assemble eq => <<END, avx512=>1;
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K loop => 16;
  $N->for(sub
   {my ($i) = @_;
    $t->put($i, $i);
   });
  ($N/2)->for(sub
   {my ($i) = @_;
    $t->printInOrder("AAAA");
    $t->delete($i * 2);
   });
  ($N/2)->for(sub
   {my ($i) = @_;
    $t->printInOrder("BBBB");
    $t->delete($i * 2 + 1);
   });
  $t->printInOrder("CCCC");

  ok Assemble eq => <<END, avx512=>1;
AAAA  16:    0   1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
AAAA  15:    1   2   3   4   5   6   7   8   9   A   B   C   D   E   F
AAAA  14:    1   3   4   5   6   7   8   9   A   B   C   D   E   F
AAAA  13:    1   3   5   6   7   8   9   A   B   C   D   E   F
AAAA  12:    1   3   5   7   8   9   A   B   C   D   E   F
AAAA  11:    1   3   5   7   9   A   B   C   D   E   F
AAAA  10:    1   3   5   7   9   B   C   D   E   F
AAAA   9:    1   3   5   7   9   B   D   E   F
BBBB   8:    1   3   5   7   9   B   D   F
BBBB   7:    3   5   7   9   B   D   F
BBBB   6:    5   7   9   B   D   F
BBBB   5:    7   9   B   D   F
BBBB   4:    9   B   D   F
BBBB   3:    B   D   F
BBBB   2:    D   F
BBBB   1:    F
CCCC- empty
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::delete
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K loop => 36;
  $N->for(sub
   {my ($i) = @_;
    $t->put($i, $i);
   });
  $t->delete(K 1 =>  0); $t->printInOrder(" 0");
  $t->delete(K 1 =>  5); $t->printInOrder(" 5");
  $t->delete(K 1 => 10); $t->printInOrder("10");
  $t->delete(K 1 => 15); $t->printInOrder("15");
  $t->delete(K 1 => 20); $t->printInOrder("20");
  $t->delete(K 1 => 25); $t->printInOrder("25");
  $t->delete(K 1 => 30); $t->printInOrder("30");
  $t->delete(K 1 => 35); $t->printInOrder("35");

  $t->delete(K 1 =>  1); $t->printInOrder(" 1");
  $t->delete(K 1 =>  6); $t->printInOrder(" 6");
  $t->delete(K 1 => 11); $t->printInOrder("11");
  $t->delete(K 1 => 16); $t->printInOrder("16");
  $t->delete(K 1 => 21); $t->printInOrder("21");
  $t->delete(K 1 => 26); $t->printInOrder("26");
  $t->delete(K 1 => 31); $t->printInOrder("31");

  $t->delete(K 1 =>  2); $t->printInOrder(" 2");
  $t->delete(K 1 =>  7); $t->printInOrder(" 7");
  $t->delete(K 1 => 12); $t->printInOrder("12");
  $t->delete(K 1 => 17); $t->printInOrder("17");
  $t->delete(K 1 => 22); $t->printInOrder("22");
  $t->delete(K 1 => 27); $t->printInOrder("27");
  $t->delete(K 1 => 32); $t->printInOrder("32");

  $t->delete(K 1 =>  3); $t->printInOrder(" 3");
  $t->delete(K 1 =>  8); $t->printInOrder(" 8");
  $t->delete(K 1 => 13); $t->printInOrder("13");
  $t->delete(K 1 => 18); $t->printInOrder("18");
  $t->delete(K 1 => 23); $t->printInOrder("23");
  $t->delete(K 1 => 28); $t->printInOrder("28");
  $t->delete(K 1 => 33); $t->printInOrder("33");

  $t->delete(K 1 =>  4); $t->printInOrder(" 4");
  $t->delete(K 1 =>  9); $t->printInOrder(" 9");
  $t->delete(K 1 => 14); $t->printInOrder("14");
  $t->delete(K 1 => 19); $t->printInOrder("19");
  $t->delete(K 1 => 24); $t->printInOrder("24");
  $t->delete(K 1 => 29); $t->printInOrder("29");
  $t->delete(K 1 => 34); $t->printInOrder("34");

  ok Assemble eq => <<END, avx512=>1;
 0  35:    1   2   3   4   5   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23
 5  34:    1   2   3   4   6   7   8   9   A   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23
10  33:    1   2   3   4   6   7   8   9   B   C   D   E   F  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23
15  32:    1   2   3   4   6   7   8   9   B   C   D   E  10  11  12  13  14  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23
20  31:    1   2   3   4   6   7   8   9   B   C   D   E  10  11  12  13  15  16  17  18  19  1A  1B  1C  1D  1E  1F  20  21  22  23
25  30:    1   2   3   4   6   7   8   9   B   C   D   E  10  11  12  13  15  16  17  18  1A  1B  1C  1D  1E  1F  20  21  22  23
30  29:    1   2   3   4   6   7   8   9   B   C   D   E  10  11  12  13  15  16  17  18  1A  1B  1C  1D  1F  20  21  22  23
35  28:    1   2   3   4   6   7   8   9   B   C   D   E  10  11  12  13  15  16  17  18  1A  1B  1C  1D  1F  20  21  22
 1  27:    2   3   4   6   7   8   9   B   C   D   E  10  11  12  13  15  16  17  18  1A  1B  1C  1D  1F  20  21  22
 6  26:    2   3   4   7   8   9   B   C   D   E  10  11  12  13  15  16  17  18  1A  1B  1C  1D  1F  20  21  22
11  25:    2   3   4   7   8   9   C   D   E  10  11  12  13  15  16  17  18  1A  1B  1C  1D  1F  20  21  22
16  24:    2   3   4   7   8   9   C   D   E  11  12  13  15  16  17  18  1A  1B  1C  1D  1F  20  21  22
21  23:    2   3   4   7   8   9   C   D   E  11  12  13  16  17  18  1A  1B  1C  1D  1F  20  21  22
26  22:    2   3   4   7   8   9   C   D   E  11  12  13  16  17  18  1B  1C  1D  1F  20  21  22
31  21:    2   3   4   7   8   9   C   D   E  11  12  13  16  17  18  1B  1C  1D  20  21  22
 2  20:    3   4   7   8   9   C   D   E  11  12  13  16  17  18  1B  1C  1D  20  21  22
 7  19:    3   4   8   9   C   D   E  11  12  13  16  17  18  1B  1C  1D  20  21  22
12  18:    3   4   8   9   D   E  11  12  13  16  17  18  1B  1C  1D  20  21  22
17  17:    3   4   8   9   D   E  12  13  16  17  18  1B  1C  1D  20  21  22
22  16:    3   4   8   9   D   E  12  13  17  18  1B  1C  1D  20  21  22
27  15:    3   4   8   9   D   E  12  13  17  18  1C  1D  20  21  22
32  14:    3   4   8   9   D   E  12  13  17  18  1C  1D  21  22
 3  13:    4   8   9   D   E  12  13  17  18  1C  1D  21  22
 8  12:    4   9   D   E  12  13  17  18  1C  1D  21  22
13  11:    4   9   E  12  13  17  18  1C  1D  21  22
18  10:    4   9   E  13  17  18  1C  1D  21  22
23   9:    4   9   E  13  18  1C  1D  21  22
28   8:    4   9   E  13  18  1D  21  22
33   7:    4   9   E  13  18  1D  22
 4   6:    9   E  13  18  1D  22
 9   5:    E  13  18  1D  22
14   4:   13  18  1D  22
19   3:   18  1D  22
24   2:   1D  22
29   1:   22
34- empty
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::findNext
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K loop => 8;
  $N->for(sub
   {my ($i) = @_;
    $t->put(2*$i, 2*$i);
   });

  (2*$N)->for(sub
   {my ($i) = @_;
    $i->outRightInDec(K(key => 4)); PrintOutString " -> ";
    $t->findNext($i);
    $t->found->out("f: ", " ");
    If $t->found > 0, Then {$t->key->out};
    PrintOutStringNL '.';
   });

  ok Assemble eq => <<END, avx512=>1;
   0 -> f: .... .... .... ...1 key: .... .... .... ...2.
   1 -> f: .... .... .... ...1 key: .... .... .... ...2.
   2 -> f: .... .... .... ...1 key: .... .... .... ...4.
   3 -> f: .... .... .... ...1 key: .... .... .... ...4.
   4 -> f: .... .... .... ...1 key: .... .... .... ...6.
   5 -> f: .... .... .... ...1 key: .... .... .... ...6.
   6 -> f: .... .... .... ...1 key: .... .... .... ...8.
   7 -> f: .... .... .... ...1 key: .... .... .... ...8.
   8 -> f: .... .... .... ...1 key: .... .... .... ...A.
   9 -> f: .... .... .... ...1 key: .... .... .... ...A.
  10 -> f: .... .... .... ...1 key: .... .... .... ...C.
  11 -> f: .... .... .... ...1 key: .... .... .... ...C.
  12 -> f: .... .... .... ...2 key: .... .... .... ...E.
  13 -> f: .... .... .... ...2 key: .... .... .... ...E.
  14 -> f: .... .... .... .... .
  15 -> f: .... .... .... .... .
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::findPrev
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K loop => 8;
  $N->for(sub
   {my ($i) = @_;
    $t->put(2*$i, 2*$i);
   });

  (2*$N)->for(sub
   {my ($i) = @_;
    $i->outRightInDec(K(key => 4)); PrintOutString " -> ";
    $t->findPrev($i);
    $t->found->out("f: ", " ");
    If $t->found > 0, Then {$t->key->out};
    PrintOutStringNL '.';
   });

  ok Assemble eq => <<END, avx512=>1;
   0 -> f: .... .... .... .... .
   1 -> f: .... .... .... ...1 key: .... .... .... .....
   2 -> f: .... .... .... ...1 key: .... .... .... .....
   3 -> f: .... .... .... ...1 key: .... .... .... ...2.
   4 -> f: .... .... .... ...1 key: .... .... .... ...2.
   5 -> f: .... .... .... ...1 key: .... .... .... ...4.
   6 -> f: .... .... .... ...1 key: .... .... .... ...4.
   7 -> f: .... .... .... ...1 key: .... .... .... ...6.
   8 -> f: .... .... .... ...1 key: .... .... .... ...6.
   9 -> f: .... .... .... ...1 key: .... .... .... ...8.
  10 -> f: .... .... .... ...1 key: .... .... .... ...8.
  11 -> f: .... .... .... ...1 key: .... .... .... ...A.
  12 -> f: .... .... .... ...1 key: .... .... .... ...A.
  13 -> f: .... .... .... ...1 key: .... .... .... ...C.
  14 -> f: .... .... .... ...1 key: .... .... .... ...C.
  15 -> f: .... .... .... ...2 key: .... .... .... ...E.
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::by
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K loop => 16;
  $N->for(sub
   {my ($i) = @_;
    $t->put($i, 2 * $i);
   });

  $t->by(sub
   {my ($tree, $start, $next, $end) = @_;
    $tree->key->out("");  $tree->data->outNL(" ");
   });

  ok Assemble eq => <<END, avx512=>1;
.... .... .... .... .... .... .... ....
.... .... .... ...1 .... .... .... ...2
.... .... .... ...2 .... .... .... ...4
.... .... .... ...3 .... .... .... ...6
.... .... .... ...4 .... .... .... ...8
.... .... .... ...5 .... .... .... ...A
.... .... .... ...6 .... .... .... ...C
.... .... .... ...7 .... .... .... ...E
.... .... .... ...8 .... .... .... ..10
.... .... .... ...9 .... .... .... ..12
.... .... .... ...A .... .... .... ..14
.... .... .... ...B .... .... .... ..16
.... .... .... ...C .... .... .... ..18
.... .... .... ...D .... .... .... ..1A
.... .... .... ...E .... .... .... ..1C
.... .... .... ...F .... .... .... ..1E
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::yb
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K loop => 16;
  $N->for(sub
   {my ($i) = @_;
    $t->put($i, 2* $i);
   });

  $t->yb(sub
   {my ($tree, $start, $prev, $end) = @_;
    $tree->key->out("");  $tree->data->outNL(" ");
   });

  ok Assemble eq => <<END, avx512=>1;
.... .... .... ...F .... .... .... ..1E
.... .... .... ...E .... .... .... ..1C
.... .... .... ...D .... .... .... ..1A
.... .... .... ...C .... .... .... ..18
.... .... .... ...B .... .... .... ..16
.... .... .... ...A .... .... .... ..14
.... .... .... ...9 .... .... .... ..12
.... .... .... ...8 .... .... .... ..10
.... .... .... ...7 .... .... .... ...E
.... .... .... ...6 .... .... .... ...C
.... .... .... ...5 .... .... .... ...A
.... .... .... ...4 .... .... .... ...8
.... .... .... ...3 .... .... .... ...6
.... .... .... ...2 .... .... .... ...4
.... .... .... ...1 .... .... .... ...2
.... .... .... .... .... .... .... ....
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::push #TNasm::X86::Tree::peek #TNasm::X86::Tree::pop #TNasm::X86::Tree::get
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K loop => 16;
  $N->for(sub
   {my ($i) = @_;
    $t->push($i);
   });

  $t->peek(K key => 1)->data ->outNL;
  $t->peek(K key => 2)->data ->outNL;
  $t->peek(K key => 3)->found->outNL;
  $t->peek(2 * $N    )->found->outNL;

  $t->size->outNL;
  $t->get(K(key => 8)); $t->found->out("f: ", " ");  $t->key->out("i: ", " "); $t->data->outNL;

  $N->for(sub
   {my ($i) = @_;
    $t->pop; $t->found->out("f: ", " ");  $t->key->out("i: ", " "); $t->data->outNL;
   });
  $t->pop; $t->found->outNL("f: ");

  ok Assemble eq => <<END, avx512=>1;
data: .... .... .... ...F
data: .... .... .... ...E
found: .... .... .... ...1
found: .... .... .... ....
size of tree: .... .... .... ..10
f: .... .... .... ...1 i: .... .... .... ...8 data: .... .... .... ...8
f: .... .... .... ...1 i: .... .... .... ...F data: .... .... .... ...F
f: .... .... .... ...1 i: .... .... .... ...E data: .... .... .... ...E
f: .... .... .... ...1 i: .... .... .... ...D data: .... .... .... ...D
f: .... .... .... ...1 i: .... .... .... ...C data: .... .... .... ...C
f: .... .... .... ...1 i: .... .... .... ...B data: .... .... .... ...B
f: .... .... .... ...1 i: .... .... .... ...A data: .... .... .... ...A
f: .... .... .... ...1 i: .... .... .... ...9 data: .... .... .... ...9
f: .... .... .... ...1 i: .... .... .... ...8 data: .... .... .... ...8
f: .... .... .... ...1 i: .... .... .... ...7 data: .... .... .... ...7
f: .... .... .... ...1 i: .... .... .... ...6 data: .... .... .... ...6
f: .... .... .... ...1 i: .... .... .... ...5 data: .... .... .... ...5
f: .... .... .... ...1 i: .... .... .... ...4 data: .... .... .... ...4
f: .... .... .... ...1 i: .... .... .... ...3 data: .... .... .... ...3
f: .... .... .... ...1 i: .... .... .... ...2 data: .... .... .... ...2
f: .... .... .... ...1 i: .... .... .... ...1 data: .... .... .... ...1
f: .... .... .... ...1 i: .... .... .... .... data: .... .... .... ....
f: .... .... .... ....
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::clear #TNasm::X86::Tree::free #TNasm::X86::Area::freeChainSpace  #TNasm::X86::Area::clear
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $N = K loop => 16;

  $N->for(sub {my ($i) = @_; $t->push($i+1)});
  $t->size->out("t: ", " ");
  $a->used->out("u: ", " ");
  $a->freeChainSpace->out("f: ", " ");
  $a->size->outNL;
  $t->clear;
  $t->size->out("t: ", " ");
  $a->used->out("u: ", " ");
  $a->freeChainSpace->out("f: ", " ");
  $a->size->outNL;

  $N->for(sub {my ($i) = @_; $t->push($i+1)});
  $t->size->out("t: ", " ");
  $a->used->out("u: ", " ");
  $a->freeChainSpace->out("f: ", " ");
  $a->size->outNL;
  $t->clear;
  $t->size->out("t: ", " ");
  $a->used->out("u: ", " ");
  $a->freeChainSpace->out("f: ", " ");
  $a->size->outNL;

  $N->for(sub {my ($i) = @_; $t->push($i+1)});
  $t->free;
  $a->used->out("Clear tree:            u: ");
  $a->freeChainSpace->out(" f: ", " ");
  $a->size->outNL;

  $a->clear;
  $a->used->out("Clear area:            u: ");
  $a->freeChainSpace->out(" f: ", " ");
  $a->size->outNL;

  ok Assemble eq => <<END, avx512=>1;
t: .... .... .... ..10 u: .... .... .... .B80 f: .... .... .... .... size of area: .... .... .... 10..
t: .... .... .... .... u: .... .... .... .B80 f: .... .... .... .B40 size of area: .... .... .... 10..
t: .... .... .... ..10 u: .... .... .... .B80 f: .... .... .... .... size of area: .... .... .... 10..
t: .... .... .... .... u: .... .... .... .B80 f: .... .... .... .B40 size of area: .... .... .... 10..
Clear tree:            u: .... .... .... .B80 f: .... .... .... .B40 size of area: .... .... .... 10..
Clear area:            u: .... .... .... .... f: .... .... .... .... size of area: .... .... .... 10..
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Area::allocZmmBlock #TNasm::X86::Area::freeZmmBlock #TNasm::X86::Area::getZmmBlock #TNasm::X86::Area::putZmmBlock #TNasm::X86::Area::clearZmmBlock #TNasm::X86::Area::dump
  my $a = CreateArea;

  my $m = $a->allocZmmBlock;
  K(K => Rd(1..16))->loadZmm(31);

  $a->putZmmBlock  ($m, 31);
  $a->dump("A");

  $a->getZmmBlock  ($m, 30);
  $a->clearZmmBlock($m);
  $a->getZmmBlock  ($m, 29);

  $a->clearZmmBlock($m);
  PrintOutRegisterInHex 31, 30, 29;

  ok Assemble eq => <<END, avx512=>1;
A
Area     Size:     4096    Used:      128
.... .... .... .... | __10 ____ ____ ____  80__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | .1__ ____ .2__ ____  .3__ ____ .4__ ____  .5__ ____ .6__ ____  .7__ ____ .8__ ____  .9__ ____ .A__ ____  .B__ ____ .C__ ____  .D__ ____ .E__ ____  .F__ ____ 10__ ____
.... .... .... ..80 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
 zmm31: .... ..10 .... ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
 zmm30: .... ..10 .... ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
 zmm29: .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... .... + .... .... .... ....  .... .... .... .... - .... .... .... ....  .... .... .... ....
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Area::allocZmmBlock #TNasm::X86::Area::freeZmmBlock #TNasm::X86::Area::getZmmBlock #TNasm::X86::Area::putZmmBlock  #TNasm::X86::Area::dump
  my $a = CreateArea;

  K(loop => 3)->for(sub
   {my ($i, $start, $next, $end) = @_;
    $i->outNL;
    my $m1 = $a->allocZmmBlock;
    my $m2 = $a->allocZmmBlock;

    K(K => Rd(1..16))->loadZmm(31);
    K(K => Rd(17..32))->loadZmm(30);
    PrintOutRegisterInHex 31, 30;

    $a->putZmmBlock($m1, 31);
    $a->putZmmBlock($m2, 30);
    $a->dump("A");

    $a->getZmmBlock($m1, 30);
    $a->getZmmBlock($m2, 31);
    PrintOutRegisterInHex 31, 30;

    $a->clearZmmBlock($m1);
    $a->freeZmmBlock($m1);
    $a->dump("B");

    $a->freeZmmBlock($m2);
    $a->dump("C");
   });

  ok Assemble eq => <<END, avx512=>1;
index: .... .... .... ....
 zmm31: .... ..10 .... ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1C .... ..1B  .... ..1A .... ..19 + .... ..18 .... ..17  .... ..16 .... ..15 - .... ..14 .... ..13  .... ..12 .... ..11
A
Area     Size:     4096    Used:      192
.... .... .... .... | __10 ____ ____ ____  C0__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | .1__ ____ .2__ ____  .3__ ____ .4__ ____  .5__ ____ .6__ ____  .7__ ____ .8__ ____  .9__ ____ .A__ ____  .B__ ____ .C__ ____  .D__ ____ .E__ ____  .F__ ____ 10__ ____
.... .... .... ..80 | 11__ ____ 12__ ____  13__ ____ 14__ ____  15__ ____ 16__ ____  17__ ____ 18__ ____  19__ ____ 1A__ ____  1B__ ____ 1C__ ____  1D__ ____ 1E__ ____  1F__ ____ 20__ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
 zmm31: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1C .... ..1B  .... ..1A .... ..19 + .... ..18 .... ..17  .... ..16 .... ..15 - .... ..14 .... ..13  .... ..12 .... ..11
 zmm30: .... ..10 .... ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
B
Area     Size:     4096    Used:      192
.... .... .... .... | __10 ____ ____ ____  C0__ ____ ____ ____  ____ ____ ____ ____  40__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | 11__ ____ 12__ ____  13__ ____ 14__ ____  15__ ____ 16__ ____  17__ ____ 18__ ____  19__ ____ 1A__ ____  1B__ ____ 1C__ ____  1D__ ____ 1E__ ____  1F__ ____ 20__ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
C
Area     Size:     4096    Used:      192
.... .... .... .... | __10 ____ ____ ____  C0__ ____ ____ ____  ____ ____ ____ ____  80__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | 40__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
index: .... .... .... ...1
 zmm31: .... ..10 .... ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1C .... ..1B  .... ..1A .... ..19 + .... ..18 .... ..17  .... ..16 .... ..15 - .... ..14 .... ..13  .... ..12 .... ..11
A
Area     Size:     4096    Used:      192
.... .... .... .... | __10 ____ ____ ____  C0__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | 11__ ____ 12__ ____  13__ ____ 14__ ____  15__ ____ 16__ ____  17__ ____ 18__ ____  19__ ____ 1A__ ____  1B__ ____ 1C__ ____  1D__ ____ 1E__ ____  1F__ ____ 20__ ____
.... .... .... ..80 | .1__ ____ .2__ ____  .3__ ____ .4__ ____  .5__ ____ .6__ ____  .7__ ____ .8__ ____  .9__ ____ .A__ ____  .B__ ____ .C__ ____  .D__ ____ .E__ ____  .F__ ____ 10__ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
 zmm31: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1C .... ..1B  .... ..1A .... ..19 + .... ..18 .... ..17  .... ..16 .... ..15 - .... ..14 .... ..13  .... ..12 .... ..11
 zmm30: .... ..10 .... ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
B
Area     Size:     4096    Used:      192
.... .... .... .... | __10 ____ ____ ____  C0__ ____ ____ ____  ____ ____ ____ ____  80__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | 11__ ____ 12__ ____  13__ ____ 14__ ____  15__ ____ 16__ ____  17__ ____ 18__ ____  19__ ____ 1A__ ____  1B__ ____ 1C__ ____  1D__ ____ 1E__ ____  1F__ ____ 20__ ____
.... .... .... ..80 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
C
Area     Size:     4096    Used:      192
.... .... .... .... | __10 ____ ____ ____  C0__ ____ ____ ____  ____ ____ ____ ____  40__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | 80__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
index: .... .... .... ...2
 zmm31: .... ..10 .... ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
 zmm30: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1C .... ..1B  .... ..1A .... ..19 + .... ..18 .... ..17  .... ..16 .... ..15 - .... ..14 .... ..13  .... ..12 .... ..11
A
Area     Size:     4096    Used:      192
.... .... .... .... | __10 ____ ____ ____  C0__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | .1__ ____ .2__ ____  .3__ ____ .4__ ____  .5__ ____ .6__ ____  .7__ ____ .8__ ____  .9__ ____ .A__ ____  .B__ ____ .C__ ____  .D__ ____ .E__ ____  .F__ ____ 10__ ____
.... .... .... ..80 | 11__ ____ 12__ ____  13__ ____ 14__ ____  15__ ____ 16__ ____  17__ ____ 18__ ____  19__ ____ 1A__ ____  1B__ ____ 1C__ ____  1D__ ____ 1E__ ____  1F__ ____ 20__ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
 zmm31: .... ..20 .... ..1F  .... ..1E .... ..1D - .... ..1C .... ..1B  .... ..1A .... ..19 + .... ..18 .... ..17  .... ..16 .... ..15 - .... ..14 .... ..13  .... ..12 .... ..11
 zmm30: .... ..10 .... ...F  .... ...E .... ...D - .... ...C .... ...B  .... ...A .... ...9 + .... ...8 .... ...7  .... ...6 .... ...5 - .... ...4 .... ...3  .... ...2 .... ...1
B
Area     Size:     4096    Used:      192
.... .... .... .... | __10 ____ ____ ____  C0__ ____ ____ ____  ____ ____ ____ ____  40__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | 11__ ____ 12__ ____  13__ ____ 14__ ____  15__ ____ 16__ ____  17__ ____ 18__ ____  19__ ____ 1A__ ____  1B__ ____ 1C__ ____  1D__ ____ 1E__ ____  1F__ ____ 20__ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
C
Area     Size:     4096    Used:      192
.... .... .... .... | __10 ____ ____ ____  C0__ ____ ____ ____  ____ ____ ____ ____  80__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..40 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..80 | 40__ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
.... .... .... ..C0 | ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____  ____ ____ ____ ____
END
 }

#latest:
if (1) {                                                                        #Tconvert_rax_from_utf32_to_utf8
# $ 	U+0024                 010 0100                00100100                     24
# £ 	U+00A3 	          000 1010 0011                11000010 10100011            C2 A3
# ह 	  U+0939    	0000 1001 0011 1001                11100000 10100100 10111001   E0 A4 B9
# € 	U+20AC    	0010 0000 1010 1100                11100010 10000010 10101100   E2 82 AC
# 한 	U+D55C     	1101 0101 0101 1100                11101101 10010101 10011100   ED 95 9C
# 𐍈   	U+10348 	0 0001 0000 0011 0100 1000 	11110000 10010000 10001101 10001000   F0 90 8D 88
  Mov rax, 0x40;                                                                # 0x40
  convert_rax_from_utf32_to_utf8;
  PrintOutRegisterInHex rax;

  Mov rax, 0x03b1;                                                              # 0xCE 0xB1
  convert_rax_from_utf32_to_utf8;
  PrintOutRegisterInHex rax;

  Mov rax, 0x20ac;                                                              # 0xE2 0x82 0xAC;
  convert_rax_from_utf32_to_utf8;
  PrintOutRegisterInHex rax;

  Mov rax, 0x10348;                                                             # 0xf0 0x90 0x8d 0x88
  convert_rax_from_utf32_to_utf8;
  PrintOutRegisterInHex rax;

  ok Assemble eq => <<END, avx512=>1;
   rax: .... .... .... ..40
   rax: .... .... .... B1CE
   rax: .... .... ..AC 82E2
   rax: .... .... 888D 90F0
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::outAsUtf8 #TNasm::X86::Tree::append
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);

  $t->push(K alpha => 0x03b1);
  $t->push(K beta  => 0x03b2);
  $t->push(K gamma => 0x03b3);
  $t->push(K delta => 0x03b4);

  $t->outAsUtf8NL;

  $t->append($t);
  $t->outAsUtf8NL;

  $t->append($t);
  $t->outAsUtf8NL;

  my $T = $t->substring(K(key => 4), K(key => 8));
  $T->outAsUtf8NL;

  my $r = $T->reverse;
  $r->outAsUtf8NL;

  ok Assemble eq => <<END, avx512=>1;
αβγδ
αβγδαβγδ
αβγδαβγδαβγδαβγδ
αβγδ
δγβα
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::appendAscii #TNasm::X86::Tree::outAsUtf8NL
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $b = Rb(0x41..0x51);
  $t->appendAscii(K(address=> $b), K(size => 1));
  $t->outAsUtf8NL;
  ok Assemble eq => <<END, avx512=>1;
A
END
 }

latest:
if (1) {                                                                        #TNasm::X86::Tree::push
  my $b = Rb(0x41..0x51);
  my $a = CreateArea;
  my $T;
  for my $i(1..8)
   {my $t = $a->CreateTree(length => 3);
    $t->appendAscii(K(address=> $b), K(size => 1));
    $t->push($T) if $T;
    $T = $t;
   }

  $T->dump8xx("T");
  ok Assemble eq => <<END, avx512=>1, mix=>1;
T
Tree: .... .... .... .740
At:      780                                                                                length:        2,  data:      7C0,  nodes:      800,  first:      740, root, leaf,  trees:  10
  Index:        0        1
  Keys :        0        1
  Data :       41      64*
   Tree:      640
     At:      680                                                                           length:        2,  data:      6C0,  nodes:      700,  first:      640, root, leaf,  trees:  10
       Index:        0        1
       Keys :        0        1
       Data :       41      54*
        Tree:      540
          At:      580                                                                      length:        2,  data:      5C0,  nodes:      600,  first:      540, root, leaf,  trees:  10
            Index:        0        1
            Keys :        0        1
            Data :       41      44*
             Tree:      440
               At:      480                                                                 length:        2,  data:      4C0,  nodes:      500,  first:      440, root, leaf,  trees:  10
                 Index:        0        1
                 Keys :        0        1
                 Data :       41      34*
                  Tree:      340
                    At:      380                                                            length:        2,  data:      3C0,  nodes:      400,  first:      340, root, leaf,  trees:  10
                      Index:        0        1
                      Keys :        0        1
                      Data :       41      24*
                       Tree:      240
                         At:      280                                                       length:        2,  data:      2C0,  nodes:      300,  first:      240, root, leaf,  trees:  10
                           Index:        0        1
                           Keys :        0        1
                           Data :       41      14*
                            Tree:      140
                              At:      180                                                  length:        2,  data:      1C0,  nodes:      200,  first:      140, root, leaf,  trees:  10
                                Index:        0        1
                                Keys :        0        1
                                Data :       41       4*
                                 Tree:       40
                                   At:       80                                             length:        1,  data:       C0,  nodes:      100,  first:       40, root, leaf
                                     Index:        0
                                     Keys :        0
                                     Data :       41
                                   end
                              end
                         end
                    end
               end
          end
     end
end
END
exit;
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::outAsUtf8 #TNasm::X86::Tree::append
  my $a = CreateArea;
  my $p = $a->CreateTree(length => 3, usage=>q(stack));
  my $q = $a->CreateTree(length => 3);
  my $r = $a->CreateTree(length => 3);
  my $s = $a->CreateTree(length => 3);
  my $t = $a->CreateTree(length => 3);

  $s->push(K char => ord $_) for split //, 'abc1';
  $r->push(K char => ord $_) for split //, 'abd2';
  $q->push(K char => ord $_) for split //, 'abe3';
  $p +=    K(char => ord $_) for split //, 'abf4';

  $t->putString($_) for $s, $r, $q, $p;
  $t->dump('t = abcd');

  $t->find(K key => 0x61);
  for my $f(qw(found key data subTree offset))
   {$t->{$f}->outNL(sprintf("%-8s", $f));
   }

  $t->getString($s); $t->found->outNL("found:  ");
  $s--;
  my $f = $t->getString($s); $f->found->outNL("found:  "); $f->data->outNL("data:   ");
  $s->pop;
  my $F = $t->getString($s); $F->found->outNL("found:  "); $F->data->outNL("data:   ");

  ok Assemble eq => <<END, avx512=>1;
t = abcd
At:  AC0                    length:    1,  data:  B00,  nodes:  B40,  first:  140, root, leaf,  trees:   1
  Index:    0
  Keys :   61
  Data :  BC*
     At:  BC0               length:    1,  data:  C00,  nodes:  C40,  first:  A80, root, leaf,  trees:   1
       Index:    0
       Keys :   62
       Data :  E0*
          At:  E00          length:    1,  data:  E40,  nodes:  E80,  first:  B80, root, parent
            Index:    0
            Keys :   64
            Data :   50
            Nodes:  C80  D40
              At:  C80      length:    1,  data:  CC0,  nodes:  D00,  first:  B80,  up:  E00, leaf
                Index:    0
                Keys :   63
                Data :   49
              end
              At:  D40      length:    2,  data:  D80,  nodes:  DC0,  first:  B80,  up:  E00, leaf
                Index:    0    1
                Keys :   65   66
                Data :   51   52
              end
          end
     end
end
found   .... .... .... ...1
key     .... .... .... ..61
data    .... .... .... .A80
subTree .... .... .... ...1
offset  .... .... .... .AC0
found:  .... .... .... ...1
found:  .... .... .... ...1
data:   .... .... .... ..31
found:  .... .... .... ...1
data:   .... .... .... .B80
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::popSubTree
  my $a = CreateArea;
  my $t = $a->CreateTree(length => 3);
  my $T = $a->CreateTree(length => 3);

  $T->push(K key => 1);
  $t->push($T);
  $t->dump8('AA');
  my $s = $t->popSubTree;
  $t->dump8('BB');
  $s->dump8('CC');
  ok Assemble eq => <<END, avx512=>1;
AA
Tree: .... .... .... ..40
At:      180                                                                                length:        1,  data:      1C0,  nodes:      200,  first:       40, root, leaf,  trees:   1
  Index:        0
  Keys :        0
  Data :       8*
   Tree:       80
     At:       C0                                                                           length:        1,  data:      100,  nodes:      140,  first:       80, root, leaf
       Index:        0
       Keys :        0
       Data :        1
     end
end
BB
- empty
CC
Tree: .... .... .... ..80
At:       C0                                                                                length:        1,  data:      100,  nodes:      140,  first:       80, root, leaf
  Index:        0
  Keys :        0
  Data :        1
end
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::union #TNasm::X86::Tree::intersection
  my $a = CreateArea;
  my $r = $a->CreateTree(length => 3);
  my $s = $a->CreateTree(length => 3);
  my $t = $a->CreateTree(length => 3);

  $r->put(K(key => 1), K(data => 1));
  $r->put(K(key => 2), K(data => 2));

  $s->put(K(key => 1), K(data => 1));
  $s->put(K(key => 3), K(data => 3));

  $t->push($r);
  $t->push($s);

  my $u = $t->union;
  $t->dump('input 1 2  1 3');
  $u->dump('union 1 2    3');

  my $i = $t->intersection;
  $i->dump('intersection 1');

  ok Assemble eq => <<END, avx512=>1;
input 1 2  1 3
At:  280                    length:    2,  data:  2C0,  nodes:  300,  first:   C0, root, leaf,  trees:  11
  Index:    0    1
  Keys :    0    1
  Data :  10*  1C*
     At:  100               length:    2,  data:  140,  nodes:  180,  first:   40, root, leaf
       Index:    0    1
       Keys :    1    2
       Data :    1    2
     end
     At:  1C0               length:    2,  data:  200,  nodes:  240,  first:   80, root, leaf
       Index:    0    1
       Keys :    1    3
       Data :    1    3
     end
end
union 1 2    3
At:  380                    length:    3,  data:  3C0,  nodes:  400,  first:  340, root, leaf
  Index:    0    1    2
  Keys :    1    2    3
  Data :    1    2    3
end
intersection 1
At:  480                    length:    1,  data:  4C0,  nodes:  500,  first:  440, root, leaf
  Index:    0
  Keys :    1
  Data :    1
end
END
 }

#latest:
if (1) {                                                                        #
  my $t = Subroutine                                                            #TSubroutine
   {my ($p, $s, $sub) = @_;
    PrintOutStringNL "TTTT";
    $$p{p}->outNL;
   } parameters=>[qw(p)], name=>"t";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;
    PrintOutStringNL "SSS";
    $$p{p}->outNL;
   } parameters=>[qw(p)], name=>"s";

  $s->call(parameters => {p => V(p => 1)});
  $t->call(parameters => {p => V(p => 2)});

  $s->call(parameters => {p => V(p => 3)}, override=>K call => $t->start);
  $s->call(parameters => {p => V(p => 4)}, override=>K call => $s->start);
  $s->call(parameters => {p => V(p => 5)});

  ok Assemble eq => <<END, avx512=>1;
SSS
p: .... .... .... ...1
TTTT
p: .... .... .... ...2
TTTT
p: .... .... .... ...3
SSS
p: .... .... .... ...4
SSS
p: .... .... .... ...5
END
 }

#latest:
if (1) {
  my $a = V(a => 0);
  my $b = $a;
  $a->outNL;
  $b++;
  $a->outNL;
  $b--;
  $a->outNL;
  ok Assemble eq => <<END;
a: .... .... .... ....
a: .... .... .... ...1
a: .... .... .... ....
END
 }

#latest:
if (1) {
          V(a => 2);
          V(a => 1);
  my $a = V(a => 0)->address;
  ($a+ 0)->dereference->outNL;
  ($a+ 8)->dereference->outNL;
  ($a+16)->dereference->outNL;
  ($a+16)->update(K key => 3);
  ($a+16)->dereference->outNL;
  ok Assemble eq => <<END;
deref (addr a add 0): .... .... .... ....
deref (addr a add 8): .... .... .... ...1
deref (addr a add 16): .... .... .... ...2
deref (addr a add 16): .... .... .... ...3
END
 }

#D1 Library                                                                     # Create a library and call the methods contained in it.

sub CreateLibrary(%)                                                            # Create a library.
 {my (%library) = @_;                                                           # Library definition

  $library{subroutines} or confess "Subroutines required";
  $library{file}        or confess "Subroutines file name required";

  my @s = $library{subroutines}->@*;

  Mov rax, scalar @s;
  Ret;
  my @l = map {my $l = Label; Mov rax, $l; $l} @s;                              # Vector of subroutine addresses

  my @c = map {&$_} @s;                                                         # Call the subroutines provided to write their code into the program and return the details of the subroutine so written

  for my $c(keys @c)                                                            # Write the entry point of each routine
   {my $e = $c[$c]->start;
    push @text, <<END;
$l[$c] equ $e
END
   }

  unlink my $f = $library{file};                                                # The name of the file containing the library

  Assemble library => $f;                                                       # Create the library file

  $library{address} = undef;                                                    # Address of the library once it has been loaded
  $library{size}    = undef;                                                    # Size of the library in bytes
  $library{meta}    = \@c;                                                      # Array describing each subroutine in the order they are held in the library
  $library{name}{$c[$_]{name}} = $c[$_] for keys @c;                            # Subroutine description by name

  genHash "Nasm::X86::Library", %library
 }

# Pilates of East Lake
sub Nasm::X86::Library::load($)                                                 # Load a library and return the addresses of its subroutines as variables.
 {my ($library) = @_;                                                           # Description of library to load

  my @offsets = sub                                                             # Examine library at run time
   {my $c = readBinaryFile $$library{file};
    my (undef, $n) = unpack "SQ", $c;
    my @v = unpack "SQC(SQ)[$n]", $c;
    map {$_ > 2 && $_ % 2 == 0 ? ($v[$_]) : () } keys @v
   }->();

  my @s = $$library{meta}->@*;
  $s[$_]{offset} = V(entry=>$offsets[$_]) for keys @s;                          # Variable offset of each subroutine

  ($library->address, $library->size) = ReadFile $$library{file};               # Load library at run time
 }

sub Nasm::X86::Library::call($$%)                                               # Call a library routine
 {my ($library, $name, %options) = @_;                                          # Description of library, method name, options - which includes parameters and structures
  @_ >= 2 or confess "Two or more parameters";

  $library->name->{$name}->call(library => $library->address, %options);
 }

#latest:
if (1) {                                                                        #TCreateLibrary #Nasm::X86::Library::load #Nasm::X86::Library::call
  my $l = CreateLibrary
   (subroutines =>
     [sub
       {Subroutine
         {my ($p, $s, $sub) = @_;
          PrintOutStringNL "SSSS";
         } name=>"ssss";
       },
      sub
       {Subroutine
         {my ($p, $s, $sub) = @_;
          PrintOutStringNL "TTTT";
          $$p{p}->outNL;
         } name=>"tttt",  parameters=>[qw(p)];
       },
     ],
    file => q(library),
   );

  my ($address, $size) = $l->load;

  $l->call(q(ssss));
  $l->call(q(tttt), parameters=>{p => V key => 42});

  ok Assemble eq => <<END, avx512=>0;
SSSS
TTTT
p: .... .... .... ..2A
END
  unlink $l->file;
 }

#latest:
if (1) {                                                                        #TNasm::X86::Variable::dClassify
  K(K => Rd(map {32 * $_     } 0..15))->loadZmm(29);
  K(K => Rd(map {32 * $_ + 16} 0..15))->loadZmm(30);

  V(classify => 20)->dClassify(29, 30)->outNL;
  V(classify => 14)->dClassify(29, 30)->outNL;
  V(classify => 40)->dClassify(29, 30)->outNL;

  ok Assemble eq => <<END, avx512=>1;
point: .... .... .... ....
point: .... .... .... ...1
point: .... .... .... ...2
END
 }

sub Nasm::X86::Unisyn::Lex::Number::S {0}                                       # Start symbol
sub Nasm::X86::Unisyn::Lex::Number::F {1}                                       # End symbol
sub Nasm::X86::Unisyn::Lex::Number::A {2}                                       # ASCII characters extended with circled characters to act as escape sequences.
sub Nasm::X86::Unisyn::Lex::Letter::A {(0x0,0x1,0x2,0x3,0x4,0x5,0x6,0x7,0x8,0x9,0xa,0xb,0xc,0xd,0xe,0xf,0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f,0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5a,0x5b,0x5c,0x5d,0x5e,0x5f,0x60,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6a,0x6b,0x6c,0x6d,0x6e,0x6f,0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7a,0x7b,0x7c,0x7d,0x7e,0x7f,0x24b6,0x24b7,0x24b8,0x24b9,0x24ba,0x24bb,0x24bc,0x24bd,0x24be,0x24bf,0x24c0,0x24c1,0x24c2,0x24c3,0x24c4,0x24c5,0x24c6,0x24c7,0x24c8,0x24c9,0x24ca,0x24cb,0x24cc,0x24cd,0x24ce,0x24cf,0x24d0,0x24d1,0x24d2,0x24d3,0x24d4,0x24d5,0x24d6,0x24d7,0x24d8,0x24d9,0x24da,0x24db,0x24dc,0x24dd,0x24de,0x24df,0x24e0,0x24e1,0x24e2,0x24e3,0x24e4,0x24e5,0x24e6,0x24e7,0x24e8,0x24e9)} # ASCII characters extended with circled characters to act as escape sequences.
sub Nasm::X86::Unisyn::Lex::Number::d {3}                                       # Infix operator with left to right binding at priority 3
sub Nasm::X86::Unisyn::Lex::Letter::d {(0x1d400,0x1d401,0x1d402,0x1d403,0x1d404,0x1d405,0x1d406,0x1d407,0x1d408,0x1d409,0x1d40a,0x1d40b,0x1d40c,0x1d40d,0x1d40e,0x1d40f,0x1d410,0x1d411,0x1d412,0x1d413,0x1d414,0x1d415,0x1d416,0x1d417,0x1d418,0x1d419,0x1d41a,0x1d41b,0x1d41c,0x1d41d,0x1d41e,0x1d41f,0x1d420,0x1d421,0x1d422,0x1d423,0x1d424,0x1d425,0x1d426,0x1d427,0x1d428,0x1d429,0x1d42a,0x1d42b,0x1d42c,0x1d42d,0x1d42e,0x1d42f,0x1d430,0x1d431,0x1d432,0x1d433,0x1d6a8,0x1d6a9,0x1d6aa,0x1d6ab,0x1d6ac,0x1d6ad,0x1d6ae,0x1d6af,0x1d6b0,0x1d6b1,0x1d6b2,0x1d6b3,0x1d6b4,0x1d6b5,0x1d6b6,0x1d6b7,0x1d6b8,0x1d6b9,0x1d6ba,0x1d6bb,0x1d6bc,0x1d6bd,0x1d6be,0x1d6bf,0x1d6c0,0x1d6c1,0x1d6c2,0x1d6c3,0x1d6c4,0x1d6c5,0x1d6c6,0x1d6c7,0x1d6c8,0x1d6c9,0x1d6ca,0x1d6cb,0x1d6cc,0x1d6cd,0x1d6ce,0x1d6cf,0x1d6d0,0x1d6d1,0x1d6d2,0x1d6d3,0x1d6d4,0x1d6d5,0x1d6d6,0x1d6d7,0x1d6d8,0x1d6d9,0x1d6da,0x1d6db,0x1d6dc,0x1d6dd,0x1d6de,0x1d6df,0x1d6e0,0x1d6e1)} # Infix operator with left to right binding at priority 3
sub Nasm::X86::Unisyn::Lex::Number::p {4}                                       # Prefix operator - applies only to the following variable or bracketed term
sub Nasm::X86::Unisyn::Lex::Letter::p {(0x1d468,0x1d469,0x1d46a,0x1d46b,0x1d46c,0x1d46d,0x1d46e,0x1d46f,0x1d470,0x1d471,0x1d472,0x1d473,0x1d474,0x1d475,0x1d476,0x1d477,0x1d478,0x1d479,0x1d47a,0x1d47b,0x1d47c,0x1d47d,0x1d47e,0x1d47f,0x1d480,0x1d481,0x1d482,0x1d483,0x1d484,0x1d485,0x1d486,0x1d487,0x1d488,0x1d489,0x1d48a,0x1d48b,0x1d48c,0x1d48d,0x1d48e,0x1d48f,0x1d490,0x1d491,0x1d492,0x1d493,0x1d494,0x1d495,0x1d496,0x1d497,0x1d498,0x1d499,0x1d49a,0x1d49b,0x1d71c,0x1d71d,0x1d71e,0x1d71f,0x1d720,0x1d721,0x1d722,0x1d723,0x1d724,0x1d725,0x1d726,0x1d727,0x1d728,0x1d729,0x1d72a,0x1d72b,0x1d72c,0x1d72d,0x1d72e,0x1d72f,0x1d730,0x1d731,0x1d732,0x1d733,0x1d734,0x1d735,0x1d736,0x1d737,0x1d738,0x1d739,0x1d73a,0x1d73b,0x1d73c,0x1d73d,0x1d73e,0x1d73f,0x1d740,0x1d741,0x1d742,0x1d743,0x1d744,0x1d745,0x1d746,0x1d747,0x1d748,0x1d749,0x1d74a,0x1d74b,0x1d74c,0x1d74d,0x1d74e,0x1d74f,0x1d750,0x1d751,0x1d752,0x1d753,0x1d754,0x1d755)} # Prefix operator - applies only to the following variable or bracketed term
sub Nasm::X86::Unisyn::Lex::Number::a {5}                                       # Assign infix operator with right to left binding at priority 2
sub Nasm::X86::Unisyn::Lex::Letter::a {(0x210e,0x2190,0x2191,0x2192,0x2193,0x2194,0x2195,0x2196,0x2197,0x2198,0x2199,0x219a,0x219b,0x219c,0x219d,0x219e,0x219f,0x21a0,0x21a1,0x21a2,0x21a3,0x21a4,0x21a5,0x21a6,0x21a7,0x21a8,0x21a9,0x21aa,0x21ab,0x21ac,0x21ad,0x21ae,0x21af,0x21b0,0x21b1,0x21b2,0x21b3,0x21b4,0x21b5,0x21b6,0x21b7,0x21b8,0x21b9,0x21ba,0x21bb,0x21bc,0x21bd,0x21be,0x21bf,0x21c0,0x21c1,0x21c2,0x21c3,0x21c4,0x21c5,0x21c6,0x21c7,0x21c8,0x21c9,0x21ca,0x21cb,0x21cc,0x21cd,0x21ce,0x21cf,0x21d0,0x21d1,0x21d2,0x21d3,0x21d4,0x21d5,0x21d6,0x21d7,0x21d8,0x21d9,0x21da,0x21db,0x21dc,0x21dd,0x21de,0x21df,0x21e0,0x21e1,0x21e2,0x21e3,0x21e4,0x21e5,0x21e6,0x21e7,0x21e8,0x21e9,0x21ea,0x21eb,0x21ec,0x21ed,0x21ee,0x21ef,0x21f0,0x21f1,0x21f2,0x21f3,0x21f4,0x21f5,0x21f6,0x21f7,0x21f8,0x21f9,0x21fa,0x21fb,0x21fc,0x21fd,0x21fe,0xff1d,0x1d434,0x1d435,0x1d436,0x1d437,0x1d438,0x1d439,0x1d43a,0x1d43b,0x1d43c,0x1d43d,0x1d43e,0x1d43f,0x1d440,0x1d441,0x1d442,0x1d443,0x1d444,0x1d445,0x1d446,0x1d447,0x1d448,0x1d449,0x1d44a,0x1d44b,0x1d44c,0x1d44d,0x1d44e,0x1d44f,0x1d450,0x1d451,0x1d452,0x1d453,0x1d454,0x1d456,0x1d457,0x1d458,0x1d459,0x1d45a,0x1d45b,0x1d45c,0x1d45d,0x1d45e,0x1d45f,0x1d460,0x1d461,0x1d462,0x1d463,0x1d464,0x1d465,0x1d466,0x1d467,0x1d6e2,0x1d6e3,0x1d6e4,0x1d6e5,0x1d6e6,0x1d6e7,0x1d6e8,0x1d6e9,0x1d6ea,0x1d6eb,0x1d6ec,0x1d6ed,0x1d6ee,0x1d6ef,0x1d6f0,0x1d6f1,0x1d6f2,0x1d6f3,0x1d6f4,0x1d6f5,0x1d6f6,0x1d6f7,0x1d6f8,0x1d6f9,0x1d6fa,0x1d6fb,0x1d6fc,0x1d6fd,0x1d6fe,0x1d6ff,0x1d700,0x1d701,0x1d702,0x1d703,0x1d704,0x1d705,0x1d706,0x1d707,0x1d708,0x1d709,0x1d70a,0x1d70b,0x1d70c,0x1d70d,0x1d70e,0x1d70f,0x1d710,0x1d711,0x1d712,0x1d713,0x1d714,0x1d715,0x1d716,0x1d717,0x1d718,0x1d719,0x1d71a,0x1d71b)} # Assign infix operator with right to left binding at priority 2
sub Nasm::X86::Unisyn::Lex::Number::v {6}                                       # Variable names
sub Nasm::X86::Unisyn::Lex::Letter::v {(0x1d5d4,0x1d5d5,0x1d5d6,0x1d5d7,0x1d5d8,0x1d5d9,0x1d5da,0x1d5db,0x1d5dc,0x1d5dd,0x1d5de,0x1d5df,0x1d5e0,0x1d5e1,0x1d5e2,0x1d5e3,0x1d5e4,0x1d5e5,0x1d5e6,0x1d5e7,0x1d5e8,0x1d5e9,0x1d5ea,0x1d5eb,0x1d5ec,0x1d5ed,0x1d5ee,0x1d5ef,0x1d5f0,0x1d5f1,0x1d5f2,0x1d5f3,0x1d5f4,0x1d5f5,0x1d5f6,0x1d5f7,0x1d5f8,0x1d5f9,0x1d5fa,0x1d5fb,0x1d5fc,0x1d5fd,0x1d5fe,0x1d5ff,0x1d600,0x1d601,0x1d602,0x1d603,0x1d604,0x1d605,0x1d606,0x1d607,0x1d756,0x1d757,0x1d758,0x1d759,0x1d75a,0x1d75b,0x1d75c,0x1d75d,0x1d75e,0x1d75f,0x1d760,0x1d761,0x1d762,0x1d763,0x1d764,0x1d765,0x1d766,0x1d767,0x1d768,0x1d769,0x1d76a,0x1d76b,0x1d76c,0x1d76d,0x1d76e,0x1d76f,0x1d770,0x1d771,0x1d772,0x1d773,0x1d774,0x1d775,0x1d776,0x1d777,0x1d778,0x1d779,0x1d77a,0x1d77b,0x1d77c,0x1d77d,0x1d77e,0x1d77f,0x1d780,0x1d781,0x1d782,0x1d783,0x1d784,0x1d785,0x1d786,0x1d787,0x1d788,0x1d789,0x1d78a,0x1d78b,0x1d78c,0x1d78d,0x1d78e,0x1d78f)} # Variable names
sub Nasm::X86::Unisyn::Lex::Number::q {7}                                       # Suffix operator - applies only to the preceding variable or bracketed term
sub Nasm::X86::Unisyn::Lex::Letter::q {(0x1d63c,0x1d63d,0x1d63e,0x1d63f,0x1d640,0x1d641,0x1d642,0x1d643,0x1d644,0x1d645,0x1d646,0x1d647,0x1d648,0x1d649,0x1d64a,0x1d64b,0x1d64c,0x1d64d,0x1d64e,0x1d64f,0x1d650,0x1d651,0x1d652,0x1d653,0x1d654,0x1d655,0x1d656,0x1d657,0x1d658,0x1d659,0x1d65a,0x1d65b,0x1d65c,0x1d65d,0x1d65e,0x1d65f,0x1d660,0x1d661,0x1d662,0x1d663,0x1d664,0x1d665,0x1d666,0x1d667,0x1d668,0x1d669,0x1d66a,0x1d66b,0x1d66c,0x1d66d,0x1d66e,0x1d66f,0x1d790,0x1d791,0x1d792,0x1d793,0x1d794,0x1d795,0x1d796,0x1d797,0x1d798,0x1d799,0x1d79a,0x1d79b,0x1d79c,0x1d79d,0x1d79e,0x1d79f,0x1d7a0,0x1d7a1,0x1d7a2,0x1d7a3,0x1d7a4,0x1d7a5,0x1d7a6,0x1d7a7,0x1d7a8,0x1d7a9,0x1d7aa,0x1d7ab,0x1d7ac,0x1d7ad,0x1d7ae,0x1d7af,0x1d7b0,0x1d7b1,0x1d7b2,0x1d7b3,0x1d7b4,0x1d7b5,0x1d7b6,0x1d7b7,0x1d7b8,0x1d7b9,0x1d7ba,0x1d7bb,0x1d7bc,0x1d7bd,0x1d7be,0x1d7bf,0x1d7c0,0x1d7c1,0x1d7c2,0x1d7c3,0x1d7c4,0x1d7c5,0x1d7c6,0x1d7c7,0x1d7c8,0x1d7c9)} # Suffix operator - applies only to the preceding variable or bracketed term
sub Nasm::X86::Unisyn::Lex::Number::s {8}                                       # Infix operator with left to right binding at priority 1
sub Nasm::X86::Unisyn::Lex::Letter::s {(0x27e2)}                                # Infix operator with left to right binding at priority 1
sub Nasm::X86::Unisyn::Lex::Number::e {9}                                       # Infix operator with left to right binding at priority 4
sub Nasm::X86::Unisyn::Lex::Letter::e {(0xac,0xb1,0xd7,0xf7,0x3f6,0x606,0x607,0x608,0x200b,0x200c,0x200d,0x200e,0x200f,0x2010,0x2011,0x2012,0x2013,0x2014,0x2015,0x2016,0x2017,0x2018,0x2019,0x201a,0x201b,0x201c,0x201d,0x201e,0x201f,0x2020,0x2021,0x2022,0x2023,0x2024,0x2025,0x2026,0x2027,0x2028,0x2029,0x202a,0x202b,0x202c,0x202d,0x202e,0x202f,0x2030,0x2031,0x2032,0x2033,0x2034,0x2035,0x2036,0x2037,0x2038,0x2039,0x203a,0x203b,0x203c,0x203d,0x203e,0x203f,0x2040,0x2041,0x2042,0x2043,0x2044,0x2047,0x2048,0x2049,0x204a,0x204b,0x204c,0x204d,0x204e,0x204f,0x2050,0x2051,0x2052,0x2053,0x2054,0x2055,0x2056,0x2057,0x2058,0x2059,0x205a,0x205b,0x205c,0x205d,0x205e,0x205f,0x2060,0x2061,0x2065,0x2066,0x2067,0x2068,0x2069,0x207a,0x207b,0x207c,0x208a,0x208b,0x208c,0x2118,0x2140,0x2141,0x2142,0x2143,0x2144,0x214b,0x2200,0x2201,0x2202,0x2203,0x2204,0x2205,0x2206,0x2207,0x2208,0x2209,0x220a,0x220b,0x220c,0x220d,0x220e,0x220f,0x2210,0x2211,0x2212,0x2213,0x2214,0x2215,0x2216,0x2217,0x2218,0x2219,0x221a,0x221b,0x221c,0x221d,0x221e,0x221f,0x2220,0x2221,0x2222,0x2223,0x2224,0x2225,0x2226,0x2227,0x2228,0x2229,0x222a,0x222b,0x222c,0x222d,0x222e,0x222f,0x2230,0x2231,0x2232,0x2233,0x2234,0x2235,0x2236,0x2237,0x2238,0x2239,0x223a,0x223b,0x223c,0x223d,0x223e,0x223f,0x2240,0x2241,0x2242,0x2243,0x2244,0x2245,0x2246,0x2247,0x2248,0x2249,0x224a,0x224b,0x224c,0x224d,0x224e,0x224f,0x2250,0x2251,0x2252,0x2253,0x2254,0x2255,0x2256,0x2257,0x2258,0x2259,0x225a,0x225b,0x225c,0x225d,0x225e,0x225f,0x2260,0x2261,0x2262,0x2263,0x2264,0x2265,0x2266,0x2267,0x2268,0x2269,0x226a,0x226b,0x226c,0x226d,0x226e,0x226f,0x2270,0x2271,0x2272,0x2273,0x2274,0x2275,0x2276,0x2277,0x2278,0x2279,0x227a,0x227b,0x227c,0x227d,0x227e,0x227f,0x2280,0x2281,0x2282,0x2283,0x2284,0x2285,0x2286,0x2287,0x2288,0x2289,0x228a,0x228b,0x228c,0x228d,0x228e,0x228f,0x2290,0x2291,0x2292,0x2293,0x2294,0x2295,0x2296,0x2297,0x2298,0x2299,0x229a,0x229b,0x229c,0x229d,0x229e,0x229f,0x22a0,0x22a1,0x22a2,0x22a3,0x22a4,0x22a5,0x22a6,0x22a7,0x22a8,0x22a9,0x22aa,0x22ab,0x22ac,0x22ad,0x22ae,0x22af,0x22b0,0x22b1,0x22b2,0x22b3,0x22b4,0x22b5,0x22b6,0x22b7,0x22b8,0x22b9,0x22ba,0x22bb,0x22bc,0x22bd,0x22be,0x22bf,0x22c0,0x22c1,0x22c2,0x22c3,0x22c4,0x22c5,0x22c6,0x22c7,0x22c8,0x22c9,0x22ca,0x22cb,0x22cc,0x22cd,0x22ce,0x22cf,0x22d0,0x22d1,0x22d2,0x22d3,0x22d4,0x22d5,0x22d6,0x22d7,0x22d8,0x22d9,0x22da,0x22db,0x22dc,0x22dd,0x22de,0x22df,0x22e0,0x22e1,0x22e2,0x22e3,0x22e4,0x22e5,0x22e6,0x22e7,0x22e8,0x22e9,0x22ea,0x22eb,0x22ec,0x22ed,0x22ee,0x22ef,0x22f0,0x22f1,0x22f2,0x22f3,0x22f4,0x22f5,0x22f6,0x22f7,0x22f8,0x22f9,0x22fa,0x22fb,0x22fc,0x22fd,0x22fe,0x22ff,0x2300,0x2301,0x2302,0x2303,0x2304,0x2305,0x2306,0x2307,0x230c,0x230d,0x230e,0x230f,0x2310,0x2311,0x2312,0x2313,0x2314,0x2315,0x2316,0x2317,0x2318,0x2319,0x231a,0x231b,0x231c,0x231d,0x231e,0x231f,0x2320,0x2321,0x2322,0x2323,0x2324,0x2325,0x2326,0x2327,0x2328,0x232c,0x232d,0x232e,0x232f,0x2330,0x2331,0x2332,0x2333,0x2334,0x2335,0x2336,0x2337,0x2338,0x2339,0x233a,0x233b,0x233c,0x233d,0x233e,0x233f,0x2340,0x2341,0x2342,0x2343,0x2344,0x2345,0x2346,0x2347,0x2348,0x2349,0x234a,0x234b,0x234c,0x234d,0x234e,0x234f,0x2350,0x2351,0x2352,0x2353,0x2354,0x2355,0x2356,0x2357,0x2358,0x2359,0x235a,0x235b,0x235c,0x235d,0x235e,0x235f,0x2360,0x2361,0x2362,0x2363,0x2364,0x2365,0x2366,0x2367,0x2368,0x2369,0x236a,0x236b,0x236c,0x236d,0x236e,0x236f,0x2370,0x2371,0x2372,0x2373,0x2374,0x2375,0x2376,0x2377,0x2378,0x2379,0x237a,0x237b,0x237c,0x237d,0x237e,0x237f,0x2380,0x2381,0x2382,0x2383,0x2384,0x2385,0x2386,0x2387,0x2388,0x2389,0x238a,0x238b,0x238c,0x238d,0x238e,0x238f,0x2390,0x2391,0x2392,0x2393,0x2394,0x2395,0x2396,0x2397,0x2398,0x2399,0x239a,0x239b,0x239c,0x239d,0x239e,0x239f,0x23a0,0x23a1,0x23a2,0x23a3,0x23a4,0x23a5,0x23a6,0x23a7,0x23a8,0x23a9,0x23aa,0x23ab,0x23ac,0x23ad,0x23ae,0x23af,0x23b0,0x23b1,0x23b2,0x23b3,0x23b4,0x23b5,0x23b6,0x23b7,0x23b8,0x23b9,0x23ba,0x23bb,0x23bc,0x23bd,0x23be,0x23bf,0x23c0,0x23c1,0x23c2,0x23c3,0x23c4,0x23c5,0x23c6,0x23c7,0x23c8,0x23c9,0x23ca,0x23cb,0x23cc,0x23cd,0x23ce,0x23cf,0x23d0,0x23d1,0x23d2,0x23d3,0x23d4,0x23d5,0x23d6,0x23d7,0x23d8,0x23d9,0x23da,0x23db,0x23dc,0x23dd,0x23de,0x23df,0x23e0,0x23e1,0x23e2,0x23e3,0x23e4,0x23e5,0x23e6,0x23e7,0x23e8,0x23e9,0x23ea,0x23eb,0x23ec,0x23ed,0x23ee,0x23ef,0x23f0,0x23f1,0x23f2,0x23f3,0x23f4,0x23f5,0x23f6,0x23f7,0x23f8,0x23f9,0x23fa,0x23fb,0x23fc,0x23fd,0x23fe,0x23ff,0x25a0,0x25a1,0x25a2,0x25a3,0x25a4,0x25a5,0x25a6,0x25a7,0x25a8,0x25a9,0x25aa,0x25ab,0x25ac,0x25ad,0x25ae,0x25af,0x25b0,0x25b1,0x25b2,0x25b3,0x25b4,0x25b5,0x25b6,0x25b7,0x25b8,0x25b9,0x25ba,0x25bb,0x25bc,0x25bd,0x25be,0x25bf,0x25c0,0x25c1,0x25c2,0x25c3,0x25c4,0x25c5,0x25c6,0x25c7,0x25c8,0x25c9,0x25ca,0x25cb,0x25cc,0x25cd,0x25ce,0x25cf,0x25d0,0x25d1,0x25d2,0x25d3,0x25d4,0x25d5,0x25d6,0x25d7,0x25d8,0x25d9,0x25da,0x25db,0x25dc,0x25dd,0x25de,0x25df,0x25e0,0x25e1,0x25e2,0x25e3,0x25e4,0x25e5,0x25e6,0x25e7,0x25e8,0x25e9,0x25ea,0x25eb,0x25ec,0x25ed,0x25ee,0x25ef,0x25f0,0x25f1,0x25f2,0x25f3,0x25f4,0x25f5,0x25f6,0x25f7,0x25f8,0x25f9,0x25fa,0x25fb,0x25fc,0x25fd,0x25fe,0x25ff,0x2600,0x2601,0x2602,0x2603,0x2604,0x2605,0x2606,0x2607,0x2608,0x2609,0x260a,0x260b,0x260c,0x260d,0x260e,0x260f,0x2610,0x2611,0x2612,0x2613,0x2614,0x2615,0x2616,0x2617,0x2618,0x2619,0x261a,0x261b,0x261c,0x261d,0x261e,0x261f,0x2620,0x2621,0x2622,0x2623,0x2624,0x2625,0x2626,0x2627,0x2628,0x2629,0x262a,0x262b,0x262c,0x262d,0x262e,0x262f,0x2630,0x2631,0x2632,0x2633,0x2634,0x2635,0x2636,0x2637,0x2638,0x2639,0x263a,0x263b,0x263c,0x263d,0x263e,0x263f,0x2640,0x2641,0x2642,0x2643,0x2644,0x2645,0x2646,0x2647,0x2648,0x2649,0x264a,0x264b,0x264c,0x264d,0x264e,0x264f,0x2650,0x2651,0x2652,0x2653,0x2654,0x2655,0x2656,0x2657,0x2658,0x2659,0x265a,0x265b,0x265c,0x265d,0x265e,0x265f,0x2660,0x2661,0x2662,0x2663,0x2664,0x2665,0x2666,0x2667,0x2668,0x2669,0x266a,0x266b,0x266c,0x266d,0x266e,0x266f,0x2670,0x2671,0x2672,0x2673,0x2674,0x2675,0x2676,0x2677,0x2678,0x2679,0x267a,0x267b,0x267c,0x267d,0x267e,0x267f,0x2680,0x2681,0x2682,0x2683,0x2684,0x2685,0x2686,0x2687,0x2688,0x2689,0x268a,0x268b,0x268c,0x268d,0x268e,0x268f,0x2690,0x2691,0x2692,0x2693,0x2694,0x2695,0x2696,0x2697,0x2698,0x2699,0x269a,0x269b,0x269c,0x269d,0x269e,0x269f,0x26a0,0x26a1,0x26a2,0x26a3,0x26a4,0x26a5,0x26a6,0x26a7,0x26a8,0x26a9,0x26aa,0x26ab,0x26ac,0x26ad,0x26ae,0x26af,0x26b0,0x26b1,0x26b2,0x26b3,0x26b4,0x26b5,0x26b6,0x26b7,0x26b8,0x26b9,0x26ba,0x26bb,0x26bc,0x26bd,0x26be,0x26bf,0x26c0,0x26c1,0x26c2,0x26c3,0x26c4,0x26c5,0x26c6,0x26c7,0x26c8,0x26c9,0x26ca,0x26cb,0x26cc,0x26cd,0x26ce,0x26cf,0x26d0,0x26d1,0x26d2,0x26d3,0x26d4,0x26d5,0x26d6,0x26d7,0x26d8,0x26d9,0x26da,0x26db,0x26dc,0x26dd,0x26de,0x26df,0x26e0,0x26e1,0x26e2,0x26e3,0x26e4,0x26e5,0x26e6,0x26e7,0x26e8,0x26e9,0x26ea,0x26eb,0x26ec,0x26ed,0x26ee,0x26ef,0x26f0,0x26f1,0x26f2,0x26f3,0x26f4,0x26f5,0x26f6,0x26f7,0x26f8,0x26f9,0x26fa,0x26fb,0x26fc,0x26fd,0x26fe,0x26ff,0x2715,0x27c0,0x27c1,0x27c2,0x27c3,0x27c4,0x27c5,0x27c6,0x27c7,0x27c8,0x27c9,0x27ca,0x27cb,0x27cc,0x27cd,0x27ce,0x27cf,0x27d0,0x27d1,0x27d2,0x27d3,0x27d4,0x27d5,0x27d6,0x27d7,0x27d8,0x27d9,0x27da,0x27db,0x27dc,0x27dd,0x27de,0x27df,0x27e0,0x27e1,0x27e3,0x27e4,0x27e5,0x27f0,0x27f1,0x27f2,0x27f3,0x27f4,0x27f5,0x27f6,0x27f7,0x27f8,0x27f9,0x27fa,0x27fb,0x27fc,0x27fd,0x27fe,0x27ff,0x2800,0x2801,0x2802,0x2803,0x2804,0x2805,0x2806,0x2807,0x2808,0x2809,0x280a,0x280b,0x280c,0x280d,0x280e,0x280f,0x2810,0x2811,0x2812,0x2813,0x2814,0x2815,0x2816,0x2817,0x2818,0x2819,0x281a,0x281b,0x281c,0x281d,0x281e,0x281f,0x2820,0x2821,0x2822,0x2823,0x2824,0x2825,0x2826,0x2827,0x2828,0x2829,0x282a,0x282b,0x282c,0x282d,0x282e,0x282f,0x2830,0x2831,0x2832,0x2833,0x2834,0x2835,0x2836,0x2837,0x2838,0x2839,0x283a,0x283b,0x283c,0x283d,0x283e,0x283f,0x2840,0x2841,0x2842,0x2843,0x2844,0x2845,0x2846,0x2847,0x2848,0x2849,0x284a,0x284b,0x284c,0x284d,0x284e,0x284f,0x2850,0x2851,0x2852,0x2853,0x2854,0x2855,0x2856,0x2857,0x2858,0x2859,0x285a,0x285b,0x285c,0x285d,0x285e,0x285f,0x2860,0x2861,0x2862,0x2863,0x2864,0x2865,0x2866,0x2867,0x2868,0x2869,0x286a,0x286b,0x286c,0x286d,0x286e,0x286f,0x2870,0x2871,0x2872,0x2873,0x2874,0x2875,0x2876,0x2877,0x2878,0x2879,0x287a,0x287b,0x287c,0x287d,0x287e,0x287f,0x2880,0x2881,0x2882,0x2883,0x2884,0x2885,0x2886,0x2887,0x2888,0x2889,0x288a,0x288b,0x288c,0x288d,0x288e,0x288f,0x2890,0x2891,0x2892,0x2893,0x2894,0x2895,0x2896,0x2897,0x2898,0x2899,0x289a,0x289b,0x289c,0x289d,0x289e,0x289f,0x28a0,0x28a1,0x28a2,0x28a3,0x28a4,0x28a5,0x28a6,0x28a7,0x28a8,0x28a9,0x28aa,0x28ab,0x28ac,0x28ad,0x28ae,0x28af,0x28b0,0x28b1,0x28b2,0x28b3,0x28b4,0x28b5,0x28b6,0x28b7,0x28b8,0x28b9,0x28ba,0x28bb,0x28bc,0x28bd,0x28be,0x28bf,0x28c0,0x28c1,0x28c2,0x28c3,0x28c4,0x28c5,0x28c6,0x28c7,0x28c8,0x28c9,0x28ca,0x28cb,0x28cc,0x28cd,0x28ce,0x28cf,0x28d0,0x28d1,0x28d2,0x28d3,0x28d4,0x28d5,0x28d6,0x28d7,0x28d8,0x28d9,0x28da,0x28db,0x28dc,0x28dd,0x28de,0x28df,0x28e0,0x28e1,0x28e2,0x28e3,0x28e4,0x28e5,0x28e6,0x28e7,0x28e8,0x28e9,0x28ea,0x28eb,0x28ec,0x28ed,0x28ee,0x28ef,0x28f0,0x28f1,0x28f2,0x28f3,0x28f4,0x28f5,0x28f6,0x28f7,0x28f8,0x28f9,0x28fa,0x28fb,0x28fc,0x28fd,0x28fe,0x28ff,0x2900,0x2901,0x2902,0x2903,0x2904,0x2905,0x2906,0x2907,0x2908,0x2909,0x290a,0x290b,0x290c,0x290d,0x290e,0x290f,0x2910,0x2911,0x2912,0x2913,0x2914,0x2915,0x2916,0x2917,0x2918,0x2919,0x291a,0x291b,0x291c,0x291d,0x291e,0x291f,0x2920,0x2921,0x2922,0x2923,0x2924,0x2925,0x2926,0x2927,0x2928,0x2929,0x292a,0x292b,0x292c,0x292d,0x292e,0x292f,0x2930,0x2931,0x2932,0x2933,0x2934,0x2935,0x2936,0x2937,0x2938,0x2939,0x293a,0x293b,0x293c,0x293d,0x293e,0x293f,0x2940,0x2941,0x2942,0x2943,0x2944,0x2945,0x2946,0x2947,0x2948,0x2949,0x294a,0x294b,0x294c,0x294d,0x294e,0x294f,0x2950,0x2951,0x2952,0x2953,0x2954,0x2955,0x2956,0x2957,0x2958,0x2959,0x295a,0x295b,0x295c,0x295d,0x295e,0x295f,0x2960,0x2961,0x2962,0x2963,0x2964,0x2965,0x2966,0x2967,0x2968,0x2969,0x296a,0x296b,0x296c,0x296d,0x296e,0x296f,0x2970,0x2971,0x2972,0x2973,0x2974,0x2975,0x2976,0x2977,0x2978,0x2979,0x297a,0x297b,0x297c,0x297d,0x297e,0x297f,0x2980,0x2981,0x2982,0x2999,0x299a,0x299b,0x299c,0x299d,0x299e,0x299f,0x29a0,0x29a1,0x29a2,0x29a3,0x29a4,0x29a5,0x29a6,0x29a7,0x29a8,0x29a9,0x29aa,0x29ab,0x29ac,0x29ad,0x29ae,0x29af,0x29b0,0x29b1,0x29b2,0x29b3,0x29b4,0x29b5,0x29b6,0x29b7,0x29b8,0x29b9,0x29ba,0x29bb,0x29bc,0x29bd,0x29be,0x29bf,0x29c0,0x29c1,0x29c2,0x29c3,0x29c4,0x29c5,0x29c6,0x29c7,0x29c8,0x29c9,0x29ca,0x29cb,0x29cc,0x29cd,0x29ce,0x29cf,0x29d0,0x29d1,0x29d2,0x29d3,0x29d4,0x29d5,0x29d6,0x29d7,0x29d8,0x29d9,0x29da,0x29db,0x29dc,0x29dd,0x29de,0x29df,0x29e0,0x29e1,0x29e2,0x29e3,0x29e4,0x29e5,0x29e6,0x29e7,0x29e8,0x29e9,0x29ea,0x29eb,0x29ec,0x29ed,0x29ee,0x29ef,0x29f0,0x29f1,0x29f2,0x29f3,0x29f4,0x29f5,0x29f6,0x29f7,0x29f8,0x29f9,0x29fa,0x29fb,0x29fe,0x29ff,0x2a00,0x2a01,0x2a02,0x2a03,0x2a04,0x2a05,0x2a06,0x2a07,0x2a08,0x2a09,0x2a0a,0x2a0b,0x2a0c,0x2a0d,0x2a0e,0x2a0f,0x2a10,0x2a11,0x2a12,0x2a13,0x2a14,0x2a15,0x2a16,0x2a17,0x2a18,0x2a19,0x2a1a,0x2a1b,0x2a1c,0x2a1d,0x2a1e,0x2a1f,0x2a20,0x2a21,0x2a22,0x2a23,0x2a24,0x2a25,0x2a26,0x2a27,0x2a28,0x2a29,0x2a2a,0x2a2b,0x2a2c,0x2a2d,0x2a2e,0x2a2f,0x2a30,0x2a31,0x2a32,0x2a33,0x2a34,0x2a35,0x2a36,0x2a37,0x2a38,0x2a39,0x2a3a,0x2a3b,0x2a3c,0x2a3d,0x2a3e,0x2a3f,0x2a40,0x2a41,0x2a42,0x2a43,0x2a44,0x2a45,0x2a46,0x2a47,0x2a48,0x2a49,0x2a4a,0x2a4b,0x2a4c,0x2a4d,0x2a4e,0x2a4f,0x2a50,0x2a51,0x2a52,0x2a53,0x2a54,0x2a55,0x2a56,0x2a57,0x2a58,0x2a59,0x2a5a,0x2a5b,0x2a5c,0x2a5d,0x2a5e,0x2a5f,0x2a60,0x2a61,0x2a62,0x2a63,0x2a64,0x2a65,0x2a66,0x2a67,0x2a68,0x2a69,0x2a6a,0x2a6b,0x2a6c,0x2a6d,0x2a6e,0x2a6f,0x2a70,0x2a71,0x2a72,0x2a73,0x2a74,0x2a75,0x2a76,0x2a77,0x2a78,0x2a79,0x2a7a,0x2a7b,0x2a7c,0x2a7d,0x2a7e,0x2a7f,0x2a80,0x2a81,0x2a82,0x2a83,0x2a84,0x2a85,0x2a86,0x2a87,0x2a88,0x2a89,0x2a8a,0x2a8b,0x2a8c,0x2a8d,0x2a8e,0x2a8f,0x2a90,0x2a91,0x2a92,0x2a93,0x2a94,0x2a95,0x2a96,0x2a97,0x2a98,0x2a99,0x2a9a,0x2a9b,0x2a9c,0x2a9d,0x2a9e,0x2a9f,0x2aa0,0x2aa1,0x2aa2,0x2aa3,0x2aa4,0x2aa5,0x2aa6,0x2aa7,0x2aa8,0x2aa9,0x2aaa,0x2aab,0x2aac,0x2aad,0x2aae,0x2aaf,0x2ab0,0x2ab1,0x2ab2,0x2ab3,0x2ab4,0x2ab5,0x2ab6,0x2ab7,0x2ab8,0x2ab9,0x2aba,0x2abb,0x2abc,0x2abd,0x2abe,0x2abf,0x2ac0,0x2ac1,0x2ac2,0x2ac3,0x2ac4,0x2ac5,0x2ac6,0x2ac7,0x2ac8,0x2ac9,0x2aca,0x2acb,0x2acc,0x2acd,0x2ace,0x2acf,0x2ad0,0x2ad1,0x2ad2,0x2ad3,0x2ad4,0x2ad5,0x2ad6,0x2ad7,0x2ad8,0x2ad9,0x2ada,0x2adb,0x2adc,0x2add,0x2ade,0x2adf,0x2ae0,0x2ae1,0x2ae2,0x2ae3,0x2ae4,0x2ae5,0x2ae6,0x2ae7,0x2ae8,0x2ae9,0x2aea,0x2aeb,0x2aec,0x2aed,0x2aee,0x2aef,0x2af0,0x2af1,0x2af2,0x2af3,0x2af4,0x2af5,0x2af6,0x2af7,0x2af8,0x2af9,0x2afa,0x2afb,0x2afc,0x2afd,0x2afe,0x2aff,0x2b00,0x2b01,0x2b02,0x2b03,0x2b04,0x2b05,0x2b06,0x2b07,0x2b08,0x2b09,0x2b0a,0x2b0b,0x2b0c,0x2b0d,0x2b0e,0x2b0f,0x2b10,0x2b11,0x2b12,0x2b13,0x2b14,0x2b15,0x2b16,0x2b17,0x2b18,0x2b19,0x2b1a,0x2b1b,0x2b1c,0x2b1d,0x2b1e,0x2b1f,0x2b20,0x2b21,0x2b22,0x2b23,0x2b24,0x2b25,0x2b26,0x2b27,0x2b28,0x2b29,0x2b2a,0x2b2b,0x2b2c,0x2b2d,0x2b2e,0x2b2f,0x2b30,0x2b31,0x2b32,0x2b33,0x2b34,0x2b35,0x2b36,0x2b37,0x2b38,0x2b39,0x2b3a,0x2b3b,0x2b3c,0x2b3d,0x2b3e,0x2b3f,0x2b40,0x2b41,0x2b42,0x2b43,0x2b44,0x2b45,0x2b46,0x2b47,0x2b48,0x2b49,0x2b4a,0x2b4b,0x2b4c,0x2b4d,0x2b4e,0x2b4f,0x2b50,0x2b51,0x2b52,0x2b53,0x2b54,0x2b55,0x2b56,0x2b57,0x2b58,0x2e00,0x2e01,0x2e02,0x2e03,0x2e04,0x2e05,0x2e06,0x2e07,0x2e08,0x2e09,0x2e0a,0x2e0b,0x2e0c,0x2e0d,0x2e0e,0x2e0f,0x2e10,0x2e11,0x2e12,0x2e13,0x2e14,0x2e15,0x2e16,0x2e17,0x2e18,0x2e19,0x2e1a,0x2e1b,0x2e1c,0x2e1d,0x2e1e,0x2e1f,0x2e2a,0x2e2b,0x2e2c,0x2e2d,0x2e2e,0x2e2f,0x2e30,0xfb29,0xfe62,0xfe64,0xfe65,0xfe66,0xff0b,0xff1c,0xff1e,0xff5c,0xff5e,0xffe2,0x1eef0,0x1eef1)} # Infix operator with left to right binding at priority 4
sub Nasm::X86::Unisyn::Lex::Number::b {10}                                      # Open
sub Nasm::X86::Unisyn::Lex::Letter::b {(0x2308,0x230a,0x2329,0x2768,0x276a,0x276c,0x276e,0x2770,0x2772,0x2774,0x27e6,0x27e8,0x27ea,0x27ec,0x27ee,0x2983,0x2985,0x2987,0x2989,0x298b,0x298d,0x298f,0x2991,0x2993,0x2995,0x2997,0x29fc,0x2e28,0x3008,0x300a,0x3010,0x3014,0x3016,0x3018,0x301a,0xfd3e,0xff08,0xff5f)} # Open
sub Nasm::X86::Unisyn::Lex::Number::B {11}                                      # Close
sub Nasm::X86::Unisyn::Lex::Letter::B {(0x2309,0x230b,0x232a,0x2769,0x276b,0x276d,0x276f,0x2771,0x2773,0x2775,0x27e7,0x27e9,0x27eb,0x27ed,0x27ef,0x2984,0x2986,0x2988,0x298a,0x298c,0x298e,0x2990,0x2992,0x2994,0x2996,0x2998,0x29fd,0x2e29,0x3009,0x300b,0x3011,0x3015,0x3017,0x3019,0x301b,0xfd3f,0xff09,0xff60)} # Close

sub Nasm::X86::Unisyn::Lex::composeUnisyn($)                                  # Compose phrases of Earl Zero, write them to a temporary file, return the temporary file name
 {my ($words) = @_;                                                             # String of words
  my $s = '';

  my $dyad = sub                                                                # Variable name
   {my ($chars) = @_;                                                           # Characters
    my @c = Nasm::X86::Unisyn::Lex::Letter::d;
    $s .= chr $c[ord($_) - ord('a')] for split //, $chars;
   };

  my $var = sub                                                                 # Variable name
   {my ($chars) = @_;                                                           # Characters
    my @c = Nasm::X86::Unisyn::Lex::Letter::v;
    $s .= chr $c[ord($_) - ord('a')] for split //, $chars;
   };

  my sub c($$)                                                                  # Character from table
   {my ($pos, $alpha) = @_;                                                     # Position, character table name
    my @c = eval "Nasm::X86::Unisyn::Lex::Letter::$alpha";                      # Alphabet in array context
    chr $c[$pos]                                                                # Character requested
   };


  for my $w(split /\s+/, $words)
   {if    ($w =~ m(\AA(.*)))  {$s .= $1}                                        # Ascii - normal letters where possible
    elsif ($w =~ m(\Aa=))     {$s .= "＝"}                                       # Assign chosen by number
    elsif ($w =~ m(\Aa(\d+))) {$s .= c $1, "a"}                                 # Assign chosen by number
    elsif ($w =~ m/\Ab\(/)    {$s .= '【'}                                       # Open bracket
    elsif ($w =~ m/\Ab\[/)    {$s .= '⟦'}                                       # Open bracket
    elsif ($w =~ m/\Ab\</)    {$s .= '⟨'}                                       # Open bracket
    elsif ($w =~ m(\Ab(\d+))) {$s .= c $1, "b"}                                 # Open bracket
    elsif ($w =~ m/\AB\)/)    {$s .= '】'}                                       # Open bracket
    elsif ($w =~ m/\AB\]/)    {$s .= '⟧'}                                       # Open bracket
    elsif ($w =~ m/\AB\>/)    {$s .= '⟩'}                                       # Open bracket
    elsif ($w =~ m(\AB(\d+))) {$s .= c $1, "B"}                                 # Close bracket
    elsif ($w =~ m(\Ad(\d+))) {$s .= c $1, "d"}                                 # Dyad   chosen by number
    elsif ($w =~ m(\Ad(\w+))) {$s .= $dyad->($1)}                               # Dyad-1 name
    elsif ($w =~ m(\Ae\*))    {$s .= "✕"}                                       # Multiply
    elsif ($w =~ m(\Ae\+))    {$s .= "＋"}                                       # Plus
    elsif ($w =~ m(\Ae(\d+))) {$s .= c $1, "e"}                                 # Dyad2  chosen by number
    elsif ($w =~ m(\Ap(\d+))) {$s .= c $1, "p"}                                 # Prefix chosen by number
    elsif ($w =~ m(\Aq(\d+))) {$s .= c $1, "q"}                                 # Suffix chosen by number
    elsif ($w =~ m(\As\Z))    {$s .= c 0, "s"}                                 # Semicolon
    elsif ($w =~ m(\AS\Z))    {$s .= ' '}                                       # Space
    elsif ($w =~ m(\Av(\w+))) {$s .= $var ->($1)}                               # Variable name
    else {confess "Cannot create Unisyn from $w"}                               # Variable name
   }

  writeTempFile $s                                                              # Composed string to temporary file
 }

sub Nasm::X86::Unisyn::Lex::PermissibleTransitions($)                           # Create and load the table of lexical transitions.
 {my ($area) = @_;                                                              # Area in which to create the table
  my $t = $area->CreateTree(length => 3);
  my $a = Nasm::X86::Unisyn::Lex::Number::a;                                    # Assign-2 - right to left
  my $A = Nasm::X86::Unisyn::Lex::Number::A;                                    # Ascii
  my $b = Nasm::X86::Unisyn::Lex::Number::b;                                    # Open
  my $B = Nasm::X86::Unisyn::Lex::Number::B;                                    # Close
  my $d = Nasm::X86::Unisyn::Lex::Number::d;                                    # Dyad-3   - left to right
  my $e = Nasm::X86::Unisyn::Lex::Number::e;                                    # Dyad-4   - left to right
  my $F = Nasm::X86::Unisyn::Lex::Number::F;                                    # Finish
  my $p = Nasm::X86::Unisyn::Lex::Number::p;                                    # Prefix
  my $q = Nasm::X86::Unisyn::Lex::Number::q;                                    # Suffix
  my $s = Nasm::X86::Unisyn::Lex::Number::s;                                    # Semicolon-1
  my $S = Nasm::X86::Unisyn::Lex::Number::S;                                    # Start
  my $v = Nasm::X86::Unisyn::Lex::Number::v;                                    # Variable

  my %x = (                                                                     # The transitions table: this tells us which combinations of lexical items are valid.  The table is augmented with start and end symbols so that we kno where to start and end.
    $a => [    $A, $b,                             $v],
    $A => [$a,         $B, $d, $e, $F,     $q, $s,   ],
    $b => [    $A, $b, $B,             $p,     $s, $v],
    $B => [$a,         $B, $d, $e, $F,     $q, $s    ],
    $d => [    $A, $b, $B,             $p,         $v],
    $e => [    $A, $b,                 $p,         $v],
    $p => [    $A, $b,                             $v],
    $q => [$a, $A,     $B, $d, $e, $F,         $s    ],
    $s => [    $A, $b, $B,         $F, $p,     $s, $v],
    $S => [    $A, $b,             $F, $p,     $s, $v],
    $v => [$a,         $B, $d, $e, $F,     $q, $s    ],
  );

  my $T   = $area->CreateTree(length => 3);                                     # Tree of trees
  for my $x(sort keys %x)                                                       # Each source lexical item
   {my @y = $x{$x}->@*;
    my $t = $area->CreateTree(length => 3);                                     # A tree containing each target lexical item for the source item
    $t->put(K(next => $_), K key => 1) for @y;                                  # Load target set
    $T->put(K(key => $x), $t);                                                  # Save target set
   }

  $T                                                                            # Tree of source to target
 }

sub Nasm::X86::Unisyn::Lex::OpenClose($)                                        # Create and load the table of open to close bracket mappings
 {my ($area) = @_;                                                              # Area in which to create the table
  my $o = $area->CreateTree(length => 3);                                       # Open to close
  my $c = $area->CreateTree(length => 3);                                       # Close to open
  my @b = Nasm::X86::Unisyn::Lex::Letter::b;                                    # Open
  my @B = Nasm::X86::Unisyn::Lex::Letter::B;                                    # Close

  @b == @B or confess "Bracket lengths mismatched";

  for my $i(keys @b)                                                            # Each open/close
   {my $O = K open  => $b[$i];
    my $C = K close => $B[$i];
    $o->put($O, $C);
    $c->put($C, $O);
   }

  ($o, $c)                                                                      # Open close tree, close open tree
 }

#latest:
if (1) {                                                                        #TNasm::X86::Unisyn::Lex::PermissibleTransitions
  my $a = CreateArea;
  my $t = Nasm::X86::Unisyn::Lex::PermissibleTransitions $a;
  $t->size->outNL;
  ok Assemble eq => <<END, avx512=>1;
size of tree: .... .... .... ...B
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Unisyn::Lex::PermissibleTransitions
  my $a = CreateArea;
  my ($o, $c) = Nasm::X86::Unisyn::Lex::OpenClose($a);
  $o->printInOrder('OC');
  $c->printInOrder('CO');
  ok Assemble eq => <<END, avx512=>1;
OC  38: 2308230A23292768276A276C276E27702772277427E627E827EA27EC27EE2983298529872989298B298D298F299129932995299729FC2E283008300A3010301430163018301AFD3EFF08FF5F
CO  38: 2309230B232A2769276B276D276F27712773277527E727E927EB27ED27EF298429862988298A298C298E2990299229942996299829FD2E293009300B3011301530173019301BFD3FFF09FF60
END
 }

sub Nasm::X86::Unisyn::Lex::LoadAlphabets($)                                    # Create and load the table of lexical alphabets.
 {my ($a) = @_;                                                                 # Area in which to create the table
  my $t = $a->CreateTree(length => 3);
  my @l = qw(A a b B d e p q s v);
  for my $l(@l)
   {my $n = K lex   => eval "Nasm::X86::Unisyn::Lex::Number::$l";
    my @c =            eval "Nasm::X86::Unisyn::Lex::Letter::$l";
    my $c = K count => scalar(@c);
    my $d = K(chars => Rd(@c));

    $c->for(sub
     {my ($i, $start, $next, $end) = @_;
      my  $e = ($d + $i * 4)->dereference;
      $t->put($e, $n);
     });
   }
  $t
 }

#latest:
if (1) {                                                                        #TNasm::X86::Unisyn::Lex::LoadAlphabets
  my $a = CreateArea;
  my $t = Nasm::X86::Unisyn::Lex::LoadAlphabets $a;
  $t->find(K alpha => ord('𝝰')); $t->found->outNL; $t->data ->outNL;
  ok Assemble eq => <<END, avx512=>1;
found: .... .... .... ...1
data: .... .... .... ...6
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Unisyn::Lex::composeUnisyn
  my $f = Nasm::X86::Unisyn::Lex::composeUnisyn
   ('va a= b( vb e+ vc B) e* vd dif ve');
  is_deeply readFile($f), "𝗔＝【𝗕＋𝗖】✕𝗗𝐈𝐅𝗘\n";
  my ($a8, $s8) = ReadFile K file => Rs $f;                                     # Address and size of memory containing contents of the file
  $s8->outNL;

  my ($a32, $s32, $count, $fail) = ConvertUtf8ToUtf32 $a8, $s8;                 # Convert an allocated block  string of utf8 to an allocated block of utf32 and return its address and length.
  $_->outNL for $s32, $count, $fail;

  ok Assemble eq => <<END, avx512=>1;
size: .... .... .... ..2C
s32: .... .... .... ..B0
count: .... .... .... ...D
fail: .... .... .... ....
END
  unlink $f;
 }

#latest:
if (1) {                                                                        #TOR #TAND
  my $a = K(key => 1);

  OR (sub{$a==$a})             ->outNL;
  OR (sub{$a!=$a})             ->outNL;
  OR (sub{$a!=$a}, sub{$a==$a})->outNL;
  OR (sub{$a!=$a}, sub{$a!=$a})->outNL;

  AND(sub{$a==$a})             ->outNL;
  AND(sub{$a!=$a})             ->outNL;
  AND(sub{$a==$a}, sub{$a==$a})->outNL;
  AND(sub{$a==$a}, sub{$a!=$a})->outNL;

  If OR(sub{$a==$a}, sub{$a!=$a}) > 0,
  Then
   {PrintOutStringNL "AAAA";
   };

  If OR(sub{$a!=$a}, sub{$a!=$a}) > 0,
  Then
   {PrintOutStringNL "BBBB";
   };
  ok Assemble eq => <<END, avx512=>1;
or: .... .... .... ...1
or: .... .... .... ....
or: .... .... .... ...1
or: .... .... .... ....
and: .... .... .... ...1
and: .... .... .... ....
and: .... .... .... ...1
and: .... .... .... ....
AAAA
END
 }

sub Nasm::X86::Unisyn::Lex::Reason::Success           {0};                      # Successful parse
sub Nasm::X86::Unisyn::Lex::Reason::BadUtf8           {1};                      # Bad utf8 character encountered
sub Nasm::X86::Unisyn::Lex::Reason::InvalidChar       {2};                      # Character not part of Earl Zero
sub Nasm::X86::Unisyn::Lex::Reason::InvalidTransition {3};                      # Transition from one lexical item to another not allowed
sub Nasm::X86::Unisyn::Lex::Reason::TrailingClose     {4};                      # Trailing closing bracket discovered
sub Nasm::X86::Unisyn::Lex::Reason::Mismatch          {5};                      # Mismatched bracket
sub Nasm::X86::Unisyn::Lex::Reason::NotFinal          {6};                      # Expected something after final character
sub Nasm::X86::Unisyn::Lex::Reason::BracketsNotClosed {7};                      # Open brackets not closed at end of

sub Nasm::X86::Unisyn::Lex::position {0};                                       # Position of the parsed item in the input text
sub Nasm::X86::Unisyn::Lex::length   {1};                                       # Length of the lexical item in bytes
sub Nasm::X86::Unisyn::Lex::type     {2};                                       # Type of the lexical item
sub Nasm::X86::Unisyn::Lex::left     {3};                                       # Left operand
sub Nasm::X86::Unisyn::Lex::right    {4};                                       # Right operand
sub Nasm::X86::Unisyn::Lex::symbol   {5};                                       # Symbol

sub Nasm::X86::Unisyn::Parse($$$)                                               # Parse a string of utf8 characters
 {my ($area, $a8, $s8) = @_;                                                    # Area in which to create the parse tree, add ress of utf8 string, size of the utf8 string in bytes
  my ($openClose, $closeOpen) = Nasm::X86::Unisyn::Lex::OpenClose $area;        # Open to close bracket matching
  my $brackets    = $area->CreateTree(length => 3);                             # Bracket stack
  my $parse       = $area->CreateTree(length => 3);                             # Parse tree stack
  my $symbols     = $area->CreateQuarks;                                        # Quarks assigning every lexical item string a unique number

  my $alphabets   = Nasm::X86::Unisyn::Lex::LoadAlphabets          $area;       # Create and load the table of alphabetic classifications
  my $transitions = Nasm::X86::Unisyn::Lex::PermissibleTransitions $area;       # Create and load the table of lexical transitions.
  my $position    = V pos => 0;                                                 # Position in input string
  my $last        = V last => Nasm::X86::Unisyn::Lex::Number::S;                # Last lexical type
  my $next        = $transitions->cloneDescriptor;                              # Clone the transitions table so we can step down it without losing the original table
     $next->find($last);                                                        # Locate the current classification
     $next->down;                                                               # Tree of possible transitions on lexical type

  my $parseFail   = V parseFail   => 1;                                         # If not zero the parse has failed for some reason
  my $parseReason = V parseReason => 0;                                         # The reason code describing the failure
  my $parseMatch  = V parseMatch  => 0;                                         # The position of the bracket we failed to match
  my $parseChar   = V parseChar   => 0;                                         # The last character recognized

  my $startPos    = V startPos    => 0;                                         # Start position of the last lexical item
  my $lastNew     = V lastNew     => 0;                                         # Last lexical created
  my $started;                                                                  # True after we have added the first symbol and so can have a previous symbol

  my $dumpStack = sub                                                           # Dump the parse stack
   {my $i = V i => 0;                                                           # Position in stack
    PrintOutStringNL "Dump parse stack";
    $parse->by(sub                                                              # Each item on stack
     {my ($T, $start, $next) = @_;
      my $t = $T->describeTree->position($T->data);                             # Assume that each stack element is a parse tree

      $i++; $i->outRightInDec(K width => 4);
      $t->find(K key => Nasm::X86::Unisyn::Lex::type);
      If $t->data == K(t => Nasm::X86::Unisyn::Lex::Number::S), Then {PrintOutString "Start    "};
      If $t->data == K(t => Nasm::X86::Unisyn::Lex::Number::F), Then {PrintOutString "End      "};
      If $t->data == K(t => Nasm::X86::Unisyn::Lex::Number::A), Then {PrintOutString "ASCII    "};
      If $t->data == K(t => Nasm::X86::Unisyn::Lex::Number::d), Then {PrintOutString "Infix3   "};
      If $t->data == K(t => Nasm::X86::Unisyn::Lex::Number::p), Then {PrintOutString "Prefix   "};
      If $t->data == K(t => Nasm::X86::Unisyn::Lex::Number::a), Then {PrintOutString "Assign   "};
      If $t->data == K(t => Nasm::X86::Unisyn::Lex::Number::v), Then {PrintOutString "Variable "};
      If $t->data == K(t => Nasm::X86::Unisyn::Lex::Number::q), Then {PrintOutString "Suffix   "};
      If $t->data == K(t => Nasm::X86::Unisyn::Lex::Number::s), Then {PrintOutString "Seperator"};
      If $t->data == K(t => Nasm::X86::Unisyn::Lex::Number::e), Then {PrintOutString "Infix4   "};
      If $t->data == K(t => Nasm::X86::Unisyn::Lex::Number::b), Then {PrintOutString "Open     "};
      If $t->data == K(t => Nasm::X86::Unisyn::Lex::Number::B), Then {PrintOutString "Close    "};

      $t->data->outRightInDec(K width => 4);  PrintOutString "  ";
      $t->dumpParseTree($a8);
     });
   };

  my $updateLength = sub                                                        # Update the length of the previous lexical item
   {my $t = $parse->position($lastNew);                                         # The description of the last lexical item

    my $l = $position - $startPos;                                              # Length of previous item
    $t->put(K(t => Nasm::X86::Unisyn::Lex::length), $l);                        # Record length of previous item in its describing tree
#   my $s = $symbols->put($a8+$startPos, $l);                                   # The symbol number for the last lexical item
#    $t->put(K(t => Nasm::X86::Unisyn::Lex::symbol), $s);                        # Record length of previous item in its describing tree
   };

  my $new = sub                                                                 # Create a new lexical item
   {my $l = $area->CreateTree(length => 3);                                     # Tree to hold lexical item description
    $l->put(K(t => Nasm::X86::Unisyn::Lex::length),   K(one => 1));             # Length so far of lexical item - not really necessary but it does aid debugging
    $l->put(K(t => Nasm::X86::Unisyn::Lex::type),     $last);                   # Last lexical item recognized
    $l->put(K(t => Nasm::X86::Unisyn::Lex::position), $position);               # Position of lexical item
    if ($started)
     {&$updateLength;                                                           # Update the length of the previous lexical item
      $startPos->copy($position);                                               # This item now becomes the last lexical item
     }
    else
     {$started++                                                                # At least one item has been processed
     }
    $lastNew ->copy($l->first);                                                 # This item now becomes the last lexical item
    $l
   };

  my $push = sub                                                                # Push the current lexical item on to the stack and return its tree descriptor
   {$parse->push(my $n = &$new);
    $n
   };

  &$push for 1..3;                                                              # Initialize the parse tree with three start symbols to act as sentinels

  my $prev = sub                                                                # Lexical type of the previous item on the parse stack
   {my $p = $parse->peekSubTree(K one => 1);
    $p->find(K type => Nasm::X86::Unisyn::Lex::type);                           # Lexical type
    $p                                                                          # Guaranteed to exist
   };

  my $prev2 = sub                                                               # Lexical type of the previous previous item on the parse stack
   {my $p = $parse->peekSubTree(K key => 2);
    $p->find(K key => Nasm::X86::Unisyn::Lex::type);                            # Lexical type
    $p                                                                          # Guaranteed to exist
   };

  my $double = sub                                                              # Double reduction - the right most item is placed under the second right most item
   {my $right = $parse->popSubTree;
    &$prev->put(K(l => Nasm::X86::Unisyn::Lex::left), $right);
   };

  my $triple = sub                                                              # Triple reduction
   {my $right = $parse->popSubTree;                                             # Right operand
    my $op    = $parse->popSubTree;                                             # Operator
    my $left  = $parse->popSubTree;                                             # Left operand
    $parse->push($op);
    $op->put(K(l => Nasm::X86::Unisyn::Lex::left ), $left);
    $op->put(K(r => Nasm::X86::Unisyn::Lex::right), $right);
   };

  my $a = sub                                                                   # Dyad2 = right to left associative
   {#PrintErrStringNL "Type: a";
    my $q = &$prev2;                                                            # Second previous item
    If OR
     (sub {$q->data == K p => Nasm::X86::Unisyn::Lex::Number::d},               # Dyad2 preceeded by dyad3 or dyad4
      sub {$q->data == K p => Nasm::X86::Unisyn::Lex::Number::e}),
    Then
     {&$triple;                                                                 # Reduce
     };
    &$push;                                                                     # Push dyad2
   };

  my $A = sub                                                                   # Ascii
   {#PrintErrStringNL "Type: A";
    my $p = &$prev;
    If $p->data == K(p => Nasm::X86::Unisyn::Lex::Number::p),
    Then                                                                        # Previous is a prefix operator
     {$p->put(K(l => Nasm::X86::Unisyn::Lex::left), &$new);                     # Push onto prev
     },
    Else                                                                        # Previous is not a prefix operator
     {&$push;                                                                   # Push ascii
     },
   };

  my $b = sub                                                                   # Open bracket
   {#PrintErrStringNL "Type: b";
    &$push;                                                                     # Push open bracket
   };

  my $B = sub                                                                   # Close bracket
   {#PrintErrStringNL "Type: B";
    If &$prev->data == K(p => Nasm::X86::Unisyn::Lex::Number::s),               # Pointless statement separator
    Then
     {$parse->pop;
     };
    Block                                                                       # Non empty pair of brackets - a single intervening bracket represents a previously collapsed bracketed expression
     {my ($end, $start) = @_;
      my $p = &$prev2;
      If $p->data == K(p => Nasm::X86::Unisyn::Lex::Number::b),
      Then                                                                      # Single item in brackets
       {&$double;
       },
      Ef {$p->data != K(p => Nasm::X86::Unisyn::Lex::Number::S)}
      Then                                                                      # Triple reduce back to start
       {&$triple;
        Jmp $start;                                                             # Keep on reducing until we meet the matching opening bracket
       };
     };
    If &$prev2->data == K(p => Nasm::X86::Unisyn::Lex::Number::p),              # Prefix operator preceding brackets
    Then
     {&$double;
     };
   };

  my $d = sub                                                                   # Dyad3
   {my $q = &$prev2;                                                            # Second previous item
    If OR
     (sub {$q->data == K p => Nasm::X86::Unisyn::Lex::Number::d},               # Dyad3 preceeded by dyad3 or dyad4
      sub {$q->data == K p => Nasm::X86::Unisyn::Lex::Number::e}),
    Then
     {&$triple;                                                                 # Reduce
     };
    &$push;                                                                     # Push dyad3
   };

  my $e = sub                                                                   # Dyad4
   {#PrintErrStringNL "Type: e";
    my $q = &$prev2;                                                            # Second previous item
    If $q->data == K(p => Nasm::X86::Unisyn::Lex::Number::e),
    Then                                                                        # Dyad4 preceded by dyad4
     {&$triple;                                                                 # Reduce
     };
    &$push;                                                                     # Push dyad4
   };

  my $F = sub                                                                   # Final: at this point there are no brackets left.
   {#PrintErrStringNL "Type: F";
    &$updateLength;                                                             # Update the length of the previous lexical item - if there were none it will the length of the start symbol that is updated
    $parse->size->for(sub                                                       # Reduce
     {my ($index, $start, $next, $end) = @_;
      my $p = &$prev2;
      If $p->data != K(p => Nasm::X86::Unisyn::Lex::Number::S),
      Then                                                                      # Not at the end yet
       {&$triple;
       },
      Else                                                                      # Down to the start line
       {Jmp $end;
       };
     });
    my ($top) = map {$parse->popSubTree} 1..4;                                  # Top of the parse tree - with three starts below
    $parse->push($top);                                                         # New top of the parse tree
   };

  my $p = sub                                                                   # Prefix
   {#PrintErrStringNL "Type: p";
    &$push;                                                                     # Push prefix
   };

  my $q = sub                                                                   # Suffix
   {#PrintErrStringNL "Type: q";
    my $t = $parse->popSubTree;                                                 # Pop existing item description
    my $p = &$push;                                                             # Push suffix
    $p->push($t);                                                               # Restore previous item but now under suffix
   };

  my $s = sub                                                                   # Statement separator
   {#PrintErrStringNL "Type: s";
    Block
     {my ($end, $start) = @_;
      my $p = &$prev;                                                           # Previous item
      If OR                                                                     # Separator preceded by open or start - do nothing
       (sub {$p->data == K p => Nasm::X86::Unisyn::Lex::Number::b},
        sub {$p->data == K p => Nasm::X86::Unisyn::Lex::Number::s},
        sub {$p->data == K p => Nasm::X86::Unisyn::Lex::Number::S}),
      Then                                                                      # Eliminate useless statement separator
       {Jmp $end;
       };
      my $q = &$prev2;                                                          # Second previous item
      If $q->data == K(p => Nasm::X86::Unisyn::Lex::Number::s),
      Then                                                                      # Second previous is a statement separator
       {&$triple;                                                               # Reduce
        Jmp $end;                                                               # No need to push as we already have a statement separator on top of the stack
       };
      If OR
       (sub {$q->data == K p => Nasm::X86::Unisyn::Lex::Number::b},             # Statement separator preceded by singleton
        sub {$q->data == K p => Nasm::X86::Unisyn::Lex::Number::S}),
      Then
       {&$push;                                                                 # Push statement separator after singleton
        Jmp $end;
       };
      &$triple;                                                                 # An operator at a higher level than statement separator so we can reduce
      Jmp $start;                                                               # Keep on reducing until we meet the matching opening bracket or start
     }
   };

  my $v = sub                                                                   # Variable
   {#PrintErrStringNL "Type: v";
    my $p = &$prev;
    If $p->data == K(p => Nasm::X86::Unisyn::Lex::Number::p),
    Then                                                                        # Previous is a prefix operator
     {$p->put(K(l => Nasm::X86::Unisyn::Lex::left), &$new);                     # Push onto prev
     },
    Else                                                                        # Previous is not a prefix operator
     {&$push;                                                                   # Push variable
     },
   };

  $s8->for(sub                                                                  # Process up to the maximum number of characters
   {my ($index, undef, undef, $end) = @_;
    my ($char, $size, $fail) = GetNextUtf8CharAsUtf32 $a8 + $position;          # Get the next UTF-8 encoded character from the addressed memory and return it as a UTF-32 char.
    $parseChar->copy($char);                                                    # Copy the current character

    If $fail > 0,
    Then                                                                        # Failed to convert a utf8 character
     {$parseReason  ->copy(Nasm::X86::Unisyn::Lex::Reason::BadUtf8);
      Jmp $end;
     };

    $alphabets->find($char);                                                    # Classify character
    If $alphabets->found == 0,
    Then                                                                        # Failed to classify character
     {$parseReason->copy(Nasm::X86::Unisyn::Lex::Reason::InvalidChar);
      Jmp $end;
     };

    my $change = V change => 0;                                                 # Changing from one lexical item to the next

    If $alphabets->data == K(open => Nasm::X86::Unisyn::Lex::Number::b),        # Match brackets
    Then                                                                        # Opening bracket
     {$openClose->find($char);                                                  # Locate corresponding closer
      my $t = $area->CreateTree(length => 3);                                   # Tree recording the details of the opening bracket
      $t->push($position);                                                      # Position in source
      $t->push($char);                                                          # The opening bracket
      $t->push($openClose->data);                                               # The corresponding closing bracket - guaranteed to exist
      $brackets->push($t);                                                      # Save bracket description on bracket stack
      $change->copy(1);                                                         # Changing because we are on a bracket
#     &$b;                                                                      # Push the open bracket
     },
    Ef {$alphabets->data == K(open => Nasm::X86::Unisyn::Lex::Number::B)}
    Then                                                                        # Closing bracket
     {my $t = $brackets->popSubTree;                                            # Match with brackets stack
      If $t->found > 0,                                                         # Something to match with on the brackets stack
      Then
       {$t->find(K out => 2);                                                   # Expected bracket
        If $t->data != $char,                                                   # Did not match the expected bracket
        Then
         {$t->find(K position => 0);
          $parseMatch ->copy($t->data);
          $parseReason->copy(Nasm::X86::Unisyn::Lex::Reason::Mismatch);         # Mismatched bracket
          Jmp $end;
         };
        $change->copy(1);                                                       # Changing because we are on a bracket
#       &$B;                                                                    # Push the open bracket
       },
      Else
       {$parseReason->copy(Nasm::X86::Unisyn::Lex::Reason::TrailingClose);
        Jmp $end;
       };
     },
    Ef {$alphabets->data != $last}
    Then                                                                        # Change of current lexical item
     {$change->copy(1);                                                         # Changing because we are on a different lexical item
     },
    Ef {$alphabets->data == K(sep => Nasm::X86::Unisyn::Lex::Number::s)}
    Then                                                                        # Statement separator is always one character wide as more would be pointless
     {$change->copy(1);                                                         # Changing because we are on a different lexical item
     };

    If $change > 0,                                                             # Check the transition from the previous item
    Then                                                                        # Change of current lexical item
     {$next->find($alphabets->data);                                            # Locate next lexical item in the tree of possible transitions for the last lexical item
      If $next->found > 0,
      Then                                                                      # The transition on this lexical type was a valid transition
       {$next->copyDescriptor($transitions);                                    # Restart at the top of the transitions tree
        $next->find($alphabets->data);                                          # Tree of possible transitions on this lexical type
        $next->down;                                                            # Tree of possible transitions on lexical type
        $last->copy($alphabets->data);                                          # Treat unbroken sequences of a symbol as one lexical item
       },
      Else                                                                      # The transition on this lexical type was an invalid transition
       {$parseReason->copy(Nasm::X86::Unisyn::Lex::Reason::InvalidTransition);
        Jmp $end;
       };

      my $l = &$new;                                                            # Description of the lexical item

      Block                                                                     # Parse each lexical item to produce a parse tree of trees
       {my ($end, $start) = @_;                                                 # Code with labels supplied
        for my $l(qw(a A b B d e F p q s S v))
         {eval qq(If \$last == K($l => Nasm::X86::Unisyn::Lex::Number::$l), Then {&\$$l; Jmp \$end});
         }
        PrintErrTraceBack "Unexpected lexical type";                            # Something unexpected came along
       };
     };                                                                         # Else not required - we are continuing in the same lexical item

    $position->copy($position + $size);                                         # Point to next character to be parsed
    If $position > $s8,
    Then                                                                        # We have reached the end of the input
     {$next->find(K finish => Nasm::X86::Unisyn::Lex::Number::F);               # Check that we can locate the final state from the last symbol encountered
      If $next->found > 0,
      Then                                                                      # We are able to transition to the final state
       {If $brackets->size == 0,
        Then                                                                    # No outstanding brackets
         {&$F;
          $parseFail->copy(0);                                                  # Show success as a lack of failure
         },
        Else                                                                    # Open brackets not yet closed
         {$parseFail->copy(Nasm::X86::Unisyn::Lex::Reason::BracketsNotClosed);  # Error code
         };
       },
      Else                                                                      # We are not able to transition to the final state
       {$parseFail->copy(Nasm::X86::Unisyn::Lex::Reason::NotFinal);             # Error code
       };
      Jmp $end;                                                                 # Cannot parse further
     };
   });

  my $parseTree = $parse->popSubTree; $parse->free; $brackets->free;            # Obtain the parse tree and free the brackets and stack trees

   ($parseTree,                                                                 # The resulting parse tree
    $parseChar,                                                                 # Last character processed
    $parseFail,                                                                 # If not zero the parse has failed for some reason
    $position,                                                                  # The position reached in the input string
    $parseMatch,                                                                # The position of the matching bracket  that did not match
    $parseReason)                                                               # The reason code describing the failure
 } # Parse

#latest:
if (1) {                                                                        #TNasm::X86::Unisyn::Lex::composeUnisyn
  my $f = Nasm::X86::Unisyn::Lex::composeUnisyn
   ('va a= b( vb e+ vc B) e* vd dif ve');
  is_deeply readFile($f), "𝗔＝【𝗕＋𝗖】✕𝗗𝐈𝐅𝗘\n";
  my ($a8, $s8) = ReadFile K file => Rs $f;                                     # Address and size of memory containing contents of the file

  my $a = CreateArea;                                                           # Area in which we will do the parse
  my ($parse, @a) = Nasm::X86::Unisyn::Parse $a, $a8, $s8-2;                    # Parse the utf8 string minus the final new line and zero?

  $_->outNL for @a;
  $parse->dumpParseTree($a8);

  ok Assemble eq => <<END, avx512=>1;
parseChar: .... .... ...1 D5D8
parseFail: .... .... .... ....
pos: .... .... .... ..2B
parseMatch: .... .... .... ....
parseReason: .... .... .... ....
＝
._𝗔
._𝐈𝐅
._._✕
._._._【
._._._._＋
._._._._._𝗕
._._._._._𝗖
._._._𝗗
._._𝗘
END
  unlink $f;
 }

sub unisynParse($$$)                                                            # Test the parse of a unisyn expression
 {my ($compose, $text, $parse) = @_;                                            # The composing expression used to create a unisyn expression, the expected composed expression, the expected parse tree
  my $f = Nasm::X86::Unisyn::Lex::composeUnisyn($compose);
# say STDERR readFile($f);
  is_deeply readFile($f), $text;
  my ($a8, $s8) = ReadFile K file => Rs $f;                                     # Address and size of memory containing contents of the file

  my $a = CreateArea;                                                           # Area in which we will do the parse
  my ($p, @a) = Nasm::X86::Unisyn::Parse $a, $a8, $s8-2;                        # Parse the utf8 string minus the final new line and zero?

  $p->dumpParseTree($a8);
  ok Assemble eq => $parse, avx512=>1, mix=>0;
  say STDERR readFile(q(zzzOut.txt)) =~ s(\n) (\\n)gsr;
  unlink $f;
 };

unisynParse '',                                        "\n",                    qq(\n\n);
unisynParse 'va',                                      "𝗔\n",                   qq(𝗔\n);
unisynParse 'va a= va',                                "𝗔＝𝗔\n",                 qq(＝\n._𝗔\n._𝗔\n);
unisynParse 'va e+ vb',                                "𝗔＋𝗕\n",                 qq(＋\n._𝗔\n._𝗕\n);
unisynParse 'va a= vb e+ vc',                          "𝗔＝𝗕＋𝗖\n",               qq(＝\n._𝗔\n._＋\n._._𝗕\n._._𝗖\n);
unisynParse 'va a= vb e* vc',                          "𝗔＝𝗕✕𝗖\n",              qq(＝\n._𝗔\n._✕\n._._𝗕\n._._𝗖\n);
unisynParse 'b( B)',                                   "【】\n",                  qq(【\n);
unisynParse 'b( b[ B] B)',                             "【⟦⟧】\n",                qq(【\n._⟦\n);
unisynParse 'b( b[ b< B> B] B)',                       "【⟦⟨⟩⟧】\n",              qq(【\n._⟦\n._._⟨\n);

unisynParse 'b( va B)',                                "【𝗔】\n",                 qq(【\n._𝗔\n);
unisynParse 'b( b[ va B] B)',                          "【⟦𝗔⟧】\n",               qq(【\n._⟦\n._._𝗔\n);
unisynParse 'b( b[ va e+ vb B] B)',                    "【⟦𝗔＋𝗕⟧】\n",             qq(【\n._⟦\n._._＋\n._._._𝗔\n._._._𝗕\n);
unisynParse 'b( b[ va e+ vb B] e* b[ va e+ vb B] B)',  "【⟦𝗔＋𝗕⟧✕⟦𝗔＋𝗕⟧】\n",       qq(【\n._✕\n._._⟦\n._._._＋\n._._._._𝗔\n._._._._𝗕\n._._⟦\n._._._＋\n._._._._𝗔\n._._._._𝗕\n);
unisynParse 's s s s s',                               "⟢⟢⟢⟢⟢\n",               qq();
unisynParse 'va s vb',                                 "𝗔⟢𝗕\n",                 qq(⟢\n._𝗔\n._𝗕\n);
unisynParse 'va s s vb',                               "𝗔⟢⟢𝗕\n",                qq(⟢\n._𝗔\n._𝗕\n);
unisynParse 's s va s s vb s s',                       "⟢⟢𝗔⟢⟢𝗕⟢⟢\n",            qq(⟢\n._𝗔\n._𝗕\n);
unisynParse 'va a= vb a= vc',                          "𝗔＝𝗕＝𝗖\n",               qq(＝\n._𝗔\n._＝\n._._𝗕\n._._𝗖\n);
unisynParse 'va a= vb e+ vc a= vd e+ ve',              "𝗔＝𝗕＋𝗖＝𝗗＋𝗘\n",           qq(＝\n._𝗔\n._＝\n._._＋\n._._._𝗕\n._._._𝗖\n._._＋\n._._._𝗗\n._._._𝗘\n);
unisynParse 'va a= vb e+ vc s vd a= ve e+ vf',         "𝗔＝𝗕＋𝗖⟢𝗗＝𝗘＋𝗙\n",         qq(⟢\n._＝\n._._𝗔\n._._＋\n._._._𝗕\n._._._𝗖\n._＝\n._._𝗗\n._._＋\n._._._𝗘\n._._._𝗙\n);
unisynParse 'va dif vb',                               "𝗔𝐈𝐅𝗕\n",                qq(𝐈𝐅\n._𝗔\n._𝗕\n);
unisynParse 'va dif vb delse vc',                      "𝗔𝐈𝐅𝗕𝐄𝐋𝐒𝐄𝗖\n",           qq(𝐄𝐋𝐒𝐄\n._𝐈𝐅\n._._𝗔\n._._𝗕\n._𝗖\n);
unisynParse 'va a= b1 vb e+ vc B1 e* vd dif ve',       "𝗔＝⌊𝗕＋𝗖⌋✕𝗗𝐈𝐅𝗘\n",        qq(＝\n._𝗔\n._𝐈𝐅\n._._✕\n._._._⌊\n._._._._＋\n._._._._._𝗕\n._._._._._𝗖\n._._._𝗗\n._._𝗘\n);
unisynParse 'va a= vb dif vc e* vd s vA a= vB dif  vC e* vD s', "𝗔＝𝗕𝐈𝐅𝗖✕𝗗⟢𝝰＝𝝱𝐈𝐅𝝲✕𝝳⟢\n",  qq(⟢\n._＝\n._._𝗔\n._._𝐈𝐅\n._._._𝗕\n._._._✕\n._._._._𝗖\n._._._._𝗗\n._＝\n._._𝝰\n._._𝐈𝐅\n._._._𝝱\n._._._✕\n._._._._𝝲\n._._._._𝝳\n);
unisynParse 'p11 va',                                  "𝑳𝗔\n",                  qq(𝑳\n._𝗔\n);
unisynParse 'va q11',                                  "𝗔𝙇\n",                  qq(𝙇\n._𝗔\n);
unisynParse 'p11 va q10',                              "𝑳𝗔𝙆\n",                 qq(𝙆\n._𝑳\n._._𝗔\n);
unisynParse 'p11 b( B) q10',                           "𝑳【】𝙆\n",                qq(𝙆\n._𝑳\n._._【\n);
unisynParse 'p21 b( va e* vb B) q22',                  "𝑽【𝗔✕𝗕】𝙒\n",             qq(𝙒\n._𝑽\n._._【\n._._._✕\n._._._._𝗔\n._._._._𝗕\n);
unisynParse 'va e+ vb q11',                            "𝗔＋𝗕𝙇\n",                qq(＋\n._𝗔\n._𝙇\n._._𝗕\n);
unisynParse 'va e+ p11 vb q11',                        "𝗔＋𝑳𝗕𝙇\n",              qq(＋\n._𝗔\n._𝙇\n._._𝑳\n._._._𝗕\n);
unisynParse 'va e+ p11 vb q11 e+ p21 b( va e* vb B) q22',  "𝗔＋𝑳𝗕𝙇＋𝑽【𝗔✕𝗕】𝙒\n",           qq(＋\n._＋\n._._𝗔\n._._𝙇\n._._._𝑳\n._._._._𝗕\n._𝙒\n._._𝑽\n._._._【\n._._._._✕\n._._._._._𝗔\n._._._._._𝗕\n);
unisynParse 'va e+ p11 vb q11 dif p21 b( vc e* vd B) q22 delse ve e* vf',
            "𝗔＋𝑳𝗕𝙇𝐈𝐅𝑽【𝗖✕𝗗】𝙒𝐄𝐋𝐒𝐄𝗘✕𝗙\n",                                          qq(𝐄𝐋𝐒𝐄\n._𝐈𝐅\n._._＋\n._._._𝗔\n._._._𝙇\n._._._._𝑳\n._._._._._𝗕\n._._𝙒\n._._._𝑽\n._._._._【\n._._._._._✕\n._._._._._._𝗖\n._._._._._._𝗗\n._✕\n._._𝗘\n._._𝗙\n);

sub Nasm::X86::Tree::dumpParseTree($$)                                          # Dump a parse tree
 {my ($tree, $source) = @_;                                                     # Tree, variable addressing source being parsed
  @_ == 2 or confess "Two parameters";

  my $s = Subroutine                                                            # Print a tree
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    my $t      = $$s{tree};                                                     # Tree
    my $source = $$p{source};                                                   # Source
    my $depth  = $$p{depth};                                                    # Depth
    my $area   = $t->area;                                                      # Area
    If $depth < K(key => 99),
    Then {                                                                      # Not in a recursive loop yet ?
                  $t->find(K pos => Nasm::X86::Unisyn::Lex::length);
    my $length   = $t->data->clone("Length");                                   # Length of input

                   $t->find(K pos => Nasm::X86::Unisyn::Lex::position);
    my $position = $t->data->clone("Position");                                 # Position in input

                   $t->find(K pos => Nasm::X86::Unisyn::Lex::type);
    my $type     = $t->data->clone("Type");                                     # Type of operator

                   $t->find(K pos => Nasm::X86::Unisyn::Lex::left);
    my $leftF    = $t->found->clone("Left");                                    # Left operand found
    my $left     = $t->data ->clone('left');                                    # Left operand

                   $t->find(K pos => Nasm::X86::Unisyn::Lex::right);
    my $rightF   = $t->found->clone("Right");                                   # Right operand found
    my $right    = $t->data ->clone('right');                                   # Right operand

    If $length > 0,                                                             # Source text of lexical item
    Then
     {$depth->for(sub
       {PrintOutString "._";
       });
      ($source + $position)->printOutMemoryNL($length);
     };

    If $leftF > 0,
    Then                                                                        # There is a left sub tree
     {$sub->call(structures => {tree  => $t->position($left)},
                 parameters => {depth => $depth+1, source=> $source});
     };

    If $rightF > 0,
    Then                                                                        # There is a right sub tree
     {$sub->call(structures => {tree  => $t->position($right)},
                 parameters => {depth => $depth+1, source=> $source});
     };
     };
   } structures => {tree => $tree}, parameters=>[qw(depth source)],
     name       => "Nasm::X86::Tree::dumpParseTree";

# PrintOutStringNL $title;                                                      # Title of the piece so we do not lose it

  If $tree->size == 0,                                                          # Empty tree
  Then
   {#PrintOutStringNL "- empty";
   },
  Else                                                                          # Print root node
   {#PrintOutString ": ";
    $s->call(structures => {tree  => $tree},
             parameters => {depth => K(depth => 0), source=> $source});
    #PrintOutNL;
   };
 }

#D1 Quarks                                                                      # Translate between a unique string and a unique number.

sub Nasm::X86::Quarks::StringToNumber {0}                                       # The field in the quarks tree that contains the offset of the tree that maps strings to numbers
sub Nasm::X86::Quarks::NumberToString {1}                                       # The field in the quarks tree that contains the offset of the tree that maps numbers to strings

sub Nasm::X86::Area::CreateQuarks($%)                                           # Create a set if quarks in an area.
 {my ($area, %options) = @_;                                                    # Area description, quark options
  @_ % 2 == 1 or confess "Odd number of parameters required";

  my $q = $area->CreateTree(length => 3);                                       # A tree descriptor for a set of  quarks == tree in the specified area
  my $s = $area->CreateTree(length => 3);                                       # Strings to numbers
  my $n = $area->CreateTree(length => 3);                                       # Numbers to strings
  $q->put(K(key => Nasm::X86::Quarks::StringToNumber), $s);                     # Strings to numbers
  $q->put(K(key => Nasm::X86::Quarks::NumberToString), $n);                     # Numbers to strings
  bless {%$q}, q(Nasm::X86::Quarks)                                             # A tree descriptor for a set of  quarks == tree in the specified area
 }

sub Nasm::X86::Quarks::dump($$)                                                 # Dump quarks
 {my ($quarks, $title) = @_;                                                    # Area description, quark options
  @_ == 2 or confess "Two parameters";
  (bless {%$quarks}, q(Nasm::X86::Tree))->dump($title);
 }

sub Nasm::X86::Quarks::put($$$)                                                 # Add a string of specified length to the set of quarks and return its number as as a variable.
 {my ($quarks, $address, $size) = @_;                                           # Area description, quark options
  @_ == 3 or confess "Three parameters";
  my $t = bless {%$quarks}, "Nasm::X86::Tree";                                  # Quarks == Tree
  my $s = $t->findSubTree(K key => Nasm::X86::Quarks::StringToNumber);          # Strings to numbers
  my $n = $t->findSubTree(K key => Nasm::X86::Quarks::NumberToString);          # Numbers to strings
  my $q = $n->size;

  my $i = $t->area->treeFromString($address, $size);                            # Create an input tree string - expensive - we should look up the quark directly from the input string but this way is easier to code.
  my $I = $s->getString($i);                                                    # Look up the input string
  If $I->found == 0,                                                            # We can add it as it does not exist
  Then
   {$i->push($q);
    $s->putString($i);
    $n->push($i);
   },
  Else                                                                          # It already exists so returns its number
   {$q->copy($I->data);
    $i->free;                                                                   # We do not need the tree string as it is already present int the string tree.
   };
  $q
 }

sub Nasm::X86::Area::treeFromString($$$)                                        # Create a tree from a string of bytes held at a variable address with a variable length and return the resulting tree.  The first element of the tree is the specified length, in bytes, of the string.
 {my ($area, $address, $size) = @_;                                             # Area description, address of string, length of string in bytes
  @_ == 3 or confess "Three parameters";

  my $t = $area->CreateTree(length => 3);                                       # Create a tree to be used to store the string

  $t->push($size);                                                              # Push the length of the string

  If $size > 0,
  Then                                                                          # Push string of non zero length
   {PushR 13, 14, 15;

    my $two = K two => 2;
   ($size >> $two)->for(sub                                                     # Push each full dword of the input string into the tree
     {my ($i, $start, $next, $end) = @_;
      $i->setReg(15);                                                           # Index of chunk to push
      $address->setReg(14);                                                     # Start of string
      Mov r15, "[r14+4*r15]";                                                   # 4 means dword
      $t->push(V chunk => r15)                                                  # Load chunk and push into string tree
     });

    ClearRegisters r13;
    $address->setReg(14);                                                       # Start of string
    $size   ->setReg(15);                                                       # Length of string in bytes

    my $remainder = $size  - ($size >> $two << $two);                           # Any remainder
    If $remainder == 3,
    Then                                                                        # Last three bytes
     {Mov r13w, "[r14+r15-2]";                                                  # Last two bytes
      Shl r13, 8;                                                               # Make room for remaining word
      Mov r13b, "[r14+r15-3]";                                                  # Third last byte
     },
    Ef {$remainder == 2}
    Then                                                                        # Last two bytes
     {Mov r13w, "[r14+r15-2]";                                                  # Last two bytes
     },
    Ef {$remainder == 1}
    Then                                                                        # Last byte
     {Mov r13w, "[r14+r15-1]";                                                  # Last byte
     };

    If $remainder > 0,
    Then                                                                        # Save last few bytes
     {$t->push(V last => r13)                                                   # Last few bytes
     };
    PopR;
   };

  $t                                                                            # Description of tree loaded from string
 }

#latest:
if (0) {                                                                        #
  my $a =     CreateArea;
  my $q = $a->CreateQuarks;

  ok Assemble eq => <<END, avx512=>1;
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::treeFromString #TaddressAndLengthOfConstantStringAsVariables
  my $a = CreateArea;
  my ($s, $l) = addressAndLengthOfConstantStringAsVariables("1234567");
  my $t = $a->treeFromString($s, $l);
     $t->dump8xx("AA");

     $t->push(my $v = K key => 0x99);
     $t->dump8xx("BB");

  my $T = $a->CreateTree(length => 3);
     $T->putString($t);
     $T->dump8xx("CC");

     $t->pop;
  my $S = $T->getString($t);
     $S->found->outNL;
     $S->data ->outNL;
  ok Assemble eq => <<END, avx512=>1;
AA
Tree: .... .... .... ..40
At:       80                                                                                length:        3,  data:       C0,  nodes:      100,  first:       40, root, leaf
  Index:        0        1        2
  Keys :        0        1        2
  Data :        7 34333231   373635
end
BB
Tree: .... .... .... ..40
At:      200                                                                                length:        1,  data:      240,  nodes:      280,  first:       40, root, parent
  Index:        0
  Keys :        1
  Data : 34333231
  Nodes:       80      140
    At:       80                                                                            length:        1,  data:       C0,  nodes:      100,  first:       40,  up:      200, leaf
      Index:        0
      Keys :        0
      Data :        7
    end
    At:      140                                                                            length:        2,  data:      180,  nodes:      1C0,  first:       40,  up:      200, leaf
      Index:        0        1
      Keys :        2        3
      Data :   373635       99
    end
end
CC
Tree: .... .... .... .2C0
At:      340                                                                                length:        1,  data:      380,  nodes:      3C0,  first:      2C0, root, leaf,  trees:   1
  Index:        0
  Keys :        7
  Data :      30*
   Tree:      300
     At:      440                                                                           length:        1,  data:      480,  nodes:      4C0,  first:      300, root, leaf,  trees:   1
       Index:        0
       Keys : 34333231
       Data :      40*
        Tree:      400
          At:      500                                                                      length:        1,  data:      540,  nodes:      580,  first:      400, root, leaf
            Index:        0
            Keys :   373635
            Data :       99
          end
     end
end
found: .... .... .... ...1
data: .... .... .... ..99
END
 }

#latest:
if (1) {                                                                        #TNasm::X86::Tree::treeFromString #TaddressAndLengthOfConstantStringAsVariables
  my $a = CreateArea;
  my $q = $a->CreateQuarks;

  my sub put($)                                                                 # Quark from string
   {my ($string) = @_;                                                          # String to load
    my ($a, $l) = addressAndLengthOfConstantStringAsVariables($string);
    $q->put($a, $l)
   }

  my $n1 = put("1");
  my $n2 = put("12");
  my $n3 = put("123");

  my $N1 = put("1");
  my $N2 = put("12");
  my $N3 = put("123");

  $_->outRightInDecNL(K width => 1) for $n1, $N1, $n2, $N2, $n3, $N3;

  $q->dump("AA");

#  1         105,382         357,640         105,382         357,640      1.069422          0.38  at /home/phil/perl/cpan/NasmX86/lib/Nasm/X86.pm line 31764
  ok Assemble eq => <<END, avx512=>1, trace=>1;
0
0
1
1
2
2
AA
At:  100                    length:    2,  data:  140,  nodes:  180,  first:   40, root, leaf,  trees:  11
  Index:    0    1
  Keys :    0    1
  Data :  30*  48*
     At:  300               length:    3,  data:  340,  nodes:  380,  first:   80, root, leaf,  trees: 111
       Index:    0    1    2
       Keys :    1    2    3
       Data :  3C*  68*  88*
          At:  3C0          length:    1,  data:  400,  nodes:  440,  first:  2C0, root, leaf
            Index:    0
            Keys :   31
            Data :    0
          end
          At:  680          length:    1,  data:  6C0,  nodes:  700,  first:  640, root, leaf
            Index:    0
            Keys : 3231
            Data :    1
          end
          At:  880          length:    1,  data:  8C0,  nodes:  900,  first:  840, root, leaf
            Index:    0
            Keys : 3231
            Data :    2
          end
     end
     At:  480               length:    3,  data:  4C0,  nodes:  500,  first:   C0, root, leaf,  trees: 111
       Index:    0    1    2
       Keys :    0    1    2
       Data :  20*  58*  78*
          At:  200          length:    3,  data:  240,  nodes:  280,  first:  1C0, root, leaf
            Index:    0    1    2
            Keys :    0    1    2
            Data :    1   49    0
          end
          At:  580          length:    3,  data:  5C0,  nodes:  600,  first:  540, root, leaf
            Index:    0    1    2
            Keys :    0    1    2
            Data :    2 12849    1
          end
          At:  780          length:    3,  data:  7C0,  nodes:  800,  first:  740, root, leaf
            Index:    0    1    2
            Keys :    0    1    2
            Data :    3 3355185    2
          end
     end
end
END
 }

#latest:
if (1) {                                                                        #TTraceMode
  $TraceMode = 1;
  Mov rax, Rq(0x22);
  Mov rax, Rq(0x22);
  Mov rax, Rq(0x22);
  Mov rax, Rq(0x22);
  Mov rax, Rq(0x22);
  Mov rax, "[rax]";
  Mov rax, "[rax]";
  Mov rax, "[rax]";
  Mov rax, Rq(0x22);
  Mov rax, Rq(0x22);
  Mov rax, Rq(0x22);
  Mov rax, Rq(0x22);

  PrintOutRegisterInHex rax;
  eval {Assemble avx512=>1, trace=>1, mix=>0};
  ok readFile(q(zzzTraceBack.txt)) =~ m(TraceBack start:)s;
 }

#latest:
if (1) {                                                                        #TTraceMode
  $TraceMode = 1;                                                               # Enabling tracing

  my $S = Subroutine                                                            # Load and print rax
   {my ($p, $s, $sub) = @_;
    Mov rax, "[rax]";
    PrintOutRegisterInHex rax;
    If $$p{fail} > 0,                                                           # Fail if requested
    Then
     {Mov rax, "[rax]";
     };
   } name => "s", parameters=>[qw(fail)], trace=>1;

  my $T = Subroutine                                                            # Fail
   {my ($p, $s, $sub) = @_;
    Mov rax, Rq(0x22);
    $S->call(parameters => {fail => K(zero=> 1)});
   } name => "t";


  Mov rax, Rq(0x11);
  $S->call(parameters => {fail => K(zero=> 0)});                                # call
  $T->call;

  Assemble eq=><<END, avx512=>1, trace=>1, mix=>0;
   rax: .... .... .... ..11
   rax: .... .... .... ..22
END
 }

#latest:

#latest:
if (0) {                                                                        #
  ok Assemble eq => <<END, avx512=>1;
END
 }

done_testing;

unlink $_ for qw(sde-footprint.txt sde-log.txt);

say STDERR sprintf("# Time: %.2fs, bytes: %s, execs: %s",
  time - $start,
  map {numberWithCommas $_} totalBytesAssembled, $instructionsExecuted);
