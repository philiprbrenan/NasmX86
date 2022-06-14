#!/usr/bin/perl -I/home/phil/perl/cpan/DataTableText/lib/ -I. -Ilib/ -I/home/phil/perl/cpan/AsmC/lib/
#-------------------------------------------------------------------------------
# Generate X86 assembler code using Perl as a macro pre-processor.
# Philip R Brenan at appaapps dot com, Appa Apps Ltd Inc., 2021
#-------------------------------------------------------------------------------
# podDocumentation (\A.{80})\s+(#.*\Z) \1\2        (^sub.*#.*[^.]$) \1.
# 0x401000 from sde-mix-out addresses to get offsets in z.txt
# tree::print - speed up decision as to whether we are on a tree or not
# Make hash accept parameters at: #THash
# Document that V > 0 is required to create a boolean test
# Make sure that we are using bts and bzhi as much as possible in mask situations
# Replace calls to Tree::position with Tree::down
# Do not use r11 over extended ranges because Linux sets it to the flags register on syscalls. Free: rsi rdi, r11, rbx, rcx, rdx, likewise the mmx registers mm0-7, zmm 0..15 and k0..3.
# Make a tree read only - collapse all nodes possible, remove all leaf node arrays
# Make trees faster by using an array for small keys
# Jump forwarding
# All options checking immediately after parameters
# Which subs do we actually need SaveFirst four on?
package Nasm::X86;
our $VERSION = "20220606";
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
my $interpreter  = q(-I /usr/lib64/ld-linux-x86-64.so.2);                       # The ld command needs an interpreter if we are linking with C.
my $develop      = -e q(/home/phil/);                                           # Developing
our $sdeMixOut   = q(sde-mix-out.txt);                                          # Emulator hot spot output file
our $sdeTraceOut = q(sde-debugtrace-out.txt);                                   # Emulator trace output file
our $sdePtrCheck = q(sde-ptr-check.out.txt);                                    # Emulator pointer check file
our $traceBack   = q(zzzTraceBack.txt);                                         # Trace back of last error observed in emulator trace file if tracing is on
our $programErr  = q(zzzErr.txt);                                               # Program error  file
our $programOut  = q(zzzOut.txt);                                               # Program output file
our $sourceFile  = q(z.asm);                                                    # Source file

our $stdin       = 0;                                                           # File descriptor for standard input
our $stdout      = 1;                                                           # File descriptor for standard output
our $stderr      = 2;                                                           # File descriptor for standard error

our $TraceMode   = 0;                                                           # 1: writes trace data into rax after every instruction to show the call stack by line number in this file for the instruction being executed.  This information is then visible in the sde trace from whence it is easily extracted to give a trace back for instructions executed in this mode.  This mode assumes that you will not be using the mm0 register (most people are not)and that you have any IDE like Geany that can interpret a Perl error line number and position on that line in this file.
our $DebugMode   = 0;                                                           # 1: enables checks that take time and sometimes catch programming errors.
our $LibraryMode = 0;                                                           # 1: we are building a library so constants must appear in line in the text section rather than in a block in the data section

my %Registers;                                                                  # The names of all the registers
my %RegisterContaining;                                                         # The largest register containing a register
my @GeneralPurposeRegisters = qw(rax rbx rcx rdx rsi rdi), map {"r$_"} 8..15;   # General purpose registers
my $bitsInByte;                                                                 # The number of bits in a byte
my @declarations;                                                               # Register and instruction declarations
my %loadAreaIntoAssembly;                                                       # Areas already loaded by file name

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
include
incbin
END

  my @i2 =  split /\s+/, <<END;                                                 # Double operand instructions
add and bsf bsr bt btc btr bts
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
vpgatherqd vpgatherqq
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
pdep pext
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

sub byteRegister($)                                                             # The byte register corresponding to a full size register.
 {my ($r) = @_;                                                                 # Full size register
  if ($r =~ m(\Ar([abcd])x\Z)) {return $1."l"};
  return dil if $r eq rdi;
  return sil if $r eq rsi;
  $r."b"
 }

sub wordRegister($)                                                             # The word register corresponding to a full size register.
 {my ($r) = @_;                                                                 # Full size register
  if ($r =~ m(\Ar([abcd])x\Z)) {return $1."x"};
  return di if $r eq rdi;
  return si if $r eq rsi;
  $r."w"
 }

sub dWordRegister($)                                                            # The double word register corresponding to a full size register.
 {my ($r) = @_;                                                                 # Full size register
  if ($r =~ m(\Ar([abcd])x\Z)) {return "e".$1."x"};
  return edi if $r eq rdi;
  return esi if $r eq rsi;
  $r."d"
 }

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
  if ($LibraryMode)                                                             # Create data in a library - we put it inline so that is copied with the position independent subroutine after optimizing the jumps just before assembly.
   {my $l = Label; my $x = Label;                                               # New data - create a label for the data  and then jump over it as it is in the code section -- we will have to optimize jumps later
    push @text, <<END;                                                          # Save in read only data
    Jmp $x;
    $l: d$s $d
    $x:
END
    $rodata{$s}{$d} = $l;                                                       # Record label
    return $l;
   }
  else
   {my $l = Label;                                                              # New data - create a label
    push @rodata, <<END;                                                        # Save in read only data
    $l: d$s $d
END
    $rodata{$s}{$d} = $l;                                                       # Record label
    return $l;
   }
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

  if ($LibraryMode)                                                             # Create data in a library - we put it inline so that is copied with the position independent subroutine after optimizing the jumps just before assembly.
   {my $l = Label; my $x = Label;                                               # New label for new data
    $rodatas{$e} = $l;                                                          # Record label
    push @text, <<END;                                                          # Define bytes
  Jmp $x;
  $l: db  $e, 0;
  $x:
END
    return $l;                                                                  # Return label
   }
  else
   {my $l = Label;                                                              # New label for new data
    $rodatas{$e} = $l;                                                          # Record label
    push @rodata, <<END;                                                        # Define bytes
  $l: db  $e, 0;
END
    return $l                                                                   # Return label
   }
 }

sub Rutf8(@)                                                                    # Layout a utf8 encoded string as bytes in read only memory and return their label.
 {my (@d) = @_;                                                                 # Data to be laid out
  confess unless @_;
  my $d = join '', @_;
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
  my @p;                                                                        # Non zmm registers
  my @z;                                                                        # Zmm registers
  for my $r(map {&registerNameFromNumber($_)} @r)
   {if ($r =~ m(\Azmm))                                                         # Do zmm's last as they can be optimized
     {unshift @z, $r;
     }
    else                                                                        # Non zmm registers
     {push @p, $r;
      my $size = RegisterSize $r;
      $size or confess "No such register: $r";
      if    ($size > $w)                                                        # Wide registers
       {Sub rsp, $size;
        Vmovdqu64 "[rsp]", $r;
       }
      elsif ($r =~ m(\Ak))                                                      # Mask as they do not respond to push
       {Sub rsp, $size;
        Kmovq "[rsp]", $r;
       }
      else                                                                      # Normal register
       {Push $r;
       }
     }
   }
  if (@z)                                                                       # Zmm registers
   {my $w = RegisterSize(zmm0);                                                 # Register width
    Sub rsp, $w * @z;                                                           # Reduce stack to make room for zmm registers being pushed
    for my $i(keys @z)                                                          # Copy each zmm register being pushed to the stack
     {Vmovdqu64 "[rsp+$i*$w]", $z[$i];
     }
   }
  my @R = (@p, reverse @z);                                                     # Actual push sequence - for some strange reason we have to put it in a variable first
 }

my @PushR;                                                                      # Track pushes

sub PushR(@)                                                                    #P Push registers onto the stack.
 {my (@r) = @_;                                                                 # Registers
  my @p = PushRR @r;                                                            # Push
  push @PushR, [@p];                                                            # Registers pushed we can pop them in order
  scalar(@PushR)                                                                # Stack depth
 }

sub PopRR(@)                                                                    #P Pop registers from the stack without tracking.
 {my (@r) = @_;                                                                 # Register
  my $w = RegisterSize rax;
  my $W = RegisterSize zmm0;
  my $z = 0;                                                                    # Offset in stack of zmm register
  @r = reverse map{&registerNameFromNumber($_)} @r;                             # Pop registers in reverse order- any zmm registers will be first

  for my $r(@r)                                                                 # Pop registers in reverse order- any zmm registers will be first
   {if ($r =~ m(\Azmm))                                                         # The zmm registers come first and are popped by offset
     {Vmovdqu64 $r, "[rsp+$z]";
      $z += $W;
     }
   }
  Add rsp, $z if $z;                                                            # Move up over any zmm registers

  for my $r(@r)                                                                 # Pop non zmm registers in reverse order
   {my $size = RegisterSize $r;
    if    ($size == $W) {}                                                      # The zmm registers have already been popped
    elsif    ($size > $w)                                                       # Xmm, ymm
     {Vmovdqu64 $r, "[rsp]";
      Add rsp, $size;
     }
    elsif ($r =~ m(\Ak))                                                        # Mask registers
     {Kmovq $r, "[rsp]";
      Add rsp, $size;
     }
    else                                                                        # General purpose registers
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

sub registerNameFromNumber($)                                                   # Register name from number where possible.
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

  my $mask = rdi, my $low = rsi, my $high = rbx;                                # Choose three work registers and push them
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
  map {m/\Azmm/ ? $_ : "zmm$_"} @_;
 }

sub zmmM($$)                                                                    # Add zmm to the front of a register number and a mask after it.
 {my ($z, $m) = @_;                                                             # Zmm number, mask register
  "zmm$z\{k$m}"
 }

sub zmmMZ($$)                                                                   # Add zmm to the front of a register number and mask and zero after it.
 {my ($z, $m) = @_;                                                             # Zmm number, mask register number
  "zmm$z\{k$m}\{z}"
 }

sub LoadZmm($@)                                                                 # Load a numbered zmm with the specified bytes.
 {my ($zmm, @bytes) = @_;                                                       # Numbered zmm, bytes
  my $b = Rb(@bytes);
  Vmovdqu8 "zmm$zmm", "[$b]";
 }

sub checkZmmRegister($)                                                         # Check that a register is a zmm register.
 {my ($z) = @_;                                                                 # Parameters
  $z =~ m(\A(0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|16|17|18|19|20|21|22|23|24|25|26|27|28|29|30|31)\Z) or confess "$z is not the number of a zmm register";
 }

sub bRegFromZmm($$$)                                                            # Load the specified register from the byte at the specified offset located in the numbered zmm.
 {my ($register, $zmm, $offset) = @_;                                           # Register to load, numbered zmm register to load from, constant offset in bytes

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

  $offset >= 0 && $offset <= RegisterSize zmm0 or confess "Out of range";

  PushR $zmm;                                                                   # Push source register

  my $b = byteRegister $register;                                               # Corresponding byte register

  Mov "[rsp+$offset]", $b;                                                      # Save byte at specified offset
  PopR;                                                                         # Reload zmm
 }

sub wRegFromZmm($$$)                                                            # Load the specified register from the word at the specified offset located in the numbered zmm.
 {my ($register, $zmm, $offset) = @_;                                           # Register to load, numbered zmm register to load from, constant offset in bytes

  my $z = registerNameFromNumber $zmm;
  $offset >= 0 && $offset <= RegisterSize zmm0 or confess "Out of range";

  my $W = RegisterSize $z;                                                      # Register size
  Vmovdqu32 "[rsp-$W]", $z;
  my $w = wordRegister $register;                                               # Corresponding word register

  Mov $w, "[rsp-$W+$offset]";                                                   # Load word register from offset
 }

sub wRegIntoZmm($$$)                                                            # Put the specified register into the word in the numbered zmm at the specified offset in the zmm.
 {my ($register,  $zmm, $offset) = @_;                                          # Register to load, numbered zmm register to load from, constant offset in bytes

  $offset >= 0 && $offset <= RegisterSize zmm0 or confess "Out of range";

  PushR $zmm;                                                                   # Push source register

  my $w = wordRegister $register;                                               # Corresponding word register

  Mov "[rsp+$offset]", $w;                                                      # Save word at specified offset
  PopR;                                                                         # Reload zmm
 }

sub LoadRegFromMm($$$)                                                          # Load the specified register from the numbered zmm at the quad offset specified as a constant number.
 {my ($mm, $offset, $reg) = @_;                                                 # Mm register, offset in quads, general purpose register to load

  my $w = RegisterSize rax;                                                     # Size of rax
  my $W = RegisterSize $mm;                                                     # Size of mm register
  Vmovdqu64 "[rsp-$W]", $mm;                                                    # Write below the stack
  Mov $reg, "[rsp+$w*$offset-$W]";                                              # Load register from offset
 }

sub SaveRegIntoMm($$$)                                                          # Save the specified register into the numbered zmm at the quad offset specified as a constant number.
 {my ($mm, $offset, $reg) = @_;                                                 # Mm register, offset in quads, general purpose register to load

  my $w = RegisterSize rax;                                                     # Size of rax
  my $W = RegisterSize $mm;                                                     # Size of mm register
  Vmovdqu64 "[rsp-$W]", $mm;                                                    # Write below the stack
  Mov "[rsp+$w*$offset-$W]", $reg;                                              # Save register into offset
  Vmovdqu64 $mm, "[rsp-$W]";                                                    # Reload from the stack
 }

sub extractRegisterNumberFromMM($)                                              # Extract the register number from an *mm register.
 {my ($mm) = @_;                                                                # Mmm register
      $mm =~ m(\A([zyx]mm)?(\d{1,2})\Z) ? $2 : confess "Not an mm register";
 }

sub getBwdqFromMm($$$$%)                                                        # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable.
 {my ($xyz, $size, $mm, $offset, %options) = @_;                                # Size of mm, size of get, mm register, offset in bytes either as a constant or as a variable, options
  my $set = $options{set};                                                      # Optionally set this register or variable rather than returning a new variable
  my $setVar = $set && ref($set) =~ m(Variable);                                # Set a this variable to the result

  my $n = extractRegisterNumberFromMM $mm;                                      # Register number or fail if not an mm register
  my $m = $xyz.'mm'.$n;                                                         # Full name of register

  if (!ref($offset) and $offset == 0 and $set and !$setVar)                     # Use Pextr in this special circumstance - need to include other such
   {my $d = dWordRegister $set;                                                 # Target a dword register as set is not a variable
    push @text, <<END;
vpextr$size $d, xmm$n, 0
END
    return;
   }

  my $r = $setVar ? rdi : ($set // rdi);                                        # Choose a work register

  my $o;                                                                        # The offset into the mm register
  if (ref($offset))                                                             # The offset is being passed in a variable
   {$offset->setReg($o = rsi);
    confess "Cannot use rsi"  if $r eq rsi;                                     # Rsi is the offset to apply if a variable offset is supplied so we cannot use rsi in these circumstances as the target register
   }
  else                                                                          # The offset is being passed as a register expression
   {$o = $offset;
   }

  my $w = RegisterSize $m;                                                      # Size of mm register
  Vmovdqu32 "[rsp-$w]", $m;                                                     # Write below the stack

  ClearRegisters $r if $size !~ m(q|d);                                         # Clear the register if necessary
  Mov  byteRegister($r), "[rsp+$o-$w]" if $size =~ m(b);                        # Load byte register from offset
  Mov  wordRegister($r), "[rsp+$o-$w]" if $size =~ m(w);                        # Load word register from offset
  Mov dWordRegister($r), "[rsp+$o-$w]" if $size =~ m(d);                        # Load double word register from offset
  Mov $r,                "[rsp+$o-$w]" if $size =~ m(q);                        # Load register from offset

  if ($setVar)                                                                  # Set the supplied variable
   {$set->copy($r);
    return;
   }

  V("$size at offset $offset in $m", $r) unless $set;                           # Create variable unless a target register has been supplied
 }

sub bFromX($$)                                                                  # Get the byte from the numbered xmm register and return it in a variable.
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMm('x', 'b', "xmm$xmm", $offset)                                   # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub wFromX($$)                                                                  # Get the word from the numbered xmm register and return it in a variable.
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMm('x', 'w', "xmm$xmm", $offset)                                   # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub dFromX($$)                                                                  # Get the double word from the numbered xmm register and return it in a variable.
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMm('x', 'd', "xmm$xmm", $offset)                                   # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub qFromX($$)                                                                  # Get the quad word from the numbered xmm register and return it in a variable.
 {my ($xmm, $offset) = @_;                                                      # Numbered xmm, offset in bytes
  getBwdqFromMm('x', 'q', "xmm$xmm", $offset)                                   # Get the numbered byte|word|double word|quad word from the numbered xmm register and return it in a variable
 }

sub bFromZ($$%)                                                                 # Get the byte from the numbered zmm register and return it in a variable.
 {my ($zmm, $offset, %options) = @_;                                            # Numbered zmm, offset in bytes, options
  my $z = registerNameFromNumber $zmm;
  getBwdqFromMm('z', 'b', $z, $offset, %options)                                # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub wFromZ($$%)                                                                 # Get the word from the numbered zmm register and return it in a variable.
 {my ($zmm, $offset, %options) = @_;                                            # Numbered zmm, offset in bytes,options
  my $z = registerNameFromNumber $zmm;
  getBwdqFromMm('z', 'w', $z, $offset, %options)                                # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub dFromZ($$%)                                                                 # Get the double word from the numbered zmm register and return it in a variable.
 {my ($zmm, $offset, %options) = @_;                                            # Numbered zmm, offset in bytes, options
  my $z = extractRegisterNumberFromMM $zmm;
  getBwdqFromMm('z', 'd', $z, $offset, %options)                                # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

sub qFromZ($$%)                                                                 # Get the quad word from the numbered zmm register and return it in a variable.
 {my ($zmm, $offset, %options) = @_;                                            # Numbered zmm, offset in bytes
  my $z = registerNameFromNumber $zmm;
  getBwdqFromMm('z', 'q', $z, $offset, %options)                                # Get the numbered byte|word|double word|quad word from the numbered zmm register and return it in a variable
 }

#D2 Mask                                                                        # Operations on mask registers

sub CheckMaskRegister($)                                                        # Check that a register is in fact a numbered mask register.
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
  my $m = registerNameFromNumber $mask;
  Mov rdi, $value;                                                              # Load mask into a general purpose register
  Kmovq $m, rdi;                                                                # Load mask register from general purpose register
 }

sub createBitNumberFromAlternatingPattern($@)                                   # Create a number from a bit pattern.
 {my ($prefix, @values) = @_;                                                   # Prefix bits, +n 1 bits -n 0 bits
  @_ > 1 or confess "Four or more parameters required";                         # Must have some values

  $prefix =~ m(\A[01]*\Z) or confess "Prefix must be binary";                   # Prefix must be binary
  @values = grep {$_ != 0} @values;                                             # Remove zeroes as they would produce no string

  for my $i(0..$#values-1)                                                      # Check each value alternates with the following values
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

sub Subroutine(&%);
sub Comment(@);
sub K($$);
sub V($$);
sub CreateArea(%);
sub PrintErrStringNL(@);

#D1 Structured Programming                                                      # Structured programming constructs

#D2 If                                                                          # If statements

sub If($$;$)                                                                    # If statement.
 {my ($jump, $then, $else) = @_;                                                # Jump op code of variable, then - required , else - optional
  @_ >= 2 && @_ <= 3 or confess;

  ref($jump) or $jump =~ m(\AJ(c|e|g|ge|h|l|le|nc|ne|ns|nz|s|z)\Z)
             or confess "Invalid jump: $jump";

  if (ref($jump))                                                               # Variable expression,  if it is non zero perform the then block else the else block
   {if (ref($jump) =~ m(scalar)i)                                               # Type of jump opposes the boolean operator
     { __SUB__->($$jump, $then, $else);
     }
    else                                                                        # Anything other than a scalar reference indicates that the 'If' statement was handed something other than a Boolean expression
     {confess "Not a boolean expression";
     }
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

#sub OR(@)                                                                      # Return a variable containing 1 if any of the conditions is true else 0 by evaluating the conditions in order and stopping as soon as the result is known.
# {my (@c) = @_;                                                                # Conditions enclosed in subs
#  my $r = &V(or => 0);
#  &Block(sub
#   {my ($end, $start) = @_;
#    for my $c(@c)
#     {If &$c, Then {$r->copy(1); Jmp $end}
#     }
#   });
#  $r
# }
#
#sub AND(@)                                                                     # Return a variable containing 1 if all of the conditions are true else 0 by evaluating the conditions in order and stopping as soon as the result is known.
# {my (@c) = @_;                                                                # Conditions enclosed in subs
#  my $r = &V(and => 1);
#  &Block(sub
#   {my ($end, $start) = @_;
#    for my $c(@c)
#     {If &$c, Then {}, Else {$r->copy(0); Jmp $end}
#     }
#   });
#  $r
# }

sub opposingJump($)                                                             # Return the opposite of a jump.
 {my ($j) = @_;                                                                 # Jump
  my %j = qw(Je Jne  Jl Jge  Jle Jg  Jne Je  Jge Jl  Jg Jl);                    # Branch possibilities
  my $o = $j{$j};
  confess "Invalid jump $j" unless $o;
  $o
 }

sub ifOr($$;$)                                                                  # Execute then or else block based on a multiplicity of OR conditions executed until one succeeds.
 {my ($conditions, $Then, $Else) = @_;                                          # Array of conditions, then sub, else sub

  my $test = Label;                                                             # Start of test block
  my $then = Label;                                                             # Start of then block
  my $else = Label;                                                             # Start of else block
  my $end  = Label;                                                             # End of block

  Jmp $test;                                                                    # Jump over then and else
  SetLabel $then;                                                               # Then block
  &$Then;
  Jmp $end;
  SetLabel $else;
  &$Else if $Else;
  Jmp $end;

  SetLabel $test;                                                               # Start of tests

  for my $c(@$conditions)
   {my $j = opposingJump ${&$c};
    push @text, qq($j $then\n);
   }
  Jmp $else if $Else;
  SetLabel $end;
 }

sub ifAnd($$;$)                                                                 # Execute then or else block based on a multiplicity of AND conditions executed until one fails.
 {my ($conditions, $Then, $Else) = @_;                                          # Array of conditions, then sub, else sub

  my $test = Label;                                                             # Start of test block
  my $then = Label;                                                             # Start of then block
  my $else = Label;                                                             # Start of else block
  my $end  = Label;                                                             # End of block

  Jmp $test;                                                                    # Jump over then and else
  SetLabel $then;                                                               # Then block
  &$Then;
  Jmp $end;
  SetLabel $else;
  &$Else if $Else;
  Jmp $end;

  SetLabel $test;                                                               # Start of tests

  for my $c(@$conditions)
   {my $j = ${&$c};
    push @text, qq($j $else\n) if     $Else;
    push @text, qq($j $end\n)  unless $Else;
   }
  Jmp $then;
  SetLabel $end;
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

#D2 Boolean Blocks                                                              # Perform blocks depending on boolean conditions

sub Pass(&)                                                                     # Pass block for an L<OrBlock>.
 {my ($block) = @_;                                                             # Block
  $block;
 }

sub Fail(&)                                                                     # Fail block for an L<AndBlock>.
 {my ($block) = @_;                                                             # Block
  $block;
 }

sub Block(&)                                                                    # Execute a block of code with labels supplied for the start and end of this code.
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

#D2 Iteration                                                                   # Iterate with for loops

sub For(&$$;$)                                                                  # For - iterate the block as long as register is less than limit incrementing by increment each time. Nota Bene: The register is not explicitly set to zero as you might want to start at some other number.
 {my ($block, $register, $limit, $increment) = @_;                              # Block, register, limit on loop, increment on each iteration
  @_ == 3 or @_ == 4 or confess;
  $increment //= 1;                                                             # Default increment
  my $next = Label;                                                             # Next iteration
  Comment "For $register $limit";
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

sub uptoNTimes(&$$)                                                             # Execute a block of code up to a constant number of times controlled by the named register.
 {my ($code, $register, $limit) = @_;                                           # Block of code, register controlling loop, constant limit
  confess "Limit must be a positive inter constant"                             # Check for a specific limit
    unless $limit =~ m(\A\d+\Z) and $limit > 0;

  Mov $register, $limit;                                                        # Set the limit
  SetLabel(my $start = Label);                                                  # Start of block
  my $end  = Label;                                                             # End of block
  &$code($end, $start);                                                         # Code with labels supplied
  Sub $register, 1;                                                             # Set flags
  Jnz $start;                                                                   # Continue if count still greater than zero
  SetLabel $end;                                                                # End of block
 }

sub ForEver(&)                                                                  # Iterate for ever.
 {my ($block) = @_;                                                             # Block to iterate

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
    my $maxCount  = r8;                                                         # Maximum number of parameters - should be r11 but r11 is free in linux and does not survive syscalls.
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
  PrintErrStringNL $message;
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

sub copyStructureMinusVariables($)                                              # Copy a non recursive structure ignoring variables.
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
  my $export     = $options{export};                                            # File to export this subroutine to and all its contained subroutines
  my $name       = $options{name};                                              # Subroutine name
  my $parameters = $options{parameters};                                        # Parameters block
  my $structures = $options{structures};                                        # Structures provided as parameters
  my $trace      = $options{trace};                                             # If we are tracing and this subroutine is marked as traceable we always generate a new version of it so that we can trace each specific instance to get the exact context in which this subroutine was called rather than the context in which the original copy was called.

  if (1)                                                                        # Validate options
   {my %o = %options;
    delete $o{$_} for qw(export name parameters structures trace);
    if (my @i = sort keys %o)
     {confess "Invalid parameters: ".join(', ',@i);
     }
   }

  my %subroutinesSaved;                                                         # Current set of subroutine definitions
  my %rodataSaved;                                                              # Current set of read only elements
  my %rodatasSaved;                                                             # Current set of read only strings
  if ($export)                                                                  # Create a new set of subroutines for this routine and all of its sub routines
   {%subroutinesSaved = %subroutines;                                           # Save current set of subroutines
    %subroutines      = ();                                                     # New set of subroutines
    %rodataSaved      = %rodata;                                                # Current set of read only elements
    %rodata           = ();                                                     # New set of read only elements
    %rodatasSaved     = %rodatas;                                               # Current set of read only strings
    %rodatas          = ();                                                     # New set of read only strings
    $LibraryMode      = 1;                                                      # Please do not try to create a library while creating another library - create them one after the other.
   }

  $name or confess "Name required for subroutine, use name=>";
  if ($name and my $s = $subroutines{$name})                                    # Return the label of a pre-existing copy of the code possibly after running the subroutine. Make sure that the subroutine name is different for different subs as otherwise the unexpected results occur.
   {return $s unless $TraceMode and $trace and !$export;                        # If we are tracing and this subroutine is marked as traceable we always generate a new version of it so that we can trace each specific instance to get the exact context in which this subroutine was called rather than the context in which the original copy was called.
   }

  if (1)                                                                        # Check for duplicate parameters
   {my %c;
    $c{$_}++ && confess "Duplicate parameter $_" for @$parameters;
   }

  SubroutineStartStack;                                                         # Open new stack layout with references to parameters
  my %parameters = map {$_ => R($_)} @$parameters;                              # Create a reference for each parameter.

  my %structureCopies;                                                          # Copies of the structures being passed that can be use inside the subroutine to access their variables in the stack frame of the subroutine
  if ($structures)                                                              # Structure provided in the parameter list
   {for my $name(sort keys %$structures)                                        # Each structure passed
     {$structureCopies{$name} = copyStructureMinusVariables($$structures{$name})# A new copy of the structure with its variables left in place
     }
   }

  my $end   =    Label; Jmp $end;                                               # End label.  Subroutines are only ever called - they are not executed in-line so we jump over the implementation of the subroutine.  This can cause several forward jumps in a row if a number of subroutines are defined together.
  my $start = SetLabel;                                                         # Start label

  my $s = $subroutines{$name} = genHash(__PACKAGE__."::Subroutine",             # Subroutine definition
    block              => $block,                                               # Block used to generate this subroutine
    end                => $end,                                                 # End label for this subroutine
    export             => $export,                                              # File this subroutine was exported to if any
    name               => $name,                                                # Name of the subroutine from which the entry label is located
    nameString         => Rutf8($name),                                         # Name of the sub as a string constant in read only storage
    offset             => undef,                                                # The offset of this routine in its library if it is in a library
    options            => \%options,                                            # Options used by the author of the subroutine
    parameters         => $parameters,                                          # Parameters definitions supplied by the author of the subroutine which get mapped in to parameter variables.
    start              => $start,                                               # Start label for this subroutine which includes the enter instruction used to create a new stack frame
    structureCopies    => \%structureCopies,                                    # Copies of the structures passed to this subroutine with their variables replaced with references
    structureVariables => {},                                                   # Map structure variables to references at known positions in the sub
    variables          => {%parameters},                                        # Map parameters to references at known positions in the sub
    vars               => $VariableStack[-1],                                   # Number of variables in subroutine
   );

  $s->mapStructureVariables(\%structureCopies) if $structures;                  # Map structures before we generate code so that we can put the parameters first in the new stack frame
  my $E = @text;                                                                # Code entry that will contain the Enter instruction

  Enter 0, 0;                                                                   # The Enter instruction is 4 bytes long
  &$block({%parameters}, {%structureCopies}, $s);                               # Code with parameters and structures

  my $V = pop @VariableStack;                                                   # Number of variables in subroutine stack frame. As parameters and structures are mapped into variables in the subroutine stack frame these variables will be included in the count as well.
     $V += RegisterSize(zmm0) / RegisterSize rax;                               # Ensures that we can save the parameter list using a full zmm register without the necessity o loading a mask register
  Leave if $V;                                                                  # Remove frame if there was one
  Ret;                                                                          # Return from the sub
  SetLabel $end;                                                                # The end point of the sub where we return to normal code
  my $w = RegisterSize rax;
  $text[$E] = $V ? <<END : '';                                                  # Rewrite enter instruction now that we know how much stack space, in bytes, that we need
  Enter $V*$w, 0
END

  if ($export)                                                                  # Create a new set of subroutines for this routine and all of its sub routines
   {$s->writeToArea({%subroutines});                                            # Place the subroutine in an area then write the area containing the subroutine and its contained routines to a file
    %subroutines = %subroutinesSaved;                                           # Save current set of subroutines
    %rodata      = %rodataSaved;                                                # Restore current set of read only elements
    %rodatas     = %rodatasSaved;                                               # Restore current set of read only strings
    $subroutines{$name} = $s;                                                   # Save current subroutine so we do not regenerate it
    $LibraryMode = 0;                                                           # Please do not try to create a library while creating another library - create them one after the other.
   }

  $s                                                                            # Return subroutine definition
 }

sub Nasm::X86::Subroutine::writeToArea($$)                                      #P Write a subroutine and its sub routines to an area then save the area in a file so that the subroutine can be reloaded at a later date either as separate file or via incorporation into a thing.  A thing was originally an assembly of people as in "The Allthing" or the "Stort Thing".
 {my ($s, $subs) = @_;                                                          # Sub definition of containing subroutine, definitions of contained subroutines
  my $a = CreateArea;
  my $address = K address => $s->start;
  my $size    = K size => "$$s{end}-$$s{start}";
  my $off     = $a->appendMemory($address, $size);                              # Copy a subroutine into an area

  my $y = $a->yggdrasil;
  my ($N, $L) = constantString($s->name);                                       # The name of the subroutine
  my $n = $y->putKeyString(&Nasm::X86::Yggdrasil::UniqueStrings,     $N, $L);   # Make the name of the subroutine into a unique number
  my $o = $a->appendMemory($address, $size);                                    # Copy a subroutine into an area
  $y->put2(                &Nasm::X86::Yggdrasil::SubroutineOffsets, $n, $off); # Record the offset of the subroutine under the unique string number

  my $U = $y->findSubTree(&Nasm::X86::Yggdrasil::UniqueStrings);                # Find the unique string sub tree created above
  my $O = $y->findSubTree(&Nasm::X86::Yggdrasil::SubroutineOffsets);            # Find the unique subroutine offset tree created above

  my %saved;                                                                    # An array of sub routine definitions preceded by this helpful string.  It is entirely possible that this string is not unique in this area - in that case one would have to parse Yggdrasil in Perl - but for the  moment this would be overkill.
  for my $sub(sort keys %$subs)                                                 # Each sub routine definition contained in this subroutine
   {my $r = $$subs{$sub};                                                       # A routine within the subroutine
    my ($N, $L) = constantString($r->name);                                     # The name of the sub
    my $n = $U->putStringFromMemory($N, $L);                                    # Make the name of the sub routine into a unique number
    my $o = $off + K delta => "$$r{start}-$$s{start}";                          # Offset to this sub routine within the subroutine
    $O->put($n, $o);                                                            # Record the offset of the subroutine under the unique string number

    $saved{$r->name} = $$subs{$sub};                                            # Saved this subroutine definition as the sub is included in the area
   }

  if (1)                                                                        # Save the definitions of the subs in this area
   {my $s = "SubroutineDefinitions:".dump(\%saved)."ZZZZ";                      # String to save
    my $d = $a->appendMemory(constantString($s));                               # Offset of string containing subroutine definition
    $y->put(&Nasm::X86::Yggdrasil::SubroutineDefinitions, $d);                  # Record the offset of the subroutine definition under the unique string number for this subroutine
   }

   $a->write(V file => Rs $s->export);                                          # Save the area to the named file
   $a->free;
 }

sub Nasm::X86::Subroutine::mapStructureVariables($$@)                           # Find the paths to variables in the copies of the structures passed as parameters and replace those variables with references so that in the subroutine we can refer to these variables regardless of where they are actually defined.
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

sub Nasm::X86::Subroutine::uploadStructureVariablesToNewStackFrame($$$@)        # Create references to variables in parameter structures from variables in the stack frame of the subroutine.
 {my ($sub, $sv, $S, @P) = @_;                                                  # Sub definition, Structure variables, Source tree of input structures, path through source structures tree

  for my $s(sort keys %$S)                                                      # Source keys
   {my $e = $$S{$s};
    my $r = ref $e;
    next unless $r;                                                             # Element in structure is not a variable or another hash describing a sub structure
    if ($r =~ m(Variable)i)                                                     # Variable located
     {push @P, $s;                                                              # Extend path
      my $p = dump([@P]);                                                       # Path as string
      my $R = $sub->structureVariables->{$p};                                   # Reference
      if (defined($R))
       {$sub->uploadToNewStackFrame($sv, $e, $R);                               # Reference to structure variable from subroutine stack frame
       }
      else                                                                      # Unable to locate the corresponding reference
       {confess "No entry for $p in structure variables";
       }
      pop @P;
     }
    else                                                                        # A hash that is not a variable and is therefore assumed to be a non recursive substructure
     {push @P, $s;
      $sub->uploadStructureVariablesToNewStackFrame($sv, $e, @P);
      pop @P;
     }
   }
 }

sub Nasm::X86::Subroutine::uploadToNewStackFrame($$$$)                          #P Map a variable in the current stack into a reference in the next stack frame being the one that will be used by this sub.
 {my ($sub, $sv, $source, $target) = @_;                                        # Subroutine descriptor, structure variables, source variable in the current stack frame, the reference in the new stack frame
  @_ == 4 or confess "Four parameters";

  my $label = $source->label;                                                   # Source in current frame

  if ($source->reference)                                                       # Source is a reference
   {Mov r15, "[$label]";
    push @$sv, [$source, $target, 1];                                           # Source to target mapping and target is a reference
   }
  else                                                                          # Source is not a reference
   {Lea r15, "[$label]";
    push @$sv, [$source, $target, 0];                                           # Source to target mapping and target is not a reference
   }

  my $q = $target->label;
     $q =~ s(rbp) (rsp);                                                        # Labels are based off the stack frame but we are building a new stack frame here so we must rename the stack pointer.
  my $w = RegisterSize r15;
  Mov "[$q-$w*2]", r15;                                                         # Step over subroutine name pointer and previous frame pointer.
 }

sub Nasm::X86::Subroutine::validateParameters($%)                               #P Check that the parameters and structures presented in a call to a subroutine math those defined for the subroutine.
 {my ($sub, %options) = @_;                                                     # Subroutine descriptor, options

  my %o = %options;                                                             # Validate options
  delete $o{$_} for qw(parameters structures override library);                 # Parameters are variables, structures are Perl data structures with variables embedded in them,  override is a variable that contains the actual address of the subroutine

  if (my @i = sort keys %o)
   {confess "Invalid parameters: ".join(', ',@i);
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
  elsif ($sub->parameters->@*)                                                  # Complain about a lack of parameters if parameters have been defined for this subroutine
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
  elsif ($sub->options and                                                      # Complain about a lack of structures if structures have been defined for this subroutine
         $sub->options->{structures} and $sub->options->{structures}->%*)
   {confess "Structures required";
   }

  ($parameters, $structures)
 }

sub Nasm::X86::Subroutine::call($%)                                             # Call a sub optionally passing it parameters.
 {my ($sub, %options) = @_;                                                     # Subroutine descriptor, options

  my ($parameters, $structures) = $sub->validateParameters(%options);           # Validate the supplied parameters and structures against the specification defining this subroutine

  my $new = sub                                                                 # Regenerate the subroutine if we are tracing in general and this subroutine is specifically traceable.  We do not trace all subroutines because the generated asm code would be big.
   {if ($sub->options->{trace} and $TraceMode)                                  # Call the latest version of this subroutine not the original version in case the latest version fails so we can see the exact call stack of the latest version than the call stack of the original version in the context in which it was originally called.
     {return Subroutine(sub{$$sub{block}->&*}, $sub->options->%*);
     }
    undef
   }->();

  my $w = RegisterSize r15;                                                     # Size of a parameter
  PushR 15;                                                                     # Use this register to transfer between the current frame and the next frame
  Mov "dword[rsp  -$w*3]", Rs($sub->name);                                      # Point to subroutine name
  Mov "byte [rsp-1-$w*2]", $sub->vars;                                          # Number of parameters to enable trace back with parameters

  for my $name(sort keys $parameters->%*)                                       # Upload the variables referenced by the parameters to the new stack frame
   {my $s = $$parameters{$name};
    my $t = $sub->variables->{$name};
    $sub->uploadToNewStackFrame(my $structureVariables = [], $s, $t);
   }

  my $name = $$sub{name};                                                       # The name of the sub

  if ($structures)                                                              # Upload the variables of each referenced structure to the new stack frame
   {push @text, <<END;                                                          # A comment we can reverse up to if we decide to use a zmm to transfer the parameters
;AAAAAAAA $name
END
    $sub->uploadStructureVariablesToNewStackFrame
     (my $structureVariables = [], $structures);
                                                                                # Use zmm registers, if possible, to reduce the number of instructions required to zap the parameter list
    my %st; my $nr = 0; my $nd = 0;                                             # Target to source mapping for parameters. Number of references, number of direct parameters.
    for my $v(@$structureVariables)                                             # Each source to target pair
     {my $s = $$v[0]->position;                                                 # Source position in old stack frame
      my $r = $$v[0]->reference ? 1 : 0;                                        # Reference parameter or direct parameter
      my $t = $$v[1]->position;                                                 # Target position in the new stack frame
      my $k = sprintf "%08d", $t;                                               # Normalize the target position so it can be sorted
      $st{$k} = $s;                                                             # Target from source mapping
      $r ? ++$nr : ++$nd;                                                       # Number of references versus number of direct parameters
     }

    my @st = map{[$_+0, $st{$_}]} sort keys %st;                                # Parameters in stack frame order

    if (1 and (!$nr && $nd or $nr && !$nd) and                                  # The mapping is compact so we can do the whole thing without masking - and - the mapping is big enough to use zmm registers.  Further we are either doing everything by reference or everything directly - we do not have a mixture of references and directs require more instructions to handle - the goal here is, after all, to reduce the number of instructions required to construct a parameter list.
        @st >= 4 and 1 + $st[-1][0] - $st[0][0] == @st)
     {pop @text while @text and $text[-1] !~ m(\;AAAAAAAA);                     # Back up to the start of the structure parameters
      my $w = RegisterSize rax;                                                 # Size of one parameter
      my $W = RegisterSize zmm0;                                                # Space in parameter block
      my $b = $W / $w;                                                          # Number of parameters per block
      my @o;                                                                    # The offsets to load into one zmm register at a time to zap the parameter list.

      Vpbroadcastq zmm0, rbp if $nd;                                            # Direct    parameters: Load the value of the stack base pointer into every cell to compute the address of each source parameter

      my $stackOffsetForParameterBlock = 1 + $st[0][0];                         # We start to load the parameters into the new stack (first) at this location
      for my $i(keys @st)                                                       # Each source to target mapping
       {push @o, $st[$i][1];                                                    # Offset of source
        if (@o == $b or $i == $#st)                                             # Dump the latest block of parameters
         {push @o, 0 while @o < $b;                                             # Pad to a full block
          my $o = Rq map {$w * -$_} reverse @o;                                 # Offsets for this zap block
          if ($nd)                                                              # All direct parameters
           {Vpaddq zmm1, zmm0, "[$o]";                                          # Add the offsets of the base of the stack frame to get the address of each parameter
           }
          else                                                                  # All direct parameters
           {Vmovdqu8 zmm0, qq([$o]);                                            # Load offsets from zap table
            Kxnorq k1, k1, k1;                                                  # Reference parameters: Set mask to all ones - we can safely load offsets of zero as they will simply load the value of rbp. Mask register set to zero at all bits where it loaded successfully.
            Vpgatherqq zmmM(1, 1), "[rbp+zmm0]";                                # Load the contents of memory at these offsets from rbp
           }
          my $p = $w * $stackOffsetForParameterBlock + $W;                      # Offset at which we start the layout of the latest parameter block
          Vmovdqu8 qq([rsp-$p]), zmm1;                                          # Layout the parameter zap table
          $stackOffsetForParameterBlock += $b;                                  # Next block of parameters
          @o = ();                                                              # Clear parameter block to accept new parameters
         }
       }
     }
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
   {#$o->setReg(rdi);
    #Call rdi;
    Call $o->addressExpr;
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

sub Nasm::X86::Subroutine::inline($%)                                           # Call a sub by in-lining it, optionally passing it parameters.
 {my ($sub, %options) = @_;                                                     # Subroutine descriptor, options

  my ($parameters, $structures) = $sub->validateParameters(%options);           # Validate the supplied parameters and structures against the specification defining this subroutine

  $sub->block->($parameters, $structures, $sub);                                # Generate code using the supplied parameters and structures
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

#D1 Print                                                                       # Print the values of registers.  The print commands do not overwrite the free registes as doing so would make debugging difficult.

#D2 Strings                                                                     # Print constant and variable strings

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
  my @c = caller 0;
  my (undef, $file, $line) = @c;
  PrintErrString " called at $file line $line";
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

#D2 Registers                                                                   # Print selected registers in a variety of formats.

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
    if ($channel == $stderr)                                                    # Print location in the source file in a format that Geany understands
     {my @c = caller 1;
      my (undef, $file, $line) = @c;
      PrintString $channel, " called at $file line $line";
     }
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

#D2 Zero Flag                                                                   # Print zero flag

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

#D2 Hexadecimal                                                                 # Print numbers in hexadecimal right justified in a field

sub PrintRightInHex($$$)                                                        # Print out a number in hex right justified in a field of specified width on the specified channel.
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

#D2 Binary                                                                      # Print numbers in binary right justified in a field

sub PrintRightInBin($$$)                                                        # Print out a number in hex right justified in a field of specified width on the specified channel.
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

#D2 Decimal                                                                     # Print numbers in decimal right justified in fields of specified width.

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
    Mov r10, 10;                                                                # Base of number system used to divide rax
    my $convert = SetLabel;
      Mov rdx, 0;                                                               # Rdx must be clear to receive remainder
      Idiv r10;                                                                 # Remainder after integer division of rax by 10
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
 {my ($width) = @_;                                                             # Width                  ::copy
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

#D2 Text                                                                        # Print the contents of a register as text.

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

  my $label;                                                                    # Label associated with this variable
  my $position;                                                                 # Position in stack frame or undef for a constant
  if ($const)                                                                   # Constant variable
   {defined($expr) or confess "Value required for constant";
    $expr =~ m(r) and confess
     "Cannot use register expression $expr to initialize a constant";
    RComment qq(Constant name: "$name", value $expr);
    $label = Rq($expr);
   }
  else                                                                          # Local variable: Position on stack of variable
   {my $stack = $position = ++$VariableStack[-1];                               # Position in stack frame
    $label = "rbp-8*($stack)";

    if (defined $expr)                                                          # Initialize variable if an initializer was supplied
     {if ($Registers{$expr} and $expr =~ m(\Ar))                                # Expression is ready to go
       {Mov "[$label]", $expr;
       }
      elsif ($expr =~ m(\A\d+\Z))                                               # Transfer constant expression
       {Mov "qword[$label]", $expr;
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
    position  => $position,                                                     # Position in stack frame
    reference => $options{reference},                                           # Reference to another variable
#    width     => RegisterSize(rax),                                            # Size of the variable in bytes
   );
 }

sub Nasm::X86::Variable::at($)                                                  # Return a "[register expression]" to address the data in the variable in the current stack frame.
 {my ($variable) = @_;                                                          # Variable descriptor
  "[".$variable->label."]"
 }

#sub G(*;$%)                                                                    # Define a global variable. Global variables with the same name are not necessarily the same variable.  Two global variables are identical iff they have have the same label field.
# {my ($name, $expr, %options) = @_;                                            # Name of variable, initializing expression, options
#  &Variable($name, $expr, global => 1, %options);
# }

sub K($$)                                                                       # Define a constant variable.
 {my ($name, $expr) = @_;                                                       # Name of variable, initializing expression
  &Variable(@_, constant => 1)
 }

sub R($)                                                                        # Define a reference variable.
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

  if ($newLine == 2)                                                            # Print location in the source file in a format that Geany understands
   {my @c = caller 1;
    my (undef, $file, $line) = @c;
    PrintString $channel, " called at $file line $line";
   }

  PrintNL($channel) if $newLine;
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

sub Nasm::X86::Variable::d($;$$)                                                # Dump the value of a variable on stderr and append the source file calling line in a format that Geany understands.
 {my ($left, $title1, $title2) = @_;                                            # Left variable, optional leading title, optional trailing title
  $left->dump($stderr, 2, $title1, $title2);
 }

sub Nasm::X86::Variable::outNL($;$$)                                            # Dump the value of a variable on stdout and append a new line.
 {my ($left, $title1, $title2) = @_;                                            # Left variable, optional leading title, optional trailing title
  $left->dump($stdout, 1, $title1, $title2);
 }

sub Nasm::X86::Variable::debug22($)                                             # Dump the value of a variable on stderr with an indication of where the dump came from.
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

sub Nasm::X86::Variable::errRightInHex($$)                                      # Write the specified variable number in hexadecimal right justified in a field of specified width to stderr.
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInHex($stderr, $number, $width);
 }

sub Nasm::X86::Variable::errRightInHexNL($$)                                    # Write the specified variable number in hexadecimal right justified in a field of specified width to stderr followed by a new line.
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInHex($stderr, $number, $width);
  PrintErrNL;
 }

sub Nasm::X86::Variable::outRightInHex($$)                                      # Write the specified variable number in hexadecimal right justified in a field of specified width to stdout.
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInHex($stdout, $number, $width);
 }

sub Nasm::X86::Variable::outRightInHexNL($$)                                    # Write the specified variable number in hexadecimal right justified in a field of specified width to stdout followed by a new line.
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

sub Nasm::X86::Variable::errRightInBin($$)                                      # Write the specified variable number in binary right justified in a field of specified width to stderr.
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInBin($stderr, $number, $width);
 }

sub Nasm::X86::Variable::errRightInBinNL($$)                                    # Write the specified variable number in binary right justified in a field of specified width to stderr followed by a new line.
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInBin($stderr, $number, $width);
  PrintErrNL;
 }

sub Nasm::X86::Variable::outRightInBin($$)                                      # Write the specified variable number in binary right justified in a field of specified width to stdout.
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInBin($stdout, $number, $width);
 }

sub Nasm::X86::Variable::outRightInBinNL($$)                                    # Write the specified variable number in binary right justified in a field of specified width to stdout followed by a new line.
 {my ($number, $width) = @_;                                                    # Number to print as a variable, width of output field
  @_ == 2 or confess "Two parameters";
  PrintRightInBin($stdout, $number, $width);
  PrintOutNL;
 }

#D3 Spaces                                                                      # Print out a variable number of spaces.

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

sub Nasm::X86::Variable::address($)                                             # Create a variable that contains the address of another variable.
 {my ($source) = @_;                                                            # Source variable
  @_ == 1 or confess "One parameter";
  Lea rdi, $source->addressExpr;                                                # Address of variable
  V("addr ".$source->name => rdi)                                               # Return variable containing address of source
 }

sub Nasm::X86::Variable::dereference($)                                         # Create a variable that contains the contents of the variable addressed by the specified variable.
 {my ($address) = @_;                                                           # Source variable
  @_ == 1 or confess "One parameter";
  $address->setReg(rdi);                                                        # Address of referenced variable
  Mov rdi, "[rdi]";                                                             # Content of referenced variable
  V "deref ".$address->name => rdi                                              # Return variable containing content of addressed variable
 }

sub Nasm::X86::Variable::update($$)                                             # Update the content of the addressed variable with the content of the specified variable.
 {my ($address, $content) = @_;                                                 # Source variable, content
  @_ == 2 or confess "Two parameters";
  PushR 14, 15;
  $address->setReg(14);                                                         # Address of referenced variable
  $content->setReg(15);                                                         # Content
  Mov "[r14]", r15;                                                             # Move content to addressed variable;
  PopR;
 }

sub constantString($)                                                           # Return the address and length of a constant string as two variables.
 {my ($string) = @_;                                                            # Constant utf8 string
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

sub Nasm::X86::Variable::addressExpr($;$)                                       # Create a register expression to address an offset form a variable.
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

  if (ref $right)                                                               # Right hand side is a variable expression
   {my $l = $left ->addressExpr;
    my $r = $right->addressExpr;                                                # Variable address

    Mov rdi, $r;                                                                # Load right hand side

    if (ref($right) and $right->reference)                                      # Dereference a reference
     {Mov rdi, "[rdi]";
     }

    if ($left ->reference)                                                      # Copy a reference
     {Mov rsi, $l;
      Mov "[rsi]", rdi;
     }
    else                                                                        # Copy a non reference
     {Mov $l, rdi;
     }
   }
  else                                                                          # Right hand size is a register expression
   {my $l = $left->addressExpr;
    if ($left->reference)                                                       # Copy a constant to a reference
     {my $r = $right =~ m(rsi) ? rdi : rsi;                                     # Choose a transfer register
      Mov $r, $l;                                                               # Load reference
      Mov "qword [$r]", $right;                                                 # Copy to referenced variable
     }
    else                                                                        # Copy a constant to a non reference
     {Mov "qword $l", $right;
     }
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
  $left->constant and confess "Cannot assign to a constant";

  Comment "Variable assign";
  Mov rdi, $left ->addressExpr;
  if ($left->reference)                                                         # Dereference left if necessary
   {Mov rdi, "[rdi]";
   }
  if (!ref($right))                                                             # Load right constant
   {Mov rsi, $right;
   }
  else                                                                          # Load right variable
   {Mov rsi, $right->addressExpr;
    if ($right->reference)                                                      # Dereference right if necessary
     {Mov rsi, "[rsi]";
     }
   }
  &$op(rdi, rsi);
  if ($left->reference)                                                         # Store in reference on left if necessary
   {Mov r11, $left->addressExpr;
    Mov "[r11]", rdi;
   }
  else                                                                          # Store in variable
   {Mov $left ->addressExpr, rdi;
   }

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
  Mov rsi, $l;
  if ($left->reference)                                                         # Dereference left if necessary
   {Mov rsi, "[rsi]";
   }
  Mov rbx, $r;
  if (ref($right) and $right->reference)                                        # Dereference right if necessary
   {Mov rbx, "[rbx]";
   }
  &$op(rsi, rbx);
  my $v = V(join(' ', '('.$left->name, $name, (ref($right) ? $right->name : $right).')'), rsi);
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
#  PushR rcx, 15;
  $left ->setReg(rbx);                                                          # Value to shift
  confess "Variable required not $right" unless ref($right);
  $right->setReg(rcx);                                                          # Amount to shift
  Shl rbx, cl;                                                                  # Shift
  my $r = V "shift left" => rbx;                                                # Save result in a new variable
#  PopR;
  $r
 }

sub Nasm::X86::Variable::shiftRight($$)                                         # Shift the left hand variable right by the number of bits specified in the right hand variable and return the result as a new variable.
 {my ($left, $right) = @_;                                                      # Left variable, right variable
# PushR rcx, 15;
  $left ->setReg(rbx);                                                          # Value to shift
  confess "Variable required not $right" unless ref($right);
  $right->setReg(rcx);                                                          # Amount to shift
  Shr rbx, cl;                                                                  # Shift
  my $r = V "shift right" => rbx;                                               # Save result in a new variable
# PopR;
  $r
 }

sub Nasm::X86::Variable::not($)                                                 # Form two complement of left hand side and return it as a variable.
 {my ($left) = @_;                                                              # Left variable
  $left->setReg(rdi);                                                           # Value to negate
  Not rdi;                                                                      # Two's complement
  V "neg" => rdi;                                                               # Save result in a new variable
 }

sub Nasm::X86::Variable::booleanZF($$$$)                                        # Combine the left hand variable with the right hand variable via a boolean operator and indicate the result by setting the zero flag if the result is true.
 {my ($sub, $op, $left, $right) = @_;                                           # Operator, operator name, Left variable,  right variable

  !ref($right) or ref($right) =~ m(Variable) or confess "Variable expected";
  my $r = ref($right) ? $right->addressExpr : $right;                           # Right can be either a variable reference or a constant

  Comment "Boolean ZF Start";

  if ($op =~ m(\Ag)i)
   {($left, $right) = ($right, $left);
   }

  if (ref($right) and $right->reference)                                        # Dereference on right if necessary
   {Mov r11, $left ->addressExpr;
    Mov r11, "[r11]" if $left->reference;
    Mov rdi, $right ->addressExpr;
    Mov rdi, "[rdi]";
    Cmp r11, rdi;
   }
  elsif (ref($right))                                                           # Variable but not a reference on the right
   {Mov r11, $left ->addressExpr;
    Mov r11, "[r11]" if $left->reference;
    Cmp r11, $right->addressExpr;
   }
  elsif ($left->reference)                                                      # Left is a reference, right is a constant
   {Mov r11, $left ->addressExpr;
    Mov r11, "[r11]";
    Cmp r11, $right;
   }
  else                                                                          # Not a reference on the left and a constant on the right
   {Cmp "qword ".$left->addressExpr, $right;
   }
  Comment "Boolean ZF Arithmetic end $op";

  \$op
 }

sub Nasm::X86::Variable::eq($$)                                                 # Check whether the left hand variable is equal to the right hand variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanZF(\&IfEq, q(Jne),  $left, $right);
 }

sub Nasm::X86::Variable::ne($$)                                                 # Check whether the left hand variable is not equal to the right hand variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanZF(\&IfNe, q(Je), $left, $right);
 }

sub Nasm::X86::Variable::ge($$)                                                 # Check whether the left hand variable is greater than or equal to the right hand variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanZF(\&IfGe, q(Jl), $left, $right);
 }

sub Nasm::X86::Variable::gt($$)                                                 # Check whether the left hand variable is greater than the right hand variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanZF(\&IfGt, q(Jle), $left, $right);
 }

sub Nasm::X86::Variable::le($$)                                                 # Check whether the left hand variable is less than or equal to the right hand variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanZF(\&IfLe, q(Jg), $left, $right);
 }

sub Nasm::X86::Variable::lt($$)                                                 # Check whether the left hand variable is less than the right hand variable.
 {my ($left, $right) = @_;                                                      # Left variable,  right variable
  Nasm::X86::Variable::booleanZF(\&IfLt, q(Jge), $left, $right);
 }

sub Nasm::X86::Variable::isRef($)                                               # Check whether the specified  variable is a reference to another variable.
 {my ($variable) = @_;                                                          # Variable
  @_ == 1 or confess "One parameter";
  my $n = $variable->name;                                                      # Variable name
  $variable->reference
 }

sub Nasm::X86::Variable::setReg($$)                                             # Set the named registers from the content of the variable.
 {my ($variable, $register) = @_;                                               # Variable, register to load
  @_ == 2 or confess "Two parameters";

  my $r = registerNameFromNumber $register;
  if (CheckMaskRegister($r))                                                    # Mask register is being set
   {Mov  rdi, $variable->addressExpr;
    if ($variable->isRef)
     {Kmovq $r, "[rdi]";
     }
    else
     {Kmovq $r, rdi;
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

  $register                                                                     # Name of register being set
 }

sub Nasm::X86::Variable::compare($$)                                            # Compare the content of a variable with a numeric constant.
 {my ($variable, $compare) = @_;                                                # Variable, value to compare
  @_ == 2 or confess "Two parameters";

  if ($variable->isRef)
   {Mov rsi, $variable->addressExpr;
    Cmp "qword [rsi]", $compare;
   }
  else
   {Cmp "qword ".$variable->addressExpr, $compare;
   }
 }

sub Nasm::X86::Variable::getReg($$)                                             # Load the variable from a register expression.
 {my ($variable, $register) = @_;                                               # Variable, register expression to load
  @_ == 2 or confess "Two parameters";
  my $r = registerNameFromNumber $register;
  if ($variable->isRef)                                                         # Move to the location referred to by this variable
   {Comment "Get variable value from register $r";
    my $p = $r eq rdi ? rsi : rdi;
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
   {Mov rsi, $l;
    push @text, <<END;
    $op qword [rsi]
END
    return $left;
   }
  else
   {push @text, <<END;
    $op qword $l
END
    return $left;
   }
# else
#  {PushR r15;
#   Mov r15, $l;
#   &$op(r15);
#   Mov $l, r15;
#   PopR;
#   return $left;
#  }
 }

sub Nasm::X86::Variable::inc($)                                                 # Increment a variable.
 {my ($left) = @_;                                                              # Variable
  $left->incDec("inc");
 }

sub Nasm::X86::Variable::dec($)                                                 # Decrement a variable.
 {my ($left) = @_;                                                              # Variable
  $left->incDec("dec");
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
  $variable->copy(getBwdqFromMm 'z', 'b', $zmm, $offset);                       # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::wFromZ($$$)                                            # Get the word from the numbered zmm register and put it in a variable.
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  $variable->copy(getBwdqFromMm 'z', 'w', $zmm, $offset);                       # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::dFromZ($$$)                                            # Get the double word from the numbered zmm register and put it in a variable.
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  $variable->copy(getBwdqFromMm 'z', 'd', $zmm, $offset);                       # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub Nasm::X86::Variable::qFromZ($$$)                                            # Get the quad word from the numbered zmm register and put it in a variable.
 {my ($variable, $zmm, $offset) = @_;                                           # Variable, numbered zmm, offset in bytes
  @_ == 3 or confess "Three parameters";
  $variable->copy(getBwdqFromMm 'z', 'q', $zmm, $offset);                       # Get the numbered byte|word|double word|quad word from the numbered zmm register and put it in a variable
 }

sub dFromPointInZ($$%)                                                          # Get the double word from the numbered zmm register at a point specified by the variable or register and return it in a variable.
 {my ($point, $zmm, %options) = @_;                                             # Point, numbered zmm, options

  my $s = $options{set} // rsi;                                                 # Register to set else a variable will be returned
  my $x = $zmm =~ m(\A(zmm)?0\Z) ? 1 : 0;                                       # The zmm we will extract into
  if (ref($point) =~ m(Variable))  {$point->setReg(k1)}                         # Point is in a variable
  else                             {Kmovq k1, $point}                           # Point is in a register
  my ($z) = zmm $zmm;
  Vpcompressd "zmm$x\{k1}", $z;
  Vpextrd dWordRegister($s), xmm($x), 0;                                        # Extract dword from corresponding xmm
  V d => $s unless $options{set};                                               # Create a variable unless a register to set was provided
 }

sub Nasm::X86::Variable::dFromPointInZ($$%)                                     # Get the double word from the numbered zmm register at a point specified by the variable and return it in a variable.
 {my ($point, $zmm, %options) = @_;                                             # Point, numbered zmm, options
  @_ >= 2 or confess "Two or more parameters";
  dFromPointInZ($point, $zmm, %options);                                        # Register to set else a variable will be returned
 }

sub Nasm::X86::Variable::dIntoPointInZ($$$)                                     # Put the variable double word content into the numbered zmm register at a point specified by the variable.
 {my ($point, $zmm, $content) = @_;                                             # Point, numbered zmm, content to be inserted as a variable
  $content->setReg(rdi);
  $point->setReg(rsi);
  Kmovq k1, rsi;
  Vpbroadcastd zmmM($zmm, 1), edi;                                              # Insert dword at desired location
 }

sub Nasm::X86::Variable::putBwdqIntoMm($$$$)                                    # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register.
 {my ($content, $size, $mm, $offset) = @_;                                      # Variable with content, size of put, numbered zmm, offset in bytes
  @_ == 4 or confess "Four parameters";

  my $o;                                                                        # The offset into the mm register
  if (ref $offset)                                                              # The offset is being passed in a variable
   {$offset->setReg($o = rdi);   ## rsi
   }
  else                                                                          # The offset is being passed as a register expression
   {$o = $offset;
    Comment "Put $size at $offset in $mm";
    $offset >= 0 && $offset <= RegisterSize $mm or
      confess "Out of range" if $offset =~ m(\A\d+\Z);                          # Check the offset if it is a number
   }

  $content->setReg(rsi);         ## rsi
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
  my $z = extractRegisterNumberFromMM $zmm;
# checkZmmRegister($zmm);
  $content->putBwdqIntoMm('d', "zmm$z", $offset)                                # Place the value of the content variable at the byte|word|double word|quad word in the numbered zmm register
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
  &ClearMemory($address, $size);                                                # Free the memory
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

sub Nasm::X86::Variable::allocateMemory($)                                      # Allocate a variable amount of memory via mmap and return its address.
 {my ($size) = @_;                                                              # Size as a variable
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

sub PrintMemory($)                                                              # Print the memory addressed by rax for a length of rdi on the specified channel where channel can be a constant number or a register expression using a bound register.
 {my ($channel) = @_;                                                           # Channel
  @_ == 1 or confess "One parameter";

  SaveFirstFour;
  Mov rsi, rax;
  Mov rdx, rdi;
  Mov rax, 1;                                                                   # Request
  Mov rdi, $channel;                                                            # Channel can be a constant or a register expression
  Syscall;
  RestoreFirstFour;
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
    if ($DebugMode)
     {Cmp rax, -1;                                                              # Check return code
      IfEq
      Then
       {PrintErrTraceBack "Cannot allocate memory, return code -1";
       };
      Cmp eax, 0xffffffea;                                                      # Check return code
      IfEq
      Then
       {PrintErrTraceBack "Cannot allocate memory, return code 0xffffffea";
       };
      Cmp rax, -12;                                                             # Check return code
      IfEq
      Then
       {PrintErrTraceBack "Cannot allocate memory, return code -12";
       };
     }
    $$p{address}->getReg(rax);                                                  # Amount of memory
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

sub ClearMemory($$)                                                             # Clear memory with a variable address and variable length.
 {my ($address, $size) = @_;                                                    # Address of memory as a variable, size of memory as a variable
  @_ == 2 or confess "address, size required";
  Comment "Clear memory";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    PushR zmm0; PushR rax, rdi, rsi, rdx;                                       # Reliance on push order which no longer matches the order of the arguments
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

    PopR; PopR;
   } parameters=>[qw(size address)], name => 'ClearMemory';

  $s->call(parameters => {address => $address, size => $size});
 }

sub CopyMemory($$$)                                                             # Copy memory.
 {my ($source, $target, $size) = @_;                                            # Source address variable, target address variable, length variable
  @_ == 3 or confess "Source, target, size required";

  SaveFirstSeven;
  $source->setReg(rsi);                                                         # Source location
  $target->setReg(rax);                                                         # Target location
  $size  ->setReg(rdi);                                                         # Size of area to copy
  ClearRegisters rdx;
  For                                                                           # Clear memory
   {Mov "r8b", "[rsi+rdx]";
    Mov "[rax+rdx]", "r8b";
   } rdx, rdi, 1;
  RestoreFirstSeven;
 }

sub CopyMemory64($$$)                                                           # Copy memory in 64 byte blocks.
 {my ($source, $target, $size) = @_;                                            # Source address variable, target address variable, number of 64 byte blocks to move
  @_ == 3 or confess "Source, target, size required";

  PushR my $s = r8, my $t = r9, my $z = r10, my $c = r11, 31;

  $source->setReg($s);                                                          # Source location
  $target->setReg($t);                                                          # Target location
  $size  ->setReg($c);                                                          # Size of area to copy
  my $end = Label;                                                              # End of move loop
  Cmp $c, 0;
  Je $end;                                                                      # Nothing to move
  my $start = SetLabel;                                                         # Move loop
    Vmovdqu64 zmm31, "[$s]";
    Vmovdqu64 "[$t]", zmm31;
    Add $s, 64;
    Add $t, 64;
    Sub $c, 1;
    Jnz $start;
  SetLabel $end;
  PopR;
 }

sub CopyMemory4K($$$)                                                           # Copy memory in 4K byte blocks.
 {my ($source, $target, $size) = @_;                                            # Source address variable, target address variable, number of 4K byte blocks to move
  @_ == 3 or confess "Source, target, size required";

  PushR my $s = r8, my $t = r9, my $z = r10, my $c = r11, zmm(0..31);
  my $k2 = 2 ** 11;                                                             # Half of 4K == the bytes we can shift in one go using all zmm registers
  $size  ->setReg($c);                                                          # Size of area to copy
  my $end = Label;                                                              # End of move loop
  Cmp $c, 0;
  Je $end;                                                                      # Nothing to move

  $source->setReg($s);                                                          # Source location
  $target->setReg($t);                                                          # Target location
  ClearRegisters $z;                                                            # Offset into move

  my $start = SetLabel;                                                         # Move loop
    Vmovdqu64 "zmm$_", "[$s+$z+64*$_]"              for 0..31;                  # Load 2K
    Vmovdqu64          "[$t+$z+64*$_]",     "zmm$_" for 0..31;                  # Store 2k
    Vmovdqu64 "zmm$_", "[$s+$z+64*$_+$k2]"          for 0..31;                  # Load next 2k
    Vmovdqu64          "[$t+$z+64*$_+$k2]", "zmm$_" for 0..31;                  # Store next 2k
    Add $z, $k2 * 2;                                                            # Next move offset
    Sub $c, 1;                                                                  # Decrement loop counter
    Jnz $start;                                                                 # Continue unless we are finished
  SetLabel $end;
  PopR;
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

sub OpenWrite()                                                                 # Create the file named by the terminated string addressed by rax for write.  The file handle will be returned in rax.
 {@_ == 0 or confess "Zero parameters";

  my $s = Subroutine
   {my %s = getSystemConstantsFromIncludeFile "fcntl.h", qw(O_CREAT O_WRONLY);  # Constants for creating a file
    my $w = $s{O_WRONLY} | $s{O_CREAT};

    SaveFirstFour;
    Mov rdi, rax;
    Mov rax, 2;
    Mov rsi, $w;
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
 {my ($File) = @_;                                                              # Variable addressing a zero terminated string naming the file to be read in by mapping it
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

sub executeFileViaBash($)                                                       # Execute the file named in a variable.
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

sub convert_rax_from_utf32_to_utf8                                              # Convert a utf32 character held in rax to a utf8 character held in rax.
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

#   PushR 11, 12, 13, 14, 15;
    $$p{fail}->getConst(0);                                                     # Clear failure indicator
    $$p{in}->setReg(rbx);                                                       # Character to convert
    ClearRegisters rdx;                                                         # Move to byte register below does not clear the entire register
    Mov dl, "[rbx]";
    Block
     {my ($success) = @_;                                                       # As shown at: https://en.wikipedia.org/wiki/UTF-8

      Cmp rdx, 0x7f;                                                            # Ascii
      IfLe
      Then
       {$$p{out}->getReg(rdx);
        $$p{size}->copy(1);
        Jmp $success;
       };

      Cmp rdx, 0xdf;                                                            # Char size is: 2 bytes
      IfLe
      Then
       {Mov dil, "[rbx+1]";
        And rdi, 0x3f;
        And rdx, 0x1f;
        Shl rdx, 6;
        Or  rdx,  rdi;
        $$p{out}->getReg(rdx);
        $$p{size}->copy(2);
        Jmp $success;
       };

      Cmp rdx, 0xef;                                                            # Char size is: 3 bytes
      IfLe
      Then
       {Mov sil, "[rbx+2]";
        And rsi, 0x3f;
        Mov dil, "[rbx+1]";
        And rdi, 0x3f;
        And rdx, 0x0f;
        Shl rdi,  6;
        Shl rdx, 12;
        Or  rdx,  rdi;
        Or  rdx,  rsi;
        $$p{out}->getReg(rdx);
        $$p{size}->copy(3);
        Jmp $success;
       };

      Cmp rdx, 0xf7;                                                            # Char size is: 4 bytes
      IfLe
      Then
       {Mov r11b, "[rbx+3]";
        And r11, 0x3f;
        Mov sil, "[rbx+2]";
        And rsi, 0x3f;
        Mov dil, "[rbx+1]";
        And rdi, 0x3f;
        And rdx, 0x07;
        Shl rsi,  6;
        Shl rdi, 12;
        Shl rdx, 18;
        Or  rdx,  rdi;
        Or  rdx,  rsi;
        Or  rdx,  r11;
        $$p{out}->getReg(rdx);
        $$p{size}->copy(4);
        Jmp $success;
       };

      $$p{fail}->getConst(1);                                                   # Conversion failed
     };

#    PopR;
   } parameters=>[qw(in out  size  fail)], name => 'GetNextUtf8CharAsUtf32';

  my $out  = V(out  => 0);                                                      # Utf32 equivalent
  my $size = V(size => 0);                                                      # Size of utf8 converted
  my $fail = V(fail => 0);                                                      # Failed if true else false

  $s->inline(parameters=>{in=>$in, out=>$out, size=>$size, fail=>$fail});

 ($out, $size, $fail)                                                           # Output character variable, output size of input, output error if any

 } # GetNextUtf8CharAsUtf32

sub ConvertUtf8ToUtf32($$)                                                      # Convert an allocated block  string of utf8 to an allocated block of utf32 and return its address and length.
 {my ($a8, $s8) = @_;                                                           # Utf8 string address variable, utf8 length variable
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

    $$p{count}->getReg(r12);                                                    # Number of unicode points converted from utf8 to utf32
    PopR;
   } parameters=>[qw(a8 s8 a32 s32 count fail)], name => 'ConvertUtf8ToUtf32';

  my $a32   = V(a32   => 0);
  my $s32   = V(s32   => 0);
  my $count = V(count => 0);
  my $fail  = V(fail  => 0);                                                    # Assume we will succeed

  $s->call(parameters=>
    {a8  => $a8,  s8  => $s8,
     a32 => $a32, s32 => $s32, count=>$count, fail => $fail});

  ($a32, $s32, $count, $fail)                                                   # Utf32 string address as a variable, utf32 area length as a variable, number of characters converted, fail if one else zero
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

#D2 Constructors                                                                # Construct an area either in memory or by reading it from a file or by incorporating it into an assembly.

sub DescribeArea(%)                                                             # Describe a relocatable area.
 {my (%options) = @_;                                                           # Optional variable addressing the start of the area
  my $B = 12;                                                                   # Log2 of size of initial allocation for the area
  my $N = 2 ** $B;                                                              # Initial size of area
  my $w = RegisterSize 31;

  my $quad = RegisterSize rax;                                                  # Field offsets
  my $size = 0;
  my $used = $size + $quad;                                                     # Amount of memory in the area that has been used - includes the free chain.
  my $free = $used + $quad;                                                     # Free chain blocks = freed zmm blocks
  my $tree = $free + $quad;                                                     # Start of Yggdrasil,
  my $data = $w;                                                                # Data starts in the next zmm block

  genHash(__PACKAGE__."::Area",                                                 # Definition of area
    B          => $B,                                                           # Log2 of size of initial allocation
    N          => $N,                                                           # Initial allocation
    sizeOffset => $size,                                                        # Size field offset
    usedOffset => $used,                                                        # Used field offset
    freeOffset => $free,                                                        # Free chain offset
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

sub ReadArea($)                                                                 # Read an area stored in a file into memory and return an area descriptor for the area so created.
 {my ($file) = @_;                                                              # Name of file to read
  my ($address, $size) = ReadFile $file;                                        # Read the file into memory
  DescribeArea address => $address;                                             # Describe it as an area
 }

sub loadAreaIntoAssembly($)                                                     # Load an area into the current assembly and return a descriptor for it.
 {my ($file) = @_;                                                              # File containing an area

  if (my $l = $loadAreaIntoAssembly{$file})                                     # Check for a pre existing area
   {return DescribeArea address => V area=>$l;                                  # Describe area
   }

  my  $areaFinish = $loadAreaIntoAssembly{$file} = Label;                       # Label at start of area
  Jmp $areaFinish;                                                              # Jump over area
  push @text, <<END;
  align 16
END
  my  $areaStart = SetLabel;
  Incbin qq("$file");                                                           # Include area as a binary file
  SetLabel $areaFinish;

  DescribeArea address => V area=>$areaStart;                                   # Describe area
 }

sub Nasm::X86::Area::free($)                                                    # Free an area.
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";
  FreeMemory($area->address, $area->size)
 }

#D2 Memory                                                                      # Manage memory controlled by an area.

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

sub Nasm::X86::Area::size($)                                                    # Get the size of an area as a variable.
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";

  PushR rax;
  $area->address->setReg(rax);                                                  # Address area
  Mov rax, "[rax+$$area{sizeOffset}]";                                          # Get size
  my $size = V 'size of area' => rax;                                           # Save size in a variable
  PopR;
  $size                                                                         # Return size
 }

sub Nasm::X86::Area::updateSpace($$)                                            #P Make sure that a variable addressed area has enough space to accommodate content of a variable size.
 {my ($area, $size) = @_;                                                       # Area descriptor, variable size needed
  @_ == 2 or confess "Two parameters";
  my $base     = rdi;                                                           # Base of area
  my $newSize  = rsi;                                                           # New size needed
  my $areaSize = "[$base+$$area{sizeOffset}]";                                  # Size of area
  my $areaUsed = "[$base+$$area{usedOffset}]";                                  # Used space in area

  my $s = Subroutine
   {my ($p, $s)  = @_;                                                          # Parameters, structures
    PushR my $base = r15, my $newSize = r14, my $proposed = r13;                # Base of area, New size needed, Proposed size
    my $areaSize = "[$base+$$area{sizeOffset}]";                                # Size of area
    my $areaUsed = "[$base+$$area{usedOffset}]";                                # Used space in area

    my $area = $$s{area};                                                       # Area
    $area->address->setReg($base);                                              # Address area

    $$p{size}->setReg($newSize);                                                # Space requested
    Add $newSize, $areaUsed;                                                    # Space needed in area

    Mov $proposed, $areaSize;                                                   # Minimum proposed area size

    K(loop=>36)->for(sub                                                        # Maximum number of shifts
     {my ($index, $start, $next, $end) = @_;
      Shl $proposed, 1;                                                         # New proposed size
      Cmp $proposed, $newSize;                                                  # Big enough?
      Jge $end;                                                                 # Big enough!
     });

    my $address = AllocateMemory V size => $proposed;                           # Create new area
    CopyMemory4K($area->address, $address, $area->size>>K(k4 => $area->B));     # Copy old area into new area 4K at a time
    FreeMemory $area->address, $area->size;                                     # Free previous memory previously occupied area
    $area->address->copy($address);                                             # Save new area address
    $address->setReg($base);                                                    # Address area
    Mov "[$base+$$area{sizeOffset}]", $proposed;                                # Save the new size in the area

    PopR;
   } parameters => [qw(size)],
     structures => {area => $area},
     name       => 'Nasm::X86::Area::updateSpace';

  $area->address->setReg($base);                                                # Address area
  $size->setReg($newSize);                                                      # Space requested
  Add $newSize, $areaUsed;                                                      # Space needed in area
  Cmp $newSize, $areaSize;                                                      # Compare size needed with current size
  IfGt                                                                          # New size is bigger than current size
  Then                                                                          # More space needed
   {$s->call(parameters=>{size => $size}, structures=>{area => $area});         # Allocate more space for area
   };
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

  PushR rax;

  $area->address->setReg(rax);                                                  # Address of area
  my $firstBlock = "dword[rax+$$area{freeOffset}]";                             # Offset of first block in free chain if such a block exists

  Cmp $firstBlock, 0;
  IfGt                                                                          # Check free chain
  Then                                                                          # Free block available on free chain
   {PushR my $first = r14, my $second = r15, my $block = 31;
    my $firstD  = $first.'d';
    my $secondD = $second.'d';
    Mov $firstD, $firstBlock;                                                   # Offset of first block
    $area->getZmmBlock(V(offset => $first), $block);                            # Load the first block on the free chain
    dFromZ($block, 0)->setReg($second);                                         # The location of the second block if any
    Mov $firstBlock, $secondD;                                                  # Offset of first block in free chain if such a block exists
    ClearRegisters $block;                                                      # Clear the zmm block - possibly this only needs to be done if we are reusing a block
    $offset->getReg($first);                                                    # First block is the allocated block
    $area->putZmmBlock($offset, $block);
    PopR;
   },
  Else                                                                          # Cannot reuse a free block so allocate
   {$offset->copy($area->allocate(K size => $area->zmmBlock));                  # Copy offset of allocation
   };

  PopR;

  $offset                                                                       # Return offset of allocated block
 }

sub Nasm::X86::Area::allocZmmBlock3($)                                          # Allocate three zmm blocks in one go and return their offsets.
 {my ($area) = @_;                                                              # Area
  @_ == 1 or confess "One parameter";
  my $o1 = V(o1 => 0);                                                          # First block
  my $o2 = V(o2 => 0);                                                          # Second block
  my $o3 = V(o3 => 0);                                                          # Third block

  PushR rax;

  $area->address->setReg(rax);                                                  # Address of area
  my $firstBlock = "dword[rax+$$area{freeOffset}]";                             # Offset of first block in free chain if such a block exists

  Cmp $firstBlock, 0;
  IfGt                                                                          # Check free chain
  Then                                                                          # Free block available on free chain
   {$o1->copy($area->allocZmmBlock);
    $o2->copy($area->allocZmmBlock);
    $o3->copy($area->allocZmmBlock);
   },
  Else                                                                          # Cannot reuse a free block so allocate
   {$o1->copy($area->allocate(K size => $area->zmmBlock * 3));                  # Copy offset of allocation
    $o2->copy($o1 + RegisterSize zmm0);                                         # Cut out sub blocks
    $o3->copy($o2 + RegisterSize zmm0);
   };

  PopR;

  ($o1, $o2, $o3)                                                               # Return offsets of allocated blocks
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

sub Nasm::X86::Area::freeChainSpace($)                                          # Count the number of blocks available on the free chain.
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
 {my ($area, $block, $zmm) = @_;                                                # Area descriptor, offset of the block as a variable or register, number of zmm register to contain block
  @_ == 3 or confess "Three parameters";

  my $a = rdi;                                                                  # Work registers
  my $o = ref($block) =~ m(Variable) ? rsi : $block;                            # Offset of block in area via register or variable

  $area->address->setReg($a);                                                   # Area address
  $block        ->setReg($o) if ref($block) =~ m(Variable);                     # Offset of block in area via variable

  if ($DebugMode)
   {Cmp $o, $area->dataOffset;
    IfLt                                                                        # We could have done this using variable arithmetic, but such arithmetic is expensive and so it is better to use register arithmetic if we can.
    Then
     {PrintErrTraceBack "Attempt to get block before start of area";
     };
   }

  Vmovdqu64 "zmm$zmm", "[$a+$o]";                                               # Read from memory
 }

sub Nasm::X86::Area::putZmmBlock($$$)                                           #P Write the numbered zmm to the block at the specified offset in the specified area.
 {my ($area, $block, $zmm) = @_;                                                # Area descriptor, offset of the block as a variable, number of zmm register to contain block
  @_ == 3 or confess "Three parameters";

  my $a = rdi;                                                                  # Work registers
  my $o = rsi;

  $area->address->setReg($a);                                                   # Area address
  $block->setReg($o);                                                           # Offset of block in area

  if ($DebugMode)
   {Cmp $o, $area->dataOffset;
    IfLt                                                                        # We could have done this using variable arithmetic, but such arithmetic is expensive and so it is better to use register arithmetic if we can.
    Then
     {PrintErrTraceBack "Attempt to put block before start of area";
     };
   }
  Vmovdqu64 "[$a+$o]", "zmm$zmm";                                               # Read from memory
 }

sub Nasm::X86::Area::clearZmmBlock($$)                                          #P Clear the zmm block at the specified offset in the area.
 {my ($area, $offset) = @_;                                                     # Area descriptor, offset of the block as a variable
  @_ == 2 or confess "Two parameters";

  ClearRegisters 1;
  $area->putZmmBlock($offset, 1);
 }

#D2 Yggdrasil                                                                   # The world tree from which we can address so many other things

sub Nasm::X86::Yggdrasil::UniqueStrings        {K key => 0}                     # A tree of strings that assigns unique numbers to strings.
sub Nasm::X86::Yggdrasil::SubroutineOffsets    {K key => 1}                     # Translates a string number into the offset of a subroutine in an area.
sub Nasm::X86::Yggdrasil::SubroutineDefinitions{K key => 2}                     # Maps the unique string number for a subroutine name to the offset in the are that contains the length (as a dword) followed by the string content of the Perl data structure describing the subroutine in question.
sub Nasm::X86::Yggdrasil::Unisyn::Alphabets    {K key => 3}                     # Unisyn alphabets.
sub Nasm::X86::Yggdrasil::Unisyn::Open         {K key => 4}                     # Open bracket to close bracket
sub Nasm::X86::Yggdrasil::Unisyn::Close        {K key => 5}                     # Close bracket to open bracket
sub Nasm::X86::Yggdrasil::Unisyn::Transitions  {K key => 6}                     # Permissible transitions from alphabet to alphabet

sub Nasm::X86::Area::yggdrasil($)                                               # Return a tree descriptor to the Yggdrasil world tree for an area creating the world tree Yggdrasil if it has not already been created.
 {my ($area) = @_;                                                              # Area descriptor
  @_ == 1 or confess "One parameter";

  my $t = $area->DescribeTree;                                                  # Tree descriptor for Yggdrasil
  PushR rax, r15;
  $area->address->setReg(rax);                                                  # Address underlying area
  Mov r15, "[rax+$$area{treeOffset}]";                                          # Address Yggdrasil

  Cmp r15, 0;                                                                   # Does Yggdrasil even exist?
  IfNe
  Then                                                                          # Yggdrasil has already been created so we can address it
   {$t->first->getReg(r15);
   },
  Else                                                                          # Yggdrasil has not been created
   {my $T = $area->CreateTree;
    $t->first->copy($T->first);
    $T->first->setReg(r15);
    $area->address->setReg(rax);                                                # Address underlying area - it might have moved
    Mov "[rax+$$area{treeOffset}]", r15;                                        # Save offset of Yggdrasil
   };
  PopR;
  $t
 }

sub Nasm::X86::Area::checkYggdrasilCreated($)                                   #P Return a tree descriptor for the Yggdrasil world tree for an area. If Yggdrasil has not been created the found field of the returned descriptor will have zero in it else one.
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
  PopR rax;
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

    $$p{offset}->copy($oldUsed);                                                # Return offset of content in area

    RestoreFirstFour;
   } structures => {area => $area},
     parameters => [qw(address size offset)],
     name       => 'Nasm::X86::Area::m';

  my $offset = V offset => 0;                                                   # Offset within the area at which the content was appended
  $s->call(structures => {area => $area},
           parameters => {address => $address, size => $size,
                          offset  => $offset});
  $offset
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

sub Nasm::X86::Area::clear($)                                                   # Clear an area but keep it at the same size.
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

sub Nasm::X86::Area::read($@)                                                   # Read a file specified by a variable addressed zero terminated string and append its content to the specified area.
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

sub Nasm::X86::Area::write($$)                                                  # Write the content of the specified area to a file specified by a zero terminated string.
 {my ($area, $file) = @_;                                                       # Area descriptor, variable addressing zero terminated file name
  @_ == 2 or confess "Two parameters";

  my $s = Subroutine
   {my ($p) = @_;                                                               # Parameters
    SaveFirstFour;
    $$p{file}->setReg(rax);
    OpenWrite;                                                                  # Open file
    my $file = V(fd => rax);                                                    # File descriptor

    $$p{address}->setReg(rsi);                                                  # Write from start of area
    Mov rdx, "[rsi+$$area{usedOffset}]";                                        # Length of the area to write

    Mov rax, 1;                                                                 # Write content to file
    $file->setReg(rdi);                                                         # File number
    Syscall;

    $file->setReg(rax);                                                         # Close the file
    CloseFile;
    RestoreFirstFour;
   } parameters=>[qw(file address)], name => 'Nasm::X86::Area::write';

  $s->call(parameters=>{address => $area->address, file => $file});
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

#D2 Constructors                                                                # Construct a tree.

sub DescribeTree(%)                                                             #P Return a descriptor for a tree with the specified options.
 {my (%options)  = @_;                                                          # Tree description options
  my $area       = delete $options{area};                                       # The area containing the tree
  my $lowKeys    = delete $options{lowKeys};                                    # 1 - Where possible low numbered keys should be placed in the first block. 2 - (1) and the low keys should always be considered present and not trees so there is no need to process either the present or tree bits. Fields that have not been set will return zero. This configuration make the first block behave like a conventional flat data structure.  Processing of keys beyond the first block are not affected bh this flag.
  my $lowTree    = delete $options{lowTree};                                    # This tree is at the lowest level if true. As there are no sub trees hanging from this tree we may optimize put, find, delete to not process information required to describe sub trees.  This action has not been done yet except n the case of low key processing.
  my $stringKeys = delete $options{stringKeys};                                 # The key offsets designate 64 byte blocks of memory in the same area that contain the actual keys to the tree as strings.  If the actual string is longer than 64 bytes then the rest of it appears in the sub tree indicated by the data element.
  my $length     = delete $options{length};                                     # Maximum number of keys per node
     $length     = 13;                                                          # Maximum number of keys per node
  confess "Invalid options: ".join(", ", sort keys %options) if keys %options;  # Complain about any invalid keys

  my $b = RegisterSize 31;                                                      # Size of a block == size of a zmm register
  my $o = RegisterSize eax;                                                     # Size of a double word

  my $keyAreaWidth = $b - $o * 2 ;                                              # Key / data area width  in bytes
  my $kwdw   = $keyAreaWidth / $o;                                              # Number of keys in a maximal block

  confess "Length: $length is even not odd" unless $length % 2;                 # Ideally length is odd
  confess "Length must be greater than 2, not: $length" unless $length > 2;     # Check minimum length
  confess "Length must be less than or equal to $kwdw, not $length"             # Check maximum length
    unless $length <= $kwdw;

  my $l2 = int($length/2);                                                      # Minimum number of keys in a node

  genHash(__PACKAGE__."::Tree",                                                 # Tree
    area        => ($area // DescribeArea),                                     # Area definition.
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
    lowKeys      => $lowKeys,                                                   # Low keys should be placed in first block where possible
    lowTree      => $lowTree,                                                   # No sub trees depend on this tree

    rootOffset   => $o * 0,                                                     # Offset of the root field in the first block - the root field contains the offset of the block containing the keys of the root of the tree
    upOffset     => $o * 1,                                                     # Offset of the up field  in the first block -  points to any containing tree
    sizeOffset   => $o * 2,                                                     # Offset of the size field  in the first block - tells us the number of  keys in the tree
    fcControl    => $o * 3,                                                     # Offset of the tree bits and present bits in the first cache of low key values for this tree.
    fcPresentOff => $o * 3,                                                     # Byte offset of word  containing present bits
    fcPresent    => 0,                                                          # Offset of the present bits in the control dword
    fcTreeBitsOff=> $o * 3 + RegisterSize(ax),                                  # Byte offset of word containing tree bits
    fcTreeBits   => 16,                                                         # Offset of the tree bits in bits in the control dword
    fcArray      => $o * 4,                                                     # Offset of cached array in first block
    fcDWidth     => $b / $o - 4,                                                # Number of dwords available in the first cache.  The first cache supplies an alternate area to store the values of keys less than this value  to fill the otherwise unused space in a way that improves the performance of trees when used to represent small arrays, stacks or structures.
    middleOffset => $o * ($l2 + 0),                                             # Offset of the middle slot in bytes
    rightOffset  => $o * ($l2 + 1),                                             # Offset of the first right slot in bytes

    data         => V(data    => 0),                                            # Variable containing the current data
    first        => V(first   => 0),                                            # Variable addressing offset to first block of the tree which is the header block
    found        => V(found   => 0),                                            # Variable indicating whether the last find was successful or not
    key          => V(key     => 0),                                            # Variable containing the current key
    offset       => V(offset  => 0),                                            # Variable containing the offset of the block containing the current key
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
  my $o    = $tree->area->allocZmmBlock;                                        # Allocate header
  $tree->first->copy($o);                                                       # Install header

  $tree                                                                         # Description of array
 }

sub Nasm::X86::Tree::describeTree($%)                                           # Create a description of a tree.
 {my ($tree, %options) = @_;                                                    # Tree descriptor, {first=>first node of tree if not the existing first node; area=>area used by tree if not the existing area}
  @_ >= 1 or confess "At least one parameter";

  $tree->area->DescribeTree(%options);                                          # Return a descriptor for a tree
 }

sub Nasm::X86::Tree::position($$)                                               # Create a new tree description for a tree positioned at the specified location.
 {my ($tree, $first) = @_;                                                      # Tree descriptor, offset of tree
  my $t = $tree->describeTree(length=>$tree->length);                           # Length of new tree must be same as old tree

  $t->first->copy($first);                                                      # Variable addressing offset to first block of keys.
  $t                                                                            # Return new descriptor
 }

sub Nasm::X86::Tree::reposition($$)                                             # Reposition an existing tree at the specified location.
 {my ($tree, $first) = @_;                                                      # Tree descriptor, offset to reposition on
  $tree->first->copy($first);                                                   # Variable addressing offset to first block of keys.
  $tree                                                                         # Return existing tree descriptor
 }

sub Nasm::X86::Tree::cloneDescriptor($)                                         # Clone the descriptor of a tree to make a new tree descriptor.
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess "One parameter";
  my $t = $tree->describeTree(length=>$tree->length);                           # Length of new tree must be same as old tree
  $t->first->copy($tree->first);                                                # Load new descriptor from original descriptor
  $t                                                                            # Return new descriptor
 }

sub Nasm::X86::Tree::copyDescriptor($$)                                         # Copy the description of one tree into another.
 {my ($target, $source) = @_;                                                   # The target of the copy, the source of the copy
  @_ == 2 or confess "Two parameters";
  $target->first->copy($source->first);                                         # Load the target from the source
  $target                                                                       # Return target
 }

sub Nasm::X86::Tree::down($)                                                    # Use the current B<find> result held in B<data> to position on the referenced subtree at the next level down.
 {my ($tree) = @_;                                                              # Tree descriptor which has just completed a successful find
  @_ == 1 or confess "One parameter";
  If $tree->data == 0,
  Then
   {PrintErrTraceBack "Invalid sub tree offset";
   };
  $tree->first->copy($tree->data);                                              # The next sub tree down is addressed by the B<data> field of the tree descriptor
  $tree                                                                         # Return original descriptor
 }

sub Nasm::X86::Tree::cloneAndDown($)                                            # Use the current B<find> result held in B<data> to position a new sub tree on the referenced subtree at the next level down.
 {my ($tree) = @_;                                                              # Tree descriptor which has just completed a successful find
  @_ == 1 or confess "One parameter";
  my $t = $tree->describeTree;                                                  # Clone the supplied tree
  $t->first->copy($tree->data);                                                 # The next sub tree down is addressed by the B<data> field of the tree descriptor
  $t                                                                            # Return original descriptor
 }

sub Nasm::X86::Tree::copyDescription($)                                         #P Make a copy of a tree descriptor.
 {my ($tree) = @_;                                                              # Tree descriptor
  my $t = $tree->describeTree;

  $t->data   ->copy($tree->data );                                              # Variable containing the last data found
# $t->debug  ->copy($tree->debug);                                              # Write debug trace if true
  $t->first  ->copy($tree->first);                                              # Variable addressing offset to first block of keys.
  $t->found  ->copy($tree->found);                                              # Variable indicating whether the last find was successful or not
# $t->index  ->copy($tree->index);                                              # Index of key in last node found
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

sub Nasm::X86::Tree::rootFromFirst($$%)                                         #P Return a variable containing the offset of the root block of a tree from the first block when held in a zmm register.
 {my ($tree, $zmm, %options) = @_;                                              # Tree descriptor, number of zmm containing first block, options
  @_ >= 2 or confess "Two or more parameters";

  dFromZ $zmm, $tree->rootOffset, %options;
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

sub Nasm::X86::Tree::incSize($)                                                 #P Increment the size of a tree.
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess "One parameter";
  $tree->firstFromMemory(1);
  $tree->incSizeInFirst (1);
  $tree->firstIntoMemory(1);
 }

sub Nasm::X86::Tree::decSizeInFirst($$)                                         #P Decrement the size field in the first block of a tree when the first block is held in a zmm register.
 {my ($tree, $zmm) = @_;                                                        # Tree descriptor, number of zmm containing first block
  @_ == 2 or confess "Two parameters";
  my $s = dFromZ $zmm, $tree->sizeOffset;

  if ($DebugMode)
   {If $s == 0,
    Then
     {PrintErrTraceBack "Cannot decrement zero length tree";
     };
   }

  $tree->sizeIntoFirst($zmm, $s-1);
 }

sub Nasm::X86::Tree::decSize($)                                                 #P Decrement the size of a tree.
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess "One parameter";
  $tree->firstFromMemory(1);
  $tree->decSizeInFirst (1);
  $tree->firstIntoMemory(1);
 }

sub Nasm::X86::Tree::size($)                                                    # Return in a variable the number of elements currently in the tree.
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess "One parameter";
  my $F = zmm1;
  $tree->firstFromMemory($F);
  my $s = $tree->sizeFromFirst($F);
  $s->name = q(size of tree);
  $s
 }

sub Nasm::X86::Tree::allocBlock($$$$)                                           #P Allocate a keys/data/node block and place it in the numbered zmm registers.
 {my ($tree, $K, $D, $N) = @_;                                                  # Tree descriptor, numbered zmm for keys, numbered zmm for data, numbered zmm for children
  @_ == 4 or confess "4 parameters";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    my $t = $$s{tree};                                                          # Tree
    my $a = $t->area;                                                           # Area

    my ($k, $d, $n) = $a->allocZmmBlock3;                                       # Keys, data, children

    $t->putLoop($d, $K);                                                        # Set the link from key to data
    $t->putLoop($n, $D);                                                        # Set the link from data to node
    $t->putLoop($t->first, $N);                                                 # Set the link from node to tree first block
    $$p{address}->copy($k);                                                     # Address of block
   } structures => {tree => $tree},
     parameters => [qw(address)],
     name       =>
     qq(Nasm::X86::Tree::allocBlock-${K}-${D}-${N}-$$tree{length});             # Create a subroutine for each combination of registers encountered

  $s->inline
   (structures => {tree => $tree},
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

sub Nasm::X86::Tree::upFromData($$)                                             #P Up from the data zmm in a block in a tree.
 {my ($tree, $zmm) = @_;                                                        # Tree descriptor, number of zmm containing data block
  @_ == 2 or confess "Two parameters";
  dFromZ $zmm, $tree->up;
 }

sub Nasm::X86::Tree::upIntoData($$$)                                            #P Up into the data zmm in a block in a tree.
 {my ($tree, $value, $zmm) = @_;                                                # Tree descriptor, variable containing value to put, number of zmm containing first block
  @_ == 3 or confess "Three parameters";
  $value->dIntoZ($zmm, $tree->up);
 }

sub Nasm::X86::Tree::lengthFromKeys($$%)                                        #P Get the length of the keys block in the numbered zmm and return it as a variable.
 {my ($t, $zmm, %options) = @_;                                                 # Tree descriptor, zmm number, options
  @_ >= 2 or confess "Two or more parameters";

  bFromZ($zmm, $t->lengthOffset, %options);                                     # The length field as a variable
 }

sub Nasm::X86::Tree::lengthIntoKeys($$$)                                        #P Get the length of the block in the numbered zmm from the specified variable.
 {my ($t, $zmm, $length) = @_;                                                  # Tree, zmm number, length variable
  @_ == 3 or confess "Three parameters";
  ref($length) or confess dump($length);
  $length->bIntoZ($zmm, $t->lengthOffset)                                       # Set the length field
 }

sub Nasm::X86::Tree::incLengthInKeys($$)                                        #P Increment the number of keys in a keys block or complain if such is not possible.
 {my ($t, $K) = @_;                                                             # Tree, zmm number
  @_ == 2 or confess "Two parameters";
  my $l = $t->lengthOffset;                                                     # Offset of length bits
  bRegFromZmm rbx, $K, $l;                                                      # Length

  if ($DebugMode)                                                               # With checking
   {Cmp bl, $t->length;
    IfLt
    Then
     {Inc rbx;
      bRegIntoZmm rbx, $K, $l;
     },
    Else
     {PrintErrTraceBack "Cannot increment length of block beyond ".$t->length;
     };
   }
  else                                                                          # Without checking
   {Inc rbx;
    bRegIntoZmm rbx, $K, $l;
   }
 }

sub Nasm::X86::Tree::decLengthInKeys($$)                                        #P Decrement the number of keys in a keys block or complain if such is not possible.
 {my ($t, $K) = @_;                                                             # Tree, zmm number
  @_ == 2 or confess "Two parameters";
  my $l = $t->lengthOffset;                                                     # Offset of length bits
  ClearRegisters r15;
  bRegFromZmm rbx, $K, $l;                                                      # Length

  if ($DebugMode)                                                               # With checking
   {Cmp bl, 0;
    IfGt
    Then
     {Dec rbx;
      bRegIntoZmm rbx, $K, $l;
     },
    Else
     {PrintErrTraceBack "Cannot decrement length of block below 0";
     };
   }
  else                                                                          # Without checking
   {Dec rbx;
    bRegIntoZmm rbx, $K, $l;
   }
 }

sub Nasm::X86::Tree::leafFromNodes($$%)                                         #P Return a variable containing true if we are on a leaf.  We determine whether we are on a leaf by checking the offset of the first sub node.  If it is zero we are on a leaf otherwise not.
 {my ($tree, $zmm, %options) = @_;                                              # Tree descriptor, number of zmm containing node block, options
  @_ >= 2 or confess "Two or more parameters";
  if ($options{set})                                                            # Register version
   {dFromZ $zmm, 0, %options;
   }
  else                                                                          # Variable version
   {my $n = dFromZ $zmm, 0;                                                     # Get first node
    my $l = V leaf => 0;                                                        # Return a variable which is non zero if  this is a leaf
    If $n == 0, Then {$l->copy(1)};                                             # Leaf if the node is zero
    return $l                                                                   # Variable containing result
   }
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

sub Nasm::X86::Tree::maskForFullKeyArea                                         #P Place a mask for the full key area in the numbered mask register.
 {my ($tree, $maskRegister) = @_;                                               # Tree description, mask register
  my $m = registerNameFromNumber $maskRegister;
  ClearRegisters $m;                                                            # Zero register
  Knotq $m, $m;                                                                 # Invert to fill with ones
  Kshiftrw $m, $m, 2;                                                           # Mask with ones in the full key area
 }

sub Nasm::X86::Tree::maskForFullNodesArea                                       #P Place a mask for the full nodes area in the numbered mask register.
 {my ($tree, $maskRegister) = @_;                                               # Tree description, mask register
  my $m = registerNameFromNumber $maskRegister;
  ClearRegisters $m;                                                            # Zero register
  Knotq $m, $m;                                                                 # Invert to fill with ones
  Kshiftrw $m, $m, 1;                                                           # Mask with ones in the full key area
 }

sub Nasm::X86::Tree::getBlock($$$$$)                                            #P Get the keys, data and child nodes for a tree node from the specified offset in the area for the tree.
 {my ($tree, $offset, $K, $D, $N) = @_;                                         # Tree descriptor, offset of block as a variable, numbered zmm for keys, numbered data for keys, numbered zmm for nodes
  @_ == 5 or confess "Five parameters";
  my $a = $tree->area;                                                          # Underlying area

  if (ref($offset) =~ m(Variable))                                              # Using variables
   {$a->getZmmBlock($offset,  $K);                                              # Get the keys block
    my $data = $tree->getLoop($K);                                              # Get the offset of the corresponding data block
    $a->getZmmBlock($data,    $D);                                              # Get the data block
    my $node = $tree->getLoop($D);                                              # Get the offset of the corresponding node block
    $a->getZmmBlock($node,    $N);                                              # Get the node block
   }
  else                                                                          # Using registers
   {my $A = rsi; my $O = rdi;
    $a->address->setReg($A);

    Vmovdqu64 zmm($K), "[$A+$offset]";                                          # Read keys from memory
    Mov edi, "[$A+$offset+$$tree{loop}]";                                       # Loop offset

    Vmovdqu64 zmm($D), "[$A+rdi]";                                              # Read data from memory
    Mov edi, "[$A+rdi+$$tree{loop}]";                                           # Loop nodes offset

    Vmovdqu64 zmm($N), "[$A+rdi]";                                              # Read from memory
   }
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

sub Nasm::X86::Tree::firstNode($$$$)                                            #P Return as a variable the last node block in the specified tree node held in a zmm.
 {my ($tree, $K, $D, $N) = @_;                                                  # Tree definition, key zmm, data zmm, node zmm for a node block
  @_ == 4 or confess "Four parameters";

  dFromZ($N, 0)
 }

sub Nasm::X86::Tree::lastNode($$$$)                                             #P Return as a variable the last node block in the specified tree node held in a zmm.
 {my ($tree, $K, $D, $N) = @_;                                                  # Tree definition, key zmm, data zmm, node zmm for a node block
  @_ == 4 or confess "Four parameters";

  dFromZ($N, $tree->lengthFromKeys($K) * $tree->width)
 }

sub Nasm::X86::Tree::relativeNode($$$$$)                                        #P Return as a variable a node offset relative (specified as ac constant) to another offset in the same node in the specified zmm.
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
   {if ($DebugMode)                                                             # With checking
     {Cmp r15, 0;
      IfEq Then{PrintErrTraceBack "Cannot get offset before first offset"};
     }
    Sub r15, 1;                                                                 # Set flags
   }
  if ($relative > 0)
   {if ($DebugMode)                                                             # With checking
     {Cmp r15, $tree->length;
      IfGt Then{PrintErrTraceBack "Cannot get offset beyond last offset"};
     }
    Add r15, 1;                                                                 # Set flags
   }
  my $r = dFromZ $N, V(offset => r15) * $tree->width;                           # Select offset
  PopR;

  $r
 }

sub Nasm::X86::Tree::nextNode($$$$)                                             #P Return as a variable the next node block offset after the specified one in the specified zmm.
 {my ($tree, $offset, $K, $N) = @_;                                             # Tree definition, offset, key zmm, node zmm
  @_ == 4 or confess "Four parameters";
  $tree->relativeNode($offset, +1, $K, $N);
 }

sub Nasm::X86::Tree::prevNode($$$$)                                             #P Return as a variable the previous node block offset after the specified one in the specified zmm.
 {my ($tree, $offset, $K, $N) = @_;                                             # Tree definition, offset, key zmm, node zmm
  @_ == 4 or confess "Four parameters";
  $tree->relativeNode($offset, -1, $K, $N);
 }

sub Nasm::X86::Tree::indexNode($$$$)                                            #P Return, as a variable, the point mask obtained by testing the nodes in a block for specified offset. We have to supply the keys as well so that we can find the number of nodes. We need the number of nodes so that we only search the valid area not all possible node positions in the zmm.
 {my ($tree, $offset, $K, $N) = @_;                                             # Tree definition, key as a variable, zmm containing keys, comparison from B<Vpcmp>
  @_ == 4 or confess "Four parameters";
  my $l = $tree->lengthFromKeys($K);                                            # Current length of the keys block

  my $A = $K == 1 ? 0 : 1;                                                      # The broadcast facility 1 to 16 does not seem to work reliably so we load an alternate zmm

  $offset->setReg(rdi);                                                         # The offset we are looking for
  Vpbroadcastd zmm($A), edi;                                                    # Load offset to test
  Vpcmpud k1, zmm($N, $A), $Vpcmp->eq;                                          # Check for nodes equal to offset
  $l->setReg(rcx);                                                              # Create a mask of ones that matches the width of a key node in the current tree.
  Mov   rsi, 2;                                                                 # A one in position two because the number of nodes is always one more than the number of keys
  Shl   rsi, cl;                                                                # Position the one at end of nodes block
  Dec   rsi;                                                                    # Reduce to fill block with ones
  Kmovq rdi, k1;                                                                # Matching nodes
  And   rsi, rdi;                                                               # Matching nodes in mask area
  V index => rsi;                                                               # Save result as a variable
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

        if ($DebugMode)                                                         # With checking
         {If $plp == 0,                                                         # Zero implies that the left child is not registered in its parent
          Then
           {PrintErrTraceBack "Cannot find left node in parent";
           };
         }

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
         {my $r = $plp << K(one => 1);                                          # The position of the node to the right known to exist because we are not currently on the last node
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
            $t->freeBlock($P, $PK, $PD, $PN);                                   # The parent is no longer required because the left node s the new root
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
     name => qq(Nasm::X86::Tree::expand-$$tree{length});

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
   } name =>
     qq(Nasm::X86::Tree::overWriteKeyDataTreeInLeaf-$K-$D-$$tree{length}),      # Different variants for different blocks of registers.
     structures => {tree=>$tree},
     parameters => [qw(point key data subTree)];

  $s->inline
   (structures => {tree  => $tree},
    parameters => {key   => $IK, data => $ID,
                   point => $point, subTree => $subTree});
 } # overWriteKeyDataTreeInLeaf

#D2 Insert                                                                      # Insert a key into the tree.

sub Nasm::X86::Tree::indexXX($$$$$%)                                            #P Return, as a variable, the mask obtained by performing a specified comparison on the key area of a node against a specified key.
 {my ($tree, $key, $K, $cmp, $inc, %options) = @_;                              # Tree definition, key to search for as a variable or a zmm containing a copy of the key to be searched for in each slot, zmm containing keys, comparison from B<Vpcmp>, whether to increment the result by one, options
  @_ >= 5 or confess "Five or more parameters";

  my $r = $options{set} // rsi;                                                 # Target register supplied or implied
  confess "Cannot use rdi as a target:" if $r eq rdi;

  $tree->lengthFromKeys($K, set=>rdi);                                          # Current length of the keys block
  my $masks = Rq(map {2**$_ -1} 0..15);                                         # Mask for each length
  Mov $r, "[$masks+rdi*8]";                                                     # Load mask address

  my $A = sub                                                                   # Zmm containing key to test
   {return $key unless ref $key;                                                # Zmm already contains keys
    my $A = $K == 1 ? 0 : 1;                                                    # Choose a free zmm to load the keys into
    $key->setReg(rdi);                                                          # Set key
    Vpbroadcastd zmm($A), edi;                                                  # Load key to test
    $A                                                                          # Return zmm loaded with key to test
   }->();

  Vpcmpud k1, zmm($K, $A), $cmp;                                                # Check keys from memory broadcast
  Kmovq rdi, k1;                                                                # Matching keys
  And   $r, rdi;                                                                # Matching keys in mask area
  Add   $r, 1 if $inc;                                                          # Add sets flags whereas Inc would not
  V index => rsi unless $options{set};                                          # Save result as a variable unless a target register has been supplied
 }

sub Nasm::X86::Tree::indexEq($$$%)                                              #P Return the  position of a key in a zmm equal to the specified key as a point in a variable.
 {my ($tree, $key, $K, %options) = @_;                                          # Tree definition, key as a variable, zmm containing keys, options
  @_ >= 3 or confess "Three parameters";

  $tree->indexXX($key, $K, $Vpcmp->eq, 0, %options);                            # Check for equal keys from the broadcasted memory
 }

sub Nasm::X86::Tree::insertionPoint($$$%)                                       #P Return the position at which a key should be inserted into a zmm as a point in a variable.
 {my ($tree, $key, $K, %options) = @_;                                          # Tree definition, key as a variable, zmm containing keys, options
  @_ >= 3 or confess "Three or more parameters";

  $tree->indexXX($key, $K, $Vpcmp->le, 1, %options);                            # Check for less than or equal keys
 }

sub Nasm::X86::Tree::insertKeyDataTreeIntoLeaf($$$$$$$$)                        #P Insert a new key/data/sub tree triple into a set of zmm registers if there is room, increment the length of the node and set the tree bit as indicated and increment the number of elements in the tree.
 {my ($tree, $point, $F, $K, $D, $IK, $ID, $subTree) = @_;                      # Tree descriptor, point at which to insert formatted as a one in a sea of zeros, first, key, data, insert key, insert data, sub tree if tree.

  @_ == 8 or confess "Eight parameters";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    my $t = $$s{tree};                                                          # Address tree

    my $point = $$p{point};                                                     # Point at which to insert
    $$p{point}->setReg(rdi);                                                    # Load mask register showing point of insertion.

    Kmovq k3, rdi;                                                              # A sea of zeros with a one at the point of insertion

    $t->maskForFullKeyArea(2);                                                  # Mask for key area

    Kandnq  k1, k3, k2;                                                         # Mask for key area with a hole at the insertion point

    Vpexpandd zmmM($K, 1), zmm($K);                                             # Expand to make room for the value to be inserted
    Vpexpandd zmmM($D, 1), zmm($D);

    $$p{key}  ->setReg(rdi); Vpbroadcastd zmmM($K, 3), edi;                     # Insert value at expansion point
    $$p{data} ->setReg(rdi); Vpbroadcastd zmmM($D, 3), edi;

    $t->incLengthInKeys($K);                                                    # Increment the length of this node to include the inserted value

    $t->insertIntoTreeBits($K, 3, $$p{subTree});                                # Set the matching tree bit depending on whether we were supplied with a tree or a variable

    $t->incSizeInFirst($F);                                                     # Update number of elements in entire tree.
   } name =>
     qq(Nasm::X86::Tree::insertKeyDataTreeIntoLeaf-$F-$K-$D-$$tree{length}),    # Different variants for different blocks of registers.
     structures => {tree=>$tree},
     parameters => [qw(point key data subTree)];

  $s->inline
   (structures => {tree  => $tree},
    parameters => {key   => $IK, data => $ID,
                   point => $point, subTree => $subTree});
 } # insertKeyDataTreeIntoLeaf

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

      my $t    = $$s{tree};                                                     # Tree
      my $area = $t->area;                                                      # Area

      PushR 22...31;
      ClearRegisters 22..31;                                                    # Otherwise we get left over junk

      my $offset = $$p{offset};                                                 # Offset of block in area
      my $split  = $$p{split};                                                  # Indicate whether we split or not
      $t->getBlock($offset, $LK, $LD, $LN);                                     # Load node as left

      my $length = $t->lengthFromKeys($LK);
      If $length < $t->maxKeys,
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
        $t->splitNotRoot    ($r,      $PK, $PD, $PN, $LK,$LD,$LN, $RK,$RD,$RN);
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
     };                                                                         # Insert completed successfully
    PopR;
   }  structures => {tree => $tree},
      parameters => [qw(offset split)],
      name       => qq(Nasm::X86::Tree::splitNode-$$tree{length});

  $s->inline
   (structures => {tree   => $tree},
    parameters => {offset => $offset, split => my $p = V split => 1});

  $p                                                                            # Return a variable containing one if the node was split else zero.
 } # splitNode

sub Nasm::X86::Tree::splitNotRoot($$$$$$$$$$$)                                  #P Split a non root left node pushing its excess right and up.
 {my ($tree, $newRight, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN) = @_;      # Tree definition, variable offset in area of right node block, parent keys zmm, data zmm, nodes zmm, left keys zmm, data zmm, nodes zmm, right keys, data, node zmm
  @_ == 11 or confess "Eleven parameters required";

  my $w         = $tree->width;                                                 # Size of keys, data, nodes
  my $zw        = $tree->zWidthD;                                               # Number of dwords in a zmm
  my $zwn       = $tree->maxNodesZ;                                             # Maximum number of dwords that could be used for nodes in a zmm register.
  my $zwk       = $tree->maxKeysZ;                                              # Maximum number of dwords used for keys/data in a zmm
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

    &$mask("00", $zwk);                                                         # Copy Left node to right node

    Vmovdqu32    zmmM($RK, 7),  zmm($LK);                                       # Copy keys from left to right
    Vmovdqu32    zmmM($RD, 7),  zmm($LD);                                       # Copy data from left to right

    &$mask("0",  $zwn);
    Vmovdqu32    zmmM($RN, 7),  zmm($LN);                                       # Copy nodes from left to right

    &$mask("00", $lw-$zwk,  $lr, -$ll-1);                                       # Compress right data/keys
    Vpcompressd  zmmM($RK, 7),  zmm($RK);                                       # Compress copied right keys
    Vpcompressd  zmmM($RD, 7),  zmm($RD);                                       # Compress right copied data

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
  name       => join('-', qq(Nasm::X86::Tree::splitNotRoot), $$tree{length},
                          $lw, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN);

  $s->inline(
    structures => {tree => $tree},
    parameters => {newRight => $newRight});
 } # splitNotRoot

sub Nasm::X86::Tree::splitRoot($$$$$$$$$$$$)                                    #P Split a non root node into left and right nodes with the left half left in the left node and splitting key/data pushed into the parent node with the remainder pushed into the new right node.
 {my ($tree, $nLeft, $nRight, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN) = @_;# Tree definition, variable offset in area of new left node block, variable offset in area of new right node block, parent keys zmm, data zmm, nodes zmm, left keys zmm, data zmm, nodes zmm, right keys, data , nodes zmm
  @_ == 12 or confess "Twelve parameters required";

  my $w         = $tree->width;                                                 # Size of keys, data, nodes
  my $zw        = $tree->zWidthD;                                               # Number of dwords in a zmm
  my $zwn       = $tree->maxNodesZ;                                             # Maximum number of dwords that could be used for nodes in a zmm register.
  my $zwk       = $tree->maxKeysZ;                                              # Maximum number of dwords used for keys/data in a zmm
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
  name       => join '-', "Nasm::X86::Tree::splitRoot", $$tree{length},
                  $lw, $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN;

  $s->inline
   (structures => {tree => $tree},
    parameters => {newLeft => $nLeft, newRight => $nRight});
 } # splitRoot

sub Nasm::X86::Tree::put($$$)                                                   # Put a variable key and data into a tree. The data could be a tree descriptor to place a sub tree into a tree at the indicated key.
 {my ($tree, $key, $data) = @_;                                                 # Tree definition, key as a variable, data as a variable or a tree descriptor
  @_ == 3 or confess "Three parameters";

  my $dt = ref($data) =~ m(Tree);                                               # We are inserting a sub tree if true

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    Block
     {my ($success) = @_;                                                       # End label
      PushR my ($F, $K, $D, $N, $key) = reverse 27..31;                         # First, keys, data, nodes, search key
      my $t = $$s{tree};
      my $k = $$p{key};
      my $d = $$p{data};
      my $S = $$p{subTree};
      my $a = $t->area;
      $k->setReg(rdi);
      Vpbroadcastd zmm($key), edi;                                              # Load key to test once

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

      my $eq = $t->indexEq($key, $K);                                           # Check for an equal key
      If $eq > 0,                                                               # Equal key found
      Then                                                                      # Overwrite the existing key/data
       {$t->overWriteKeyDataTreeInLeaf($eq, $K, $D, $k, $d, $S);
        $t->putBlock                  ($Q,  $K, $D, $N);
        Jmp $success;
       };

      If $t->lengthFromKeys($K) >= $t->maxKeys,
      Then                                                                      # Split full blocks
       {$t->splitNode($Q);
        Jmp $start;                                                             # Restart the descent now that this block has been split
       };

      If $t->leafFromNodes($N) > 0,
      Then                                                                      # On a leaf
       {my $i = $t->insertionPoint($key, $K);                                   # Find insertion point
        $t->insertKeyDataTreeIntoLeaf($i, $F, $K, $D, $k, $d, $S);
        $t->putBlock                 ($Q, $K, $D, $N);
        $t->firstIntoMemory          ($F);                                      # First back into memory
        Jmp $success;
       };

      my $in = $t->insertionPoint($key, $K);                                    # The position at which the key would be inserted if this were a leaf
      my $next = $in->dFromPointInZ($N);                                        # The node to the left of the insertion point - this works because the insertion point can be upto one more than the maximum number of keys
      if ($text[-1] =~ m(\Amov.*rsi\s*\Z))                                      # Optimize by removing pointless load/unload/load
       {pop @text;
        $Q->getReg(rsi);
       }
      else
       {$Q->copy($next);                                                        # Get the offset of the next node - we are not on a leaf so there must be one
       }
      Jmp $descend;                                                             # Descend to the next level
     };
    PopR;
   } name => qq(Nasm::X86::Tree::put-$$tree{length}),
     structures => {tree=>$tree},
     parameters => [qw(key data subTree)];

  Block                                                                         # Place low keys if requested and possible
   {my ($end) = @_;                                                             # End of block
    if ($tree->lowKeys)                                                         # only if low key placement is enabled for this tree. Small trees benefit more than large trees from this optimization.
     {my $co = $tree->fcControl / $tree->width;                                 # Offset of low keys control word in dwords
      confess "Should be three" unless $co == 3;

      if ($key->constant)                                                       # The key is a constant so we can check if it should go in the first cache
       {my $k = $key->expr;                                                     # Key value
        if ($k >= 0 and $k < $tree->fcDWidth)                                   # Key is small enough to go in cache
         {my $F = 1;                                                            # Place first block in this zmm
          $tree->firstFromMemory($F);                                           # Load first block
          my $p = $k * $tree->width + $tree->fcArray;                           # Offset of dword in bytes
          ($dt ? $data->first : $data)->dIntoZ($F, $p);                         # Save dword - either the supplied data or the offset of the sub tree
          if ($tree->lowKeys == 1)                                              # Only if low key placement is enabled for this tree. Small trees benefit more than large trees from this optimization.
           {PushR my $control = r15;                                            # Copy of the control dword
            Pextrd $control."d", xmm1, $co;                                     # Get the control dword
            my $b = $k+$tree->fcPresent;                                        # Present bit
            my $B = $k+$tree->fcTreeBits;                                       # Tree bit
            Bts $control, $b;                                                   # Set present bit
            IfNc
            Then                                                                # Not previously present so increase length
             {$tree->incSizeInFirst(zmm $F);                                    # Increment the size field in the first block of a tree when the first block is held in a zmm register.
             };                                                                 # Putting the previous code inline will enable us to use a free register and thus avoid the PushR PopR
            if ($dt)                                                            # Tree
             {Bts $control, $B;                                                 # Set tree bit
             }
            else                                                                # Not a tree
             {Btr $control, $B;                                                 # Clear tree bit
             }
            Pinsrd xmm1, $control."d", $co;                                     # Save control word
            PopR;
           }
          $tree->firstIntoMemory($F);                                           # Save updated first block
          Jmp $end;                                                             # Successfully saved
         }
       }

      else                                                                      # The key is a variable, we check if it should go in the first cache
       {ifAnd [sub {$key < $tree->fcDWidth}, sub {$key >= 0}],                  # Key in range
        Then                                                                    # Less than the upper limit
         {my $F = 1;                                                            # Place first block in this zmm
          $tree->firstFromMemory($F);                                           # Load first block
          my $p = $key * $tree->width + $tree->fcArray;                         # Offset of dword in bytes
          ($dt ? $data->first : $data)->dIntoZ($F, $p);                         # Save dword - either the supplied data or the offset of the sub tree

          if ($tree->lowKeys == 1)                                              # Only if low key placement is enabled for this tree. Small trees benefit more than large trees from this optimization.
           {PushR my $bit = r14, my $control = r15;                             # Copy of the control dword
            Pextrd $control."d", xmm1, $co;                                     # Get the control dword
            my $b = $key+$tree->fcPresent;                                      # Present bit
            my $B = $key+$tree->fcTreeBits;                                     # Tree bit
            $b->setReg($bit);                                                   # Bit to set
            Bts $control, $bit;                                                 # Set bit and place old value in carry
            IfNc
            Then                                                                # Not previously present so increase length
             {$tree->incSizeInFirst(zmm $F);                                    # Increment the size field in the first block of a tree when the first block is held in a zmm register.
             };                                                                 # Putting the previous code inline will enable us to use a free register and thus avoid the PushR PopR
            $B->setReg($bit);                                                   # Bit to set
            if ($dt)                                                            # Tree
             {Bts $control, $bit;                                               # Set tree bit
             }
            else                                                                # Not a tree
             {Btr $control, $bit;                                               # Clear tree bit
             }
            Pinsrd xmm1, $control."d", $co;                                     # Save control word
            PopR;
           }
          $tree->firstIntoMemory($F);                                           # Save updated first block
          Jmp $end;                                                             # Successfully saved
         };
       }
     }

    if ($dt)                                                                    # Put a sub tree
     {$s->call(structures => {tree    => $tree},
               parameters => {key     => $key,
                              data    => $data->first,
                              subTree => K(key => 1)});
     }
    else                                                                        # Not a usb tree
     {$s->call(structures => {tree    => $tree},
               parameters => {key     => $key,
                              data    => $data,
                              subTree => K(zero => 0)});
     }
   }
 } # put

#D2 Find                                                                        # Find a key in the tree. Trees have dword integer keys and so can act as arrays as well.

sub Nasm::X86::Tree::zero($)                                                    #P Zero the return fields of a tree descriptor.
 {my ($tree) = @_;                                                              # Tree descriptor
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
    my $F = zmm1, my $K = zmm2, my $D = zmm3, my $N = zmm4, my $key = zmm5;     # We are boldly assuming that these registers are not being used independently
    PushR my $Q = r15, my $loop = r14, my $eqr = r13;

    Block
     {my ($success) = @_;                                                       # Short circuit if ladders by jumping directly to the end after a successful push

      my $t = $$s{tree};                                                        # Tree to search
      $t->zero;                                                                 # Clear search fields

      $t->key->copy(my $k = $$p{key});                                          # Copy in key so we know what was searched for

      $t->firstFromMemory      ($F);                                            # Load first block

      $t->rootFromFirst($F, set => $Q);                                         # Start the search from the root

      Cmp $Q, 0;
      Je $success;                                                              # Empty tree so we have not found the key
      $k->setReg(rdi);
      Vpbroadcastd zmm($key), edi;                                              # Load key to test once

      uptoNTimes                                                                # Step down through tree
       {my (undef, $start) = @_;
        $t->getBlock($Q, $K, $D, $N);                                           # Get the keys/data/nodes

        $t->indexEq($key, $K, set=>$eqr);                                       # The position of a key in a zmm equal to the specified key as a point in a variable.
        IfNz                                                                    # Result mask is non zero so we must have found the key
        Then
         {dFromPointInZ $eqr, $D, set=>rsi;                                     # Get the corresponding data
          $t->data  ->copy(rsi);                                                # Data associated with the key
          $t->found ->copy($eqr);                                               # Show found
          $t->offset->copy($Q);                                                 # Offset of the containing block
          $t->getTreeBit($K, $eqr, set => rdx);                                 # Get corresponding tree bit
          $t->subTree->copy(rdx);                                               # Save corresponding tree bit
          Jmp $success;                                                         # Return
         };

        $t->leafFromNodes($N, set=>rsi),                                        # Check whether this is a leaf by looking at the first sub node - if it is zero this must be a leaf as no node van have a zero offset in an area
        Cmp rsi, 0;                                                             # Leaf if zero
        Jz $success;                                                            # Return

        $t->insertionPoint($key, $K, set => rsi);                               # The insertion point if we were inserting
        dFromPointInZ     (rsi,  $N, set =>  $Q);                               # Get the corresponding offset to the next sub tree
        Sub $loop, 1;
        Jnz $start;                                                             # Keep going but not for ever
       } $loop, 99;                                                             # Loop a limited number of times
      PrintErrTraceBack "Stuck in find";                                        # We seem to be looping endlessly
     };                                                                         # Find completed successfully

    PopR;
   } parameters => [qw(key)],
     structures => {tree=>$tree},
     name       => qq(Nasm::X86::Tree::find-$$tree{length});

  Block                                                                         # Find low keys if possible
   {my ($end) = @_;                                                             # End of block
    if ($tree->lowKeys)                                                         # only if low key placement is enabled for this tree. Small tres benefit nore than large trees from this optimization.
     {my $co = $tree->fcControl / $tree->width;                                 # Offset of low keys control word in dwords
      confess "Should be three" unless $co == 3;

      if ($key->constant)                                                       # The key is a constant so we can check if it should go in the first cache
       {my $k = $key->expr;                                                     # Key is small enough to go in cache
        if ($k >= 0 and $k < $tree->fcDWidth)                                   # Key is small enough to go in cache
         {if ($tree->lowKeys == 1)                                              # The low keys are behaving just like normal keys
           {my $F = zmm1;                                                       # Place first block in this zmm
            $tree->firstFromMemory($F);                                         # Load first block
            my $o = $k * $tree->width + $tree->fcArray;                         # Offset in bytes of data
            my $d = dFromZ($F, $o);                                             # Get dword representing data
            PushR my $control = r15;                                            # Copy of the control dword
            Pextrd $control."d", xmm1, $co;                                     # Get the control dword
            my $b = $k+$tree->fcPresent;                                        # Present bit
            my $B = $k+$tree->fcTreeBits;                                       # Tree bit
            Bt $control, $b;                                                    # Present bit for this element
            IfC
            Then                                                                # Found
             {$tree->found->copy(1);                                            # Show as found
              $tree->data->copy($d);                                            # Save found data as it is valid
             },
            Else                                                                # Not found
             {$tree->found->copy(0);                                            # Show as not found
             };
            Bt $control, $B;                                                    # Tree bit
            IfC
            Then                                                                # Sub tree
             {$tree->subTree->copy(1);
             },
            Else                                                                # Not sub tree
             {$tree->subTree->copy(0);
             };
            PopR;
           }
          else                                                                  # The low keys are always present, not null and are not known to be represent sub trees
           {my $F = zmm1;                                                       # Place first block in this zmm
            $tree->firstFromMemory($F);                                         # Load first block
            my $o = $k * $tree->width + $tree->fcArray;                         # Offset in bytes of data
            dFromZ($F, $o, set=>$tree->data);                                   # Get dword representing data and place it in the indicated variable
           }
          Jmp $end;                                                             # Successfully saved
         }
       }

      else                                                                      # The key is a variable, we check if it should go in the first cache
       {ifAnd [sub {$key < $tree->fcDWidth}, sub {$key >= 0}],                  # Key in range
        Then                                                                    # Less than the upper limit
         {if ($tree->lowKeys == 1)                                              # The low keys are behaving just like normal keys
           {my $F = zmm1;                                                       # Place first block in this zmm
            $tree->firstFromMemory($F);                                         # Load first block
            my $o = $key * $tree->width + $tree->fcArray;                       # Offset if dword containing data
            my $d = dFromZ($F, $o);                                             # Get dword representing data
            PushR my $bit = r14, my $control = r15;                             # Bit to select, Copy of the control dword
            Pextrd $control."d", xmm1, $co;                                     # Get the control dword
            my $b = $key+$tree->fcPresent;                                      # Present bit
            my $B = $key+$tree->fcTreeBits;                                     # Tree bit
            $b->setReg($bit);
            Bt $control, $bit;                                                  # Present bit for this element
            IfC
            Then                                                                # Found
             {$tree->found->copy(1);                                            # Show as found
              $tree->data->copy($d);                                            # SAve found data as it is valid
             },
            Else                                                                # Not found
             {$tree->found->copy(0);                                            # Show as not found
             };
            $B->setReg($bit);
            Bt $control, $bit;                                                  # Tree bit
            IfC
            Then                                                                # Sub tree
             {$tree->subTree->copy(1);
             },
            Else                                                                # Not sub tree
             {$tree->subTree->copy(0);
             };
            PopR;
           }
          else                                                                  # The low keys are always present, not null and are not known to be represent sub trees
           {my $F = zmm1;                                                       # Place first block in this zmm
            $tree->firstFromMemory($F);                                         # Load first block
            my $o = $key * $tree->width + $tree->fcArray;                       # Offset in bytes of data
            dFromZ($F, $o, set=>$tree->data);                                   # Get dword representing data and place it in the indicated variable
           }
          Jmp $end;                                                             # Successfully saved
         };
       }
     }

    $s->inline(structures=>{tree => $tree}, parameters=>{key => $key});
   };
 } # find

sub Nasm::X86::Tree::findFirst($)                                               # Find the first element in a tree and set B<found>|B<key>|B<data>|B<subTree> to show the result.
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
       {$t->found->copy(0);                                                     # Could not find anything
        Jmp $success
       };

      my $root = $t->rootFromFirst($F);                                         # Root of tree
      $t->getBlock($root, $K, $D, $N);                                          # Load root

      K(loop => 99)->for(sub                                                    # Step down through the tree a reasonable number of times
       {my ($i, $start, $next, $end) = @_;

        If $t->leafFromNodes($N) > 0,                                           # Leaf node means we have arrived
        Then
         {my $k = dFromZ($K, 0);
          my $d = dFromZ($D, 0);
          my $b = $t->getTreeBit($K, K key => 1);
          $t->found  ->copy(1);
          $t->key    ->copy($k);
          $t->data   ->copy($d);
          $t->subTree->copy($b);
          Jmp $success
         };

        my $n = dFromZ($N, 0);
        $t->getBlock($n, $K, $D, $N);
       });
      PrintErrTraceBack "Stuck looking for first";
     };                                                                         # Find completed successfully
    PopR;
   } structures=>{tree=>$tree},
     name => qq(Nasm::X86::Tree::findFirst-$$tree{length});

  $s->call(structures=>{tree => $tree});
 } # findFirst

sub Nasm::X86::Tree::findLast($)                                                # Find the last key in a tree - crucial for stack like operations.
 {my ($tree) = @_;                                                              # Tree descriptor
  @_ == 1 or confess "One parameter";
  confess "Not allowed with lowKeys == 2"                                       # Only basic low keys allowed if low keys being used
    if $tree->lowKeys && $tree->lowKeys != 1;

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    Block
     {my ($success) = @_;                                                       # Successfully completed

      my $t = $$s{tree}->zero;                                                  # Tree to search

      PushR my $F = 31, my $K = 30, my $D = 29, my $N = 28;

      $t->firstFromMemory($F);                                                  # Update the size of the tree

      my $size = $t->sizeFromFirst($F);                                         # Number of entries in tree
      If $size > 0,                                                             # Non empty tree
      Then
       {if ($tree->lowKeys)                                                     # Low keys in play so the root node might not be present if all the data is now in the first block
         {PushR my $z = r13, my $bit = r14, my $present = r15;                  # The current size fo the tree, the index of the present bit for the highest remaining key, the present bits
          my $i = V key => 0;                                                   # Assume we are not in the first block
          wFromZ $F, $t->fcPresentOff, set=>$present;                           # Present bits
          Popcnt $bit, $present;                                                # Number of entries in first block
          $size->setReg($z);
          Cmp $bit, $z;                                                         # We are in the first block entries if the number of keys present in the first block is the same as the current size of the tree
          IfEq
          Then
           {Bsr $bit, $present;                                                 # Position of highest key found by reverse scan to find index of highest bit set
            $t->key->getReg($bit);                                              # Show key found
            Shl $bit, 2;                                                        # Position in first block array of dwords
            Add $bit, $t->fcArray;                                              # Position in first block
            dFromZ($F, V(position => $bit), set => $t->data);                   # Save data
            $t->found->getReg($present);                                        # Show found
            $i->copy(1);                                                        # We are in the first block
           };
          PopR;
          If $i > 0, Then {Jmp $success};                                       # Successfully found
         }

        my $root = $t->rootFromFirst($F);                                       # Root of tree
        $t->getBlock($root, $K, $D, $N);                                        # Load root

        K(loop => 99)->for(sub                                                  # Step down through the tree a reasonable number of times
         {my ($i, $start, $next, $end) = @_;
          my $l = $t->lengthFromKeys($K);

          If $t->leafFromNodes($N) > 0,                                         # Leaf node means we have arrived
          Then
           {my $o  = ($l - 1) * $t->width;
            my $k = dFromZ($K, $o);
            my $d = dFromZ($D, $o);
            my $b = $t->getTreeBit($K, $l);

            $t->found  ->copy(1);
            $t->key    ->copy($k);
            $t->data   ->copy($d);
            $t->subTree->copy($b);
            Jmp $success
           };

          my $O = $l * $t->width;
          my $n = dFromZ($N, $O);                                               # Step down to the next level
          $t->getBlock($n, $K, $D, $N);
         });
        PrintErrTraceBack "Stuck looking for last";
       };
     };                                                                         # Find completed successfully
    PopR;
   } structures=>{tree=>$tree},
     name => qq(Nasm::X86::Tree::findLast-$$tree{length});

  $s->call(structures=>{tree => $tree});                                        # Inline causes very long assembly times so we call instead.
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
     };                                                                         # Find completed successfully
    PopR;
   } parameters => [qw(key)],
     structures => {tree=>$tree},
     name       => qq(Nasm::X86::Tree::findNext-$$tree{length});

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
   } parameters => [qw(key)],
     structures => {tree=>$tree},
     name       => qq(Nasm::X86::Tree::findPrev-$$tree{length});

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

sub Nasm::X86::Tree::findSubTree($$)                                            # Find a key in the specified tree and create a sub tree from the data field if possible.
 {my ($tree, $key) = @_;                                                        # Tree descriptor, key as a dword
  @_ == 2 or confess "Two parameters";

  my $t = $tree->describeTree;                                                  # The sub tree we are attempting to load
     $t->first->copy($tree->first);                                             # Position on the tree

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition
    my $t = $$s{tree};
    $t->find($$p{key});                                                         # Find the key

    ifAnd [sub{$t->found > 0}, sub{$t->subTree > 0}],                           # Make the found data the new  tree
    Then
     {$t->first->copy($t->data);                                                # Copy the data variable to the first variable without checking whether it is valid
      $t->found->copy(1);
     },
    Else
     {$t->first->copy(-1);                                                      # Remove any hint of a tree
      $t->found->copy(0);                                                       # We did not find the sub tree
     };
    } parameters => [qw(key)],
      structures => {tree=>$t},
      name       => qq(Nasm::X86::Tree::findSubTree);

  $s->call(structures=>{tree => $t}, parameters=>{key => $key});

  $t
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
     };                                                                         # Insert completed successfully
    PopR;
   } structures => {tree => $tree},
     parameters => [qw(node offset)],
     name       => $dir==0 ? qq(Nasm::X86::Tree::leftMost-$$tree{length}) :
                             qq(Nasm::X86::Tree::rightMost-$$tree{length});

  $s->call
   (structures => {tree=>$tree},
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
     };                                                                         # Insert completed successfully
    PopR;
   }  structures => {tree => $tree},
      parameters => [qw(node depth)],
      name       => qq(Nasm::X86::Tree::depth-$$tree{length});

  $s->call(structures => {tree => $tree->copyDescription},
           parameters => {node => $node, depth => my $d = V depth => 0});

  $d
 } # depth

##D2 Sub trees                                                                   # Construct trees of trees - all private.

sub Nasm::X86::Tree::isTree($$$)                                                #P Set the Zero Flag to oppose the tree bit in the numbered zmm register holding the keys of a node to indicate whether the data element indicated by the specified register is an offset to a sub tree in the containing area or not.
{my ($t, $zmm, $point) = @_;                                                    # Tree descriptor, numbered zmm register holding the keys for a node in the tree, register showing point to test
 @_ == 3 or confess "Three parameters";

  my $z = registerNameFromNumber $zmm;                                          # Full name of zmm register
  my $o = $t->treeBits;                                                         # Bytes from tree bits to end of zmm
  my $w = $t->zWidth;                                                           # Size of zmm register
  Vmovdqu64    "[rsp-$w]", $z;                                                  # Write beyond stack
  Test $point, "[rsp-$w+$o]";                                                   # Test the tree bit under point
 } # isTree

sub Nasm::X86::Tree::getTreeBit($$$%)                                           #P Get the tree bit from the numbered zmm at the specified point and return it in a variable as a one or a zero.
 {my ($t, $zmm, $point, %options) = @_;                                         # Tree descriptor, register showing point to test, numbered zmm register holding the keys for a node in the tree, options
  @_ >= 3 or confess "Three or more parameters";

  if (ref($point))                                                              # Point is a variable so we will do everything in variables
   {$t->getTreeBits($zmm, rdi);                                                 # Tree bits
    $point->setReg(rsi);
    And rdi, rsi;                                                               # Write beyond stack
    my $r = V treeBit => 0;
    Cmp di, 0;
    IfNe Then {$r->copy(1)};
    return $r
   }
  else                                                                          # Point is a register so we will do everything in registers
   {my $s = $options{set} // rdi;                                               # The register we are going to be set to something other than zero if the tree bit is set
    confess "Target cannot be rsi" if $s eq rsi;
    $t->getTreeBits($zmm, $s);                                                  # Tree bits
    And $s, $point;                                                             # Jnz jumps if the tree bit has been set
   }
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
    if ($DebugMode)                                                             # With checking
     {If $t->leafFromNodes($N) == 0,                                            # If the zero Flag is zero then this is not a leaf
      Then                                                                      # We can only perform this operation on a leaf
       {PrintErrTraceBack "Cannot extract from a non leaf node";
       };
     }

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
   } parameters => [qw(point)],
     structures => {tree=>$tree},
     name       => qq(Nasm::X86::Tree::extract-$K-$D-$N-$$tree{length});

  $s->inline(structures=>{tree => $tree}, parameters=>{point => $point});
 } # extract

sub Nasm::X86::Tree::extractFirst($$$$)                                         #P Extract the first key/data and tree bit at the specified point from the block held in the specified zmm registers and place the extracted data/bit in tree data/subTree.
 {my ($tree, $K, $D, $N) = @_;                                                  # Tree descriptor, keys zmm, data zmm, node zmm
  @_ == 4 or confess "Four parameters";

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    my $t = $$s{tree};                                                          # Tree to search
    $t->leafFromNodes($N);                                                      # Check for a leaf
    if ($DebugMode)                                                             # Checking
     {IfNe                                                                      # If the zero Flag is zero then this is not a leaf
      Then                                                                      # We can only perform this operation on a leaf
       {PrintErrTraceBack "Cannot extract first from a non leaf node";
       };
     }
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
     name => qq(Nasm::X86::Tree::extractFirst-$K-$D-$N-$$tree{length});

  $s->call(structures=>{tree => $tree});
 } # extractFirst

sub Nasm::X86::Tree::mergeOrSteal($$)                                           #P Merge the block at the specified offset with its right sibling or steal from it. If there is no  right sibling then do the same thing but with the left sibling.  The supplied block must not be the root. The key we are looking for must be in the tree key field.
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

    if ($DebugMode)                                                             # Checking
     {If $l == 0,
      Then
       {PrintErrTraceBack "Zero offset in mergeOrSteal";
       };
     }
    $t->getBlock($l, $LK, $LD, $LN);                                            # Get the keys/data/nodes
    my $p = $t->upFromData($LD);                                                # Parent offset

    if ($DebugMode)                                                             # Checking
     {If $p == 0,
      Then
       {PrintErrTraceBack "Cannot mergeOrSteal the root";
       };
     }

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
   } parameters => [qw(offset changed)],
     structures => {tree=>$tree},
     name       => qq(Nasm::X86::Tree::mergeOrSteal-$$tree{length});

  $s->call
   (structures => {tree   => $tree},
    parameters => {offset => $offset, changed => my $changed = V changed => 0});

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
  name       => join('::',
   "Nasm::X86::Tree::stealFromRight",
    $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN, $tree->length),
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
  name       => join('::',
   "Nasm::X86::Tree::stealFromLeft",
    $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN, $tree->length),

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
     #$m->dIntoPointInZ($LN, $pn);                                              # Position parent node in left - not needed because the left and right around the parent key are the left and right node offsets - we should use this fact to update the children of the right node so that their up pointers point to the left node
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
  name       => join('::',
   "Nasm::X86::Tree::merge",
    $PK, $PD, $PN, $LK, $LD, $LN, $RK, $RD, $RN, $tree->length),
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
  name => qq(Nasm::X86::Tree::deleteFirstKeyAndData-$K-$D-$$tree{length}),
  structures => {tree => $tree};

  $s->call(structures => {tree => $tree});

  $tree                                                                         # Chain tree - actual data is in key, data,  subTree, found variables
 }

sub Nasm::X86::Tree::delete($$)                                                 # Find a key in a tree and delete it returning he value of the l=key deleted if found.
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
                my $data    = $t->data->clone("data");
                my $subTree = $t->subTree->clone("data");
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
      PrintErrTraceBack "Stuck looking for leaf" if $DebugMode;
     };                                                                         # Find completed successfully
    PopR;
   } parameters =>[qw(key)],
     structures =>{tree=>$tree},
     name       => qq(Nasm::X86::Tree::delete-$$tree{length});

  Block                    ## Need to detect sub tree or not                    # Delete low keys if possible
   {my ($end) = @_;                                                             # End of block
    if ($tree->lowKeys)                                                         # Only if low key placement is enabled for this tree. Small trees benefit more than large trees from this optimization.
     {my $co = $tree->fcControl / $tree->width;                                 # Offset of low keys control word in dwords
      confess "Should be three" unless $co == 3;

      if ($key->constant)                                                       # The key is a constant so we can check if it should go in the first cache
       {my $k = $key->expr;                                                     # Key is small enough to go in cache
        if ($k >= 0 and $k < $tree->fcDWidth)                                   # Key is small enough to go in cache
         {if ($tree->lowKeys == 1)                                              # The low keys are behaving just like normal keys
           {my $F = zmm1;                                                       # Place first block in this zmm
            $tree->firstFromMemory($F);                                         # Load first block
            my $o = $k * $tree->width + $tree->fcArray;                         # Offset in bytes of data
            my $d = dFromZ($F, $o);                                             # Get dword representing data
            PushR my $control = r15;                                            # Copy of the control dword
            Pextrd $control."d", xmm1, $co;                                     # Get the control dword
            Btr $control, $k+$tree->fcPresent;                                  # Present bit for this element test and then clear it
            IfC
            Then                                                                # Found
             {Pinsrd xmm1, $control."d", $co;                                   # Save control word
              $tree->found->copy(1);                                            # Show as found
              $tree->data->copy($d);                                            # Save found data as it is valid
              Bt $control, $k+$tree->fcTreeBits;                                # Tree bit for this element
              IfC
              Then                                                              # This element represents a sub tree
               {$tree->subTree->copy(1);                                        # Flag as a sub tree
               };
              $tree->decSizeInFirst($F);                                        # Decrement size as we have deleted an element
              $tree->firstIntoMemory($F);                                       # Save first block
             },
            Else                                                                # Not found
             {$tree->found->copy(0);                                            # Show as not found
             };
            PopR;
           }
          else                                                                  # The low keys are always present, not null and are not known to represent sub trees
           {my $F = zmm1;                                                       # Place first block in this zmm
            $tree->firstFromMemory($F);                                         # Load first block
            my $o = $k * $tree->width + $tree->fcArray;                         # Offset in bytes of data
            dFromZ($F, $o, set=>$tree->data);                                   # Get dword representing data and place it in the indicated variable
            K(zero => 0)->dIntoZ($F, $o);                                       # Zero the field as we are ignoring the present bits
           }
          Jmp $end;                                                             # Successfully saved
         }
       }

      else {                                                                    # The key is a variable, we check if it should go in the first cache
        ifAnd [sub {$key < $tree->fcDWidth}, sub {$key >= 0}],                  # Key in range
        Then                                                                    # Less than the upper limit
         {if ($tree->lowKeys == 1)                                              # The low keys are behaving just like normal keys
           {my $F = zmm1;                                                       # Place first block in this zmm
            $tree->firstFromMemory($F);                                         # Load first block
            my $o = $key * $tree->width + $tree->fcArray;                       # Offset if dword containing data
            my $d = dFromZ($F, $o);                                             # Get dword representing data
            PushR my $bit = r14, my $control = r15;                             # Bit to select, Copy of the control dword
            Pextrd $control."d", xmm1, $co;                                     # Get the control dword
            ($key+$tree->fcPresent)->setReg($bit);                              # Present bit
            Btr $control, $bit;                                                 # Present bit for this element - test and reset
            IfC
            Then                                                                # Found
             {Pinsrd xmm1, $control."d", $co;                                   # Save control word
              $tree->found->copy(1);                                            # Show as found
              $tree->data->copy($d);                                            # Save found data as it is valid
              ($key+$tree->fcTreeBits)->setReg($bit);
              Bt $control, $bit;                                                # Tree bit for this element
              IfC
              Then                                                              # This element represents a sub tree
               {$tree->subTree->copy(1);                                        # Flag as a sub tree
               };
              $tree->decSizeInFirst($F);                                        # Decrement size as we have deleted an element
              $tree->firstIntoMemory($F);                                       # Save first block
             },
            Else                                                                # Not found
             {$tree->found->copy(0);                                            # Show as not found
             };
            PopR;
           }
          else                                                                  # The low keys are always present, not null and are not known to be represent sub trees
           {my $F = zmm1;                                                       # Place first block in this zmm
            $tree->firstFromMemory($F);                                         # Load first block
            my $o = $key * $tree->width + $tree->fcArray;                       # Offset in bytes of data
            dFromZ($F, $o, set=>$tree->data);                                   # Get dword representing data and place it in the indicated variable
            K(zero => 0)->dIntoZ($F, $o);                                       # Zero the field as we are ignoring the present bits
           }
          Jmp $end;                                                             # Successfully saved
         };
       }
     }

    #$s->inline(structures=>{tree => $tree}, parameters=>{key => $key});
    $s->call(structures=>{tree => $tree}, parameters=>{key => $key});

    if ($tree->lowKeys and $tree->lowKeys == 1)                                 # Clear tree if it becomes empty as a result of deleting the last low key
     {If $tree->size == 0,
      Then
       {$tree->clear();
       };
     }
   };
 } # delete

sub Nasm::X86::Tree::clear($)                                                   # Delete everything in the tree except the first block recording any memory liberated on the free chain.
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
     name       => qq(Nasm::X86::Tree::clear-$$tree{length});

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

sub Nasm::X86::Tree::free($)                                                    # Free all the memory used by a tree.
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

  $tree->found->copy(0);                                                        # Assume we will not be able to find the desired element

  my $size = $tree->size;                                                       # Size of the stack
  If $back <= $size,
  Then                                                                          # Requested element is available on the stack
   {$tree->find($size - $back);
   };
  $tree
 }

sub Nasm::X86::Tree::peekSubTree($$)                                            # Pop the last value out of a tree and return a tree descriptor positioned on it with the first/found fields set.
 {my ($tree, $back) = @_;                                                       # Tree descriptor, how far back to go with 1 being the top
  @_ == 2 or confess "Two parameters";
  ref($back) =~ m(Variable) or confess "Must be a variable, not: ", dump($back);

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

sub Nasm::X86::Tree::appendAscii($$$)                                           # Append ascii bytes in memory to a tree acting as a string. The address and size of the source memory are specified via variables. Each byte should represent a valid ascii byte so that it can be considered, when left extended with 24 zero bits, as utf32.
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
   } structures => {string=>$string},
     parameters => [qw(address size)],
     name       =>  qq(Nasm::X86::Tree::m::$$string{length});

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

sub Nasm::X86::Tree::reverse($)                                                 # Create a clone of the string in reverse order.
 {my ($string) = @_;                                                            # Tree descriptor of string
  @_ == 1 or confess "One parameter";

  my $t = $string->area->CreateTree;                                            # Cloned reversed copy
  my $l = $string->size;                                                        # Size of string
  $string->by(sub
   {$t->put($l - $string->key - 1, $string->data);
   });
  $t                                                                            # Chain from the target string
 }

sub Nasm::X86::Area::treeFromString($$$)                                        # Create a tree from a string of bytes held at a variable address with a variable length and return the resulting tree.  The first element of the tree is the specified length, in bytes, of the string.
 {my ($area, $address, $size) = @_;                                             # Area description, address of string, length of string in bytes
  @_ == 3 or confess "Three parameters";

  my $t = $area->CreateTree;                                                    # Create a tree to be used to store the string

  PushR my $c = r13, my $a = r14, my $i = r15;

  ClearRegisters $i;
  $address->setReg($a);

  $size->for(sub                                                                # Push each byte of the input string into the tree
   {Mov $c."b", "[r14+r15]";                                                    # Load byte
    $t->push(V chunk => $c);                                                    # Push byte into string
    Inc $i;
   });
  PopR;

  $t                                                                            # Description of tree loaded from string
 }

#D2 Trees as sets                                                               # Trees of trees as sets

sub Nasm::X86::Tree::union($)                                                   # Given a tree of trees consider each sub tree as a set and form the union of all these sets as a new tree.
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

sub Nasm::X86::Tree::intersection($)                                            # Given a tree of trees consider each sub tree as a set and form the intersection of all these sets as a new tree.
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

#D2 Trees of strings                                                            # Trees of strings assign a unique number to a string so that given a string we can produce a unique number representing the string.

sub Nasm::X86::Tree::putString($$)                                              # Enter a string tree into a tree of strings and return the offset of the last inserted tree as the unique number of this string.
 {my ($tree, $string) = @_;                                                     # Tree descriptor representing string tree, tree representing a string to be inserted into the string tree.
  @_ == 2 or confess "Two parameters";
  confess "Second parameter must be a tree"
    unless ref($string) and ref($string) =~ m(Tree);

  my $s = V state => 1;                                                         # 1 - string found so far, 0 - inserting new string
  my $S = $tree->copyDescription;                                               # Create a new descriptor for the string tree

  $string->by(sub                                                               # Insert latest tree
   {my ($t) = @_;
    If $s == 1,
    Then                                                                        # String matches an existing string so far
     {$S->find($t->data);
      If $S->found == 0,
      Then                                                                      # Position on new element
       {$s->copy(0);
        my $T = $t->area->CreateTree;
        $S->put($t->data, $T);
        $S->first->copy($T->first);
       },
      Else
       {$S->first->copy($S->data);                                              # Position on found element
       };
     },
    Else                                                                        # String no longer matches an existing string - we are creating a new path
     {my $T = $t->area->CreateTree;
      $S->put($t->data, $T);
      $S->first->copy($T->first);
     };
   });
  $S->first;                                                                    # The offset of the start of the tree gives us a unique number for each input string.
 }

sub Nasm::X86::Tree::putStringFromMemory($$$)                                   # Enter a string in memory into a tree of strings and return the offset of the last inserted tree as the unique number of this string.
 {my ($tree, $address, $size) = @_;                                             # Tree descriptor representing string tree, variable address in memory of string, variable size of string
  @_ == 3 or confess "Three parameters";

  my $S = $tree->copyDescription;                                               # Create a new descriptor for the string tree

  my $s = Subroutine
   {my ($p, $s, $sub) = @_;

    my $S = $$s{tree};
    PushR my $c = r13, my $a = r14, my $i = r15;
    ClearRegisters $c, $i;
    $$p{address}->setReg($a);                                                   # Address of content in memory
    my $f = V state => 1;                                                       # 1 - string found so far, 0 - inserting new string

    $$p{size}->for(sub                                                          # Insert each character - obviously this can be improved by using registers instead of variables
     {my ($index) = @_;                                                         # Position in the string
      Mov $c."b", "[$a+$i]";                                                    # Get the next byte
      my $char = V char => $c;                                                  # Next character of the string

      If $f == 1,
      Then                                                                      # String matches an existing string so far
       {$S->find($char);
        If $S->found == 0,
        Then                                                                    # Position on new element
         {$f->copy(0);
          my $T = $S->area->CreateTree;
          $S->put($char, $T);
          $S->first->copy($T->first);
         },
        Else
         {$S->first->copy($S->data);                                            # Position on found element
         };
       },
      Else                                                                      # String no longer matches an existing string - we are creating a new path
       {my $T = $S->area->CreateTree;
        $S->put($char, $T);
        $S->first->copy($T->first);
       };
      Inc $i
     });

    PopR;
   } structures => {tree => $tree},
     parameters => [qw(address size)],
     name       =>  qq(Nasm::X86::Tree::putStringFromMemory);

  $s->call(parameters => {address => $address, size=>$size},
           structures => {tree    => $S});

  $S->first;                                                                    # The offset of the start of the tree gives us a unique number for each input string.  We do not need to send an indicator as to whether this subroutine failed or succeeded because it always succeeds, or if it doe not something so serious has happened that it is not plausible to report it here
 }

sub Nasm::X86::Tree::getString($$)                                              # Locate the tree in a string tree representing the specified string but only if it is present and return its data in B<found> and B<data>.  If the string is not present then return a tree descriptor with found set to zero.
 {my ($tree, $string) = @_;                                                     # Tree descriptor representing string tree, tree representing a string to be inserted into the string tree.
  @_ == 2 or confess "Two parameters";
  ref($string) =~ m(\ANasm::X86::::Tree\Z);

  my $S = $tree->copyDescription;                                               # Create a new descriptor for the string tree
  $S->found->copy(1);                                                           # The empty string maps to the offset of the string tree itself

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

sub Nasm::X86::Tree::getStringFromMemory($$$)                                   # Locate the tree in a string tree representing the specified string but only if it is present and return its data in B<found> and B<data>.  If the string is not present then return a tree descriptor with found set to zero.
 {my ($tree, $address, $size) = @_;                                             # Tree descriptor representing string tree, variable address in memory of string, variable size of string
  @_ == 3 or confess "Three parameters";

  my $S = $tree->copyDescription;                                               # Create a new descriptor for the string tree
  $S->found->copy(1);                                                           # The empty string maps to the offset of the string tree itself

  PushR my $c = r13, my $a = r14, my $i = r15;
  ClearRegisters $c, $i;
  $address->setReg($a);

  $size->for(sub                                                                # Insert each character - obviously this can be improved by using registers instead of variables
   {my ($index, $start, $next, $end) = @_;                                      # Position in the string

    Mov $c."b", "[$a+$i]";                                                      # Get the next byte
    my $char = V char => $c;                                                    # Next character of the string
    $S->find($char);
    If $S->found == 0, Then {Jmp $end};                                         # Not found
    $S->first->copy($S->data);                                                  # Position on found element
    Inc $i;
   });
  PopR;
  $S                                                                            # Tree descriptor found and data fields indicate the value and validity of the result
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

    PushR my $transfer = r8, my $treeBitsR = r9, my $treeBitsIndexR = r10,
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

      Cmp $treeBitsR, 0;                                                        # Any tree bits set?
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
     name => "Nasm::X86::Tree::dump-$$tree{length}-$width-$margin-$first";

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

sub Nasm::X86::Tree::dump8xx($$)                                                #P Dump a tree and all its sub trees using 8 character fields for numbers printing the keys and data in hexadecimal.
 {my ($tree, $title) = @_;                                                      # Tree, title
  @_ == 2 or confess "Two parameters";
  $tree->dumpWithWidth($title, 8, 80, 1, 1, 1)
 }

sub Nasm::X86::Tree::printInOrder($$)                                           # Print a tree in order.
 {my ($tree, $title) = @_;                                                      # Tree, title
  @_ == 2 or confess "Two parameters";

  PushR my $F = 31;

  my $s = Subroutine                                                            # Print a tree
   {my ($p, $s, $sub) = @_;                                                     # Parameters, structures, subroutine definition

    my $t = $$s{tree};                                                          # Tree
    my $area = $t->area;                                                        # Area

    PushR my $treeBitsR = r8, my $treeBitsIndexR = r9,
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
     name       => qq(Nasm::X86::Tree::printInOrder-$$tree{length});

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

sub Nasm::X86::Tree::outAsUtf8($)                                               # Print the data values of the specified string on stdout assuming each data value is a utf32 character and that the output device supports utf8.
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

sub Nasm::X86::Tree::plusAssign($$)                                             # Use plus to push an element to a tree being used as a stack.
 {my ($tree, $data) = @_;                                                       # Tree being used as a stack, data to push

  ref($data) =~ m(Variable|Tree) or                                             # Check right operand on right
    confess "Need a tree or variable on the right";

  $tree->push($data);                                                           # Perform the push
  $tree                                                                         # The resulting tree
 }

sub Nasm::X86::Tree::dec($)                                                     # Pop from the tree if it is being used as a stack.
 {my ($tree) = @_;                                                              # Tree being used as a stack

  $tree->pop                                                                    # Perform the pop
 }

#D1 Unisyn                                                                      # Parse Unisyn language statements.

#D2 Lex                                                                         # Lexical Analysis

sub Nasm::X86::Unisyn::Lex::Number::S {0}                                       # Start symbol.
sub Nasm::X86::Unisyn::Lex::Number::F {1}                                       # End symbol.
sub Nasm::X86::Unisyn::Lex::Number::A {2}                                       # ASCII characters extended with circled characters to act as escape sequences.

sub Nasm::X86::Unisyn::Lex::Letter::A                                           # ASCII characters extended with circled characters to act as escape sequences.
 {(0x0,0x1,0x2,0x3,0x4,0x5,0x6,0x7,0x8,0x9,0xa,0xb,0xc,0xd,0xe,0xf,0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f,0x20,0x21,0x22,0x23,0x24,0x25,0x26,0x27,0x28,0x29,0x2a,0x2b,0x2c,0x2d,0x2e,0x2f,0x30,0x31,0x32,0x33,0x34,0x35,0x36,0x37,0x38,0x39,0x3a,0x3b,0x3c,0x3d,0x3e,0x3f,0x40,0x41,0x42,0x43,0x44,0x45,0x46,0x47,0x48,0x49,0x4a,0x4b,0x4c,0x4d,0x4e,0x4f,0x50,0x51,0x52,0x53,0x54,0x55,0x56,0x57,0x58,0x59,0x5a,0x5b,0x5c,0x5d,0x5e,0x5f,0x60,0x61,0x62,0x63,0x64,0x65,0x66,0x67,0x68,0x69,0x6a,0x6b,0x6c,0x6d,0x6e,0x6f,0x70,0x71,0x72,0x73,0x74,0x75,0x76,0x77,0x78,0x79,0x7a,0x7b,0x7c,0x7d,0x7e,0x7f,0x24b6,0x24b7,0x24b8,0x24b9,0x24ba,0x24bb,0x24bc,0x24bd,0x24be,0x24bf,0x24c0,0x24c1,0x24c2,0x24c3,0x24c4,0x24c5,0x24c6,0x24c7,0x24c8,0x24c9,0x24ca,0x24cb,0x24cc,0x24cd,0x24ce,0x24cf,0x24d0,0x24d1,0x24d2,0x24d3,0x24d4,0x24d5,0x24d6,0x24d7,0x24d8,0x24d9,0x24da,0x24db,0x24dc,0x24dd,0x24de,0x24df,0x24e0,0x24e1,0x24e2,0x24e3,0x24e4,0x24e5,0x24e6,0x24e7,0x24e8,0x24e9)
 }
sub Nasm::X86::Unisyn::Lex::Number::d {3}                                       # Infix operator with left to right binding at priority 3.

sub Nasm::X86::Unisyn::Lex::Letter::d                                           # Infix operator with left to right binding at priority 3.
 {(0x1d400,0x1d401,0x1d402,0x1d403,0x1d404,0x1d405,0x1d406,0x1d407,0x1d408,0x1d409,0x1d40a,0x1d40b,0x1d40c,0x1d40d,0x1d40e,0x1d40f,0x1d410,0x1d411,0x1d412,0x1d413,0x1d414,0x1d415,0x1d416,0x1d417,0x1d418,0x1d419,0x1d41a,0x1d41b,0x1d41c,0x1d41d,0x1d41e,0x1d41f,0x1d420,0x1d421,0x1d422,0x1d423,0x1d424,0x1d425,0x1d426,0x1d427,0x1d428,0x1d429,0x1d42a,0x1d42b,0x1d42c,0x1d42d,0x1d42e,0x1d42f,0x1d430,0x1d431,0x1d432,0x1d433,0x1d6a8,0x1d6a9,0x1d6aa,0x1d6ab,0x1d6ac,0x1d6ad,0x1d6ae,0x1d6af,0x1d6b0,0x1d6b1,0x1d6b2,0x1d6b3,0x1d6b4,0x1d6b5,0x1d6b6,0x1d6b7,0x1d6b8,0x1d6b9,0x1d6ba,0x1d6bb,0x1d6bc,0x1d6bd,0x1d6be,0x1d6bf,0x1d6c0,0x1d6c1,0x1d6c2,0x1d6c3,0x1d6c4,0x1d6c5,0x1d6c6,0x1d6c7,0x1d6c8,0x1d6c9,0x1d6ca,0x1d6cb,0x1d6cc,0x1d6cd,0x1d6ce,0x1d6cf,0x1d6d0,0x1d6d1,0x1d6d2,0x1d6d3,0x1d6d4,0x1d6d5,0x1d6d6,0x1d6d7,0x1d6d8,0x1d6d9,0x1d6da,0x1d6db,0x1d6dc,0x1d6dd,0x1d6de,0x1d6df,0x1d6e0,0x1d6e1)
 }
sub Nasm::X86::Unisyn::Lex::Number::p {4}                                       # Prefix operator - applies only to the following variable or bracketed term.

sub Nasm::X86::Unisyn::Lex::Letter::p                                           # Prefix operator - applies only to the following variable or bracketed term.
 {(0x1d468,0x1d469,0x1d46a,0x1d46b,0x1d46c,0x1d46d,0x1d46e,0x1d46f,0x1d470,0x1d471,0x1d472,0x1d473,0x1d474,0x1d475,0x1d476,0x1d477,0x1d478,0x1d479,0x1d47a,0x1d47b,0x1d47c,0x1d47d,0x1d47e,0x1d47f,0x1d480,0x1d481,0x1d482,0x1d483,0x1d484,0x1d485,0x1d486,0x1d487,0x1d488,0x1d489,0x1d48a,0x1d48b,0x1d48c,0x1d48d,0x1d48e,0x1d48f,0x1d490,0x1d491,0x1d492,0x1d493,0x1d494,0x1d495,0x1d496,0x1d497,0x1d498,0x1d499,0x1d49a,0x1d49b,0x1d71c,0x1d71d,0x1d71e,0x1d71f,0x1d720,0x1d721,0x1d722,0x1d723,0x1d724,0x1d725,0x1d726,0x1d727,0x1d728,0x1d729,0x1d72a,0x1d72b,0x1d72c,0x1d72d,0x1d72e,0x1d72f,0x1d730,0x1d731,0x1d732,0x1d733,0x1d734,0x1d735,0x1d736,0x1d737,0x1d738,0x1d739,0x1d73a,0x1d73b,0x1d73c,0x1d73d,0x1d73e,0x1d73f,0x1d740,0x1d741,0x1d742,0x1d743,0x1d744,0x1d745,0x1d746,0x1d747,0x1d748,0x1d749,0x1d74a,0x1d74b,0x1d74c,0x1d74d,0x1d74e,0x1d74f,0x1d750,0x1d751,0x1d752,0x1d753,0x1d754,0x1d755)
 }
sub Nasm::X86::Unisyn::Lex::Number::a {5}                                       # Assign infix operator with right to left binding at priority 2.

sub Nasm::X86::Unisyn::Lex::Letter::a                                           # Assign infix operator with right to left binding at priority 2.
 {(0x210e,0x2190,0x2191,0x2192,0x2193,0x2194,0x2195,0x2196,0x2197,0x2198,0x2199,0x219a,0x219b,0x219c,0x219d,0x219e,0x219f,0x21a0,0x21a1,0x21a2,0x21a3,0x21a4,0x21a5,0x21a6,0x21a7,0x21a8,0x21a9,0x21aa,0x21ab,0x21ac,0x21ad,0x21ae,0x21af,0x21b0,0x21b1,0x21b2,0x21b3,0x21b4,0x21b5,0x21b6,0x21b7,0x21b8,0x21b9,0x21ba,0x21bb,0x21bc,0x21bd,0x21be,0x21bf,0x21c0,0x21c1,0x21c2,0x21c3,0x21c4,0x21c5,0x21c6,0x21c7,0x21c8,0x21c9,0x21ca,0x21cb,0x21cc,0x21cd,0x21ce,0x21cf,0x21d0,0x21d1,0x21d2,0x21d3,0x21d4,0x21d5,0x21d6,0x21d7,0x21d8,0x21d9,0x21da,0x21db,0x21dc,0x21dd,0x21de,0x21df,0x21e0,0x21e1,0x21e2,0x21e3,0x21e4,0x21e5,0x21e6,0x21e7,0x21e8,0x21e9,0x21ea,0x21eb,0x21ec,0x21ed,0x21ee,0x21ef,0x21f0,0x21f1,0x21f2,0x21f3,0x21f4,0x21f5,0x21f6,0x21f7,0x21f8,0x21f9,0x21fa,0x21fb,0x21fc,0x21fd,0x21fe,0xff1d,0x1d434,0x1d435,0x1d436,0x1d437,0x1d438,0x1d439,0x1d43a,0x1d43b,0x1d43c,0x1d43d,0x1d43e,0x1d43f,0x1d440,0x1d441,0x1d442,0x1d443,0x1d444,0x1d445,0x1d446,0x1d447,0x1d448,0x1d449,0x1d44a,0x1d44b,0x1d44c,0x1d44d,0x1d44e,0x1d44f,0x1d450,0x1d451,0x1d452,0x1d453,0x1d454,0x1d456,0x1d457,0x1d458,0x1d459,0x1d45a,0x1d45b,0x1d45c,0x1d45d,0x1d45e,0x1d45f,0x1d460,0x1d461,0x1d462,0x1d463,0x1d464,0x1d465,0x1d466,0x1d467,0x1d6e2,0x1d6e3,0x1d6e4,0x1d6e5,0x1d6e6,0x1d6e7,0x1d6e8,0x1d6e9,0x1d6ea,0x1d6eb,0x1d6ec,0x1d6ed,0x1d6ee,0x1d6ef,0x1d6f0,0x1d6f1,0x1d6f2,0x1d6f3,0x1d6f4,0x1d6f5,0x1d6f6,0x1d6f7,0x1d6f8,0x1d6f9,0x1d6fa,0x1d6fb,0x1d6fc,0x1d6fd,0x1d6fe,0x1d6ff,0x1d700,0x1d701,0x1d702,0x1d703,0x1d704,0x1d705,0x1d706,0x1d707,0x1d708,0x1d709,0x1d70a,0x1d70b,0x1d70c,0x1d70d,0x1d70e,0x1d70f,0x1d710,0x1d711,0x1d712,0x1d713,0x1d714,0x1d715,0x1d716,0x1d717,0x1d718,0x1d719,0x1d71a,0x1d71b)
 }
sub Nasm::X86::Unisyn::Lex::Number::v {6}                                       # Variable names.

sub Nasm::X86::Unisyn::Lex::Letter::v                                           # Variable names.
 {(0x1d5d4,0x1d5d5,0x1d5d6,0x1d5d7,0x1d5d8,0x1d5d9,0x1d5da,0x1d5db,0x1d5dc,0x1d5dd,0x1d5de,0x1d5df,0x1d5e0,0x1d5e1,0x1d5e2,0x1d5e3,0x1d5e4,0x1d5e5,0x1d5e6,0x1d5e7,0x1d5e8,0x1d5e9,0x1d5ea,0x1d5eb,0x1d5ec,0x1d5ed,0x1d5ee,0x1d5ef,0x1d5f0,0x1d5f1,0x1d5f2,0x1d5f3,0x1d5f4,0x1d5f5,0x1d5f6,0x1d5f7,0x1d5f8,0x1d5f9,0x1d5fa,0x1d5fb,0x1d5fc,0x1d5fd,0x1d5fe,0x1d5ff,0x1d600,0x1d601,0x1d602,0x1d603,0x1d604,0x1d605,0x1d606,0x1d607,0x1d756,0x1d757,0x1d758,0x1d759,0x1d75a,0x1d75b,0x1d75c,0x1d75d,0x1d75e,0x1d75f,0x1d760,0x1d761,0x1d762,0x1d763,0x1d764,0x1d765,0x1d766,0x1d767,0x1d768,0x1d769,0x1d76a,0x1d76b,0x1d76c,0x1d76d,0x1d76e,0x1d76f,0x1d770,0x1d771,0x1d772,0x1d773,0x1d774,0x1d775,0x1d776,0x1d777,0x1d778,0x1d779,0x1d77a,0x1d77b,0x1d77c,0x1d77d,0x1d77e,0x1d77f,0x1d780,0x1d781,0x1d782,0x1d783,0x1d784,0x1d785,0x1d786,0x1d787,0x1d788,0x1d789,0x1d78a,0x1d78b,0x1d78c,0x1d78d,0x1d78e,0x1d78f)
 }
sub Nasm::X86::Unisyn::Lex::Number::q {7}                                       # Suffix operator - applies only to the preceding variable or bracketed term.

sub Nasm::X86::Unisyn::Lex::Letter::q                                           # Suffix operator - applies only to the preceding variable or bracketed term.
 {(0x1d63c,0x1d63d,0x1d63e,0x1d63f,0x1d640,0x1d641,0x1d642,0x1d643,0x1d644,0x1d645,0x1d646,0x1d647,0x1d648,0x1d649,0x1d64a,0x1d64b,0x1d64c,0x1d64d,0x1d64e,0x1d64f,0x1d650,0x1d651,0x1d652,0x1d653,0x1d654,0x1d655,0x1d656,0x1d657,0x1d658,0x1d659,0x1d65a,0x1d65b,0x1d65c,0x1d65d,0x1d65e,0x1d65f,0x1d660,0x1d661,0x1d662,0x1d663,0x1d664,0x1d665,0x1d666,0x1d667,0x1d668,0x1d669,0x1d66a,0x1d66b,0x1d66c,0x1d66d,0x1d66e,0x1d66f,0x1d790,0x1d791,0x1d792,0x1d793,0x1d794,0x1d795,0x1d796,0x1d797,0x1d798,0x1d799,0x1d79a,0x1d79b,0x1d79c,0x1d79d,0x1d79e,0x1d79f,0x1d7a0,0x1d7a1,0x1d7a2,0x1d7a3,0x1d7a4,0x1d7a5,0x1d7a6,0x1d7a7,0x1d7a8,0x1d7a9,0x1d7aa,0x1d7ab,0x1d7ac,0x1d7ad,0x1d7ae,0x1d7af,0x1d7b0,0x1d7b1,0x1d7b2,0x1d7b3,0x1d7b4,0x1d7b5,0x1d7b6,0x1d7b7,0x1d7b8,0x1d7b9,0x1d7ba,0x1d7bb,0x1d7bc,0x1d7bd,0x1d7be,0x1d7bf,0x1d7c0,0x1d7c1,0x1d7c2,0x1d7c3,0x1d7c4,0x1d7c5,0x1d7c6,0x1d7c7,0x1d7c8,0x1d7c9)
 }
sub Nasm::X86::Unisyn::Lex::Number::s {8}                                       # Infix operator with left to right binding at priority 1.
sub Nasm::X86::Unisyn::Lex::Letter::s {(0x27e2)}                                # Infix operator with left to right binding at priority 1.
sub Nasm::X86::Unisyn::Lex::Number::e {9}                                       # Infix operator with left to right binding at priority 4.

sub Nasm::X86::Unisyn::Lex::Letter::e                                           # Infix operator with left to right binding at priority 4.
 {(0xac,0xb1,0xd7,0xf7,0x3f6,0x606,0x607,0x608,0x200b,0x200c,0x200d,0x200e,0x200f,0x2010,0x2011,0x2012,0x2013,0x2014,0x2015,0x2016,0x2017,0x2018,0x2019,0x201a,0x201b,0x201c,0x201d,0x201e,0x201f,0x2020,0x2021,0x2022,0x2023,0x2024,0x2025,0x2026,0x2027,0x2028,0x2029,0x202a,0x202b,0x202c,0x202d,0x202e,0x202f,0x2030,0x2031,0x2032,0x2033,0x2034,0x2035,0x2036,0x2037,0x2038,0x2039,0x203a,0x203b,0x203c,0x203d,0x203e,0x203f,0x2040,0x2041,0x2042,0x2043,0x2044,0x2047,0x2048,0x2049,0x204a,0x204b,0x204c,0x204d,0x204e,0x204f,0x2050,0x2051,0x2052,0x2053,0x2054,0x2055,0x2056,0x2057,0x2058,0x2059,0x205a,0x205b,0x205c,0x205d,0x205e,0x205f,0x2060,0x2061,0x2065,0x2066,0x2067,0x2068,0x2069,0x207a,0x207b,0x207c,0x208a,0x208b,0x208c,0x2118,0x2140,0x2141,0x2142,0x2143,0x2144,0x214b,0x2200,0x2201,0x2202,0x2203,0x2204,0x2205,0x2206,0x2207,0x2208,0x2209,0x220a,0x220b,0x220c,0x220d,0x220e,0x220f,0x2210,0x2211,0x2212,0x2213,0x2214,0x2215,0x2216,0x2217,0x2218,0x2219,0x221a,0x221b,0x221c,0x221d,0x221e,0x221f,0x2220,0x2221,0x2222,0x2223,0x2224,0x2225,0x2226,0x2227,0x2228,0x2229,0x222a,0x222b,0x222c,0x222d,0x222e,0x222f,0x2230,0x2231,0x2232,0x2233,0x2234,0x2235,0x2236,0x2237,0x2238,0x2239,0x223a,0x223b,0x223c,0x223d,0x223e,0x223f,0x2240,0x2241,0x2242,0x2243,0x2244,0x2245,0x2246,0x2247,0x2248,0x2249,0x224a,0x224b,0x224c,0x224d,0x224e,0x224f,0x2250,0x2251,0x2252,0x2253,0x2254,0x2255,0x2256,0x2257,0x2258,0x2259,0x225a,0x225b,0x225c,0x225d,0x225e,0x225f,0x2260,0x2261,0x2262,0x2263,0x2264,0x2265,0x2266,0x2267,0x2268,0x2269,0x226a,0x226b,0x226c,0x226d,0x226e,0x226f,0x2270,0x2271,0x2272,0x2273,0x2274,0x2275,0x2276,0x2277,0x2278,0x2279,0x227a,0x227b,0x227c,0x227d,0x227e,0x227f,0x2280,0x2281,0x2282,0x2283,0x2284,0x2285,0x2286,0x2287,0x2288,0x2289,0x228a,0x228b,0x228c,0x228d,0x228e,0x228f,0x2290,0x2291,0x2292,0x2293,0x2294,0x2295,0x2296,0x2297,0x2298,0x2299,0x229a,0x229b,0x229c,0x229d,0x229e,0x229f,0x22a0,0x22a1,0x22a2,0x22a3,0x22a4,0x22a5,0x22a6,0x22a7,0x22a8,0x22a9,0x22aa,0x22ab,0x22ac,0x22ad,0x22ae,0x22af,0x22b0,0x22b1,0x22b2,0x22b3,0x22b4,0x22b5,0x22b6,0x22b7,0x22b8,0x22b9,0x22ba,0x22bb,0x22bc,0x22bd,0x22be,0x22bf,0x22c0,0x22c1,0x22c2,0x22c3,0x22c4,0x22c5,0x22c6,0x22c7,0x22c8,0x22c9,0x22ca,0x22cb,0x22cc,0x22cd,0x22ce,0x22cf,0x22d0,0x22d1,0x22d2,0x22d3,0x22d4,0x22d5,0x22d6,0x22d7,0x22d8,0x22d9,0x22da,0x22db,0x22dc,0x22dd,0x22de,0x22df,0x22e0,0x22e1,0x22e2,0x22e3,0x22e4,0x22e5,0x22e6,0x22e7,0x22e8,0x22e9,0x22ea,0x22eb,0x22ec,0x22ed,0x22ee,0x22ef,0x22f0,0x22f1,0x22f2,0x22f3,0x22f4,0x22f5,0x22f6,0x22f7,0x22f8,0x22f9,0x22fa,0x22fb,0x22fc,0x22fd,0x22fe,0x22ff,0x2300,0x2301,0x2302,0x2303,0x2304,0x2305,0x2306,0x2307,0x230c,0x230d,0x230e,0x230f,0x2310,0x2311,0x2312,0x2313,0x2314,0x2315,0x2316,0x2317,0x2318,0x2319,0x231a,0x231b,0x231c,0x231d,0x231e,0x231f,0x2320,0x2321,0x2322,0x2323,0x2324,0x2325,0x2326,0x2327,0x2328,0x232c,0x232d,0x232e,0x232f,0x2330,0x2331,0x2332,0x2333,0x2334,0x2335,0x2336,0x2337,0x2338,0x2339,0x233a,0x233b,0x233c,0x233d,0x233e,0x233f,0x2340,0x2341,0x2342,0x2343,0x2344,0x2345,0x2346,0x2347,0x2348,0x2349,0x234a,0x234b,0x234c,0x234d,0x234e,0x234f,0x2350,0x2351,0x2352,0x2353,0x2354,0x2355,0x2356,0x2357,0x2358,0x2359,0x235a,0x235b,0x235c,0x235d,0x235e,0x235f,0x2360,0x2361,0x2362,0x2363,0x2364,0x2365,0x2366,0x2367,0x2368,0x2369,0x236a,0x236b,0x236c,0x236d,0x236e,0x236f,0x2370,0x2371,0x2372,0x2373,0x2374,0x2375,0x2376,0x2377,0x2378,0x2379,0x237a,0x237b,0x237c,0x237d,0x237e,0x237f,0x2380,0x2381,0x2382,0x2383,0x2384,0x2385,0x2386,0x2387,0x2388,0x2389,0x238a,0x238b,0x238c,0x238d,0x238e,0x238f,0x2390,0x2391,0x2392,0x2393,0x2394,0x2395,0x2396,0x2397,0x2398,0x2399,0x239a,0x239b,0x239c,0x239d,0x239e,0x239f,0x23a0,0x23a1,0x23a2,0x23a3,0x23a4,0x23a5,0x23a6,0x23a7,0x23a8,0x23a9,0x23aa,0x23ab,0x23ac,0x23ad,0x23ae,0x23af,0x23b0,0x23b1,0x23b2,0x23b3,0x23b4,0x23b5,0x23b6,0x23b7,0x23b8,0x23b9,0x23ba,0x23bb,0x23bc,0x23bd,0x23be,0x23bf,0x23c0,0x23c1,0x23c2,0x23c3,0x23c4,0x23c5,0x23c6,0x23c7,0x23c8,0x23c9,0x23ca,0x23cb,0x23cc,0x23cd,0x23ce,0x23cf,0x23d0,0x23d1,0x23d2,0x23d3,0x23d4,0x23d5,0x23d6,0x23d7,0x23d8,0x23d9,0x23da,0x23db,0x23dc,0x23dd,0x23de,0x23df,0x23e0,0x23e1,0x23e2,0x23e3,0x23e4,0x23e5,0x23e6,0x23e7,0x23e8,0x23e9,0x23ea,0x23eb,0x23ec,0x23ed,0x23ee,0x23ef,0x23f0,0x23f1,0x23f2,0x23f3,0x23f4,0x23f5,0x23f6,0x23f7,0x23f8,0x23f9,0x23fa,0x23fb,0x23fc,0x23fd,0x23fe,0x23ff,0x25a0,0x25a1,0x25a2,0x25a3,0x25a4,0x25a5,0x25a6,0x25a7,0x25a8,0x25a9,0x25aa,0x25ab,0x25ac,0x25ad,0x25ae,0x25af,0x25b0,0x25b1,0x25b2,0x25b3,0x25b4,0x25b5,0x25b6,0x25b7,0x25b8,0x25b9,0x25ba,0x25bb,0x25bc,0x25bd,0x25be,0x25bf,0x25c0,0x25c1,0x25c2,0x25c3,0x25c4,0x25c5,0x25c6,0x25c7,0x25c8,0x25c9,0x25ca,0x25cb,0x25cc,0x25cd,0x25ce,0x25cf,0x25d0,0x25d1,0x25d2,0x25d3,0x25d4,0x25d5,0x25d6,0x25d7,0x25d8,0x25d9,0x25da,0x25db,0x25dc,0x25dd,0x25de,0x25df,0x25e0,0x25e1,0x25e2,0x25e3,0x25e4,0x25e5,0x25e6,0x25e7,0x25e8,0x25e9,0x25ea,0x25eb,0x25ec,0x25ed,0x25ee,0x25ef,0x25f0,0x25f1,0x25f2,0x25f3,0x25f4,0x25f5,0x25f6,0x25f7,0x25f8,0x25f9,0x25fa,0x25fb,0x25fc,0x25fd,0x25fe,0x25ff,0x2600,0x2601,0x2602,0x2603,0x2604,0x2605,0x2606,0x2607,0x2608,0x2609,0x260a,0x260b,0x260c,0x260d,0x260e,0x260f,0x2610,0x2611,0x2612,0x2613,0x2614,0x2615,0x2616,0x2617,0x2618,0x2619,0x261a,0x261b,0x261c,0x261d,0x261e,0x261f,0x2620,0x2621,0x2622,0x2623,0x2624,0x2625,0x2626,0x2627,0x2628,0x2629,0x262a,0x262b,0x262c,0x262d,0x262e,0x262f,0x2630,0x2631,0x2632,0x2633,0x2634,0x2635,0x2636,0x2637,0x2638,0x2639,0x263a,0x263b,0x263c,0x263d,0x263e,0x263f,0x2640,0x2641,0x2642,0x2643,0x2644,0x2645,0x2646,0x2647,0x2648,0x2649,0x264a,0x264b,0x264c,0x264d,0x264e,0x264f,0x2650,0x2651,0x2652,0x2653,0x2654,0x2655,0x2656,0x2657,0x2658,0x2659,0x265a,0x265b,0x265c,0x265d,0x265e,0x265f,0x2660,0x2661,0x2662,0x2663,0x2664,0x2665,0x2666,0x2667,0x2668,0x2669,0x266a,0x266b,0x266c,0x266d,0x266e,0x266f,0x2670,0x2671,0x2672,0x2673,0x2674,0x2675,0x2676,0x2677,0x2678,0x2679,0x267a,0x267b,0x267c,0x267d,0x267e,0x267f,0x2680,0x2681,0x2682,0x2683,0x2684,0x2685,0x2686,0x2687,0x2688,0x2689,0x268a,0x268b,0x268c,0x268d,0x268e,0x268f,0x2690,0x2691,0x2692,0x2693,0x2694,0x2695,0x2696,0x2697,0x2698,0x2699,0x269a,0x269b,0x269c,0x269d,0x269e,0x269f,0x26a0,0x26a1,0x26a2,0x26a3,0x26a4,0x26a5,0x26a6,0x26a7,0x26a8,0x26a9,0x26aa,0x26ab,0x26ac,0x26ad,0x26ae,0x26af,0x26b0,0x26b1,0x26b2,0x26b3,0x26b4,0x26b5,0x26b6,0x26b7,0x26b8,0x26b9,0x26ba,0x26bb,0x26bc,0x26bd,0x26be,0x26bf,0x26c0,0x26c1,0x26c2,0x26c3,0x26c4,0x26c5,0x26c6,0x26c7,0x26c8,0x26c9,0x26ca,0x26cb,0x26cc,0x26cd,0x26ce,0x26cf,0x26d0,0x26d1,0x26d2,0x26d3,0x26d4,0x26d5,0x26d6,0x26d7,0x26d8,0x26d9,0x26da,0x26db,0x26dc,0x26dd,0x26de,0x26df,0x26e0,0x26e1,0x26e2,0x26e3,0x26e4,0x26e5,0x26e6,0x26e7,0x26e8,0x26e9,0x26ea,0x26eb,0x26ec,0x26ed,0x26ee,0x26ef,0x26f0,0x26f1,0x26f2,0x26f3,0x26f4,0x26f5,0x26f6,0x26f7,0x26f8,0x26f9,0x26fa,0x26fb,0x26fc,0x26fd,0x26fe,0x26ff,0x2715,0x27c0,0x27c1,0x27c2,0x27c3,0x27c4,0x27c5,0x27c6,0x27c7,0x27c8,0x27c9,0x27ca,0x27cb,0x27cc,0x27cd,0x27ce,0x27cf,0x27d0,0x27d1,0x27d2,0x27d3,0x27d4,0x27d5,0x27d6,0x27d7,0x27d8,0x27d9,0x27da,0x27db,0x27dc,0x27dd,0x27de,0x27df,0x27e0,0x27e1,0x27e3,0x27e4,0x27e5,0x27f0,0x27f1,0x27f2,0x27f3,0x27f4,0x27f5,0x27f6,0x27f7,0x27f8,0x27f9,0x27fa,0x27fb,0x27fc,0x27fd,0x27fe,0x27ff,0x2800,0x2801,0x2802,0x2803,0x2804,0x2805,0x2806,0x2807,0x2808,0x2809,0x280a,0x280b,0x280c,0x280d,0x280e,0x280f,0x2810,0x2811,0x2812,0x2813,0x2814,0x2815,0x2816,0x2817,0x2818,0x2819,0x281a,0x281b,0x281c,0x281d,0x281e,0x281f,0x2820,0x2821,0x2822,0x2823,0x2824,0x2825,0x2826,0x2827,0x2828,0x2829,0x282a,0x282b,0x282c,0x282d,0x282e,0x282f,0x2830,0x2831,0x2832,0x2833,0x2834,0x2835,0x2836,0x2837,0x2838,0x2839,0x283a,0x283b,0x283c,0x283d,0x283e,0x283f,0x2840,0x2841,0x2842,0x2843,0x2844,0x2845,0x2846,0x2847,0x2848,0x2849,0x284a,0x284b,0x284c,0x284d,0x284e,0x284f,0x2850,0x2851,0x2852,0x2853,0x2854,0x2855,0x2856,0x2857,0x2858,0x2859,0x285a,0x285b,0x285c,0x285d,0x285e,0x285f,0x2860,0x2861,0x2862,0x2863,0x2864,0x2865,0x2866,0x2867,0x2868,0x2869,0x286a,0x286b,0x286c,0x286d,0x286e,0x286f,0x2870,0x2871,0x2872,0x2873,0x2874,0x2875,0x2876,0x2877,0x2878,0x2879,0x287a,0x287b,0x287c,0x287d,0x287e,0x287f,0x2880,0x2881,0x2882,0x2883,0x2884,0x2885,0x2886,0x2887,0x2888,0x2889,0x288a,0x288b,0x288c,0x288d,0x288e,0x288f,0x2890,0x2891,0x2892,0x2893,0x2894,0x2895,0x2896,0x2897,0x2898,0x2899,0x289a,0x289b,0x289c,0x289d,0x289e,0x289f,0x28a0,0x28a1,0x28a2,0x28a3,0x28a4,0x28a5,0x28a6,0x28a7,0x28a8,0x28a9,0x28aa,0x28ab,0x28ac,0x28ad,0x28ae,0x28af,0x28b0,0x28b1,0x28b2,0x28b3,0x28b4,0x28b5,0x28b6,0x28b7,0x28b8,0x28b9,0x28ba,0x28bb,0x28bc,0x28bd,0x28be,0x28bf,0x28c0,0x28c1,0x28c2,0x28c3,0x28c4,0x28c5,0x28c6,0x28c7,0x28c8,0x28c9,0x28ca,0x28cb,0x28cc,0x28cd,0x28ce,0x28cf,0x28d0,0x28d1,0x28d2,0x28d3,0x28d4,0x28d5,0x28d6,0x28d7,0x28d8,0x28d9,0x28da,0x28db,0x28dc,0x28dd,0x28de,0x28df,0x28e0,0x28e1,0x28e2,0x28e3,0x28e4,0x28e5,0x28e6,0x28e7,0x28e8,0x28e9,0x28ea,0x28eb,0x28ec,0x28ed,0x28ee,0x28ef,0x28f0,0x28f1,0x28f2,0x28f3,0x28f4,0x28f5,0x28f6,0x28f7,0x28f8,0x28f9,0x28fa,0x28fb,0x28fc,0x28fd,0x28fe,0x28ff,0x2900,0x2901,0x2902,0x2903,0x2904,0x2905,0x2906,0x2907,0x2908,0x2909,0x290a,0x290b,0x290c,0x290d,0x290e,0x290f,0x2910,0x2911,0x2912,0x2913,0x2914,0x2915,0x2916,0x2917,0x2918,0x2919,0x291a,0x291b,0x291c,0x291d,0x291e,0x291f,0x2920,0x2921,0x2922,0x2923,0x2924,0x2925,0x2926,0x2927,0x2928,0x2929,0x292a,0x292b,0x292c,0x292d,0x292e,0x292f,0x2930,0x2931,0x2932,0x2933,0x2934,0x2935,0x2936,0x2937,0x2938,0x2939,0x293a,0x293b,0x293c,0x293d,0x293e,0x293f,0x2940,0x2941,0x2942,0x2943,0x2944,0x2945,0x2946,0x2947,0x2948,0x2949,0x294a,0x294b,0x294c,0x294d,0x294e,0x294f,0x2950,0x2951,0x2952,0x2953,0x2954,0x2955,0x2956,0x2957,0x2958,0x2959,0x295a,0x295b,0x295c,0x295d,0x295e,0x295f,0x2960,0x2961,0x2962,0x2963,0x2964,0x2965,0x2966,0x2967,0x2968,0x2969,0x296a,0x296b,0x296c,0x296d,0x296e,0x296f,0x2970,0x2971,0x2972,0x2973,0x2974,0x2975,0x2976,0x2977,0x2978,0x2979,0x297a,0x297b,0x297c,0x297d,0x297e,0x297f,0x2980,0x2981,0x2982,0x2999,0x299a,0x299b,0x299c,0x299d,0x299e,0x299f,0x29a0,0x29a1,0x29a2,0x29a3,0x29a4,0x29a5,0x29a6,0x29a7,0x29a8,0x29a9,0x29aa,0x29ab,0x29ac,0x29ad,0x29ae,0x29af,0x29b0,0x29b1,0x29b2,0x29b3,0x29b4,0x29b5,0x29b6,0x29b7,0x29b8,0x29b9,0x29ba,0x29bb,0x29bc,0x29bd,0x29be,0x29bf,0x29c0,0x29c1,0x29c2,0x29c3,0x29c4,0x29c5,0x29c6,0x29c7,0x29c8,0x29c9,0x29ca,0x29cb,0x29cc,0x29cd,0x29ce,0x29cf,0x29d0,0x29d1,0x29d2,0x29d3,0x29d4,0x29d5,0x29d6,0x29d7,0x29d8,0x29d9,0x29da,0x29db,0x29dc,0x29dd,0x29de,0x29df,0x29e0,0x29e1,0x29e2,0x29e3,0x29e4,0x29e5,0x29e6,0x29e7,0x29e8,0x29e9,0x29ea,0x29eb,0x29ec,0x29ed,0x29ee,0x29ef,0x29f0,0x29f1,0x29f2,0x29f3,0x29f4,0x29f5,0x29f6,0x29f7,0x29f8,0x29f9,0x29fa,0x29fb,0x29fe,0x29ff,0x2a00,0x2a01,0x2a02,0x2a03,0x2a04,0x2a05,0x2a06,0x2a07,0x2a08,0x2a09,0x2a0a,0x2a0b,0x2a0c,0x2a0d,0x2a0e,0x2a0f,0x2a10,0x2a11,0x2a12,0x2a13,0x2a14,0x2a15,0x2a16,0x2a17,0x2a18,0x2a19,0x2a1a,0x2a1b,0x2a1c,0x2a1d,0x2a1e,0x2a1f,0x2a20,0x2a21,0x2a22,0x2a23,0x2a24,0x2a25,0x2a26,0x2a27,0x2a28,0x2a29,0x2a2a,0x2a2b,0x2a2c,0x2a2d,0x2a2e,0x2a2f,0x2a30,0x2a31,0x2a32,0x2a33,0x2a34,0x2a35,0x2a36,0x2a37,0x2a38,0x2a39,0x2a3a,0x2a3b,0x2a3c,0x2a3d,0x2a3e,0x2a3f,0x2a40,0x2a41,0x2a42,0x2a43,0x2a44,0x2a45,0x2a46,0x2a47,0x2a48,0x2a49,0x2a4a,0x2a4b,0x2a4c,0x2a4d,0x2a4e,0x2a4f,0x2a50,0x2a51,0x2a52,0x2a53,0x2a54,0x2a55,0x2a56,0x2a57,0x2a58,0x2a59,0x2a5a,0x2a5b,0x2a5c,0x2a5d,0x2a5e,0x2a5f,0x2a60,0x2a61,0x2a62,0x2a63,0x2a64,0x2a65,0x2a66,0x2a67,0x2a68,0x2a69,0x2a6a,0x2a6b,0x2a6c,0x2a6d,0x2a6e,0x2a6f,0x2a70,0x2a71,0x2a72,0x2a73,0x2a74,0x2a75,0x2a76,0x2a77,0x2a78,0x2a79,0x2a7a,0x2a7b,0x2a7c,0x2a7d,0x2a7e,0x2a7f,0x2a80,0x2a81,0x2a82,0x2a83,0x2a84,0x2a85,0x2a86,0x2a87,0x2a88,0x2a89,0x2a8a,0x2a8b,0x2a8c,0x2a8d,0x2a8e,0x2a8f,0x2a90,0x2a91,0x2a92,0x2a93,0x2a94,0x2a95,0x2a96,0x2a97,0x2a98,0x2a99,0x2a9a,0x2a9b,0x2a9c,0x2a9d,0x2a9e,0x2a9f,0x2aa0,0x2aa1,0x2aa2,0x2aa3,0x2aa4,0x2aa5,0x2aa6,0x2aa7,0x2aa8,0x2aa9,0x2aaa,0x2aab,0x2aac,0x2aad,0x2aae,0x2aaf,0x2ab0,0x2ab1,0x2ab2,0x2ab3,0x2ab4,0x2ab5,0x2ab6,0x2ab7,0x2ab8,0x2ab9,0x2aba,0x2abb,0x2abc,0x2abd,0x2abe,0x2abf,0x2ac0,0x2ac1,0x2ac2,0x2ac3,0x2ac4,0x2ac5,0x2ac6,0x2ac7,0x2ac8,0x2ac9,0x2aca,0x2acb,0x2acc,0x2acd,0x2ace,0x2acf,0x2ad0,0x2ad1,0x2ad2,0x2ad3,0x2ad4,0x2ad5,0x2ad6,0x2ad7,0x2ad8,0x2ad9,0x2ada,0x2adb,0x2adc,0x2add,0x2ade,0x2adf,0x2ae0,0x2ae1,0x2ae2,0x2ae3,0x2ae4,0x2ae5,0x2ae6,0x2ae7,0x2ae8,0x2ae9,0x2aea,0x2aeb,0x2aec,0x2aed,0x2aee,0x2aef,0x2af0,0x2af1,0x2af2,0x2af3,0x2af4,0x2af5,0x2af6,0x2af7,0x2af8,0x2af9,0x2afa,0x2afb,0x2afc,0x2afd,0x2afe,0x2aff,0x2b00,0x2b01,0x2b02,0x2b03,0x2b04,0x2b05,0x2b06,0x2b07,0x2b08,0x2b09,0x2b0a,0x2b0b,0x2b0c,0x2b0d,0x2b0e,0x2b0f,0x2b10,0x2b11,0x2b12,0x2b13,0x2b14,0x2b15,0x2b16,0x2b17,0x2b18,0x2b19,0x2b1a,0x2b1b,0x2b1c,0x2b1d,0x2b1e,0x2b1f,0x2b20,0x2b21,0x2b22,0x2b23,0x2b24,0x2b25,0x2b26,0x2b27,0x2b28,0x2b29,0x2b2a,0x2b2b,0x2b2c,0x2b2d,0x2b2e,0x2b2f,0x2b30,0x2b31,0x2b32,0x2b33,0x2b34,0x2b35,0x2b36,0x2b37,0x2b38,0x2b39,0x2b3a,0x2b3b,0x2b3c,0x2b3d,0x2b3e,0x2b3f,0x2b40,0x2b41,0x2b42,0x2b43,0x2b44,0x2b45,0x2b46,0x2b47,0x2b48,0x2b49,0x2b4a,0x2b4b,0x2b4c,0x2b4d,0x2b4e,0x2b4f,0x2b50,0x2b51,0x2b52,0x2b53,0x2b54,0x2b55,0x2b56,0x2b57,0x2b58,0x2e00,0x2e01,0x2e02,0x2e03,0x2e04,0x2e05,0x2e06,0x2e07,0x2e08,0x2e09,0x2e0a,0x2e0b,0x2e0c,0x2e0d,0x2e0e,0x2e0f,0x2e10,0x2e11,0x2e12,0x2e13,0x2e14,0x2e15,0x2e16,0x2e17,0x2e18,0x2e19,0x2e1a,0x2e1b,0x2e1c,0x2e1d,0x2e1e,0x2e1f,0x2e2a,0x2e2b,0x2e2c,0x2e2d,0x2e2e,0x2e2f,0x2e30,0xfb29,0xfe62,0xfe64,0xfe65,0xfe66,0xff0b,0xff1c,0xff1e,0xff5c,0xff5e,0xffe2,0x1eef0,0x1eef1)
 }
sub Nasm::X86::Unisyn::Lex::Number::b {10}                                      # Open.

sub Nasm::X86::Unisyn::Lex::Letter::b                                           # Open.
 {(0x2308,0x230a,0x2329,0x2768,0x276a,0x276c,0x276e,0x2770,0x2772,0x2774,0x27e6,0x27e8,0x27ea,0x27ec,0x27ee,0x2983,0x2985,0x2987,0x2989,0x298b,0x298d,0x298f,0x2991,0x2993,0x2995,0x2997,0x29fc,0x2e28,0x3008,0x300a,0x3010,0x3014,0x3016,0x3018,0x301a,0xfd3e,0xff08,0xff5f)
 }
sub Nasm::X86::Unisyn::Lex::Number::B {11}                                      # Close.

sub Nasm::X86::Unisyn::Lex::Letter::B                                           # Close.
 {(0x2309,0x230b,0x232a,0x2769,0x276b,0x276d,0x276f,0x2771,0x2773,0x2775,0x27e7,0x27e9,0x27eb,0x27ed,0x27ef,0x2984,0x2986,0x2988,0x298a,0x298c,0x298e,0x2990,0x2992,0x2994,0x2996,0x2998,0x29fd,0x2e29,0x3009,0x300b,0x3011,0x3015,0x3017,0x3019,0x301b,0xfd3f,0xff09,0xff60)
 }

sub Nasm::X86::Unisyn::Lex::composeUnisyn($)                                    # Compose phrases of Earl Zero, write them to a temporary file, return the temporary file name.
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
    elsif ($w =~ m(\As\Z))    {$s .= c 0, "s"}                                  # Semicolon
    elsif ($w =~ m(\AS\Z))    {$s .= ' '}                                       # Space
    elsif ($w =~ m(\Av(\w+))) {$s .= $var ->($1)}                               # Variable name
    else {confess "Cannot create Unisyn from $w"}                               # Variable name
   }

  writeTempFile $s                                                              # Composed string to temporary file
 }

sub Nasm::X86::Unisyn::Lex::PermissibleTransitions($)                           # Create and load the table of lexical transitions.
 {my ($area) = @_;                                                              # Area in which to create the table
  my $y = $area->yggdrasil;                                                     # Yggdrasil
  my $t = $area->CreateTree;

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

  my %x = (                                                                     # The transitions table: this tells us which combinations of lexical items are valid.  The table is augmented with start and end symbols so that we know where to start and end.
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

  my $T = $area->CreateTree;                                                    # Tree of transition trees
  $y->put(Nasm::X86::Yggdrasil::Unisyn::Transitions,  $T);                      # Locate transitions between alphabets

  for my $x(sort keys %x)                                                       # Each source lexical item
   {my @y = $x{$x}->@*;
    my $t = $area->CreateTree;                                                  # A tree containing each target lexical item for the source item
    $t->put(K(next => $_), K key => 1) for @y;                                  # Load target set
    $T->put(K(key => $x), $t);                                                  # Save target set
   }

  $T                                                                            # Tree of source to target
 }

sub Nasm::X86::Unisyn::Lex::OpenClose($)                                        # Create and load the table of open to close bracket mappings.
 {my ($area) = @_;                                                              # Area in which to create the table
  my $y = $area->yggdrasil;                                                     # Yggdrasil
  my $o = $area->CreateTree;                                                    # Open to close
  my $c = $area->CreateTree;                                                    # Close to open

  $y->put(Nasm::X86::Yggdrasil::Unisyn::Open,  $o);                             # Locate open to close mapping
  $y->put(Nasm::X86::Yggdrasil::Unisyn::Close, $c);                             # Locate close to open mapping

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

sub Nasm::X86::Unisyn::Lex::LoadAlphabets($)                                    # Create and load the table of lexical alphabets.
 {my ($a) = @_;                                                                 # Area in which to create the table
  my $y = $a->yggdrasil;                                                        # Yggdrasil
  my $t = $a->CreateTree;

  $y->put(Nasm::X86::Yggdrasil::Unisyn::Alphabets, $t);                         # Make the alphabets locate-able

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

sub Nasm::X86::Unisyn::Lex::Reason::Success           {0};                      # Successful parse.
sub Nasm::X86::Unisyn::Lex::Reason::BadUtf8           {1};                      # Bad utf8 character encountered.
sub Nasm::X86::Unisyn::Lex::Reason::InvalidChar       {2};                      # Character not part of Earl Zero.
sub Nasm::X86::Unisyn::Lex::Reason::InvalidTransition {3};                      # Transition from one lexical item to another not allowed.
sub Nasm::X86::Unisyn::Lex::Reason::TrailingClose     {4};                      # Trailing closing bracket discovered.
sub Nasm::X86::Unisyn::Lex::Reason::Mismatch          {5};                      # Mismatched bracket.
sub Nasm::X86::Unisyn::Lex::Reason::NotFinal          {6};                      # Expected something after final character.
sub Nasm::X86::Unisyn::Lex::Reason::BracketsNotClosed {7};                      # Open brackets not closed at end of.

sub Nasm::X86::Unisyn::Lex::position {0};                                       # Position of the parsed item in the input text.
sub Nasm::X86::Unisyn::Lex::length   {1};                                       # Length of the lexical item in bytes.
sub Nasm::X86::Unisyn::Lex::type     {2};                                       # Type of the lexical item.
sub Nasm::X86::Unisyn::Lex::left     {3};                                       # Left operand.
sub Nasm::X86::Unisyn::Lex::right    {4};                                       # Right operand.
sub Nasm::X86::Unisyn::Lex::symbol   {5};                                       # Symbol.

sub Nasm::X86::Unisyn::LoadParseTablesFromFile{"zzzParserTablesArea.data"}      # Load parser tables from a file

sub Nasm::X86::Unisyn::LoadParseTables()                                        # Load parser tables into an area
 {my $f = Nasm::X86::Unisyn::LoadParseTablesFromFile;                           # File containing area containing parser tables

  if (!-e $f)                                                                   # Create the parser table file if not already present
   {my $c = <<'END';                                                            # Generate missing parser tables
use Nasm::X86 qw(:all);

my $area = CreateArea;                                                          # Area in which to create the tables

Nasm::X86::Unisyn::Lex::OpenClose              $area;                           # Open to close bracket matching
Nasm::X86::Unisyn::Lex::PermissibleTransitions $area;                           # Create and load the table of lexical transitions.
Nasm::X86::Unisyn::Lex::LoadAlphabets          $area;                           # Create and load the table of alphabetic classifications

$area->write(K(file => Rutf8 "XXXX"));                                          # Write area to named file
Assemble;
END
    $c =~ s(XXXX) ($f);                                                         # Insert file name
    my $p = setFileExtension $f, q(pl);                                         # Perl file name
    owf $p, $c;                                                                 # Write Perl code to create parser tables file

    qx(cat $p; perl -Ilib/ $p);                                                 # The position of the library folder if not other wise installed
   }

  my $area        = loadAreaIntoAssembly $f;                                    # Load the parser table area directly into the assembly
  my $y           = $area->yggdrasil;

  my $alphabets   = $y->findSubTree(Nasm::X86::Yggdrasil::Unisyn::Alphabets);   # Alphabets
  my $openClose   = $y->findSubTree(Nasm::X86::Yggdrasil::Unisyn::Open);        # Open to close brackets
  my $closeOpen   = $y->findSubTree(Nasm::X86::Yggdrasil::Unisyn::Close);       # Close to open brackets
  my $transitions = $y->findSubTree(Nasm::X86::Yggdrasil::Unisyn::Transitions); # Transitions

  genHash("Nasm::X86::Area::Unisyn::ParserTables",
    area        => $area,                                                       # Area containing parser tables
    alphabets   => $alphabets,                                                  # Alphabetic classifications
    closeOpen   => $closeOpen,                                                  # Close to open bracket matching
    openClose   => $openClose,                                                  # Open to close bracket matching
    transitions => $transitions,                                                # Permissible transitions
  );
 }

sub Nasm::X86::Area::ParseUnisyn($$$)                                           # Parse a string of utf8 characters.
 {my ($area, $a8, $s8) = @_;                                                    # Area in which to create the parse tree, address of utf8 string, size of the utf8 string in bytes

  my $tables      = Nasm::X86::Unisyn::LoadParseTables;                         # Load parser tables
  my $alphabets   = $tables->alphabets;                                         # Create and load the table of alphabetic classifications
  my $closeOpen   = $tables->closeOpen;                                         # Close top open bracket matching
  my $openClose   = $tables->openClose;                                         # Open to close bracket matching
  my $transitions = $tables->transitions;                                       # Create and load the table of lexical transitions.

  my $brackets    = $area->CreateTree; #(lowKeys => 1);                         # Bracket stack
  my $parse       = $area->CreateTree;                                          # Parse tree stack
  my $symbols     = $area->CreateTree;                                          # String tree of symbols encountered during the parse

  my $position    = V pos => 0;                                                 # Position in input string
  my $last        = V last => Nasm::X86::Unisyn::Lex::Number::S;                # Last lexical type starting on ths start symbol
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
#    my $m = $area->treeFromString($a8+$startPos, $l);                           # Create a tree string from the symbol in the parsing area as an easy way of loading the tree of strings - it would be better to have a version that loaded a string tree directly from memory
#    my $s = $symbols->putString($m);                                            # The symbol number for the last lexical item
#    $t->put(K(t => Nasm::X86::Unisyn::Lex::symbol), $s);                        # Record length of previous item in its describing tree
#    $m->free;                                                                   # Free the tree acting as a string now that its content has been incorporated into the tree of strings - a source of inefficiency
   };

  my $new = sub                                                                 # Create a new lexical item
   {my $l = $area->CreateTree;                                                  # Tree to hold lexical item description
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
    ifOr
     [sub {$q->data == K p => Nasm::X86::Unisyn::Lex::Number::d},               # Dyad2 preceded by dyad3 or dyad4
      sub {$q->data == K p => Nasm::X86::Unisyn::Lex::Number::e}],
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
    ifOr
     [sub {$q->data == K p => Nasm::X86::Unisyn::Lex::Number::d},               # Dyad3 preceded by dyad3 or dyad4
      sub {$q->data == K p => Nasm::X86::Unisyn::Lex::Number::e}],
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
      ifOr                                                                      # Separator preceded by open or start - do nothing
       [sub {$p->data == K p => Nasm::X86::Unisyn::Lex::Number::b},
        sub {$p->data == K p => Nasm::X86::Unisyn::Lex::Number::s},
        sub {$p->data == K p => Nasm::X86::Unisyn::Lex::Number::S}],
      Then                                                                      # Eliminate useless statement separator
       {Jmp $end;
       };
      my $q = &$prev2;                                                          # Second previous item
      If $q->data == K(p => Nasm::X86::Unisyn::Lex::Number::s),
      Then                                                                      # Second previous is a statement separator
       {&$triple;                                                               # Reduce
        Jmp $end;                                                               # No need to push as we already have a statement separator on top of the stack
       };
      ifOr
       [sub {$q->data == K p => Nasm::X86::Unisyn::Lex::Number::b},             # Statement separator preceded by singleton
        sub {$q->data == K p => Nasm::X86::Unisyn::Lex::Number::S}],
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
      my $t = $area->CreateTree;                                                # Tree recording the details of the opening bracket
      $t->push($position);                                                      # Position in source
      $t->push($char);                                                          # The opening bracket
      $t->push($openClose->data);                                               # The corresponding closing bracket - guaranteed to exist
      $brackets->push($t);                                                      # Save bracket description on bracket stack
      $change->copy(1);                                                         # Changing because we are on a bracket
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
        PrintErrTraceBack "Unexpected lexical type" if $DebugMode;              # Something unexpected came along
       };
     };                                                                         # Else not required - we are continuing in the same lexical item

    $position->copy($position + $size);                                         # Point to next character to be parsed
    If $position >= $s8,
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

  genHash "Nasm::X86::Unisyn::Parse",                                           # Parse results
    tree     => $parseTree,                                                     # The resulting parse tree
    char     => $parseChar,                                                     # Last character processed
    fail     => $parseFail,                                                     # If not zero the parse has failed for some reason
    position => $position,                                                      # The position reached in the input string
    match    => $parseMatch,                                                    # The position of the matching bracket  that did not match
    reason   => $parseReason,                                                   # The reason code describing the failure if any
    symbols  => $symbols;                                                       # The symbol tree produced by the parse
 } # Parse

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

my $lastAsmFinishTime;                                                          # The last time we finished an assembly

sub Start()                                                                     # Initialize the assembler.
 {@bss = @data = @rodata = %rodata = %rodatas = %subroutines = @text =
  @PushR = @extern = @link = @VariableStack = %loadAreaIntoAssembly = ();

  $DebugMode = 0;
  $Labels    = 0;
  $TraceMode = 0;
  SubroutineStartStack;                                                         # Number of variables at each lexical level
  $lastAsmFinishTime = time;                                                    # The last time we finished an assembly
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

sub OptimizePopPush(%)                                                          #P Perform code optimizations.
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

sub OptimizeReload(%)                                                           #P Reload: a = b; b = a;  remove second - as redundant.
 {my (%options) = @_;                                                           # Options
  my %o = map {$_=>1} $options{optimize}->@*;
  if (1 or $o{reload})
   {for my $i(1..@text-1)                                                       # Each line
     {my $a = $text[$i-1];
      my $b = $text[$i];
      if ($a =~ m(\Amov (\[.*?\]), ([^\[\]].*?)\Z))                             # Check a = b
       {my $a1 = $1; my $a2 = $2;
        if ($b eq qq(mov $a2, $a1\n))                                           # Check b = a
         {$text[$i] = q(; Reload removed: ).$text[$i];
         }
       }
     }
   }
 }

my $hasAvx512;

sub hasAvx512()                                                                 #P Check whether the current device has avx512 instructions or not.
 {return $hasAvx512 if defined $hasAvx512;
  $hasAvx512 = qx(cat /proc/cpuinfo | grep avx512) =~ m(\S) ? 1 : 0;            # Cache avx512 result
 }

sub lineNumbersToSubNamesFromSource                                             # Create a hash mapping line numbers to subroutine definitions.
 {my @s = readFile $0;                                                          # Read source file
  my %l;                                                                        # Mapping from line number to current sub
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

sub locateRunTimeErrorInDebugTraceOutput($)                                     # Locate the traceback of the last known good position in the trace file before the error occurred.
 {my ($trace) = @_;                                                             # Trace mode
  unlink $traceBack;                                                            # Traceback file
  return '' unless -e $sdeTraceOut;                                             # Need a trace file to get a traceback
  my @a = readFile $sdeTraceOut;                                                # Read trace file
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
      last;                                                                     # Finished the scan of the traceback
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
  owf($traceBack, $t);                                                          # Place into a well known file
  say STDERR $t;
  $t
 }

sub fixMixOutput                                                                # Fix mix output so we know where the code comes from in the source file.
 {return '' unless -e $sdeMixOut;                                               # Need a mix file to make this work
  my @a = readFile $sdeMixOut;                                                  # Read mix output
  my %l = lineNumbersToSubNamesFromSource();

  for my $i(keys @a)                                                            # Each line of output
   {if ($a[$i] =~ m(\AXDIS\s+[[:xdigit:]]{16}:\s+BASE\s+[[:xdigit:]]+\s+mov\s+r11,\s+(0x[[:xdigit:]]+)))
     {my $l = eval($1)+1;
      $a[$i] = sprintf "    %s called at $0 line %d\n", pad($l{$l}//'', 32), $l;
     }
   }
  my $a = join "", @a;                                                          # Updated mix out
  owf $sdeMixOut, join "", @a;                                                  # Save updated mix out
  $a
 }

sub countComments($)                                                            # Count the number of comments in the text of the program so we can see what code is being generated too often.
 {my ($count) = @_;                                                             # Comment count
  if ($count)                                                                   # Count the comments so we can see what code to put into subroutines
   {my %c; my %b;                                                               # The number of lines between the comments, the number of blocks
    for my $c(readFile $sourceFile)
     {next unless $c =~ m(\A;);
      my @w = split /\s+/, $c, 3;
      $c{$w[1]}++;
     }

    my @c;
    for my $c(keys %c)                                                          # Remove comments that do not appear often
     {push @c, [$c{$c}, $b{$c}, $c] if $c{$c} >= $count;
     }
    my @d = sort {$$b[0] <=> $$a[0]} @c;
    say STDERR formatTable(\@d, [qw(Lines Blocks Comment)]) if @d;              # Print frequently appearing comments
   }
 }

sub numberWithUnderScores($)                                                    #P Place underscores in the string representation of a number.
 {my ($n) = @_;                                                                 # Number to add commas to
  scalar reverse join '_',  unpack("(A3)*", reverse $n);
 }

sub onGitHub                                                                    # Whether we are on GitHub or not.
 {$ENV{GITHUB_REPOSITORY_OWNER}
 }

our $assembliesPerformed  = 0;                                                  # Number of assemblies performed
our $instructionsExecuted = 0;                                                  # Total number of instructions executed
our $totalBytesAssembled  = 0;                                                  # Total size of the output programs
our $testsThatPassed      = 0;                                                  # Number of runs that passed their test
our $testsThatFailed      = 0;                                                  # Number of runs that failed to pass their tests

sub Assemble(%)                                                                 # Assemble the generated code.
 {my (%options) = @_;                                                           # Options
  my $avx512     = delete $options{avx512};                                     # Avx512 instruction set needed
  my $clocks     = delete $options{clocks};                                     # Number of clocks required to execute this program - if a different number are required then a message is written to that effect.  Set mix > 0 for this to take effect.
  my $count      = delete $options{count}  // 0;                                # Count the comments that occur more frequently than this number
  my $debug      = delete $options{debug}  // 0;                                # Debug: 0 - print stderr and compare stdout to eq if present, 1 - print stdout and stderr and compare stderr to eq if present
  my $eq         = delete $options{eq};                                         # The expected output
  my $foot       = delete $options{foot};                                       # Foot print required
  my $keep       = delete $options{keep};                                       # Keep the executable rather than running it
  my $label      = delete $options{label};                                      # Label for this test if provided
  my $library    = delete $options{library};                                    # Create  the named library if supplied from the supplied assembler code
  my $list       = delete $options{list};                                       # Create and retain a listing file so we can see where a trace error occurs
  my $mix        = delete $options{mix};                                        # Create mix output and fix with line number locations in source
  my $ptr        = delete $options{ptr};                                        # Pointer check required
  my $trace      = delete $options{trace}  //0;                                 # Trace: 0 - none (minimal output), 1 - trace with sde64 and create a listing file to match
  confess "Invalid options: ".join(", ", sort keys %options) if keys %options;  # Complain about any invalid keys

  my $execFile   = $keep // q(z);                                               # Executable file
  my $listFile   = q(z.txt);                                                    # Assembler listing
  my $objectFile = $library // q(z.o);                                          # Object file
  my $o1         = $programOut;                                                 # Stdout from run
  my $o2         = $programErr;                                                 # Stderr from run

  @PushR and confess "Mismatch PushR, PopR";                                    # Match PushR with PopR

  unlink $o1, $o2, $objectFile, $execFile, $listFile, $sourceFile;              # Remove output files

  Exit 0 unless $library or @text > 4 && $text[-4] =~ m(Exit code:);            # Exit with code 0 if an exit was not the last thing coded in a program but ignore for a library.

# Optimize(@_);                                                                 # Perform any optimizations requested
  OptimizeReload(@_);

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

  my $emulate = hasAvx512 ? 0 : ($avx512 // 1) ;                                # Emulate if necessary
  my $sde     = LocateIntelEmulator;                                            # Locate the emulator
  my $run     = !$keep && !$library;                                            # Are we actually going to run the resulting code?

  if ($run and $emulate and !$sde)                                              # Complain about the emulator if we are going to run and we have not suppressed the emulator and the emulator is not present
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
    $emulate = 0;
   }

  if (my @emulatorFiles = searchDirectoryTreesForMatchingFiles(qw(. .txt)))     # Remove prior emulator output files
   {for my $f(@emulatorFiles)
     {unlink $f if $f =~ m(sde-mix-out);
     }
   }
  unlink $sdePtrCheck, $sdeMixOut, $sdeTraceOut, $traceBack;
  my $perlTime = 0; $perlTime = time - $lastAsmFinishTime if $lastAsmFinishTime;# Time we spent in Perl preparing for the assembly

  my $aStart = time;

  if (1)                                                                        # Assemble
   {my $I = @link ? $interpreter : '';                                          # Interpreter only required if calling C
    my $L = join " ",  map {qq(-l$_)} @link;                                    # List of libraries to link supplied via Link directive.
    my $e = $execFile;
    my $l = $trace || $list ? qq(-l $listFile) : q();                           # Create a list file if we are tracing because otherwise it it is difficult to know what we are tracing
    my $a = qq(nasm -O0 $l -o $objectFile $sourceFile);                         # Assembly options

    my $cmd  = $library
      ? qq($a -fbin)
      : qq($a -felf64 -g  && ld $I $L -o $e $objectFile && chmod 744 $e);

    qx($cmd);
    confess "Assembly failed $?" if $?;                                         # Stop if assembly failed
   }

  my $aTime = time - $aStart;

  countComments $count;                                                         # Count the number of comments

  my $out  = $run ? "1>$o1" : '';
  my $err  = $run ? "2>$o2" : '';

  my $exec = sub                                                                # Execution string
   {my $o = qq($sde);                                                           # Emulator
       $o = qq($o -ptr-check)      if $ptr;                                     # Emulator options - tracing
       $o = qq($o -footprint)      if $foot;                                    # Emulator options - foot print
       $o = qq($o -debugtrace)     if $trace;                                   # Emulator options - tracing
       $o = qq($o -mix)            if $mix;                                     # Emulator options - mix histogram output
#      $o = qq($o -omix /dev/null) if $mix and onGitHub;                        # Dump mix output on Github

    if ($emulate && !hasAvx512 or $trace or $mix or $ptr or $foot)              # Command to execute program via the  emulator
     {return qq($o -- ./$execFile $err $out)
     }

    qq(./$execFile $err $out);                                                  # Command to execute program without the emulator
   }->();

  my $eStart = time;

  #lll $exec;
  qx(timeout 60s $exec) if $run;                                                # Run unless suppressed by user or library

  my $er     = $?;                                                              # Execution result
  my $eTime  = time - $eStart;

  if ($run)                                                                     # Execution details
   {my $instructions       = getInstructionCount;                               # Instructions executed under emulator
    $instructionsExecuted += $instructions;                                     # Count instructions executed
    my $p = $assembliesPerformed++;                                             # Count assemblies

    my $bytes = (fileSize($execFile)//9448) - 9448;                             # Estimate the size of the output program
    $totalBytesAssembled += $bytes;                                             # Estimate total of all programs assembled

    my (undef, $file, $line) = caller();                                        # Line in caller

    say STDERR sprintf                                                          # Header if necessary
      ("# Test    %12s    %12s    %12s    %12s  %12s  %12s  %12s",
       "Clocks", "Bytes", "Total Clocks", "Total Bytes", "Run Time", "Assembler", "Perl")
      if $assembliesPerformed % 100 == 1;

    print STDERR                                                                # Rows
      sprintf("# %4s    %12s    %12s    %12s    %12s  %12.4f  %12.2f  %12.2f  at $file line $line",
      $label ? $label : sprintf("%4d", $assembliesPerformed),
      (map {numberWithUnderScores $_}
        $instructions, $bytes, $instructionsExecuted, $totalBytesAssembled),
        $eTime, $aTime, $perlTime);

    if (my $i = $instructions)                                                  # Clocks
     {if ($mix and my $c = $clocks)
       {if ($i != $c)
         {my $l = $c - $i;
          my $C = numberWithUnderScores $c;
          my $I = numberWithUnderScores $i;
          my $g = - $l;
          my $L = numberWithUnderScores $l;
          my $G = numberWithUnderScores $g;
          print STDERR "   Clocks were $C, but now $I, less $L"       if $l > 0;
          print STDERR "   Clocks were $C, but now $I, greater by $G" if $g > 0;
         }
       }
     }
    print STDERR "\n";                                                          # Complete the execution detail line
   }

  if ($run and $debug == 0 and -e $o2 and my $s = readBinaryFile $o2)           # Print only errors if not debugging
   {print STDERR $s;
   }

  if ($run and $debug == 1)                                                     # Print files if soft debugging or error
   {print STDERR readFile($o1) if -e $o1;
    print STDERR readFile($o2) if -e $o2;
   }

  sub{my $a = fixMixOutput; say STDERR $a if $mix >= 2}->() if $run and $mix;   # Fix mix output to show where code came from in the source file

  if ($run and $trace)                                                          # Locate last execution point
   {locateRunTimeErrorInDebugTraceOutput($trace);
   }

  unlink $objectFile unless $library;                                           # Delete files
  unlink $execFile   unless $keep;                                              # Delete executable unless asked to keep it or its a library

  Start;                                                                        # Clear work areas for next assembly

  if ($run and defined(my $e = $eq))                                             # Diff results against expected
   {my $g = readFile($debug ? $o2 : $o1);
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

      if (0 and onGitHub)                                                       # Dump output files that might show why the failure occurred
       {for my $f($sdeMixOut, $sdePtrCheck, $sdeMixOut, $sdeTraceOut,
                  $o1, $o2, $traceBack)
         {if (-e $f)                                                            # Dump the file if it exists
           {say STDERR qx(ls -la $f; cat $f);
           }
         }
       }
      $testsThatFailed++;
      confess "Test failed" unless onGitHub;                                    # Test failed unless we are debugging test failures
     }
    else                                                                        # Runs that passed
     {$testsThatPassed++;
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
 {my %e =  map {$_=>1} @declarations;
  for my $a(readFile $0)
   {next unless $a =~ m(\Asub.*#);                                              # Must be a sub and not a sub forward declaration
    next if     $a =~ m(::);                                                    # Must be a high level sub
    next if     $a =~ m(#P);                                                    # Must not be private
    $a =~ m(\s+(.*?)\() ?  $e{$1}++ : 0;                                        # Save sub name
   }
  say STDERR q/@EXPORT_OK    = qw(/.join(' ', sort keys %e).q/);/;
  exit;
 }

use Exporter qw(import);

use vars qw(@ISA @EXPORT @EXPORT_OK %EXPORT_TAGS);

@ISA          = qw(Exporter);
@EXPORT       = qw();
@EXPORT_OK    = qw(Add Align AllocateMemory And AndBlock Andn Assemble Block Bsf Bsr Bswap Bt Btc Btr Bts Bzhi Call CallC CheckIfMaskRegisterNumber CheckMaskRegister CheckMaskRegisterNumber ChooseRegisters ClassifyInRange ClassifyWithInRange ClassifyWithInRangeAndSaveOffset ClassifyWithInRangeAndSaveWordOffset ClearMemory ClearRegisters ClearZF CloseFile Cmova Cmovae Cmovb Cmovbe Cmovc Cmove Cmovg Cmovge Cmovl Cmovle Cmovna Cmovnae Cmovnb Cmp Comment CommentWithTraceBack ConvertUtf8ToUtf32 CopyMemory CopyMemory4K CopyMemory64 Cpuid CreateArea DComment Db Dd Dec DescribeArea Div Dq Ds Dw Ef Else Enter Exit Extern Fail For ForEver ForIn Fork FreeMemory GetNextUtf8CharAsUtf32 GetPPid GetPid GetPidInHex GetUid Hash Idiv If IfC IfEq IfGe IfGt IfLe IfLt IfNc IfNe IfNs IfNz IfS IfZ Imul Imul3 Inc Incbin Include InsertOneIntoRegisterAtPoint InsertZeroIntoRegisterAtPoint Ja Jae Jb Jbe Jc Jcxz Je Jecxz Jg Jge Jl Jle Jmp Jna Jnae Jnb Jnbe Jnc Jne Jng Jnge Jnl Jnle Jno Jnp Jns Jnz Jo Jp Jpe Jpo Jrcxz Js Jz K Kaddb Kaddd Kaddq Kaddw Kandb Kandd Kandnb Kandnd Kandnq Kandnw Kandq Kandw Kmovb Kmovd Kmovq Kmovw Knotb Knotd Knotq Knotw Korb Kord Korq Kortestb Kortestd Kortestq Kortestw Korw Kshiftlb Kshiftld Kshiftlq Kshiftlw Kshiftrb Kshiftrd Kshiftrq Kshiftrw Ktestb Ktestd Ktestq Ktestw Kunpckb Kunpckd Kunpckq Kunpckw Kxnorb Kxnord Kxnorq Kxnorw Kxorb Kxord Kxorq Kxorw Lahf Lea Leave Link LoadBitsIntoMaskRegister LoadConstantIntoMaskRegister LoadRegFromMm LoadZmm Loop Lzcnt Mov Movd Movdqa Movq Movw Mulpd Neg Not OnSegv OpenRead OpenWrite Or OrBlock Pass Pdep Pext Pextrb Pextrd Pextrq Pextrw Pinsrb Pinsrd Pinsrq Pinsrw Pop PopR Popcnt Popfq PrintCString PrintCStringNL PrintErrNL PrintErrOneRegisterInHex PrintErrOneRegisterInHexNL PrintErrRaxInHex PrintErrRaxInHexNL PrintErrRaxRightInDec PrintErrRaxRightInDecNL PrintErrRax_InHex PrintErrRax_InHexNL PrintErrRegisterInHex PrintErrRightInBin PrintErrRightInBinNL PrintErrRightInHex PrintErrRightInHexNL PrintErrSpace PrintErrString PrintErrStringNL PrintErrTraceBack PrintMemory PrintMemoryInHex PrintMemory_InHex PrintNL PrintOneRegisterInHex PrintOutNL PrintOutOneRegisterInHex PrintOutOneRegisterInHexNL PrintOutRaxInHex PrintOutRaxInHexNL PrintOutRaxRightInDec PrintOutRaxRightInDecNL PrintOutRax_InHex PrintOutRax_InHexNL PrintOutRegisterInHex PrintOutRightInBin PrintOutRightInBinNL PrintOutRightInHex PrintOutRightInHexNL PrintOutSpace PrintOutString PrintOutStringNL PrintOutTraceBack PrintRaxAsChar PrintRaxAsText PrintRaxInDec PrintRaxInHex PrintRaxRightInDec PrintRax_InHex PrintRegisterInHex PrintRightInBin PrintRightInHex PrintSpace PrintString PrintStringNL PrintTraceBack Pslldq Psrldq Push Pushfq R RComment Rb Rd Rdtsc ReadArea ReadChar ReadFile ReadInteger ReadLine ReadTimeStampCounter RegisterSize RestoreFirstFour RestoreFirstFourExceptRax RestoreFirstSeven RestoreFirstSevenExceptRax Ret Rq Rs Rutf8 Rw Sal Sar SaveFirstFour SaveFirstSeven SaveRegIntoMm SetLabel SetMaskRegister SetZF Seta Setae Setb Setbe Setc Sete Setg Setge Setl Setle Setna Setnae Setnb Setnbe Setnc Setne Setng Setnge Setnl Setno Setnp Setns Setnz Seto Setp Setpe Setpo Sets Setz Shl Shr Start StatSize StringLength Sub Subroutine Syscall Test Then Tzcnt V Vaddd Vaddpd Valignb Valignd Valignq Valignw Variable Vcvtudq2pd Vcvtudq2ps Vcvtuqq2pd Vdpps Vgetmantps Vmovd Vmovdqa32 Vmovdqa64 Vmovdqu Vmovdqu32 Vmovdqu64 Vmovdqu8 Vmovq Vmulpd Vpaddb Vpaddd Vpaddq Vpaddw Vpandb Vpandd Vpandnb Vpandnd Vpandnq Vpandnw Vpandq Vpandw Vpbroadcastb Vpbroadcastd Vpbroadcastq Vpbroadcastw Vpcmpeqb Vpcmpeqd Vpcmpeqq Vpcmpeqw Vpcmpub Vpcmpud Vpcmpuq Vpcmpuw Vpcompressd Vpcompressq Vpexpandd Vpexpandq Vpextrb Vpextrd Vpextrq Vpextrw Vpgatherqd Vpgatherqq Vpinsrb Vpinsrd Vpinsrq Vpinsrw Vpmovb2m Vpmovd2m Vpmovm2b Vpmovm2d Vpmovm2q Vpmovm2w Vpmovq2m Vpmovw2m Vpmullb Vpmulld Vpmullq Vpmullw Vporb Vpord Vporq Vporvpcmpeqb Vporvpcmpeqd Vporvpcmpeqq Vporvpcmpeqw Vporw Vprolq Vpsubb Vpsubd Vpsubq Vpsubw Vptestb Vptestd Vptestq Vptestw Vpxorb Vpxord Vpxorq Vpxorw Vsqrtpd WaitPid Xchg Xor ah al ax bFromX bFromZ bRegFromZmm bRegIntoZmm bh bl bp bpl bx byteRegister ch checkZmmRegister cl constantString copyStructureMinusVariables countComments createBitNumberFromAlternatingPattern cs cx dFromPointInZ dFromX dFromZ dWordRegister dh di dil dl ds dx eax ebp ebx ecx edi edx es esi esp executeFileViaBash extractRegisterNumberFromMM fs getBwdqFromMm gs ifAnd ifOr k0 k1 k2 k3 k4 k5 k6 k7 loadAreaIntoAssembly mm0 mm1 mm2 mm3 mm4 mm5 mm6 mm7 opposingJump qFromX qFromZ r10 r10b r10d r10l r10w r11 r11b r11d r11l r11w r12 r12b r12d r12l r12w r13 r13b r13d r13l r13w r14 r14b r14d r14l r14w r15 r15b r15d r15l r15w r8 r8b r8d r8l r8w r9 r9b r9d r9l r9w rax rbp rbx rcx rdi rdx registerNameFromNumber rflags rip rsi rsp si sil sp spl ss st0 st1 st2 st3 st4 st5 st6 st7 unlinkFile uptoNTimes wFromX wFromZ wRegFromZmm wRegIntoZmm wordRegister xmm xmm0 xmm1 xmm10 xmm11 xmm12 xmm13 xmm14 xmm15 xmm16 xmm17 xmm18 xmm19 xmm2 xmm20 xmm21 xmm22 xmm23 xmm24 xmm25 xmm26 xmm27 xmm28 xmm29 xmm3 xmm30 xmm31 xmm4 xmm5 xmm6 xmm7 xmm8 xmm9 ymm ymm0 ymm1 ymm10 ymm11 ymm12 ymm13 ymm14 ymm15 ymm16 ymm17 ymm18 ymm19 ymm2 ymm20 ymm21 ymm22 ymm23 ymm24 ymm25 ymm26 ymm27 ymm28 ymm29 ymm3 ymm30 ymm31 ymm4 ymm5 ymm6 ymm7 ymm8 ymm9 zmm zmm0 zmm1 zmm10 zmm11 zmm12 zmm13 zmm14 zmm15 zmm16 zmm17 zmm18 zmm19 zmm2 zmm20 zmm21 zmm22 zmm23 zmm24 zmm25 zmm26 zmm27 zmm28 zmm29 zmm3 zmm30 zmm31 zmm4 zmm5 zmm6 zmm7 zmm8 zmm9 zmmM zmmMZ);
%EXPORT_TAGS  = (all=>[@EXPORT, @EXPORT_OK]);

# podDocumentation
=pod

=encoding utf-8

=head1 Name

Nasm::X86 - Generate X86 assembler code using Perl as a macro pre-processor.

=head1 Synopsis

Write and execute B<x64> B<Avx512> assembler code from L<perl> using L<perl> as
a powerful macro assembler.  The generated code can be run under the Intel
emulator to obtain execution trace and instruction counts.

Please see: L<https://github.com/philiprbrenan/NasmX86> for a complete working
demonstration of how to run code produced by this module.

While this module allows you to intermix Perl and Assembler code it is
noticeable that the more Perl code that is written the less new Assembler code
is required because there are more opportunities to call a Perl routine to
generate the required Assembler code rather than writing the Assembler out by
hand.

=head2 Examples

Further examples are visible at: L<https://github.com/philiprbrenan/NasmX86>

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

=head1 Description

Generate X86 assembler code using Perl as a macro pre-processor.

=head1 Installation

This module is written in 100% Pure Perl and, thus, it is easy to read,
comprehend, use, modify and install via B<cpan>:

  sudo cpan install Nasm::X86

=head1 Author

L<philiprbrenan@gmail.com|mailto:philiprbrenan@gmail.com>

L<http://www.appaapps.com|http://www.appaapps.com>

=head1 Copyright

Copyright (c) 2016-2021 Philip R Brenan.

This module is free software. It may be used, redistributed and/or modified
under the same terms as Perl itself.

=cut

# Tests and documentation

sub test                                                                        # Run tests with correct line numbers
 {binmode($_, ":utf8") for *STDOUT, *STDERR;
  my $source = readFile $0;                                                     # Source code for this module
  my $split  = qr(\n#__DATA__);                                                 # Split point
  return if $source =~ m($split);                                               # Return if the tests are not shielded - they will be executed inline

  my ($s, $t) = split /__DATA__\n/, $source, 2;                                 # Split source into actual module and tests
  my $l       = split /\n/, $s;                                                 # Lines in module source minus tests
  $l += 2;
  eval qq(# line $l $0\n$t);                                                    # Set line numbers and file for tests
  $@ and die $@;
  1
 }

test unless caller;                                                             # Run shielded tests if called from the command line

1;
# podDocumentation

__DATA__
# line 3 "/home/phil/perl/cpan/NasmX86/lib/Nasm/X86.pm"