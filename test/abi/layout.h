{
struct b1s4I1c2i13 {
  _Bool a:1;
  short b:4;
  int :1;
  char c:2;
  int d:13;
};
TEST4(b1s4I1c2i13)
}
{
struct i3i5i15s1 {
  int a:3;
  int b:5;
  int c:15;
  short d:1;
};
TEST4(i3i5i15s1)
}
{
struct I2ic3b1c1 {
  int :2;
  int a;
  char b:3;
  _Bool c:1;
  char d:1;
};
TEST4(I2ic3b1c1)
}
{
struct B0c1c5si5 {
  _Bool :0;
  char a:1;
  char b:5;
  short c;
  int d:5;
};
TEST4(B0c1c5si5)
}
{
struct si1S9sc {
  short a;
  int b:1;
  short :9;
  short c;
  char d;
};
TEST4(si1S9sc)
}
{
struct b1i2c8c {
  _Bool a:1;
  int b:2;
  char c:8;
  char d;
};
TEST4(b1i2c8c)
}
{
struct i12c1c5s1 {
  int a:12;
  char b:1;
  char c:5;
  short d:1;
};
TEST4(i12c1c5s1)
}
{
struct b1i7i1i {
  _Bool a:1;
  int b:7;
  int c:1;
  int d;
};
TEST4(b1i7i1i)
}
{
struct i4c4i2b1 {
  int a:4;
  char b:4;
  int c:2;
  _Bool d:1;
};
TEST4(i4c4i2b1)
}
{
struct ii3S1b1s9 {
  int a;
  int b:3;
  short :1;
  _Bool c:1;
  short d:9;
};
TEST4(ii3S1b1s9)
}
{
struct c1cs3b1 {
  char a:1;
  char b;
  short c:3;
  _Bool d:1;
};
TEST4(c1cs3b1)
}
{
struct i6i12bI1s5 {
  int a:6;
  int b:12;
  _Bool c;
  int :1;
  short d:5;
};
TEST4(i6i12bI1s5)
}
{
struct i10i26ci2 {
  int a:10;
  int b:26;
  char c;
  int d:2;
};
TEST4(i10i26ci2)
}
{
struct ci6i1c {
  char a;
  int b:6;
  int c:1;
  char d;
};
TEST4(ci6i1c)
}
{
struct c1i6s16i11 {
  char a:1;
  int b:6;
  short c:16;
  int d:11;
};
TEST4(c1i6s16i11)
}
{
struct i21i8i5i {
  int a:21;
  int b:8;
  int c:5;
  int d;
};
TEST4(i21i8i5i)
}
{
struct siS7C4I0I0s4c1 {
  short a;
  int b;
  short :7;
  char :4;
  int :0;
  int :0;
  short c:4;
  char d:1;
};
TEST4(siS7C4I0I0s4c1)
}
{
struct i1c8i2I1i {
  int a:1;
  char b:8;
  int c:2;
  int :1;
  int d;
};
TEST4(i1c8i2I1i)
}
{
struct I0i13ci14i {
  int :0;
  int a:13;
  char b;
  int c:14;
  int d;
};
TEST4(I0i13ci14i)
}
{
struct sisi16 {
  short a;
  int b;
  short c;
  int d:16;
};
TEST4(sisi16)
}
{
struct c3c1I11c4b1 {
  char a:3;
  char b:1;
  int :11;
  char c:4;
  _Bool d:1;
};
TEST4(c3c1I11c4b1)
}
{
struct c6s10i30i1 {
  char a:6;
  short b:10;
  int c:30;
  int d:1;
};
TEST4(c6s10i30i1)
}
{
struct ii31b1i1 {
  int a;
  int b:31;
  _Bool c:1;
  int d:1;
};
TEST4(ii31b1i1)
}
{
struct s7i3i1b1 {
  short a:7;
  int b:3;
  int c:1;
  _Bool d:1;
};
TEST4(s7i3i1b1)
}
{
struct I0ic7ii17 {
  int :0;
  int a;
  char b:7;
  int c;
  int d:17;
};
TEST4(I0ic7ii17)
}
{
struct ii9i15b1 {
  int a;
  int b:9;
  int c:15;
  _Bool d:1;
};
TEST4(ii9i15b1)
}
{
struct ss3c1c5 {
  short a;
  short b:3;
  char c:1;
  char d:5;
};
TEST4(ss3c1c5)
}
{
struct c4s1b1i {
  char a:4;
  short b:1;
  _Bool c:1;
  int d;
};
TEST4(c4s1b1i)
}
{
struct i3i25c5s5 {
  int a:3;
  int b:25;
  char c:5;
  short d:5;
};
TEST4(i3i25c5s5)
}
{
struct i2i1i6s9 {
  int a:2;
  int b:1;
  int c:6;
  short d:9;
};
TEST4(i2i1i6s9)
}
{
struct ii7s1i7 {
  int a;
  int b:7;
  short c:1;
  int d:7;
};
TEST4(ii7s1i7)
}
{
struct s6i7S16c5i {
  short a:6;
  int b:7;
  short :16;
  char c:5;
  int d;
};
TEST4(s6i7S16c5i)
}
{
struct s10S0c1i22i {
  short a:10;
  short :0;
  char b:1;
  int c:22;
  int d;
};
TEST4(s10S0c1i22i)
}
{
struct b1i2b1I16i5 {
  _Bool a:1;
  int b:2;
  _Bool c:1;
  int :16;
  int d:5;
};
TEST4(b1i2b1I16i5)
}
{
struct i29c6s12s11 {
  int a:29;
  char b:6;
  short c:12;
  short d:11;
};
TEST4(i29c6s12s11)
}
{
struct i2s1c2b1 {
  int a:2;
  short b:1;
  char c:2;
  _Bool d:1;
};
TEST4(i2s1c2b1)
}
{
struct is13s10i1 {
  int a;
  short b:13;
  short c:10;
  int d:1;
};
TEST4(is13s10i1)
}
{
struct C1c3si24c4 {
  char :1;
  char a:3;
  short b;
  int c:24;
  char d:4;
};
TEST4(C1c3si24c4)
}
{
struct c1ci20s11 {
  char a:1;
  char b;
  int c:20;
  short d:11;
};
TEST4(c1ci20s11)
}
{
struct c7i23i5s16 {
  char a:7;
  int b:23;
  int c:5;
  short d:16;
};
TEST4(c7i23i5s16)
}
{
struct iS4c6bc1 {
  int a;
  short :4;
  char b:6;
  _Bool c;
  char d:1;
};
TEST4(iS4c6bc1)
}
{
struct cI13sc6b1 {
  char a;
  int :13;
  short b;
  char c:6;
  _Bool d:1;
};
TEST4(cI13sc6b1)
}
{
struct c2S8i11s5C0s11 {
  char a:2;
  short :8;
  int b:11;
  short c:5;
  char :0;
  short d:11;
};
TEST4(c2S8i11s5C0s11)
}
{
struct c2i15ii2 {
  char a:2;
  int b:15;
  int c;
  int d:2;
};
TEST4(c2i15ii2)
}
{
struct b1C4s1ci19 {
  _Bool a:1;
  char :4;
  short b:1;
  char c;
  int d:19;
};
TEST4(b1C4s1ci19)
}
{
struct c8iI0I15i2s4 {
  char a:8;
  int b;
  int :0;
  int :15;
  int c:2;
  short d:4;
};
TEST4(c8iI0I15i2s4)
}
{
struct b1I26C2b1c6i11 {
  _Bool a:1;
  int :26;
  char :2;
  _Bool b:1;
  char c:6;
  int d:11;
};
TEST4(b1I26C2b1c6i11)
}
{
struct s3c1i7c {
  short a:3;
  char b:1;
  int c:7;
  char d;
};
TEST4(s3c1i7c)
}
{
struct I0b1I4s5c5b1 {
  int :0;
  _Bool a:1;
  int :4;
  short b:5;
  char c:5;
  _Bool d:1;
};
TEST4(I0b1I4s5c5b1)
}
{
struct i31c4i8i15 {
  int a:31;
  char b:4;
  int c:8;
  int d:15;
};
TEST4(i31c4i8i15)
}
{
struct S3c1i15i8i11 {
  short :3;
  char a:1;
  int b:15;
  int c:8;
  int d:11;
};
TEST4(S3c1i15i8i11)
}
{
struct s1ib1i3 {
  short a:1;
  int b;
  _Bool c:1;
  int d:3;
};
TEST4(s1ib1i3)
}
{
struct i14c1bI0i {
  int a:14;
  char b:1;
  _Bool c;
  int :0;
  int d;
};
TEST4(i14c1bI0i)
}
{
struct cI0i10i3s13 {
  char a;
  int :0;
  int b:10;
  int c:3;
  short d:13;
};
TEST4(cI0i10i3s13)
}
{
struct c5i2ss1 {
  char a:5;
  int b:2;
  short c;
  short d:1;
};
TEST4(c5i2ss1)
}
{
struct i6s8cc3 {
  int a:6;
  short b:8;
  char c;
  char d:3;
};
TEST4(i6s8cc3)
}
{
struct i32c7ii11 {
  int a:32;
  char b:7;
  int c;
  int d:11;
};
TEST4(i32c7ii11)
}
{
struct s10cb1i {
  short a:10;
  char b;
  _Bool c:1;
  int d;
};
TEST4(s10cb1i)
}
{
struct c1b1c1c2 {
  char a:1;
  _Bool b:1;
  char c:1;
  char d:2;
};
TEST4(c1b1c1c2)
}
{
struct i5s7c1c3 {
  int a:5;
  short b:7;
  char c:1;
  char d:3;
};
TEST4(i5s7c1c3)
}
{
struct i18i7c7S4i28 {
  int a:18;
  int b:7;
  char c:7;
  short :4;
  int d:28;
};
TEST4(i18i7c7S4i28)
}
{
struct i7sbi1 {
  int a:7;
  short b;
  _Bool c;
  int d:1;
};
TEST4(i7sbi1)
}
{
struct c2s7i13c1 {
  char a:2;
  short b:7;
  int c:13;
  char d:1;
};
TEST4(c2s7i13c1)
}
{
struct bic2c1 {
  _Bool a;
  int b;
  char c:2;
  char d:1;
};
TEST4(bic2c1)
}
{
struct i7i15c6c {
  int a:7;
  int b:15;
  char c:6;
  char d;
};
TEST4(i7i15c6c)
}
{
struct s2i4i13I32c {
  short a:2;
  int b:4;
  int c:13;
  int :32;
  char d;
};
TEST4(s2i4i13I32c)
}
{
struct icsI16i14 {
  int a;
  char b;
  short c;
  int :16;
  int d:14;
};
TEST4(icsI16i14)
}
{
struct i4i23B1i2i23 {
  int a:4;
  int b:23;
  _Bool :1;
  int c:2;
  int d:23;
};
TEST4(i4i23B1i2i23)
}
{
struct c2s16bi17 {
  char a:2;
  short b:16;
  _Bool c;
  int d:17;
};
TEST4(c2s16bi17)
}
{
struct i8I0i5s4I13s13 {
  int a:8;
  int :0;
  int b:5;
  short c:4;
  int :13;
  short d:13;
};
TEST4(i8I0i5s4I13s13)
}
{
struct s8cii {
  short a:8;
  char b;
  int c;
  int d;
};
TEST4(s8cii)
}
{
struct c1i1c1s4 {
  char a:1;
  int b:1;
  char c:1;
  short d:4;
};
TEST4(c1i1c1s4)
}
{
struct i28ic1b1 {
  int a:28;
  int b;
  char c:1;
  _Bool d:1;
};
TEST4(i28ic1b1)
}
{
struct ci4i19c {
  char a;
  int b:4;
  int c:19;
  char d;
};
TEST4(ci4i19c)
}
{
struct C1cs7i21i7 {
  char :1;
  char a;
  short b:7;
  int c:21;
  int d:7;
};
TEST4(C1cs7i21i7)
}
{
struct i1sii {
  int a:1;
  short b;
  int c;
  int d;
};
TEST4(i1sii)
}
{
struct i12s13b1b1 {
  int a:12;
  short b:13;
  _Bool c:1;
  _Bool d:1;
};
TEST4(i12s13b1b1)
}
{
struct ii12i1s1 {
  int a;
  int b:12;
  int c:1;
  short d:1;
};
TEST4(ii12i1s1)
}
{
struct ic5i7s2 {
  int a;
  char b:5;
  int c:7;
  short d:2;
};
TEST4(ic5i7s2)
}
{
struct i3i10sc3 {
  int a:3;
  int b:10;
  short c;
  char d:3;
};
TEST4(i3i10sc3)
}
{
struct s4s6i6c7 {
  short a:4;
  short b:6;
  int c:6;
  char d:7;
};
TEST4(s4s6i6c7)
}
{
struct ib1bi1 {
  int a;
  _Bool b:1;
  _Bool c;
  int d:1;
};
TEST4(ib1bi1)
}
{
struct c3i1s6c {
  char a:3;
  int b:1;
  short c:6;
  char d;
};
TEST4(c3i1s6c)
}
{
struct b1iS12i1s {
  _Bool a:1;
  int b;
  short :12;
  int c:1;
  short d;
};
TEST4(b1iS12i1s)
}
{
struct s1sc2i10 {
  short a:1;
  short b;
  char c:2;
  int d:10;
};
TEST4(s1sc2i10)
}
{
struct i6s2s10c3 {
  int a:6;
  short b:2;
  short c:10;
  char d:3;
};
TEST4(i6s2s10c3)
}
{
struct s1c3i20i6 {
  short a:1;
  char b:3;
  int c:20;
  int d:6;
};
TEST4(s1c3i20i6)
}
{
struct i5cc1c1 {
  int a:5;
  char b;
  char c:1;
  char d:1;
};
TEST4(i5cc1c1)
}
{
struct i1s8i7i3 {
  int a:1;
  short b:8;
  int c:7;
  int d:3;
};
TEST4(i1s8i7i3)
}
{
struct i25i2b1i16 {
  int a:25;
  int b:2;
  _Bool c:1;
  int d:16;
};
TEST4(i25i2b1i16)
}
{
struct b1I9sc1I17b1 {
  _Bool a:1;
  int :9;
  short b;
  char c:1;
  int :17;
  _Bool d:1;
};
TEST4(b1I9sc1I17b1)
}
{
struct c8i7c6i24 {
  char a:8;
  int b:7;
  char c:6;
  int d:24;
};
TEST4(c8i7c6i24)
}
{
struct i22b1b1b1 {
  int a:22;
  _Bool b:1;
  _Bool c:1;
  _Bool d:1;
};
TEST4(i22b1b1b1)
}
{
struct s1c1b1s {
  short a:1;
  char b:1;
  _Bool c:1;
  short d;
};
TEST4(s1c1b1s)
}
{
struct s6cbs11 {
  short a:6;
  char b;
  _Bool c;
  short d:11;
};
TEST4(s6cbs11)
}
{
struct ii5i1i7 {
  int a;
  int b:5;
  int c:1;
  int d:7;
};
TEST4(ii5i1i7)
}
{
struct s8i2ci3 {
  short a:8;
  int b:2;
  char c;
  int d:3;
};
TEST4(s8i2ci3)
}
{
struct i2i23I1c6i {
  int a:2;
  int b:23;
  int :1;
  char c:6;
  int d;
};
TEST4(i2i23I1c6i)
}
{
struct b1i2ii14 {
  _Bool a:1;
  int b:2;
  int c;
  int d:14;
};
TEST4(b1i2ii14)
}
{
struct i7b1b1i11 {
  int a:7;
  _Bool b:1;
  _Bool c:1;
  int d:11;
};
TEST4(i7b1b1i11)
}
{
struct cii2i8 {
  char a;
  int b;
  int c:2;
  int d:8;
};
TEST4(cii2i8)
}
{
struct s9i7c1I8i25 {
  short a:9;
  int b:7;
  char c:1;
  int :8;
  int d:25;
};
TEST4(s9i7c1I8i25)
}
{
struct c6s11sb1 {
  char a:6;
  short b:11;
  short c;
  _Bool d:1;
};
TEST4(c6s11sb1)
}
{
struct c8i2ic8 {
  char a:8;
  int b:2;
  int c;
  char d:8;
};
TEST4(c8i2ic8)
}
{
struct bi4ic2 {
  _Bool a;
  int b:4;
  int c;
  char d:2;
};
TEST4(bi4ic2)
}
{
struct i31I0i2i16s4 {
  int a:31;
  int :0;
  int b:2;
  int c:16;
  short d:4;
};
TEST4(i31I0i2i16s4)
}
{
struct i2i2B1i10i7 {
  int a:2;
  int b:2;
  _Bool :1;
  int c:10;
  int d:7;
};
TEST4(i2i2B1i10i7)
}
{
struct c8c3ii {
  char a:8;
  char b:3;
  int c;
  int d;
};
TEST4(c8c3ii)
}
{
struct si2cs6 {
  short a;
  int b:2;
  char c;
  short d:6;
};
TEST4(si2cs6)
}
{
struct s8sb1i14 {
  short a:8;
  short b;
  _Bool c:1;
  int d:14;
};
TEST4(s8sb1i14)
}
{
struct b1i5i28i {
  _Bool a:1;
  int b:5;
  int c:28;
  int d;
};
TEST4(b1i5i28i)
}
{
struct b1c1s9c2 {
  _Bool a:1;
  char b:1;
  short c:9;
  char d:2;
};
TEST4(b1c1s9c2)
}
{
struct s3i3C7s5i1 {
  short a:3;
  int b:3;
  char :7;
  short c:5;
  int d:1;
};
TEST4(s3i3C7s5i1)
}
{
struct ii8s2i12 {
  int a;
  int b:8;
  short c:2;
  int d:12;
};
TEST4(ii8s2i12)
}
{
struct b1sS7ii22 {
  _Bool a:1;
  short b;
  short :7;
  int c;
  int d:22;
};
TEST4(b1sS7ii22)
}
{
struct s6bi2i {
  short a:6;
  _Bool b;
  int c:2;
  int d;
};
TEST4(s6bi2i)
}
{
struct si4ii9 {
  short a;
  int b:4;
  int c;
  int d:9;
};
TEST4(si4ii9)
}
{
struct bc1I10i15b1 {
  _Bool a;
  char b:1;
  int :10;
  int c:15;
  _Bool d:1;
};
TEST4(bc1I10i15b1)
}
{
struct c1s9ib1 {
  char a:1;
  short b:9;
  int c;
  _Bool d:1;
};
TEST4(c1s9ib1)
}
{
struct s2i2C0I6s5i20 {
  short a:2;
  int b:2;
  char :0;
  int :6;
  short c:5;
  int d:20;
};
TEST4(s2i2C0I6s5i20)
}
{
struct i1S2c2sc1 {
  int a:1;
  short :2;
  char b:2;
  short c;
  char d:1;
};
TEST4(i1S2c2sc1)
}
{
struct i11bi3i {
  int a:11;
  _Bool b;
  int c:3;
  int d;
};
TEST4(i11bi3i)
}
{
struct s1s13c6s5 {
  short a:1;
  short b:13;
  char c:6;
  short d:5;
};
TEST4(s1s13c6s5)
}
{
struct s4s9si31 {
  short a:4;
  short b:9;
  short c;
  int d:31;
};
TEST4(s4s9si31)
}
{
struct iC0s9is9 {
  int a;
  char :0;
  short b:9;
  int c;
  short d:9;
};
TEST4(iC0s9is9)
}
{
struct s4cic1 {
  short a:4;
  char b;
  int c;
  char d:1;
};
TEST4(s4cic1)
}
{
struct c4bii {
  char a:4;
  _Bool b;
  int c;
  int d;
};
TEST4(c4bii)
}
{
struct c1b1cc1 {
  char a:1;
  _Bool b:1;
  char c;
  char d:1;
};
TEST4(c1b1cc1)
}
{
struct s1i13bs6 {
  short a:1;
  int b:13;
  _Bool c;
  short d:6;
};
TEST4(s1i13bs6)
}
{
struct iii28i {
  int a;
  int b;
  int c:28;
  int d;
};
TEST4(iii28i)
}
{
struct c3ss9c7 {
  char a:3;
  short b;
  short c:9;
  char d:7;
};
TEST4(c3ss9c7)
}
{
struct c6s5c1I0C0c6 {
  char a:6;
  short b:5;
  char c:1;
  int :0;
  char :0;
  char d:6;
};
TEST4(c6s5c1I0C0c6)
}
{
struct S9s1c6i8C6s {
  short :9;
  short a:1;
  char b:6;
  int c:8;
  char :6;
  short d;
};
TEST4(S9s1c6i8C6s)
}
{
struct C0ii6s6I4b1 {
  char :0;
  int a;
  int b:6;
  short c:6;
  int :4;
  _Bool d:1;
};
TEST4(C0ii6s6I4b1)
}
{
struct I0s7c6ci5 {
  int :0;
  short a:7;
  char b:6;
  char c;
  int d:5;
};
TEST4(I0s7c6ci5)
}
{
struct ci2I0c7s15 {
  char a;
  int b:2;
  int :0;
  char c:7;
  short d:15;
};
TEST4(ci2I0c7s15)
}
{
struct c4i4ib {
  char a:4;
  int b:4;
  int c;
  _Bool d;
};
TEST4(c4i4ib)
}
{
struct i11isi17 {
  int a:11;
  int b;
  short c;
  int d:17;
};
TEST4(i11isi17)
}
{
struct I3i31S8b1c1b {
  int :3;
  int a:31;
  short :8;
  _Bool b:1;
  char c:1;
  _Bool d;
};
TEST4(I3i31S8b1c1b)
}
{
struct I17S0C5c7s11b1i2 {
  int :17;
  short :0;
  char :5;
  char a:7;
  short b:11;
  _Bool c:1;
  int d:2;
};
TEST4(I17S0C5c7s11b1i2)
}
{
struct i5b1I1i1s1 {
  int a:5;
  _Bool b:1;
  int :1;
  int c:1;
  short d:1;
};
TEST4(i5b1I1i1s1)
}
{
struct b1s9cB1s5 {
  _Bool a:1;
  short b:9;
  char c;
  _Bool :1;
  short d:5;
};
TEST4(b1s9cB1s5)
}
{
struct i9i4ii5 {
  int a:9;
  int b:4;
  int c;
  int d:5;
};
TEST4(i9i4ii5)
}
{
struct iC0s8c1i {
  int a;
  char :0;
  short b:8;
  char c:1;
  int d;
};
TEST4(iC0s8c1i)
}
{
struct i15S2b1c2c8 {
  int a:15;
  short :2;
  _Bool b:1;
  char c:2;
  char d:8;
};
TEST4(i15S2b1c2c8)
}
{
struct I4si9ci {
  int :4;
  short a;
  int b:9;
  char c;
  int d;
};
TEST4(I4si9ci)
}
{
struct i4s3c7s5 {
  int a:4;
  short b:3;
  char c:7;
  short d:5;
};
TEST4(i4s3c7s5)
}
{
struct bi15c3b1 {
  _Bool a;
  int b:15;
  char c:3;
  _Bool d:1;
};
TEST4(bi15c3b1)
}
{
struct c5s5s2b {
  char a:5;
  short b:5;
  short c:2;
  _Bool d;
};
TEST4(c5s5s2b)
}
{
struct i14i1i13i29 {
  int a:14;
  int b:1;
  int c:13;
  int d:29;
};
TEST4(i14i1i13i29)
}
{
struct i28I5i5s1s11 {
  int a:28;
  int :5;
  int b:5;
  short c:1;
  short d:11;
};
TEST4(i28I5i5s1s11)
}
{
struct C7c3i11i6c {
  char :7;
  char a:3;
  int b:11;
  int c:6;
  char d;
};
TEST4(C7c3i11i6c)
}
{
struct c3s2i2i23 {
  char a:3;
  short b:2;
  int c:2;
  int d:23;
};
TEST4(c3s2i2i23)
}
{
struct ic5c7i {
  int a;
  char b:5;
  char c:7;
  int d;
};
TEST4(ic5c7i)
}
{
struct b1is9C8i {
  _Bool a:1;
  int b;
  short c:9;
  char :8;
  int d;
};
TEST4(b1is9C8i)
}
{
struct b1s1s6s6 {
  _Bool a:1;
  short b:1;
  short c:6;
  short d:6;
};
TEST4(b1s1s6s6)
}
{
struct i15c2c8b {
  int a:15;
  char b:2;
  char c:8;
  _Bool d;
};
TEST4(i15c2c8b)
}
{
struct bbi2i {
  _Bool a;
  _Bool b;
  int c:2;
  int d;
};
TEST4(bbi2i)
}
{
struct i1i5i25s6 {
  int a:1;
  int b:5;
  int c:25;
  short d:6;
};
TEST4(i1i5i25s6)
}
{
struct i1c7i6i5 {
  int a:1;
  char b:7;
  int c:6;
  int d:5;
};
TEST4(i1c7i6i5)
}
{
struct iis6i1 {
  int a;
  int b;
  short c:6;
  int d:1;
};
TEST4(iis6i1)
}
{
struct i14ib1C1S3i2 {
  int a:14;
  int b;
  _Bool c:1;
  char :1;
  short :3;
  int d:2;
};
TEST4(i14ib1C1S3i2)
}
{
struct I0ii12i19s3 {
  int :0;
  int a;
  int b:12;
  int c:19;
  short d:3;
};
TEST4(I0ii12i19s3)
}
{
struct c7s16i1c6 {
  char a:7;
  short b:16;
  int c:1;
  char d:6;
};
TEST4(c7s16i1c6)
}
{
struct cS7b1i13s16 {
  char a;
  short :7;
  _Bool b:1;
  int c:13;
  short d:16;
};
TEST4(cS7b1i13s16)
}
{
struct i1i6c1S11i2 {
  int a:1;
  int b:6;
  char c:1;
  short :11;
  int d:2;
};
TEST4(i1i6c1S11i2)
}
{
struct i1s10i8c {
  int a:1;
  short b:10;
  int c:8;
  char d;
};
TEST4(i1s10i8c)
}
{
struct bs9bs16 {
  _Bool a;
  short b:9;
  _Bool c;
  short d:16;
};
TEST4(bs9bs16)
}
{
struct ii12si1 {
  int a;
  int b:12;
  short c;
  int d:1;
};
TEST4(ii12si1)
}
{
struct i12sc7i26 {
  int a:12;
  short b;
  char c:7;
  int d:26;
};
TEST4(i12sc7i26)
}
{
struct i21I13b1c8i1 {
  int a:21;
  int :13;
  _Bool b:1;
  char c:8;
  int d:1;
};
TEST4(i21I13b1c8i1)
}
{
struct i9c1s1i10 {
  int a:9;
  char b:1;
  short c:1;
  int d:10;
};
TEST4(i9c1s1i10)
}
{
struct c3bcs1 {
  char a:3;
  _Bool b;
  char c;
  short d:1;
};
TEST4(c3bcs1)
}
{
struct i10i4s1c {
  int a:10;
  int b:4;
  short c:1;
  char d;
};
TEST4(i10i4s1c)
}
{
struct sc5ic3 {
  short a;
  char b:5;
  int c;
  char d:3;
};
TEST4(sc5ic3)
}
{
struct c1cs4i31 {
  char a:1;
  char b;
  short c:4;
  int d:31;
};
TEST4(c1cs4i31)
}
{
struct cI6i27c6I0I4i {
  char a;
  int :6;
  int b:27;
  char c:6;
  int :0;
  int :4;
  int d;
};
TEST4(cI6i27c6I0I4i)
}
{
struct cs3b1s6 {
  char a;
  short b:3;
  _Bool c:1;
  short d:6;
};
TEST4(cs3b1s6)
}
{
struct I0S1c5s15s4s4 {
  int :0;
  short :1;
  char a:5;
  short b:15;
  short c:4;
  short d:4;
};
TEST4(I0S1c5s15s4s4)
}
{
struct B1i1iiC3c1 {
  _Bool :1;
  int a:1;
  int b;
  int c;
  char :3;
  char d:1;
};
TEST4(B1i1iiC3c1)
}
{
struct s2i10i13i5 {
  short a:2;
  int b:10;
  int c:13;
  int d:5;
};
TEST4(s2i10i13i5)
}
{
struct c4i2i1S1b1 {
  char a:4;
  int b:2;
  int c:1;
  short :1;
  _Bool d:1;
};
TEST4(c4i2i1S1b1)
}
{
struct s12c4ss8 {
  short a:12;
  char b:4;
  short c;
  short d:8;
};
TEST4(s12c4ss8)
}
{
struct c3i2i22I1i {
  char a:3;
  int b:2;
  int c:22;
  int :1;
  int d;
};
TEST4(c3i2i22I1i)
}
{
struct iii1i14 {
  int a;
  int b;
  int c:1;
  int d:14;
};
TEST4(iii1i14)
}
{
struct b1sii25 {
  _Bool a:1;
  short b;
  int c;
  int d:25;
};
TEST4(b1sii25)
}
{
struct i6c1c4s1 {
  int a:6;
  char b:1;
  char c:4;
  short d:1;
};
TEST4(i6c1c4s1)
}
{
struct si3cb1 {
  short a;
  int b:3;
  char c;
  _Bool d:1;
};
TEST4(si3cb1)
}
{
struct b1i11b1s4 {
  _Bool a:1;
  int b:11;
  _Bool c:1;
  short d:4;
};
TEST4(b1i11b1s4)
}
{
struct c4c2ci2 {
  char a:4;
  char b:2;
  char c;
  int d:2;
};
TEST4(c4c2ci2)
}
{
struct s6i30i14i {
  short a:6;
  int b:30;
  int c:14;
  int d;
};
TEST4(s6i30i14i)
}
{
struct ic2is9 {
  int a;
  char b:2;
  int c;
  short d:9;
};
TEST4(ic2is9)
}
{
struct C6C0c6i6s7c {
  char :6;
  char :0;
  char a:6;
  int b:6;
  short c:7;
  char d;
};
TEST4(C6C0c6i6s7c)
}
{
struct ii4i3s5 {
  int a;
  int b:4;
  int c:3;
  short d:5;
};
TEST4(ii4i3s5)
}
{
struct csi6c6 {
  char a;
  short b;
  int c:6;
  char d:6;
};
TEST4(csi6c6)
}
{
struct s5i32cs4 {
  short a:5;
  int b:32;
  char c;
  short d:4;
};
TEST4(s5i32cs4)
}
{
struct c1icb1 {
  char a:1;
  int b;
  char c;
  _Bool d:1;
};
TEST4(c1icb1)
}
{
struct s4S3i13i7i {
  short a:4;
  short :3;
  int b:13;
  int c:7;
  int d;
};
TEST4(s4S3i13i7i)
}
{
struct i15b1I0s7c7 {
  int a:15;
  _Bool b:1;
  int :0;
  short c:7;
  char d:7;
};
TEST4(i15b1I0s7c7)
}
{
struct i27b1i1i {
  int a:27;
  _Bool b:1;
  int c:1;
  int d;
};
TEST4(i27b1i1i)
}
{
struct s6i25b1i10 {
  short a:6;
  int b:25;
  _Bool c:1;
  int d:10;
};
TEST4(s6i25b1i10)
}
{
struct ibc5s2 {
  int a;
  _Bool b;
  char c:5;
  short d:2;
};
TEST4(ibc5s2)
}
{
struct i2s1c8i {
  int a:2;
  short b:1;
  char c:8;
  int d;
};
TEST4(i2s1c8i)
}
{
struct i2s7b1C8s {
  int a:2;
  short b:7;
  _Bool c:1;
  char :8;
  short d;
};
TEST4(i2s7b1C8s)
}
{
struct I0c1I2i1ci1 {
  int :0;
  char a:1;
  int :2;
  int b:1;
  char c;
  int d:1;
};
TEST4(I0c1I2i1ci1)
}
{
struct i1i3i1s7 {
  int a:1;
  int b:3;
  int c:1;
  short d:7;
};
TEST4(i1i3i1s7)
}
{
struct S14i13c6ci7 {
  short :14;
  int a:13;
  char b:6;
  char c;
  int d:7;
};
TEST4(S14i13c6ci7)
}
{
struct sB0bc4c5 {
  short a;
  _Bool :0;
  _Bool b;
  char c:4;
  char d:5;
};
TEST4(sB0bc4c5)
}
{
struct si2s14c3 {
  short a;
  int b:2;
  short c:14;
  char d:3;
};
TEST4(si2s14c3)
}
{
struct s4sI13i16b1 {
  short a:4;
  short b;
  int :13;
  int c:16;
  _Bool d:1;
};
TEST4(s4sI13i16b1)
}
{
struct c1s13ic7 {
  char a:1;
  short b:13;
  int c;
  char d:7;
};
TEST4(c1s13ic7)
}
{
struct b1I9i5c8c2 {
  _Bool a:1;
  int :9;
  int b:5;
  char c:8;
  char d:2;
};
TEST4(b1I9i5c8c2)
}
{
struct b1b1i18i13 {
  _Bool a:1;
  _Bool b:1;
  int c:18;
  int d:13;
};
TEST4(b1b1i18i13)
}
{
struct c4s8s11s {
  char a:4;
  short b:8;
  short c:11;
  short d;
};
TEST4(c4s8s11s)
}
{
struct s3i1s6i2 {
  short a:3;
  int b:1;
  short c:6;
  int d:2;
};
TEST4(s3i1s6i2)
}
{
struct c6c6ic2 {
  char a:6;
  char b:6;
  int c;
  char d:2;
};
TEST4(c6c6ic2)
}
{
struct i1I0i13s5s {
  int a:1;
  int :0;
  int b:13;
  short c:5;
  short d;
};
TEST4(i1I0i13s5s)
}
{
struct cI23c4c8i32 {
  char a;
  int :23;
  char b:4;
  char c:8;
  int d:32;
};
TEST4(cI23c4c8i32)
}
{
struct i6cs4c5 {
  int a:6;
  char b;
  short c:4;
  char d:5;
};
TEST4(i6cs4c5)
}
{
struct i12i6c1i3 {
  int a:12;
  int b:6;
  char c:1;
  int d:3;
};
TEST4(i12i6c1i3)
}
{
struct s14ci5i13 {
  short a:14;
  char b;
  int c:5;
  int d:13;
};
TEST4(s14ci5i13)
}
{
struct ss4cs3 {
  short a;
  short b:4;
  char c;
  short d:3;
};
TEST4(ss4cs3)
}
{
struct c6c1c1s {
  char a:6;
  char b:1;
  char c:1;
  short d;
};
TEST4(c6c1c1s)
}
{
struct i1c6C0s7i22 {
  int a:1;
  char b:6;
  char :0;
  short c:7;
  int d:22;
};
TEST4(i1c6C0s7i22)
}
{
struct ib1c4c1 {
  int a;
  _Bool b:1;
  char c:4;
  char d:1;
};
TEST4(ib1c4c1)
}
{
struct s11bi1b1 {
  short a:11;
  _Bool b;
  int c:1;
  _Bool d:1;
};
TEST4(s11bi1b1)
}
{
struct i4c6i2c1 {
  int a:4;
  char b:6;
  int c:2;
  char d:1;
};
TEST4(i4c6i2c1)
}
{
struct icii6 {
  int a;
  char b;
  int c;
  int d:6;
};
TEST4(icii6)
}
{
struct i15ci15s5 {
  int a:15;
  char b;
  int c:15;
  short d:5;
};
TEST4(i15ci15s5)
}
{
struct ssi2C0i {
  short a;
  short b;
  int c:2;
  char :0;
  int d;
};
TEST4(ssi2C0i)
}
{
struct i26b1ci {
  int a:26;
  _Bool b:1;
  char c;
  int d;
};
TEST4(i26b1ci)
}
{
struct bsi1i {
  _Bool a;
  short b;
  int c:1;
  int d;
};
TEST4(bsi1i)
}
{
struct s4iS10c3s4 {
  short a:4;
  int b;
  short :10;
  char c:3;
  short d:4;
};
TEST4(s4iS10c3s4)
}
{
struct c4b1C0b1I0c3 {
  char a:4;
  _Bool b:1;
  char :0;
  _Bool c:1;
  int :0;
  char d:3;
};
TEST4(c4b1C0b1I0c3)
}
{
struct is1i20i {
  int a;
  short b:1;
  int c:20;
  int d;
};
TEST4(is1i20i)
}
{
struct i6c7s12C1i1 {
  int a:6;
  char b:7;
  short c:12;
  char :1;
  int d:1;
};
TEST4(i6c7s12C1i1)
}
{
struct s1c2c2s6 {
  short a:1;
  char b:2;
  char c:2;
  short d:6;
};
TEST4(s1c2c2s6)
}
{
struct s12c1s5I0i9 {
  short a:12;
  char b:1;
  short c:5;
  int :0;
  int d:9;
};
TEST4(s12c1s5I0i9)
}
{
struct c4c1ii10 {
  char a:4;
  char b:1;
  int c;
  int d:10;
};
TEST4(c4c1ii10)
}
{
struct c2ii2s10 {
  char a:2;
  int b;
  int c:2;
  short d:10;
};
TEST4(c2ii2s10)
}
{
struct s4i22ss {
  short a:4;
  int b:22;
  short c;
  short d;
};
TEST4(s4i22ss)
}
{
struct i18I17i32i23s4 {
  int a:18;
  int :17;
  int b:32;
  int c:23;
  short d:4;
};
TEST4(i18I17i32i23s4)
}
{
struct i18i15i2b1 {
  int a:18;
  int b:15;
  int c:2;
  _Bool d:1;
};
TEST4(i18i15i2b1)
}
{
struct i20i6s1i13 {
  int a:20;
  int b:6;
  short c:1;
  int d:13;
};
TEST4(i20i6s1i13)
}
{
struct S0c1I9s6s1b1 {
  short :0;
  char a:1;
  int :9;
  short b:6;
  short c:1;
  _Bool d:1;
};
TEST4(S0c1I9s6s1b1)
}
{
struct i4s16i25b1 {
  int a:4;
  short b:16;
  int c:25;
  _Bool d:1;
};
TEST4(i4s16i25b1)
}
{
struct si2i21i28 {
  short a;
  int b:2;
  int c:21;
  int d:28;
};
TEST4(si2i21i28)
}
{
struct i2S10i27i31s1 {
  int a:2;
  short :10;
  int b:27;
  int c:31;
  short d:1;
};
TEST4(i2S10i27i31s1)
}
{
struct i2s8ib1 {
  int a:2;
  short b:8;
  int c;
  _Bool d:1;
};
TEST4(i2s8ib1)
}
{
struct s13bi4i {
  short a:13;
  _Bool b;
  int c:4;
  int d;
};
TEST4(s13bi4i)
}
{
struct i1s8i12s7 {
  int a:1;
  short b:8;
  int c:12;
  short d:7;
};
TEST4(i1s8i12s7)
}
{
struct s16i2S0is2 {
  short a:16;
  int b:2;
  short :0;
  int c;
  short d:2;
};
TEST4(s16i2S0is2)
}
{
struct cS0c5b1i {
  char a;
  short :0;
  char b:5;
  _Bool c:1;
  int d;
};
TEST4(cS0c5b1i)
}
{
struct B1c1S6i9s4i3 {
  _Bool :1;
  char a:1;
  short :6;
  int b:9;
  short c:4;
  int d:3;
};
TEST4(B1c1S6i9s4i3)
}
{
struct c2s7i2i24 {
  char a:2;
  short b:7;
  int c:2;
  int d:24;
};
TEST4(c2s7i2i24)
}
{
struct c2c5c3C0i2 {
  char a:2;
  char b:5;
  char c:3;
  char :0;
  int d:2;
};
TEST4(c2c5c3C0i2)
}
{
struct s7i12s15b1 {
  short a:7;
  int b:12;
  short c:15;
  _Bool d:1;
};
TEST4(s7i12s15b1)
}
{
struct b1i9c2b1 {
  _Bool a:1;
  int b:9;
  char c:2;
  _Bool d:1;
};
TEST4(b1i9c2b1)
}
{
struct B0sc1iS0i2 {
  _Bool :0;
  short a;
  char b:1;
  int c;
  short :0;
  int d:2;
};
TEST4(B0sc1iS0i2)
}
{
struct i14s4I12i1s15 {
  int a:14;
  short b:4;
  int :12;
  int c:1;
  short d:15;
};
TEST4(i14s4I12i1s15)
}
{
struct b1ii2i9 {
  _Bool a:1;
  int b;
  int c:2;
  int d:9;
};
TEST4(b1ii2i9)
}
{
struct i1ss7i31 {
  int a:1;
  short b;
  short c:7;
  int d:31;
};
TEST4(i1ss7i31)
}
{
struct b1i3i7i32 {
  _Bool a:1;
  int b:3;
  int c:7;
  int d:32;
};
TEST4(b1i3i7i32)
}
{
struct bc4B1b1i26 {
  _Bool a;
  char b:4;
  _Bool :1;
  _Bool c:1;
  int d:26;
};
TEST4(bc4B1b1i26)
}
{
struct i6s6c2S7i1 {
  int a:6;
  short b:6;
  char c:2;
  short :7;
  int d:1;
};
TEST4(i6s6c2S7i1)
}
{
struct I0I10s10cb1b1 {
  int :0;
  int :10;
  short a:10;
  char b;
  _Bool c:1;
  _Bool d:1;
};
TEST4(I0I10s10cb1b1)
}
{
struct c7c1i24i14 {
  char a:7;
  char b:1;
  int c:24;
  int d:14;
};
TEST4(c7c1i24i14)
}
{
struct s14I6iii1 {
  short a:14;
  int :6;
  int b;
  int c;
  int d:1;
};
TEST4(s14I6iii1)
}
{
struct s11i1i22i11 {
  short a:11;
  int b:1;
  int c:22;
  int d:11;
};
TEST4(s11i1i22i11)
}
{
struct i12i2i1s {
  int a:12;
  int b:2;
  int c:1;
  short d;
};
TEST4(i12i2i1s)
}
{
struct c1I0s6ic3 {
  char a:1;
  int :0;
  short b:6;
  int c;
  char d:3;
};
TEST4(c1I0s6ic3)
}
{
struct I0b1bic6 {
  int :0;
  _Bool a:1;
  _Bool b;
  int c;
  char d:6;
};
TEST4(I0b1bic6)
}
{
struct s3b1b1i2 {
  short a:3;
  _Bool b:1;
  _Bool c:1;
  int d:2;
};
TEST4(s3b1b1i2)
}
{
struct bI0I0sci13 {
  _Bool a;
  int :0;
  int :0;
  short b;
  char c;
  int d:13;
};
TEST4(bI0I0sci13)
}
{
struct i16C0s9c7b1 {
  int a:16;
  char :0;
  short b:9;
  char c:7;
  _Bool d:1;
};
TEST4(i16C0s9c7b1)
}
{
struct b1i7c1i10 {
  _Bool a:1;
  int b:7;
  char c:1;
  int d:10;
};
TEST4(b1i7c1i10)
}
{
struct i1i19i6i22 {
  int a:1;
  int b:19;
  int c:6;
  int d:22;
};
TEST4(i1i19i6i22)
}
{
struct C2I0i6i21i7C3i {
  char :2;
  int :0;
  int a:6;
  int b:21;
  int c:7;
  char :3;
  int d;
};
TEST4(C2I0i6i21i7C3i)
}
{
struct S7s4c6c5s2 {
  short :7;
  short a:4;
  char b:6;
  char c:5;
  short d:2;
};
TEST4(S7s4c6c5s2)
}
{
struct i3c1i10c4 {
  int a:3;
  char b:1;
  int c:10;
  char d:4;
};
TEST4(i3c1i10c4)
}
{
struct I0c1i11s9i6 {
  int :0;
  char a:1;
  int b:11;
  short c:9;
  int d:6;
};
TEST4(I0c1i11s9i6)
}
{
struct c4b1b1i17 {
  char a:4;
  _Bool b:1;
  _Bool c:1;
  int d:17;
};
TEST4(c4b1b1i17)
}
{
struct i1c5c1i5 {
  int a:1;
  char b:5;
  char c:1;
  int d:5;
};
TEST4(i1c5c1i5)
}
{
struct s5s2s2B1i6 {
  short a:5;
  short b:2;
  short c:2;
  _Bool :1;
  int d:6;
};
TEST4(s5s2s2B1i6)
}
{
struct i5c1c5s11 {
  int a:5;
  char b:1;
  char c:5;
  short d:11;
};
TEST4(i5c1c5s11)
}
{
struct I11ic5i7s3 {
  int :11;
  int a;
  char b:5;
  int c:7;
  short d:3;
};
TEST4(I11ic5i7s3)
}
{
struct s13cS2i27s7 {
  short a:13;
  char b;
  short :2;
  int c:27;
  short d:7;
};
TEST4(s13cS2i27s7)
}
{
struct c4s2i24s9 {
  char a:4;
  short b:2;
  int c:24;
  short d:9;
};
TEST4(c4s2i24s9)
}
{
struct i9bi25i4 {
  int a:9;
  _Bool b;
  int c:25;
  int d:4;
};
TEST4(i9bi25i4)
}
{
struct s6ss7i1 {
  short a:6;
  short b;
  short c:7;
  int d:1;
};
TEST4(s6ss7i1)
}
{
struct b1i10C7s3i {
  _Bool a:1;
  int b:10;
  char :7;
  short c:3;
  int d;
};
TEST4(b1i10C7s3i)
}
{
struct i16i17sC0s10 {
  int a:16;
  int b:17;
  short c;
  char :0;
  short d:10;
};
TEST4(i16i17sC0s10)
}
{
struct i13i12c1b1 {
  int a:13;
  int b:12;
  char c:1;
  _Bool d:1;
};
TEST4(i13i12c1b1)
}
{
struct i5c1i3c7 {
  int a:5;
  char b:1;
  int c:3;
  char d:7;
};
TEST4(i5c1i3c7)
}
{
struct i24c8c4c2 {
  int a:24;
  char b:8;
  char c:4;
  char d:2;
};
TEST4(i24c8c4c2)
}
{
struct i3cbi27 {
  int a:3;
  char b;
  _Bool c;
  int d:27;
};
TEST4(i3cbi27)
}
{
struct i23sc5i {
  int a:23;
  short b;
  char c:5;
  int d;
};
TEST4(i23sc5i)
}
{
struct ii2S3ib1 {
  int a;
  int b:2;
  short :3;
  int c;
  _Bool d:1;
};
TEST4(ii2S3ib1)
}
{
struct s15c2si2 {
  short a:15;
  char b:2;
  short c;
  int d:2;
};
TEST4(s15c2si2)
}
{
struct b1scc5 {
  _Bool a:1;
  short b;
  char c;
  char d:5;
};
TEST4(b1scc5)
}
{
struct i1cs11c7 {
  int a:1;
  char b;
  short c:11;
  char d:7;
};
TEST4(i1cs11c7)
}
{
struct i1i26sb1 {
  int a:1;
  int b:26;
  short c;
  _Bool d:1;
};
TEST4(i1i26sb1)
}
{
struct i29sc1b {
  int a:29;
  short b;
  char c:1;
  _Bool d;
};
TEST4(i29sc1b)
}
{
struct c5i24i1i14 {
  char a:5;
  int b:24;
  int c:1;
  int d:14;
};
TEST4(c5i24i1i14)
}
{
struct I1i1ii18c1 {
  int :1;
  int a:1;
  int b;
  int c:18;
  char d:1;
};
TEST4(I1i1ii18c1)
}
{
struct si8s4i3 {
  short a;
  int b:8;
  short c:4;
  int d:3;
};
TEST4(si8s4i3)
}
{
struct b1i9i23s6 {
  _Bool a:1;
  int b:9;
  int c:23;
  short d:6;
};
TEST4(b1i9i23s6)
}
{
struct I20c1c1i16C0s1 {
  int :20;
  char a:1;
  char b:1;
  int c:16;
  char :0;
  short d:1;
};
TEST4(I20c1c1i16C0s1)
}
{
struct i5s12b1s8 {
  int a:5;
  short b:12;
  _Bool c:1;
  short d:8;
};
TEST4(i5s12b1s8)
}
{
struct c8ii7c1 {
  char a:8;
  int b;
  int c:7;
  char d:1;
};
TEST4(c8ii7c1)
}
{
struct i2i1ic {
  int a:2;
  int b:1;
  int c;
  char d;
};
TEST4(i2i1ic)
}
{
struct s4s5i23i14 {
  short a:4;
  short b:5;
  int c:23;
  int d:14;
};
TEST4(s4s5i23i14)
}
{
struct s7B0cii {
  short a:7;
  _Bool :0;
  char b;
  int c;
  int d;
};
TEST4(s7B0cii)
}
{
struct i10c7si17 {
  int a:10;
  char b:7;
  short c;
  int d:17;
};
TEST4(i10c7si17)
}
{
struct ic1B0b1i {
  int a;
  char b:1;
  _Bool :0;
  _Bool c:1;
  int d;
};
TEST4(ic1B0b1i)
}
{
struct ss4c3I3s7 {
  short a;
  short b:4;
  char c:3;
  int :3;
  short d:7;
};
TEST4(ss4c3I3s7)
}
{
struct s1C1s8b1c5 {
  short a:1;
  char :1;
  short b:8;
  _Bool c:1;
  char d:5;
};
TEST4(s1C1s8b1c5)
}
{
struct s1cc3b1 {
  short a:1;
  char b;
  char c:3;
  _Bool d:1;
};
TEST4(s1cc3b1)
}
{
struct s3icc4 {
  short a:3;
  int b;
  char c;
  char d:4;
};
TEST4(s3icc4)
}
{
struct s13i2b1c4 {
  short a:13;
  int b:2;
  _Bool c:1;
  char d:4;
};
TEST4(s13i2b1c4)
}
{
struct s13i1i6i25 {
  short a:13;
  int b:1;
  int c:6;
  int d:25;
};
TEST4(s13i1i6i25)
}
{
struct i12i32iC0i1 {
  int a:12;
  int b:32;
  int c;
  char :0;
  int d:1;
};
TEST4(i12i32iC0i1)
}
{
struct I10I26i2i29i10s {
  int :10;
  int :26;
  int a:2;
  int b:29;
  int c:10;
  short d;
};
TEST4(I10I26i2i29i10s)
}
{
struct s14i1c3b1 {
  short a:14;
  int b:1;
  char c:3;
  _Bool d:1;
};
TEST4(s14i1c3b1)
}
{
struct c2b1i12i3 {
  char a:2;
  _Bool b:1;
  int c:12;
  int d:3;
};
TEST4(c2b1i12i3)
}
{
struct s7ss16i4 {
  short a:7;
  short b;
  short c:16;
  int d:4;
};
TEST4(s7ss16i4)
}
{
struct i6s2i2c {
  int a:6;
  short b:2;
  int c:2;
  char d;
};
TEST4(i6s2i2c)
}
{
struct i1c7c1b {
  int a:1;
  char b:7;
  char c:1;
  _Bool d;
};
TEST4(i1c7c1b)
}
{
struct c4C8c1ci1 {
  char a:4;
  char :8;
  char b:1;
  char c;
  int d:1;
};
TEST4(c4C8c1ci1)
}
{
struct si4cc5 {
  short a;
  int b:4;
  char c;
  char d:5;
};
TEST4(si4cc5)
}
{
struct ii1ib1 {
  int a;
  int b:1;
  int c;
  _Bool d:1;
};
TEST4(ii1ib1)
}
{
struct ii14i6i {
  int a;
  int b:14;
  int c:6;
  int d;
};
TEST4(ii14i6i)
}
{
struct i4s15c4b {
  int a:4;
  short b:15;
  char c:4;
  _Bool d;
};
TEST4(i4s15c4b)
}
{
struct bi1s5s {
  _Bool a;
  int b:1;
  short c:5;
  short d;
};
TEST4(bi1s5s)
}
{
struct i17cs1i23 {
  int a:17;
  char b;
  short c:1;
  int d:23;
};
TEST4(i17cs1i23)
}
{
struct i11c3I0b1s9 {
  int a:11;
  char b:3;
  int :0;
  _Bool c:1;
  short d:9;
};
TEST4(i11c3I0b1s9)
}
{
struct i3iii11 {
  int a:3;
  int b;
  int c;
  int d:11;
};
TEST4(i3iii11)
}
{
struct s3sc6s1 {
  short a:3;
  short b;
  char c:6;
  short d:1;
};
TEST4(s3sc6s1)
}
{
struct i8i2s9i1 {
  int a:8;
  int b:2;
  short c:9;
  int d:1;
};
TEST4(i8i2s9i1)
}
{
struct S7i4i19B1bc2 {
  short :7;
  int a:4;
  int b:19;
  _Bool :1;
  _Bool c;
  char d:2;
};
TEST4(S7i4i19B1bc2)
}
{
struct s8i2i2s2 {
  short a:8;
  int b:2;
  int c:2;
  short d:2;
};
TEST4(s8i2i2s2)
}
{
struct c1S0i3i21S3b1 {
  char a:1;
  short :0;
  int b:3;
  int c:21;
  short :3;
  _Bool d:1;
};
TEST4(c1S0i3i21S3b1)
}
{
struct i2I4b1ii2 {
  int a:2;
  int :4;
  _Bool b:1;
  int c;
  int d:2;
};
TEST4(i2I4b1ii2)
}
{
struct I28sc6sc {
  int :28;
  short a;
  char b:6;
  short c;
  char d;
};
TEST4(I28sc6sc)
}
{
struct I0c5s4ii {
  int :0;
  char a:5;
  short b:4;
  int c;
  int d;
};
TEST4(I0c5s4ii)
}
{
struct c1s7i22i5 {
  char a:1;
  short b:7;
  int c:22;
  int d:5;
};
TEST4(c1s7i22i5)
}
{
struct s13bI7s2s3 {
  short a:13;
  _Bool b;
  int :7;
  short c:2;
  short d:3;
};
TEST4(s13bI7s2s3)
}
{
struct s3i14i18i3 {
  short a:3;
  int b:14;
  int c:18;
  int d:3;
};
TEST4(s3i14i18i3)
}
{
struct bcii10 {
  _Bool a;
  char b;
  int c;
  int d:10;
};
TEST4(bcii10)
}
{
struct s15c6I0S9I0bi {
  short a:15;
  char b:6;
  int :0;
  short :9;
  int :0;
  _Bool c;
  int d;
};
TEST4(s15c6I0S9I0bi)
}
{
struct c2c1s4c1 {
  char a:2;
  char b:1;
  short c:4;
  char d:1;
};
TEST4(c2c1s4c1)
}
{
struct s14c1B1c2c5 {
  short a:14;
  char b:1;
  _Bool :1;
  char c:2;
  char d:5;
};
TEST4(s14c1B1c2c5)
}
{
struct isC1i5C4c {
  int a;
  short b;
  char :1;
  int c:5;
  char :4;
  char d;
};
TEST4(isC1i5C4c)
}
{
struct i11i24c2b1 {
  int a:11;
  int b:24;
  char c:2;
  _Bool d:1;
};
TEST4(i11i24c2b1)
}
{
struct b1S0s2ci11 {
  _Bool a:1;
  short :0;
  short b:2;
  char c;
  int d:11;
};
TEST4(b1S0s2ci11)
}
{
struct C0C4i28i9is7 {
  char :0;
  char :4;
  int a:28;
  int b:9;
  int c;
  short d:7;
};
TEST4(C0C4i28i9is7)
}
{
struct i11i30s13i {
  int a:11;
  int b:30;
  short c:13;
  int d;
};
TEST4(i11i30s13i)
}
{
struct c3i2s13i4 {
  char a:3;
  int b:2;
  short c:13;
  int d:4;
};
TEST4(c3i2s13i4)
}
{
struct i1s2sc7 {
  int a:1;
  short b:2;
  short c;
  char d:7;
};
TEST4(i1s2sc7)
}
{
struct c3si10i1 {
  char a:3;
  short b;
  int c:10;
  int d:1;
};
TEST4(c3si10i1)
}
{
struct i6c5is {
  int a:6;
  char b:5;
  int c;
  short d;
};
TEST4(i6c5is)
}
{
struct i29c8C0s8c8 {
  int a:29;
  char b:8;
  char :0;
  short c:8;
  char d:8;
};
TEST4(i29c8C0s8c8)
}
{
struct i1i4ic4 {
  int a:1;
  int b:4;
  int c;
  char d:4;
};
TEST4(i1i4ic4)
}
{
struct s7s1c1s4 {
  short a:7;
  short b:1;
  char c:1;
  short d:4;
};
TEST4(s7s1c1s4)
}
{
struct s2b1B1I1ci1 {
  short a:2;
  _Bool b:1;
  _Bool :1;
  int :1;
  char c;
  int d:1;
};
TEST4(s2b1B1I1ci1)
}
{
struct c7i8s8i9 {
  char a:7;
  int b:8;
  short c:8;
  int d:9;
};
TEST4(c7i8s8i9)
}
{
struct c5b1i3S0C0I0s {
  char a:5;
  _Bool b:1;
  int c:3;
  short :0;
  char :0;
  int :0;
  short d;
};
TEST4(c5b1i3S0C0I0s)
}
{
struct i2S4i19s1i14 {
  int a:2;
  short :4;
  int b:19;
  short c:1;
  int d:14;
};
TEST4(i2S4i19s1i14)
}
{
struct csc1i22 {
  char a;
  short b;
  char c:1;
  int d:22;
};
TEST4(csc1i22)
}
{
struct i27i30c1i2 {
  int a:27;
  int b:30;
  char c:1;
  int d:2;
};
TEST4(i27i30c1i2)
}
{
struct cs9i18i {
  char a;
  short b:9;
  int c:18;
  int d;
};
TEST4(cs9i18i)
}
{
struct i12si2s16 {
  int a:12;
  short b;
  int c:2;
  short d:16;
};
TEST4(i12si2s16)
}
{
struct ib1i18i1 {
  int a;
  _Bool b:1;
  int c:18;
  int d:1;
};
TEST4(ib1i18i1)
}
{
struct i1I0b1bi1 {
  int a:1;
  int :0;
  _Bool b:1;
  _Bool c;
  int d:1;
};
TEST4(i1I0b1bi1)
}
{
struct i5C4i15i2c1 {
  int a:5;
  char :4;
  int b:15;
  int c:2;
  char d:1;
};
TEST4(i5C4i15i2c1)
}
{
struct b1I0s8ii7 {
  _Bool a:1;
  int :0;
  short b:8;
  int c;
  int d:7;
};
TEST4(b1I0s8ii7)
}
{
struct isc4s3 {
  int a;
  short b;
  char c:4;
  short d:3;
};
TEST4(isc4s3)
}
{
struct b1i5i2s {
  _Bool a:1;
  int b:5;
  int c:2;
  short d;
};
TEST4(b1i5i2s)
}
{
struct ci29i22i22 {
  char a;
  int b:29;
  int c:22;
  int d:22;
};
TEST4(ci29i22i22)
}
{
struct cci1i1 {
  char a;
  char b;
  int c:1;
  int d:1;
};
TEST4(cci1i1)
}
{
struct B1S9s9i7C0s4i3 {
  _Bool :1;
  short :9;
  short a:9;
  int b:7;
  char :0;
  short c:4;
  int d:3;
};
TEST4(B1S9s9i7C0s4i3)
}
{
struct i2i25i12I0b {
  int a:2;
  int b:25;
  int c:12;
  int :0;
  _Bool d;
};
TEST4(i2i25i12I0b)
}
{
struct S0b1ss5s9 {
  short :0;
  _Bool a:1;
  short b;
  short c:5;
  short d:9;
};
TEST4(S0b1ss5s9)
}
{
struct s15s6c8s7 {
  short a:15;
  short b:6;
  char c:8;
  short d:7;
};
TEST4(s15s6c8s7)
}
{
struct ii17b1i13 {
  int a;
  int b:17;
  _Bool c:1;
  int d:13;
};
TEST4(ii17b1i13)
}
{
struct s4i2ci16 {
  short a:4;
  int b:2;
  char c;
  int d:16;
};
TEST4(s4i2ci16)
}
{
struct i13s9c2s {
  int a:13;
  short b:9;
  char c:2;
  short d;
};
TEST4(i13s9c2s)
}
{
struct cb1i16s3 {
  char a;
  _Bool b:1;
  int c:16;
  short d:3;
};
TEST4(cb1i16s3)
}
{
struct ii20sc {
  int a;
  int b:20;
  short c;
  char d;
};
TEST4(ii20sc)
}
{
struct b1s13c3c2 {
  _Bool a:1;
  short b:13;
  char c:3;
  char d:2;
};
TEST4(b1s13c3c2)
}
{
struct i29i8i6s {
  int a:29;
  int b:8;
  int c:6;
  short d;
};
TEST4(i29i8i6s)
}
{
struct bic3i4 {
  _Bool a;
  int b;
  char c:3;
  int d:4;
};
TEST4(bic3i4)
}
{
struct i2bib {
  int a:2;
  _Bool b;
  int c;
  _Bool d;
};
TEST4(i2bib)
}
{
struct ii22ic5 {
  int a;
  int b:22;
  int c;
  char d:5;
};
TEST4(ii22ic5)
}
{
struct I0s15ii6i6 {
  int :0;
  short a:15;
  int b;
  int c:6;
  int d:6;
};
TEST4(I0s15ii6i6)
}
{
struct i1c2i1c3 {
  int a:1;
  char b:2;
  int c:1;
  char d:3;
};
TEST4(i1c2i1c3)
}
{
struct ci24i4i32 {
  char a;
  int b:24;
  int c:4;
  int d:32;
};
TEST4(ci24i4i32)
}
{
struct i3s6c3s {
  int a:3;
  short b:6;
  char c:3;
  short d;
};
TEST4(i3s6c3s)
}
{
struct i32i15i12s8 {
  int a:32;
  int b:15;
  int c:12;
  short d:8;
};
TEST4(i32i15i12s8)
}
{
struct s8i1b1i1 {
  short a:8;
  int b:1;
  _Bool c:1;
  int d:1;
};
TEST4(s8i1b1i1)
}
{
struct b1s16s13i14 {
  _Bool a:1;
  short b:16;
  short c:13;
  int d:14;
};
TEST4(b1s16s13i14)
}
{
struct s8i5c1i9 {
  short a:8;
  int b:5;
  char c:1;
  int d:9;
};
TEST4(s8i5c1i9)
}
{
struct i3s2s15b {
  int a:3;
  short b:2;
  short c:15;
  _Bool d;
};
TEST4(i3s2s15b)
}
{
struct b1sb1i30 {
  _Bool a:1;
  short b;
  _Bool c:1;
  int d:30;
};
TEST4(b1sb1i30)
}
{
struct i7c1s10C5B1i11 {
  int a:7;
  char b:1;
  short c:10;
  char :5;
  _Bool :1;
  int d:11;
};
TEST4(i7c1s10C5B1i11)
}
{
struct i5i9s12i1 {
  int a:5;
  int b:9;
  short c:12;
  int d:1;
};
TEST4(i5i9s12i1)
}
{
struct ici3c {
  int a;
  char b;
  int c:3;
  char d;
};
TEST4(ici3c)
}
{
struct i2b1ss5 {
  int a:2;
  _Bool b:1;
  short c;
  short d:5;
};
TEST4(i2b1ss5)
}
{
struct bs5sc3 {
  _Bool a;
  short b:5;
  short c;
  char d:3;
};
TEST4(bs5sc3)
}
{
struct ci17c1C3s2 {
  char a;
  int b:17;
  char c:1;
  char :3;
  short d:2;
};
TEST4(ci17c1C3s2)
}
{
struct i5si12i6 {
  int a:5;
  short b;
  int c:12;
  int d:6;
};
TEST4(i5si12i6)
}
{
struct C2S0i1c3i2c6 {
  char :2;
  short :0;
  int a:1;
  char b:3;
  int c:2;
  char d:6;
};
TEST4(C2S0i1c3i2c6)
}
{
struct C1i21ii2c1 {
  char :1;
  int a:21;
  int b;
  int c:2;
  char d:1;
};
TEST4(C1i21ii2c1)
}
{
struct i12i18i9c4 {
  int a:12;
  int b:18;
  int c:9;
  char d:4;
};
TEST4(i12i18i9c4)
}
{
struct i8i15s2c {
  int a:8;
  int b:15;
  short c:2;
  char d;
};
TEST4(i8i15s2c)
}
{
struct S8i9ss1i {
  short :8;
  int a:9;
  short b;
  short c:1;
  int d;
};
TEST4(S8i9ss1i)
}
{
struct I2i1s9b1i30 {
  int :2;
  int a:1;
  short b:9;
  _Bool c:1;
  int d:30;
};
TEST4(I2i1s9b1i30)
}
{
struct s1ic5i24 {
  short a:1;
  int b;
  char c:5;
  int d:24;
};
TEST4(s1ic5i24)
}
{
struct I0c1iii2 {
  int :0;
  char a:1;
  int b;
  int c;
  int d:2;
};
TEST4(I0c1iii2)
}
{
struct c4ib1s6 {
  char a:4;
  int b;
  _Bool c:1;
  short d:6;
};
TEST4(c4ib1s6)
}
{
struct B1C6s1s10I9s1s {
  _Bool :1;
  char :6;
  short a:1;
  short b:10;
  int :9;
  short c:1;
  short d;
};
TEST4(B1C6s1s10I9s1s)
}
{
struct ss6c1i {
  short a;
  short b:6;
  char c:1;
  int d;
};
TEST4(ss6c1i)
}
{
struct c5s4i12i14 {
  char a:5;
  short b:4;
  int c:12;
  int d:14;
};
TEST4(c5s4i12i14)
}
{
struct i1i4i32i2 {
  int a:1;
  int b:4;
  int c:32;
  int d:2;
};
TEST4(i1i4i32i2)
}
{
struct c5I19is16s2 {
  char a:5;
  int :19;
  int b;
  short c:16;
  short d:2;
};
TEST4(c5I19is16s2)
}
{
struct iI13s12ii {
  int a;
  int :13;
  short b:12;
  int c;
  int d;
};
TEST4(iI13s12ii)
}
{
struct s13s4c2i10 {
  short a:13;
  short b:4;
  char c:2;
  int d:10;
};
TEST4(s13s4c2i10)
}
{
struct I0s9s6s10b1 {
  int :0;
  short a:9;
  short b:6;
  short c:10;
  _Bool d:1;
};
TEST4(I0s9s6s10b1)
}
{
struct is7i32s15 {
  int a;
  short b:7;
  int c:32;
  short d:15;
};
TEST4(is7i32s15)
}
{
struct i9b1s4i1 {
  int a:9;
  _Bool b:1;
  short c:4;
  int d:1;
};
TEST4(i9b1s4i1)
}
{
struct s1I2c3S12s9s5 {
  short a:1;
  int :2;
  char b:3;
  short :12;
  short c:9;
  short d:5;
};
TEST4(s1I2c3S12s9s5)
}
{
struct i2b1si7 {
  int a:2;
  _Bool b:1;
  short c;
  int d:7;
};
TEST4(i2b1si7)
}
{
struct I1i24i18s14s1 {
  int :1;
  int a:24;
  int b:18;
  short c:14;
  short d:1;
};
TEST4(I1i24i18s14s1)
}
{
struct si12S0s2i14 {
  short a;
  int b:12;
  short :0;
  short c:2;
  int d:14;
};
TEST4(si12S0s2i14)
}
{
struct B1i2i2c1b1 {
  _Bool :1;
  int a:2;
  int b:2;
  char c:1;
  _Bool d:1;
};
TEST4(B1i2i2c1b1)
}
{
struct i3si1i25 {
  int a:3;
  short b;
  int c:1;
  int d:25;
};
TEST4(i3si1i25)
}
{
struct s1i17i29i18 {
  short a:1;
  int b:17;
  int c:29;
  int d:18;
};
TEST4(s1i17i29i18)
}
{
struct i2B0i11i27b1 {
  int a:2;
  _Bool :0;
  int b:11;
  int c:27;
  _Bool d:1;
};
TEST4(i2B0i11i27b1)
}
{
struct c7s4si3 {
  char a:7;
  short b:4;
  short c;
  int d:3;
};
TEST4(c7s4si3)
}
{
struct ccs6i3 {
  char a;
  char b;
  short c:6;
  int d:3;
};
TEST4(ccs6i3)
}
{
struct c7s7s3c {
  char a:7;
  short b:7;
  short c:3;
  char d;
};
TEST4(c7s7s3c)
}
{
struct i21sS0s14i6 {
  int a:21;
  short b;
  short :0;
  short c:14;
  int d:6;
};
TEST4(i21sS0s14i6)
}
{
struct s2icI0i1 {
  short a:2;
  int b;
  char c;
  int :0;
  int d:1;
};
TEST4(s2icI0i1)
}
{
struct c1C5ii6b1 {
  char a:1;
  char :5;
  int b;
  int c:6;
  _Bool d:1;
};
TEST4(c1C5ii6b1)
}
{
struct s1c1s8i8 {
  short a:1;
  char b:1;
  short c:8;
  int d:8;
};
TEST4(s1c1s8i8)
}
{
struct ib1i7I6b {
  int a;
  _Bool b:1;
  int c:7;
  int :6;
  _Bool d;
};
TEST4(ib1i7I6b)
}
{
struct c3s8i8I4i14 {
  char a:3;
  short b:8;
  int c:8;
  int :4;
  int d:14;
};
TEST4(c3s8i8I4i14)
}
{
struct b1s4s11c4 {
  _Bool a:1;
  short b:4;
  short c:11;
  char d:4;
};
TEST4(b1s4s11c4)
}
{
struct i2c4i22i22 {
  int a:2;
  char b:4;
  int c:22;
  int d:22;
};
TEST4(i2c4i22i22)
}
{
struct s16sb1i12 {
  short a:16;
  short b;
  _Bool c:1;
  int d:12;
};
TEST4(s16sb1i12)
}
{
struct i9i4cc4 {
  int a:9;
  int b:4;
  char c;
  char d:4;
};
TEST4(i9i4cc4)
}
{
struct cc6i8i {
  char a;
  char b:6;
  int c:8;
  int d;
};
TEST4(cc6i8i)
}
{
struct i2ic4i6 {
  int a:2;
  int b;
  char c:4;
  int d:6;
};
TEST4(i2ic4i6)
}
{
struct b1c7C2c2c1 {
  _Bool a:1;
  char b:7;
  char :2;
  char c:2;
  char d:1;
};
TEST4(b1c7C2c2c1)
}
{
struct I19c5si8c6 {
  int :19;
  char a:5;
  short b;
  int c:8;
  char d:6;
};
TEST4(I19c5si8c6)
}
{
struct c8I0c1I7b1i6 {
  char a:8;
  int :0;
  char b:1;
  int :7;
  _Bool c:1;
  int d:6;
};
TEST4(c8I0c1I7b1i6)
}
{
struct i7s6ii12 {
  int a:7;
  short b:6;
  int c;
  int d:12;
};
TEST4(i7s6ii12)
}
{
struct i1i1c3s3 {
  int a:1;
  int b:1;
  char c:3;
  short d:3;
};
TEST4(i1i1c3s3)
}
{
struct s11bi2i {
  short a:11;
  _Bool b;
  int c:2;
  int d;
};
TEST4(s11bi2i)
}
{
struct s1si7c1 {
  short a:1;
  short b;
  int c:7;
  char d:1;
};
TEST4(s1si7c1)
}
{
struct c2I9s9ic {
  char a:2;
  int :9;
  short b:9;
  int c;
  char d;
};
TEST4(c2I9s9ic)
}
{
struct s6sb1c {
  short a:6;
  short b;
  _Bool c:1;
  char d;
};
TEST4(s6sb1c)
}
{
struct s5b1i4b1 {
  short a:5;
  _Bool b:1;
  int c:4;
  _Bool d:1;
};
TEST4(s5b1i4b1)
}
{
struct s3i1s16c8 {
  short a:3;
  int b:1;
  short c:16;
  char d:8;
};
TEST4(s3i1s16c8)
}
{
struct B0si1b1b1 {
  _Bool :0;
  short a;
  int b:1;
  _Bool c:1;
  _Bool d:1;
};
TEST4(B0si1b1b1)
}
{
struct I4b1s5s5c5 {
  int :4;
  _Bool a:1;
  short b:5;
  short c:5;
  char d:5;
};
TEST4(I4b1s5s5c5)
}
{
struct sb1si7 {
  short a;
  _Bool b:1;
  short c;
  int d:7;
};
TEST4(sb1si7)
}
{
struct c1i28i1i26 {
  char a:1;
  int b:28;
  int c:1;
  int d:26;
};
TEST4(c1i28i1i26)
}
{
struct c1c1i2c6 {
  char a:1;
  char b:1;
  int c:2;
  char d:6;
};
TEST4(c1c1i2c6)
}
{
struct S2ib1S0si16 {
  short :2;
  int a;
  _Bool b:1;
  short :0;
  short c;
  int d:16;
};
TEST4(S2ib1S0si16)
}
{
struct i28s6c1S1i {
  int a:28;
  short b:6;
  char c:1;
  short :1;
  int d;
};
TEST4(i28s6c1S1i)
}
{
struct i7iii1 {
  int a:7;
  int b;
  int c;
  int d:1;
};
TEST4(i7iii1)
}
{
struct i4bc1i7 {
  int a:4;
  _Bool b;
  char c:1;
  int d:7;
};
TEST4(i4bc1i7)
}
{
struct i10cI32bs10 {
  int a:10;
  char b;
  int :32;
  _Bool c;
  short d:10;
};
TEST4(i10cI32bs10)
}
{
struct i5s7i2b1 {
  int a:5;
  short b:7;
  int c:2;
  _Bool d:1;
};
TEST4(i5s7i2b1)
}
{
struct b1ci2I2i {
  _Bool a:1;
  char b;
  int c:2;
  int :2;
  int d;
};
TEST4(b1ci2I2i)
}
{
struct i1i4cs {
  int a:1;
  int b:4;
  char c;
  short d;
};
TEST4(i1i4cs)
}
{
struct b1ss8i17 {
  _Bool a:1;
  short b;
  short c:8;
  int d:17;
};
TEST4(b1ss8i17)
}
{
struct ss7i3i {
  short a;
  short b:7;
  int c:3;
  int d;
};
TEST4(ss7i3i)
}
{
struct s15s4c1i17 {
  short a:15;
  short b:4;
  char c:1;
  int d:17;
};
TEST4(s15s4c1i17)
}
{
struct i8c7i4s11 {
  int a:8;
  char b:7;
  int c:4;
  short d:11;
};
TEST4(i8c7i4s11)
}
{
struct i11bC1i5i {
  int a:11;
  _Bool b;
  char :1;
  int c:5;
  int d;
};
TEST4(i11bC1i5i)
}
{
struct c8i13i1b {
  char a:8;
  int b:13;
  int c:1;
  _Bool d;
};
TEST4(c8i13i1b)
}
{
struct b1i10C7i2s2 {
  _Bool a:1;
  int b:10;
  char :7;
  int c:2;
  short d:2;
};
TEST4(b1i10C7i2s2)
}
{
struct i7S3s9b1b {
  int a:7;
  short :3;
  short b:9;
  _Bool c:1;
  _Bool d;
};
TEST4(i7S3s9b1b)
}
{
struct I27si6cs5 {
  int :27;
  short a;
  int b:6;
  char c;
  short d:5;
};
TEST4(I27si6cs5)
}
{
struct c8i9s5c4 {
  char a:8;
  int b:9;
  short c:5;
  char d:4;
};
TEST4(c8i9s5c4)
}
{
struct ic1C2c1i10 {
  int a;
  char b:1;
  char :2;
  char c:1;
  int d:10;
};
TEST4(ic1C2c1i10)
}
{
struct i11iI4sc4 {
  int a:11;
  int b;
  int :4;
  short c;
  char d:4;
};
TEST4(i11iI4sc4)
}
{
struct i16i7i12s1 {
  int a:16;
  int b:7;
  int c:12;
  short d:1;
};
TEST4(i16i7i12s1)
}
{
struct ii8ii1 {
  int a;
  int b:8;
  int c;
  int d:1;
};
TEST4(ii8ii1)
}
{
struct s14i13i2i {
  short a:14;
  int b:13;
  int c:2;
  int d;
};
TEST4(s14i13i2i)
}
{
struct i7bC2s13s {
  int a:7;
  _Bool b;
  char :2;
  short c:13;
  short d;
};
TEST4(i7bC2s13s)
}
{
struct c3c1i1c1 {
  char a:3;
  char b:1;
  int c:1;
  char d:1;
};
TEST4(c3c1i1c1)
}
{
struct c2I0C1s8i5i7 {
  char a:2;
  int :0;
  char :1;
  short b:8;
  int c:5;
  int d:7;
};
TEST4(c2I0C1s8i5i7)
}
{
struct s13i1i5b1 {
  short a:13;
  int b:1;
  int c:5;
  _Bool d:1;
};
TEST4(s13i1i5b1)
}
{
struct s6c6i6i1 {
  short a:6;
  char b:6;
  int c:6;
  int d:1;
};
TEST4(s6c6i6i1)
}
{
struct bi20i16c3 {
  _Bool a;
  int b:20;
  int c:16;
  char d:3;
};
TEST4(bi20i16c3)
}
{
struct bs1ii14 {
  _Bool a;
  short b:1;
  int c;
  int d:14;
};
TEST4(bs1ii14)
}
{
struct iS0c8i8b {
  int a;
  short :0;
  char b:8;
  int c:8;
  _Bool d;
};
TEST4(iS0c8i8b)
}
{
struct s6iii1 {
  short a:6;
  int b;
  int c;
  int d:1;
};
TEST4(s6iii1)
}
{
struct i2s3i11b {
  int a:2;
  short b:3;
  int c:11;
  _Bool d;
};
TEST4(i2s3i11b)
}
{
struct i9ii25i {
  int a:9;
  int b;
  int c:25;
  int d;
};
TEST4(i9ii25i)
}
{
struct c4c2cs4 {
  char a:4;
  char b:2;
  char c;
  short d:4;
};
TEST4(c4c2cs4)
}
{
struct I0i5c1ib1 {
  int :0;
  int a:5;
  char b:1;
  int c;
  _Bool d:1;
};
TEST4(I0i5c1ib1)
}
{
struct csis2 {
  char a;
  short b;
  int c;
  short d:2;
};
TEST4(csis2)
}
{
struct c5i25s15s6 {
  char a:5;
  int b:25;
  short c:15;
  short d:6;
};
TEST4(c5i25s15s6)
}
{
struct c1s8ci5 {
  char a:1;
  short b:8;
  char c;
  int d:5;
};
TEST4(c1s8ci5)
}
{
struct c1s8c2s6 {
  char a:1;
  short b:8;
  char c:2;
  short d:6;
};
TEST4(c1s8c2s6)
}
{
struct ss16i9i1 {
  short a;
  short b:16;
  int c:9;
  int d:1;
};
TEST4(ss16i9i1)
}
{
struct c1s10c4b1 {
  char a:1;
  short b:10;
  char c:4;
  _Bool d:1;
};
TEST4(c1s10c4b1)
}
{
struct b1b1i13i {
  _Bool a:1;
  _Bool b:1;
  int c:13;
  int d;
};
TEST4(b1b1i13i)
}
{
struct b1s6sc7 {
  _Bool a:1;
  short b:6;
  short c;
  char d:7;
};
TEST4(b1s6sc7)
}
{
struct i18i14i1C0i3 {
  int a:18;
  int b:14;
  int c:1;
  char :0;
  int d:3;
};
TEST4(i18i14i1C0i3)
}
{
struct I20s6c1c1b1 {
  int :20;
  short a:6;
  char b:1;
  char c:1;
  _Bool d:1;
};
TEST4(I20s6c1c1b1)
}
{
struct i21b1I20b1c1 {
  int a:21;
  _Bool b:1;
  int :20;
  _Bool c:1;
  char d:1;
};
TEST4(i21b1I20b1c1)
}
{
struct s1s2s12I0s {
  short a:1;
  short b:2;
  short c:12;
  int :0;
  short d;
};
TEST4(s1s2s12I0s)
}
{
struct scc1c1 {
  short a;
  char b;
  char c:1;
  char d:1;
};
TEST4(scc1c1)
}
{
struct i3i4b1s2 {
  int a:3;
  int b:4;
  _Bool c:1;
  short d:2;
};
TEST4(i3i4b1s2)
}
{
struct s5i2bI0c3 {
  short a:5;
  int b:2;
  _Bool c;
  int :0;
  char d:3;
};
TEST4(s5i2bI0c3)
}
{
struct b1b1i1i {
  _Bool a:1;
  _Bool b:1;
  int c:1;
  int d;
};
TEST4(b1b1i1i)
}
{
struct s10c1ii {
  short a:10;
  char b:1;
  int c;
  int d;
};
TEST4(s10c1ii)
}
{
struct i23s5b1s15 {
  int a:23;
  short b:5;
  _Bool c:1;
  short d:15;
};
TEST4(i23s5b1s15)
}
{
struct i2s5i3s4 {
  int a:2;
  short b:5;
  int c:3;
  short d:4;
};
TEST4(i2s5i3s4)
}
{
struct bsiS1i {
  _Bool a;
  short b;
  int c;
  short :1;
  int d;
};
TEST4(bsiS1i)
}
{
struct c6i16i3s2 {
  char a:6;
  int b:16;
  int c:3;
  short d:2;
};
TEST4(c6i16i3s2)
}
{
struct cI4s5i1i {
  char a;
  int :4;
  short b:5;
  int c:1;
  int d;
};
TEST4(cI4s5i1i)
}
{
struct c5s2ci {
  char a:5;
  short b:2;
  char c;
  int d;
};
TEST4(c5s2ci)
}
{
struct B0ii1cs11 {
  _Bool :0;
  int a;
  int b:1;
  char c;
  short d:11;
};
TEST4(B0ii1cs11)
}
{
struct c4s2b1s3 {
  char a:4;
  short b:2;
  _Bool c:1;
  short d:3;
};
TEST4(c4s2b1s3)
}
{
struct s15bb1s2 {
  short a:15;
  _Bool b;
  _Bool c:1;
  short d:2;
};
TEST4(s15bb1s2)
}
{
struct sii24i {
  short a;
  int b;
  int c:24;
  int d;
};
TEST4(sii24i)
}
{
struct i7i18s12b1 {
  int a:7;
  int b:18;
  short c:12;
  _Bool d:1;
};
TEST4(i7i18s12b1)
}
{
struct i5i5c4s1 {
  int a:5;
  int b:5;
  char c:4;
  short d:1;
};
TEST4(i5i5c4s1)
}
{
struct si15B0c4b1 {
  short a;
  int b:15;
  _Bool :0;
  char c:4;
  _Bool d:1;
};
TEST4(si15B0c4b1)
}
{
struct c2i10cb1 {
  char a:2;
  int b:10;
  char c;
  _Bool d:1;
};
TEST4(c2i10cb1)
}
{
struct s7I1cc5i10 {
  short a:7;
  int :1;
  char b;
  char c:5;
  int d:10;
};
TEST4(s7I1cc5i10)
}
{
struct cI0iis {
  char a;
  int :0;
  int b;
  int c;
  short d;
};
TEST4(cI0iis)
}
{
struct i6i4s4i14 {
  int a:6;
  int b:4;
  short c:4;
  int d:14;
};
TEST4(i6i4s4i14)
}
{
struct S15s9i17c7s13 {
  short :15;
  short a:9;
  int b:17;
  char c:7;
  short d:13;
};
TEST4(S15s9i17c7s13)
}
{
struct i1b1s8s3 {
  int a:1;
  _Bool b:1;
  short c:8;
  short d:3;
};
TEST4(i1b1s8s3)
}
{
struct b1i6cs4 {
  _Bool a:1;
  int b:6;
  char c;
  short d:4;
};
TEST4(b1i6cs4)
}
{
struct b1c3i5c1 {
  _Bool a:1;
  char b:3;
  int c:5;
  char d:1;
};
TEST4(b1c3i5c1)
}
{
struct c3si4S7c6 {
  char a:3;
  short b;
  int c:4;
  short :7;
  char d:6;
};
TEST4(c3si4S7c6)
}
{
struct ii13ci {
  int a;
  int b:13;
  char c;
  int d;
};
TEST4(ii13ci)
}
{
struct c6i7S13c5s9 {
  char a:6;
  int b:7;
  short :13;
  char c:5;
  short d:9;
};
TEST4(c6i7S13c5s9)
}
{
struct s9i11i5s4 {
  short a:9;
  int b:11;
  int c:5;
  short d:4;
};
TEST4(s9i11i5s4)
}
{
struct s3s6i32c1 {
  short a:3;
  short b:6;
  int c:32;
  char d:1;
};
TEST4(s3s6i32c1)
}
{
struct c1bC8s7i2 {
  char a:1;
  _Bool b;
  char :8;
  short c:7;
  int d:2;
};
TEST4(c1bC8s7i2)
}
{
struct C2c2s8i1c5 {
  char :2;
  char a:2;
  short b:8;
  int c:1;
  char d:5;
};
TEST4(C2c2s8i1c5)
}
{
struct sii1i {
  short a;
  int b;
  int c:1;
  int d;
};
TEST4(sii1i)
}
{
struct s4ss11c3 {
  short a:4;
  short b;
  short c:11;
  char d:3;
};
TEST4(s4ss11c3)
}
{
struct i19i2ic1 {
  int a:19;
  int b:2;
  int c;
  char d:1;
};
TEST4(i19i2ic1)
}
{
struct ic5i21i3 {
  int a;
  char b:5;
  int c:21;
  int d:3;
};
TEST4(ic5i21i3)
}
{
struct c2i1i3s4 {
  char a:2;
  int b:1;
  int c:3;
  short d:4;
};
TEST4(c2i1i3s4)
}
{
struct i2c3sb1 {
  int a:2;
  char b:3;
  short c;
  _Bool d:1;
};
TEST4(i2c3sb1)
}
{
struct c3i3c3c4 {
  char a:3;
  int b:3;
  char c:3;
  char d:4;
};
TEST4(c3i3c3c4)
}
{
struct bc4i1c5 {
  _Bool a;
  char b:4;
  int c:1;
  char d:5;
};
TEST4(bc4i1c5)
}
{
struct s2c2sc6 {
  short a:2;
  char b:2;
  short c;
  char d:6;
};
TEST4(s2c2sc6)
}
{
struct i6bc5b1 {
  int a:6;
  _Bool b;
  char c:5;
  _Bool d:1;
};
TEST4(i6bc5b1)
}
{
struct ib1bi3 {
  int a;
  _Bool b:1;
  _Bool c;
  int d:3;
};
TEST4(ib1bi3)
}
{
struct I2ics1S3s1 {
  int :2;
  int a;
  char b;
  short c:1;
  short :3;
  short d:1;
};
TEST4(I2ics1S3s1)
}
{
struct I5i2s5i1s4 {
  int :5;
  int a:2;
  short b:5;
  int c:1;
  short d:4;
};
TEST4(I5i2s5i1s4)
}
{
struct s12s5i18b {
  short a:12;
  short b:5;
  int c:18;
  _Bool d;
};
TEST4(s12s5i18b)
}
{
struct ic3c7b1 {
  int a;
  char b:3;
  char c:7;
  _Bool d:1;
};
TEST4(ic3c7b1)
}
{
struct c1s7s3i1 {
  char a:1;
  short b:7;
  short c:3;
  int d:1;
};
TEST4(c1s7s3i1)
}
{
struct s4c7I9s7i31 {
  short a:4;
  char b:7;
  int :9;
  short c:7;
  int d:31;
};
TEST4(s4c7I9s7i31)
}
{
struct i2ii13C8c6 {
  int a:2;
  int b;
  int c:13;
  char :8;
  char d:6;
};
TEST4(i2ii13C8c6)
}
{
struct c4si14i17 {
  char a:4;
  short b;
  int c:14;
  int d:17;
};
TEST4(c4si14i17)
}
{
struct s1c1ii1 {
  short a:1;
  char b:1;
  int c;
  int d:1;
};
TEST4(s1c1ii1)
}
{
struct is13c1i14 {
  int a;
  short b:13;
  char c:1;
  int d:14;
};
TEST4(is13c1i14)
}
{
struct ci2s2b1 {
  char a;
  int b:2;
  short c:2;
  _Bool d:1;
};
TEST4(ci2s2b1)
}
{
struct b1si2c3 {
  _Bool a:1;
  short b;
  int c:2;
  char d:3;
};
TEST4(b1si2c3)
}
{
struct b1s12s14s {
  _Bool a:1;
  short b:12;
  short c:14;
  short d;
};
TEST4(b1s12s14s)
}
{
struct ii26ci7 {
  int a;
  int b:26;
  char c;
  int d:7;
};
TEST4(ii26ci7)
}
{
struct b1ib1c {
  _Bool a:1;
  int b;
  _Bool c:1;
  char d;
};
TEST4(b1ib1c)
}
{
struct I0s7ib1c5 {
  int :0;
  short a:7;
  int b;
  _Bool c:1;
  char d:5;
};
TEST4(I0s7ib1c5)
}
{
struct s2c1bs8 {
  short a:2;
  char b:1;
  _Bool c;
  short d:8;
};
TEST4(s2c1bs8)
}
{
struct I6s11c3I0ss {
  int :6;
  short a:11;
  char b:3;
  int :0;
  short c;
  short d;
};
TEST4(I6s11c3I0ss)
}
{
struct s13s1s4c7 {
  short a:13;
  short b:1;
  short c:4;
  char d:7;
};
TEST4(s13s1s4c7)
}
{
struct S5b1s1i14c6 {
  short :5;
  _Bool a:1;
  short b:1;
  int c:14;
  char d:6;
};
TEST4(S5b1s1i14c6)
}
{
struct s3s2cc5 {
  short a:3;
  short b:2;
  char c;
  char d:5;
};
TEST4(s3s2cc5)
}
{
struct ii9i3s8 {
  int a;
  int b:9;
  int c:3;
  short d:8;
};
TEST4(ii9i3s8)
}
{
struct i31c5s16i2 {
  int a:31;
  char b:5;
  short c:16;
  int d:2;
};
TEST4(i31c5s16i2)
}
{
struct c1ss13i17 {
  char a:1;
  short b;
  short c:13;
  int d:17;
};
TEST4(c1ss13i17)
}
{
struct C0s14i2c8i9 {
  char :0;
  short a:14;
  int b:2;
  char c:8;
  int d:9;
};
TEST4(C0s14i2c8i9)
}
{
struct i7s15s8c1 {
  int a:7;
  short b:15;
  short c:8;
  char d:1;
};
TEST4(i7s15s8c1)
}
{
struct C0c1i1sb {
  char :0;
  char a:1;
  int b:1;
  short c;
  _Bool d;
};
TEST4(C0c1i1sb)
}
{
struct s1b1i1b1 {
  short a:1;
  _Bool b:1;
  int c:1;
  _Bool d:1;
};
TEST4(s1b1i1b1)
}
{
struct i1i6is {
  int a:1;
  int b:6;
  int c;
  short d;
};
TEST4(i1i6is)
}
{
struct i10b1i21i7 {
  int a:10;
  _Bool b:1;
  int c:21;
  int d:7;
};
TEST4(i10b1i21i7)
}
{
struct c2b1s13s9 {
  char a:2;
  _Bool b:1;
  short c:13;
  short d:9;
};
TEST4(c2b1s13s9)
}
{
struct i14i14ii31 {
  int a:14;
  int b:14;
  int c;
  int d:31;
};
TEST4(i14i14ii31)
}
{
struct s2i2i24S0i32 {
  short a:2;
  int b:2;
  int c:24;
  short :0;
  int d:32;
};
TEST4(s2i2i24S0i32)
}
{
struct s10i2s1b1 {
  short a:10;
  int b:2;
  short c:1;
  _Bool d:1;
};
TEST4(s10i2s1b1)
}
{
struct c3ic2b1 {
  char a:3;
  int b;
  char c:2;
  _Bool d:1;
};
TEST4(c3ic2b1)
}
{
struct sc4ss13 {
  short a;
  char b:4;
  short c;
  short d:13;
};
TEST4(sc4ss13)
}
{
struct i5i11C0i31i12 {
  int a:5;
  int b:11;
  char :0;
  int c:31;
  int d:12;
};
TEST4(i5i11C0i31i12)
}
{
struct i28i6ic6 {
  int a:28;
  int b:6;
  int c;
  char d:6;
};
TEST4(i28i6ic6)
}
{
struct s16c5c5i5 {
  short a:16;
  char b:5;
  char c:5;
  int d:5;
};
TEST4(s16c5c5i5)
}
{
struct c5i2C1bc2 {
  char a:5;
  int b:2;
  char :1;
  _Bool c;
  char d:2;
};
TEST4(c5i2C1bc2)
}
{
struct c1i12i2b1 {
  char a:1;
  int b:12;
  int c:2;
  _Bool d:1;
};
TEST4(c1i12i2b1)
}
{
struct c3S5bs2i {
  char a:3;
  short :5;
  _Bool b;
  short c:2;
  int d;
};
TEST4(c3S5bs2i)
}
{
struct i4b1b1i24 {
  int a:4;
  _Bool b:1;
  _Bool c:1;
  int d:24;
};
TEST4(i4b1b1i24)
}
{
struct ci32sc1 {
  char a;
  int b:32;
  short c;
  char d:1;
};
TEST4(ci32sc1)
}
{
struct S12c7bC2i1b1 {
  short :12;
  char a:7;
  _Bool b;
  char :2;
  int c:1;
  _Bool d:1;
};
TEST4(S12c7bC2i1b1)
}
{
struct i24s12s1s10 {
  int a:24;
  short b:12;
  short c:1;
  short d:10;
};
TEST4(i24s12s1s10)
}
{
struct ic1cc5 {
  int a;
  char b:1;
  char c;
  char d:5;
};
TEST4(ic1cc5)
}
{
struct i4s4i5b1 {
  int a:4;
  short b:4;
  int c:5;
  _Bool d:1;
};
TEST4(i4s4i5b1)
}
{
struct i31i1c2b1 {
  int a:31;
  int b:1;
  char c:2;
  _Bool d:1;
};
TEST4(i31i1c2b1)
}
{
struct is9b1c3 {
  int a;
  short b:9;
  _Bool c:1;
  char d:3;
};
TEST4(is9b1c3)
}
{
struct i16icI2s11 {
  int a:16;
  int b;
  char c;
  int :2;
  short d:11;
};
TEST4(i16icI2s11)
}
{
struct b1i25i9i {
  _Bool a:1;
  int b:25;
  int c:9;
  int d;
};
TEST4(b1i25i9i)
}
{
struct i1c1c2c {
  int a:1;
  char b:1;
  char c:2;
  char d;
};
TEST4(i1c1c2c)
}
{
struct i1i11ic {
  int a:1;
  int b:11;
  int c;
  char d;
};
TEST4(i1i11ic)
}
{
struct sii5b {
  short a;
  int b;
  int c:5;
  _Bool d;
};
TEST4(sii5b)
}
{
struct I1c5s14i1c {
  int :1;
  char a:5;
  short b:14;
  int c:1;
  char d;
};
TEST4(I1c5s14i1c)
}
{
struct c4i4b1s {
  char a:4;
  int b:4;
  _Bool c:1;
  short d;
};
TEST4(c4i4b1s)
}
{
struct i31csc3 {
  int a:31;
  char b;
  short c;
  char d:3;
};
TEST4(i31csc3)
}
{
struct c2b1i7i4 {
  char a:2;
  _Bool b:1;
  int c:7;
  int d:4;
};
TEST4(c2b1i7i4)
}
{
struct i27i4ii29 {
  int a:27;
  int b:4;
  int c;
  int d:29;
};
TEST4(i27i4ii29)
}
{
struct c7s4s1i6 {
  char a:7;
  short b:4;
  short c:1;
  int d:6;
};
TEST4(c7s4s1i6)
}
{
struct S3is2i7C3i1 {
  short :3;
  int a;
  short b:2;
  int c:7;
  char :3;
  int d:1;
};
TEST4(S3is2i7C3i1)
}
{
struct ii7s2i31 {
  int a;
  int b:7;
  short c:2;
  int d:31;
};
TEST4(ii7s2i31)
}
{
struct ic2i2i2 {
  int a;
  char b:2;
  int c:2;
  int d:2;
};
TEST4(ic2i2i2)
}
{
struct i28bI3s4i3 {
  int a:28;
  _Bool b;
  int :3;
  short c:4;
  int d:3;
};
TEST4(i28bI3s4i3)
}
{
struct i11c1s10i {
  int a:11;
  char b:1;
  short c:10;
  int d;
};
TEST4(i11c1s10i)
}
{
struct s4c1cc5 {
  short a:4;
  char b:1;
  char c;
  char d:5;
};
TEST4(s4c1cc5)
}
{
struct ic3I5ci5 {
  int a;
  char b:3;
  int :5;
  char c;
  int d:5;
};
TEST4(ic3I5ci5)
}
{
struct i1I0C0i31ic {
  int a:1;
  int :0;
  char :0;
  int b:31;
  int c;
  char d;
};
TEST4(i1I0C0i31ic)
}
{
struct sc1s10c {
  short a;
  char b:1;
  short c:10;
  char d;
};
TEST4(sc1s10c)
}
{
struct s3b1i19i4 {
  short a:3;
  _Bool b:1;
  int c:19;
  int d:4;
};
TEST4(s3b1i19i4)
}
{
struct i25b1I3s2s {
  int a:25;
  _Bool b:1;
  int :3;
  short c:2;
  short d;
};
TEST4(i25b1I3s2s)
}
{
struct s2ccS3i26 {
  short a:2;
  char b;
  char c;
  short :3;
  int d:26;
};
TEST4(s2ccS3i26)
}
{
struct i28s16i2b {
  int a:28;
  short b:16;
  int c:2;
  _Bool d;
};
TEST4(i28s16i2b)
}
{
struct c8c2i4s1 {
  char a:8;
  char b:2;
  int c:4;
  short d:1;
};
TEST4(c8c2i4s1)
}
{
struct i17iii7 {
  int a:17;
  int b;
  int c;
  int d:7;
};
TEST4(i17iii7)
}
{
struct i24i6s1s5 {
  int a:24;
  int b:6;
  short c:1;
  short d:5;
};
TEST4(i24i6s1s5)
}
{
struct i15c8i1c3 {
  int a:15;
  char b:8;
  int c:1;
  char d:3;
};
TEST4(i15c8i1c3)
}
{
struct c5i7c4i {
  char a:5;
  int b:7;
  char c:4;
  int d;
};
TEST4(c5i7c4i)
}
{
struct i21c1i3c5 {
  int a:21;
  char b:1;
  int c:3;
  char d:5;
};
TEST4(i21c1i3c5)
}
{
struct c4s1i2c6 {
  char a:4;
  short b:1;
  int c:2;
  char d:6;
};
TEST4(c4s1i2c6)
}
{
struct s1i13i8i3 {
  short a:1;
  int b:13;
  int c:8;
  int d:3;
};
TEST4(s1i13i8i3)
}
{
struct s13b1i1s2 {
  short a:13;
  _Bool b:1;
  int c:1;
  short d:2;
};
TEST4(s13b1i1s2)
}
{
struct b1ss11c4 {
  _Bool a:1;
  short b;
  short c:11;
  char d:4;
};
TEST4(b1ss11c4)
}
{
struct s1sb1s2 {
  short a:1;
  short b;
  _Bool c:1;
  short d:2;
};
TEST4(s1sb1s2)
}
{
struct I28i31C0i20i12i {
  int :28;
  int a:31;
  char :0;
  int b:20;
  int c:12;
  int d;
};
TEST4(I28i31C0i20i12i)
}
{
struct B0c7isc3 {
  _Bool :0;
  char a:7;
  int b;
  short c;
  char d:3;
};
TEST4(B0c7isc3)
}
{
struct c5b1s4s14 {
  char a:5;
  _Bool b:1;
  short c:4;
  short d:14;
};
TEST4(c5b1s4s14)
}
{
struct c1b1b1i6 {
  char a:1;
  _Bool b:1;
  _Bool c:1;
  int d:6;
};
TEST4(c1b1b1i6)
}
{
struct i14sbs {
  int a:14;
  short b;
  _Bool c;
  short d;
};
TEST4(i14sbs)
}
{
struct s8i3s7b1 {
  short a:8;
  int b:3;
  short c:7;
  _Bool d:1;
};
TEST4(s8i3s7b1)
}
{
struct cs4bi20 {
  char a;
  short b:4;
  _Bool c;
  int d:20;
};
TEST4(cs4bi20)
}
{
struct ii7ii29 {
  int a;
  int b:7;
  int c;
  int d:29;
};
TEST4(ii7ii29)
}
{
struct s5i2c2s5 {
  short a:5;
  int b:2;
  char c:2;
  short d:5;
};
TEST4(s5i2c2s5)
}
{
struct b1i1bi {
  _Bool a:1;
  int b:1;
  _Bool c;
  int d;
};
TEST4(b1i1bi)
}
{
struct i6b1i6s7 {
  int a:6;
  _Bool b:1;
  int c:6;
  short d:7;
};
TEST4(i6b1i6s7)
}
{
struct b1ii10i {
  _Bool a:1;
  int b;
  int c:10;
  int d;
};
TEST4(b1ii10i)
}
{
struct ci2c2C8i2 {
  char a;
  int b:2;
  char c:2;
  char :8;
  int d:2;
};
TEST4(ci2c2C8i2)
}
{
struct sB1is1c4 {
  short a;
  _Bool :1;
  int b;
  short c:1;
  char d:4;
};
TEST4(sB1is1c4)
}
{
struct i6I30i11s1i {
  int a:6;
  int :30;
  int b:11;
  short c:1;
  int d;
};
TEST4(i6I30i11s1i)
}
{
struct s2i10cb1 {
  short a:2;
  int b:10;
  char c;
  _Bool d:1;
};
TEST4(s2i10cb1)
}
{
struct iS13i2i18s3 {
  int a;
  short :13;
  int b:2;
  int c:18;
  short d:3;
};
TEST4(iS13i2i18s3)
}
{
struct S15bbi3i6 {
  short :15;
  _Bool a;
  _Bool b;
  int c:3;
  int d:6;
};
TEST4(S15bbi3i6)
}
{
struct s12s10b1c1 {
  short a:12;
  short b:10;
  _Bool c:1;
  char d:1;
};
TEST4(s12s10b1c1)
}
{
struct ss13bc6 {
  short a;
  short b:13;
  _Bool c;
  char d:6;
};
TEST4(ss13bc6)
}
{
struct i23s5ii8 {
  int a:23;
  short b:5;
  int c;
  int d:8;
};
TEST4(i23s5ii8)
}
{
struct i4i25s8i3 {
  int a:4;
  int b:25;
  short c:8;
  int d:3;
};
TEST4(i4i25s8i3)
}
{
struct i3i15s1c6 {
  int a:3;
  int b:15;
  short c:1;
  char d:6;
};
TEST4(i3i15s1c6)
}
{
struct s5S7b1i1I0C5b1 {
  short a:5;
  short :7;
  _Bool b:1;
  int c:1;
  int :0;
  char :5;
  _Bool d:1;
};
TEST4(s5S7b1i1I0C5b1)
}
{
struct s11i13iI31s8 {
  short a:11;
  int b:13;
  int c;
  int :31;
  short d:8;
};
TEST4(s11i13iI31s8)
}
{
struct b1bc6i2 {
  _Bool a:1;
  _Bool b;
  char c:6;
  int d:2;
};
TEST4(b1bc6i2)
}
{
struct i5s2cs5 {
  int a:5;
  short b:2;
  char c;
  short d:5;
};
TEST4(i5s2cs5)
}
{
struct i12is9c8 {
  int a:12;
  int b;
  short c:9;
  char d:8;
};
TEST4(i12is9c8)
}
{
struct s6C4c5ii9 {
  short a:6;
  char :4;
  char b:5;
  int c;
  int d:9;
};
TEST4(s6C4c5ii9)
}
{
struct b1i3i20B0i32 {
  _Bool a:1;
  int b:3;
  int c:20;
  _Bool :0;
  int d:32;
};
TEST4(b1i3i20B0i32)
}
{
struct s3i7cb1 {
  short a:3;
  int b:7;
  char c;
  _Bool d:1;
};
TEST4(s3i7cb1)
}
{
struct s6sc1s9 {
  short a:6;
  short b;
  char c:1;
  short d:9;
};
TEST4(s6sc1s9)
}
{
struct i29b1c5i13 {
  int a:29;
  _Bool b:1;
  char c:5;
  int d:13;
};
TEST4(i29b1c5i13)
}
{
struct i2i3i1i4 {
  int a:2;
  int b:3;
  int c:1;
  int d:4;
};
TEST4(i2i3i1i4)
}
{
struct c8b1i1b1 {
  char a:8;
  _Bool b:1;
  int c:1;
  _Bool d:1;
};
TEST4(c8b1i1b1)
}
{
struct i1s3i30s2 {
  int a:1;
  short b:3;
  int c:30;
  short d:2;
};
TEST4(i1s3i30s2)
}
{
struct ic5c2i1 {
  int a;
  char b:5;
  char c:2;
  int d:1;
};
TEST4(ic5c2i1)
}
{
struct s1I2i1i22i15 {
  short a:1;
  int :2;
  int b:1;
  int c:22;
  int d:15;
};
TEST4(s1I2i1i22i15)
}
{
struct c1iib1 {
  char a:1;
  int b;
  int c;
  _Bool d:1;
};
TEST4(c1iib1)
}
{
struct s2c8b1b1 {
  short a:2;
  char b:8;
  _Bool c:1;
  _Bool d:1;
};
TEST4(s2c8b1b1)
}
{
struct i9s4ii2 {
  int a:9;
  short b:4;
  int c;
  int d:2;
};
TEST4(i9s4ii2)
}
{
struct cs1ci28 {
  char a;
  short b:1;
  char c;
  int d:28;
};
TEST4(cs1ci28)
}
{
struct c6s7ic4 {
  char a:6;
  short b:7;
  int c;
  char d:4;
};
TEST4(c6s7ic4)
}
{
struct c6ic1c7 {
  char a:6;
  int b;
  char c:1;
  char d:7;
};
TEST4(c6ic1c7)
}
{
struct ccc6s5 {
  char a;
  char b;
  char c:6;
  short d:5;
};
TEST4(ccc6s5)
}
{
struct is5i2B1s {
  int a;
  short b:5;
  int c:2;
  _Bool :1;
  short d;
};
TEST4(is5i2B1s)
}
{
struct S2s4I0C1ibC3i7 {
  short :2;
  short a:4;
  int :0;
  char :1;
  int b;
  _Bool c;
  char :3;
  int d:7;
};
TEST4(S2s4I0C1ibC3i7)
}
{
struct i11i18s11c8 {
  int a:11;
  int b:18;
  short c:11;
  char d:8;
};
TEST4(i11i18s11c8)
}
{
struct s2i28c1i10 {
  short a:2;
  int b:28;
  char c:1;
  int d:10;
};
TEST4(s2i28c1i10)
}
{
struct C0s1i2si11 {
  char :0;
  short a:1;
  int b:2;
  short c;
  int d:11;
};
TEST4(C0s1i2si11)
}
{
struct i6ci8C1i1 {
  int a:6;
  char b;
  int c:8;
  char :1;
  int d:1;
};
TEST4(i6ci8C1i1)
}
{
struct c8s8si4 {
  char a:8;
  short b:8;
  short c;
  int d:4;
};
TEST4(c8s8si4)
}
{
struct i24s2i1s3 {
  int a:24;
  short b:2;
  int c:1;
  short d:3;
};
TEST4(i24s2i1s3)
}
{
struct b1i8ic5 {
  _Bool a:1;
  int b:8;
  int c;
  char d:5;
};
TEST4(b1i8ic5)
}
{
struct s10c1cc7 {
  short a:10;
  char b:1;
  char c;
  char d:7;
};
TEST4(s10c1cc7)
}
{
struct s12b1i2c3 {
  short a:12;
  _Bool b:1;
  int c:2;
  char d:3;
};
TEST4(s12b1i2c3)
}
{
struct s10C0c2iS10c3 {
  short a:10;
  char :0;
  char b:2;
  int c;
  short :10;
  char d:3;
};
TEST4(s10C0c2iS10c3)
}
{
struct c2ic2c4 {
  char a:2;
  int b;
  char c:2;
  char d:4;
};
TEST4(c2ic2c4)
}
{
struct s1b1i1s11 {
  short a:1;
  _Bool b:1;
  int c:1;
  short d:11;
};
TEST4(s1b1i1s11)
}
{
struct s7s2i25c5 {
  short a:7;
  short b:2;
  int c:25;
  char d:5;
};
TEST4(s7s2i25c5)
}
{
struct c2I4i1c6i2 {
  char a:2;
  int :4;
  int b:1;
  char c:6;
  int d:2;
};
TEST4(c2I4i1c6i2)
}
{
struct b1i30i18s {
  _Bool a:1;
  int b:30;
  int c:18;
  short d;
};
TEST4(b1i30i18s)
}
{
struct i6c1C0s1c {
  int a:6;
  char b:1;
  char :0;
  short c:1;
  char d;
};
TEST4(i6c1C0s1c)
}
{
struct s1s5s15i24 {
  short a:1;
  short b:5;
  short c:15;
  int d:24;
};
TEST4(s1s5s15i24)
}
{
struct cic1c7 {
  char a;
  int b;
  char c:1;
  char d:7;
};
TEST4(cic1c7)
}
{
struct cs4ic8 {
  char a;
  short b:4;
  int c;
  char d:8;
};
TEST4(cs4ic8)
}
{
struct c1i31i30s4 {
  char a:1;
  int b:31;
  int c:30;
  short d:4;
};
TEST4(c1i31i30s4)
}
{
struct i24i7c3s11 {
  int a:24;
  int b:7;
  char c:3;
  short d:11;
};
TEST4(i24i7c3s11)
}
{
struct i4i2i13c8 {
  int a:4;
  int b:2;
  int c:13;
  char d:8;
};
TEST4(i4i2i13c8)
}
{
struct c3ci16i {
  char a:3;
  char b;
  int c:16;
  int d;
};
TEST4(c3ci16i)
}
{
struct i15i27i4i {
  int a:15;
  int b:27;
  int c:4;
  int d;
};
TEST4(i15i27i4i)
}
{
struct c3c2c1i9 {
  char a:3;
  char b:2;
  char c:1;
  int d:9;
};
TEST4(c3c2c1i9)
}
{
struct i20b1i12c5 {
  int a:20;
  _Bool b:1;
  int c:12;
  char d:5;
};
TEST4(i20b1i12c5)
}
{
struct ci2i7i9 {
  char a;
  int b:2;
  int c:7;
  int d:9;
};
TEST4(ci2i7i9)
}
{
struct ic1c1s {
  int a;
  char b:1;
  char c:1;
  short d;
};
TEST4(ic1c1s)
}
{
struct i8c8I0i3i17 {
  int a:8;
  char b:8;
  int :0;
  int c:3;
  int d:17;
};
TEST4(i8c8I0i3i17)
}
{
struct ii5c1s11 {
  int a;
  int b:5;
  char c:1;
  short d:11;
};
TEST4(ii5c1s11)
}
{
struct s8c2si15 {
  short a:8;
  char b:2;
  short c;
  int d:15;
};
TEST4(s8c2si15)
}
{
struct I0b1i25ic5 {
  int :0;
  _Bool a:1;
  int b:25;
  int c;
  char d:5;
};
TEST4(I0b1i25ic5)
}
{
struct i23C0b1s10b1 {
  int a:23;
  char :0;
  _Bool b:1;
  short c:10;
  _Bool d:1;
};
TEST4(i23C0b1s10b1)
}
{
struct i6c7s6c8 {
  int a:6;
  char b:7;
  short c:6;
  char d:8;
};
TEST4(i6c7s6c8)
}
{
struct s5i8c2C8b1 {
  short a:5;
  int b:8;
  char c:2;
  char :8;
  _Bool d:1;
};
TEST4(s5i8c2C8b1)
}
{
struct b1C7c1i2c8 {
  _Bool a:1;
  char :7;
  char b:1;
  int c:2;
  char d:8;
};
TEST4(b1C7c1i2c8)
}
{
struct cb1ci9 {
  char a;
  _Bool b:1;
  char c;
  int d:9;
};
TEST4(cb1ci9)
}
{
struct c4ii4b1 {
  char a:4;
  int b;
  int c:4;
  _Bool d:1;
};
TEST4(c4ii4b1)
}
{
struct c2c7s16i13 {
  char a:2;
  char b:7;
  short c:16;
  int d:13;
};
TEST4(c2c7s16i13)
}
{
struct s1i5i2b {
  short a:1;
  int b:5;
  int c:2;
  _Bool d;
};
TEST4(s1i5i2b)
}
{
struct ic2sb1 {
  int a;
  char b:2;
  short c;
  _Bool d:1;
};
TEST4(ic2sb1)
}
{
struct s2iib1 {
  short a:2;
  int b;
  int c;
  _Bool d:1;
};
TEST4(s2iib1)
}
{
struct I0i2i9i2s14 {
  int :0;
  int a:2;
  int b:9;
  int c:2;
  short d:14;
};
TEST4(I0i2i9i2s14)
}
{
struct i3cii {
  int a:3;
  char b;
  int c;
  int d;
};
TEST4(i3cii)
}
{
struct c4I7ss12i27 {
  char a:4;
  int :7;
  short b;
  short c:12;
  int d:27;
};
TEST4(c4I7ss12i27)
}
{
struct i5cs11i29 {
  int a:5;
  char b;
  short c:11;
  int d:29;
};
TEST4(i5cs11i29)
}
{
struct s6s4i3i9 {
  short a:6;
  short b:4;
  int c:3;
  int d:9;
};
TEST4(s6s4i3i9)
}
{
struct i29I2S6i30ii9 {
  int a:29;
  int :2;
  short :6;
  int b:30;
  int c;
  int d:9;
};
TEST4(i29I2S6i30ii9)
}
{
struct i20s5sb {
  int a:20;
  short b:5;
  short c;
  _Bool d;
};
TEST4(i20s5sb)
}
{
struct b1i30i1c3 {
  _Bool a:1;
  int b:30;
  int c:1;
  char d:3;
};
TEST4(b1i30i1c3)
}
{
struct i11b1I7s1i {
  int a:11;
  _Bool b:1;
  int :7;
  short c:1;
  int d;
};
TEST4(i11b1I7s1i)
}
{
struct sI0cs4b1 {
  short a;
  int :0;
  char b;
  short c:4;
  _Bool d:1;
};
TEST4(sI0cs4b1)
}
{
struct sC0c8c3I5i14 {
  short a;
  char :0;
  char b:8;
  char c:3;
  int :5;
  int d:14;
};
TEST4(sC0c8c3I5i14)
}
{
struct s1c2i11c1 {
  short a:1;
  char b:2;
  int c:11;
  char d:1;
};
TEST4(s1c2i11c1)
}
{
struct S2b1i28i2c3 {
  short :2;
  _Bool a:1;
  int b:28;
  int c:2;
  char d:3;
};
TEST4(S2b1i28i2c3)
}
{
struct I28b1i7i6i4 {
  int :28;
  _Bool a:1;
  int b:7;
  int c:6;
  int d:4;
};
TEST4(I28b1i7i6i4)
}
{
struct c1I0s10cs12 {
  char a:1;
  int :0;
  short b:10;
  char c;
  short d:12;
};
TEST4(c1I0s10cs12)
}
{
struct b1s5i9s14 {
  _Bool a:1;
  short b:5;
  int c:9;
  short d:14;
};
TEST4(b1s5i9s14)
}
{
struct i21ic4s1 {
  int a:21;
  int b;
  char c:4;
  short d:1;
};
TEST4(i21ic4s1)
}
{
struct s14i1I1i3c1 {
  short a:14;
  int b:1;
  int :1;
  int c:3;
  char d:1;
};
TEST4(s14i1I1i3c1)
}
{
struct b1b1ic4 {
  _Bool a:1;
  _Bool b:1;
  int c;
  char d:4;
};
TEST4(b1b1ic4)
}
{
struct ii1S12ic1 {
  int a;
  int b:1;
  short :12;
  int c;
  char d:1;
};
TEST4(ii1S12ic1)
}
{
struct s1s7c1I3s4 {
  short a:1;
  short b:7;
  char c:1;
  int :3;
  short d:4;
};
TEST4(s1s7c1I3s4)
}
{
struct i26I0iis2 {
  int a:26;
  int :0;
  int b;
  int c;
  short d:2;
};
TEST4(i26I0iis2)
}
{
struct i12b1i26s2 {
  int a:12;
  _Bool b:1;
  int c:26;
  short d:2;
};
TEST4(i12b1i26s2)
}
{
struct cb1S9i14c {
  char a;
  _Bool b:1;
  short :9;
  int c:14;
  char d;
};
TEST4(cb1S9i14c)
}
{
struct b1i5i2c3 {
  _Bool a:1;
  int b:5;
  int c:2;
  char d:3;
};
TEST4(b1i5i2c3)
}
{
struct i4b1I3c2i10 {
  int a:4;
  _Bool b:1;
  int :3;
  char c:2;
  int d:10;
};
TEST4(i4b1I3c2i10)
}
{
struct b1si4c1 {
  _Bool a:1;
  short b;
  int c:4;
  char d:1;
};
TEST4(b1si4c1)
}
{
struct b1I7i5s3i6 {
  _Bool a:1;
  int :7;
  int b:5;
  short c:3;
  int d:6;
};
TEST4(b1I7i5s3i6)
}
{
struct i9s4c4b1 {
  int a:9;
  short b:4;
  char c:4;
  _Bool d:1;
};
TEST4(i9s4c4b1)
}
{
struct cc1S0b1b1 {
  char a;
  char b:1;
  short :0;
  _Bool c:1;
  _Bool d:1;
};
TEST4(cc1S0b1b1)
}
{
struct i15i7i9b {
  int a:15;
  int b:7;
  int c:9;
  _Bool d;
};
TEST4(i15i7i9b)
}
{
struct i29ici3 {
  int a:29;
  int b;
  char c;
  int d:3;
};
TEST4(i29ici3)
}
{
struct C2ii7c3c5 {
  char :2;
  int a;
  int b:7;
  char c:3;
  char d:5;
};
TEST4(C2ii7c3c5)
}
{
struct b1si20b1 {
  _Bool a:1;
  short b;
  int c:20;
  _Bool d:1;
};
TEST4(b1si20b1)
}
{
struct cs5si26 {
  char a;
  short b:5;
  short c;
  int d:26;
};
TEST4(cs5si26)
}
{
struct i26b1iI1b1 {
  int a:26;
  _Bool b:1;
  int c;
  int :1;
  _Bool d:1;
};
TEST4(i26b1iI1b1)
}
{
struct iis16C3C3i2 {
  int a;
  int b;
  short c:16;
  char :3;
  char :3;
  int d:2;
};
TEST4(iis16C3C3i2)
}
{
struct i6i2i1i2 {
  int a:6;
  int b:2;
  int c:1;
  int d:2;
};
TEST4(i6i2i1i2)
}
{
struct I6B0c5ii3i1 {
  int :6;
  _Bool :0;
  char a:5;
  int b;
  int c:3;
  int d:1;
};
TEST4(I6B0c5ii3i1)
}
{
struct s2ibc {
  short a:2;
  int b;
  _Bool c;
  char d;
};
TEST4(s2ibc)
}
{
struct ic5c8i2 {
  int a;
  char b:5;
  char c:8;
  int d:2;
};
TEST4(ic5c8i2)
}
{
struct i7c1s5c {
  int a:7;
  char b:1;
  short c:5;
  char d;
};
TEST4(i7c1s5c)
}
{
struct s5s15ic {
  short a:5;
  short b:15;
  int c;
  char d;
};
TEST4(s5s15ic)
}
{
struct s6ci6i18 {
  short a:6;
  char b;
  int c:6;
  int d:18;
};
TEST4(s6ci6i18)
}
{
struct b1i18i22i13 {
  _Bool a:1;
  int b:18;
  int c:22;
  int d:13;
};
TEST4(b1i18i22i13)
}
{
struct s1b1i1c4 {
  short a:1;
  _Bool b:1;
  int c:1;
  char d:4;
};
TEST4(s1b1i1c4)
}
{
struct i31i8s7i7 {
  int a:31;
  int b:8;
  short c:7;
  int d:7;
};
TEST4(i31i8s7i7)
}
{
struct i1s16is4 {
  int a:1;
  short b:16;
  int c;
  short d:4;
};
TEST4(i1s16is4)
}
{
struct sS3C5ii2C8i6 {
  short a;
  short :3;
  char :5;
  int b;
  int c:2;
  char :8;
  int d:6;
};
TEST4(sS3C5ii2C8i6)
}
{
struct ic4i2b1 {
  int a;
  char b:4;
  int c:2;
  _Bool d:1;
};
TEST4(ic4i2b1)
}
{
struct c4c1c2I0i12 {
  char a:4;
  char b:1;
  char c:2;
  int :0;
  int d:12;
};
TEST4(c4c1c2I0i12)
}
{
struct c2cs2s5 {
  char a:2;
  char b;
  short c:2;
  short d:5;
};
TEST4(c2cs2s5)
}
{
struct s15si13i22 {
  short a:15;
  short b;
  int c:13;
  int d:22;
};
TEST4(s15si13i22)
}
{
struct s13bC5i7i2 {
  short a:13;
  _Bool b;
  char :5;
  int c:7;
  int d:2;
};
TEST4(s13bC5i7i2)
}
{
struct s7i1i23i28 {
  short a:7;
  int b:1;
  int c:23;
  int d:28;
};
TEST4(s7i1i23i28)
}
{
struct i19ic5b1 {
  int a:19;
  int b;
  char c:5;
  _Bool d:1;
};
TEST4(i19ic5b1)
}
{
struct b1i4ss13 {
  _Bool a:1;
  int b:4;
  short c;
  short d:13;
};
TEST4(b1i4ss13)
}
{
struct b1isi7 {
  _Bool a:1;
  int b;
  short c;
  int d:7;
};
TEST4(b1isi7)
}
{
struct C3c2I11s3c8s1 {
  char :3;
  char a:2;
  int :11;
  short b:3;
  char c:8;
  short d:1;
};
TEST4(C3c2I11s3c8s1)
}
{
struct s4i11b1i {
  short a:4;
  int b:11;
  _Bool c:1;
  int d;
};
TEST4(s4i11b1i)
}
{
struct I18ii12c1c7 {
  int :18;
  int a;
  int b:12;
  char c:1;
  char d:7;
};
TEST4(I18ii12c1c7)
}
{
struct S12C0i1iI24i3i2 {
  short :12;
  char :0;
  int a:1;
  int b;
  int :24;
  int c:3;
  int d:2;
};
TEST4(S12C0i1iI24i3i2)
}
{
struct i1i31b1s11 {
  int a:1;
  int b:31;
  _Bool c:1;
  short d:11;
};
TEST4(i1i31b1s11)
}
{
struct c3b1i11i7 {
  char a:3;
  _Bool b:1;
  int c:11;
  int d:7;
};
TEST4(c3b1i11i7)
}
{
struct b1ii8B1i4 {
  _Bool a:1;
  int b;
  int c:8;
  _Bool :1;
  int d:4;
};
TEST4(b1ii8B1i4)
}
{
struct c2c1c4i24 {
  char a:2;
  char b:1;
  char c:4;
  int d:24;
};
TEST4(c2c1c4i24)
}
{
struct i18s15c8i5 {
  int a:18;
  short b:15;
  char c:8;
  int d:5;
};
TEST4(i18s15c8i5)
}
{
struct i3c3i3i5 {
  int a:3;
  char b:3;
  int c:3;
  int d:5;
};
TEST4(i3c3i3i5)
}
{
struct i12i10c7i {
  int a:12;
  int b:10;
  char c:7;
  int d;
};
TEST4(i12i10c7i)
}
{
struct i25I0c1b1i6 {
  int a:25;
  int :0;
  char b:1;
  _Bool c:1;
  int d:6;
};
TEST4(i25I0c1b1i6)
}
{
struct s9i7b1i18 {
  short a:9;
  int b:7;
  _Bool c:1;
  int d:18;
};
TEST4(s9i7b1i18)
}
{
struct i2s5ib {
  int a:2;
  short b:5;
  int c;
  _Bool d;
};
TEST4(i2s5ib)
}
{
struct s13i6i12i1 {
  short a:13;
  int b:6;
  int c:12;
  int d:1;
};
TEST4(s13i6i12i1)
}
{
struct cc1i12s3 {
  char a;
  char b:1;
  int c:12;
  short d:3;
};
TEST4(cc1i12s3)
}
{
struct i2i15s2s2 {
  int a:2;
  int b:15;
  short c:2;
  short d:2;
};
TEST4(i2i15s2s2)
}
{
struct c1bs5s1 {
  char a:1;
  _Bool b;
  short c:5;
  short d:1;
};
TEST4(c1bs5s1)
}
{
struct sc2sb1 {
  short a;
  char b:2;
  short c;
  _Bool d:1;
};
TEST4(sc2sb1)
}
{
struct s1i8ii10 {
  short a:1;
  int b:8;
  int c;
  int d:10;
};
TEST4(s1i8ii10)
}
{
struct i3c1i1i {
  int a:3;
  char b:1;
  int c:1;
  int d;
};
TEST4(i3c1i1i)
}
{
struct I8C0c4i6b1b1 {
  int :8;
  char :0;
  char a:4;
  int b:6;
  _Bool c:1;
  _Bool d:1;
};
TEST4(I8C0c4i6b1b1)
}
{
struct c3b1i13i17 {
  char a:3;
  _Bool b:1;
  int c:13;
  int d:17;
};
TEST4(c3b1i13i17)
}
{
struct c7i18i16I5c1 {
  char a:7;
  int b:18;
  int c:16;
  int :5;
  char d:1;
};
TEST4(c7i18i16I5c1)
}
{
struct b1I0c1i18i31 {
  _Bool a:1;
  int :0;
  char b:1;
  int c:18;
  int d:31;
};
TEST4(b1I0c1i18i31)
}
{
struct c1s1C2i1b1 {
  char a:1;
  short b:1;
  char :2;
  int c:1;
  _Bool d:1;
};
TEST4(c1s1C2i1b1)
}
{
struct c4c5s3i12 {
  char a:4;
  char b:5;
  short c:3;
  int d:12;
};
TEST4(c4c5s3i12)
}
{
struct si27ci2 {
  short a;
  int b:27;
  char c;
  int d:2;
};
TEST4(si27ci2)
}
{
struct s3s6ii10 {
  short a:3;
  short b:6;
  int c;
  int d:10;
};
TEST4(s3s6ii10)
}
{
struct s4b1ii8 {
  short a:4;
  _Bool b:1;
  int c;
  int d:8;
};
TEST4(s4b1ii8)
}
{
struct ib1i2c3 {
  int a;
  _Bool b:1;
  int c:2;
  char d:3;
};
TEST4(ib1i2c3)
}
{
struct b1i13i9I27c8 {
  _Bool a:1;
  int b:13;
  int c:9;
  int :27;
  char d:8;
};
TEST4(b1i13i9I27c8)
}
{
struct c3ii2c4 {
  char a:3;
  int b;
  int c:2;
  char d:4;
};
TEST4(c3ii2c4)
}
{
struct cib1c5 {
  char a;
  int b;
  _Bool c:1;
  char d:5;
};
TEST4(cib1c5)
}
{
struct c1s16ii15 {
  char a:1;
  short b:16;
  int c;
  int d:15;
};
TEST4(c1s16ii15)
}
{
struct i1ici13 {
  int a:1;
  int b;
  char c;
  int d:13;
};
TEST4(i1ici13)
}
{
struct c1C1S1c6i2s7 {
  char a:1;
  char :1;
  short :1;
  char b:6;
  int c:2;
  short d:7;
};
TEST4(c1C1S1c6i2s7)
}
{
struct c2c7c6i {
  char a:2;
  char b:7;
  char c:6;
  int d;
};
TEST4(c2c7c6i)
}
{
struct iC0s2c5s {
  int a;
  char :0;
  short b:2;
  char c:5;
  short d;
};
TEST4(iC0s2c5s)
}
{
struct c8bi3b1 {
  char a:8;
  _Bool b;
  int c:3;
  _Bool d:1;
};
TEST4(c8bi3b1)
}
{
struct i12s6c3b1 {
  int a:12;
  short b:6;
  char c:3;
  _Bool d:1;
};
TEST4(i12s6c3b1)
}
{
struct I2i5ci8i2 {
  int :2;
  int a:5;
  char b;
  int c:8;
  int d:2;
};
TEST4(I2i5ci8i2)
}
{
struct i18i5s11i11 {
  int a:18;
  int b:5;
  short c:11;
  int d:11;
};
TEST4(i18i5s11i11)
}
{
struct S8I0i7i7s6s1 {
  short :8;
  int :0;
  int a:7;
  int b:7;
  short c:6;
  short d:1;
};
TEST4(S8I0i7i7s6s1)
}
{
struct c5b1b1c1 {
  char a:5;
  _Bool b:1;
  _Bool c:1;
  char d:1;
};
TEST4(c5b1b1c1)
}
{
struct i14i23ss5 {
  int a:14;
  int b:23;
  short c;
  short d:5;
};
TEST4(i14i23ss5)
}
{
struct ii28ci7 {
  int a;
  int b:28;
  char c;
  int d:7;
};
TEST4(ii28ci7)
}
{
struct c1ii2i21 {
  char a:1;
  int b;
  int c:2;
  int d:21;
};
TEST4(c1ii2i21)
}
{
struct b1s2i15b1 {
  _Bool a:1;
  short b:2;
  int c:15;
  _Bool d:1;
};
TEST4(b1s2i15b1)
}
{
struct i19c2i7c3 {
  int a:19;
  char b:2;
  int c:7;
  char d:3;
};
TEST4(i19c2i7c3)
}
{
struct I1cbb1i27 {
  int :1;
  char a;
  _Bool b;
  _Bool c:1;
  int d:27;
};
TEST4(I1cbb1i27)
}
{
struct ciis16 {
  char a;
  int b;
  int c;
  short d:16;
};
TEST4(ciis16)
}
{
struct i21s13si14 {
  int a:21;
  short b:13;
  short c;
  int d:14;
};
TEST4(i21s13si14)
}
{
struct ssC4i2s6 {
  short a;
  short b;
  char :4;
  int c:2;
  short d:6;
};
TEST4(ssC4i2s6)
}
{
struct b1ss1s1 {
  _Bool a:1;
  short b;
  short c:1;
  short d:1;
};
TEST4(b1ss1s1)
}
{
struct c1ii1s4 {
  char a:1;
  int b;
  int c:1;
  short d:4;
};
TEST4(c1ii1s4)
}
{
struct bii2i1 {
  _Bool a;
  int b;
  int c:2;
  int d:1;
};
TEST4(bii2i1)
}
{
struct s16iii1 {
  short a:16;
  int b;
  int c;
  int d:1;
};
TEST4(s16iii1)
}
{
struct b1ic4s9 {
  _Bool a:1;
  int b;
  char c:4;
  short d:9;
};
TEST4(b1ic4s9)
}
{
struct c5i7S14ci2 {
  char a:5;
  int b:7;
  short :14;
  char c;
  int d:2;
};
TEST4(c5i7S14ci2)
}
{
struct C0is3cb1 {
  char :0;
  int a;
  short b:3;
  char c;
  _Bool d:1;
};
TEST4(C0is3cb1)
}
{
struct i5i7iS11c6 {
  int a:5;
  int b:7;
  int c;
  short :11;
  char d:6;
};
TEST4(i5i7iS11c6)
}
{
struct I18i5i24s6I2i22 {
  int :18;
  int a:5;
  int b:24;
  short c:6;
  int :2;
  int d:22;
};
TEST4(I18i5i24s6I2i22)
}
{
struct B1c6i7i32s8 {
  _Bool :1;
  char a:6;
  int b:7;
  int c:32;
  short d:8;
};
TEST4(B1c6i7i32s8)
}
{
struct i5b1i5s12 {
  int a:5;
  _Bool b:1;
  int c:5;
  short d:12;
};
TEST4(i5b1i5s12)
}
{
struct i31ib1B0s2 {
  int a:31;
  int b;
  _Bool c:1;
  _Bool :0;
  short d:2;
};
TEST4(i31ib1B0s2)
}
{
struct i6b1B0ii {
  int a:6;
  _Bool b:1;
  _Bool :0;
  int c;
  int d;
};
TEST4(i6b1B0ii)
}
{
struct i12si10s7 {
  int a:12;
  short b;
  int c:10;
  short d:7;
};
TEST4(i12si10s7)
}
{
struct cci2i31 {
  char a;
  char b;
  int c:2;
  int d:31;
};
TEST4(cci2i31)
}
{
struct I19i1ci2c6 {
  int :19;
  int a:1;
  char b;
  int c:2;
  char d:6;
};
TEST4(I19i1ci2c6)
}
{
struct s16s1i12i14 {
  short a:16;
  short b:1;
  int c:12;
  int d:14;
};
TEST4(s16s1i12i14)
}
{
struct i1b1i12s {
  int a:1;
  _Bool b:1;
  int c:12;
  short d;
};
TEST4(i1b1i12s)
}
{
struct sii4s3 {
  short a;
  int b;
  int c:4;
  short d:3;
};
TEST4(sii4s3)
}
{
struct b1i2ii29 {
  _Bool a:1;
  int b:2;
  int c;
  int d:29;
};
TEST4(b1i2ii29)
}
{
struct s15i5i12s {
  short a:15;
  int b:5;
  int c:12;
  short d;
};
TEST4(s15i5i12s)
}
{
struct S12i14S2c3s7s7 {
  short :12;
  int a:14;
  short :2;
  char b:3;
  short c:7;
  short d:7;
};
TEST4(S12i14S2c3s7s7)
}
{
struct c1I1i1B0i15i11 {
  char a:1;
  int :1;
  int b:1;
  _Bool :0;
  int c:15;
  int d:11;
};
TEST4(c1I1i1B0i15i11)
}
{
struct I7i27i18C4ss2 {
  int :7;
  int a:27;
  int b:18;
  char :4;
  short c;
  short d:2;
};
TEST4(I7i27i18C4ss2)
}
{
struct s7s8i12S0c {
  short a:7;
  short b:8;
  int c:12;
  short :0;
  char d;
};
TEST4(s7s8i12S0c)
}
{
struct i1I1i31i12b {
  int a:1;
  int :1;
  int b:31;
  int c:12;
  _Bool d;
};
TEST4(i1I1i31i12b)
}
{
struct c3c5I0i4i {
  char a:3;
  char b:5;
  int :0;
  int c:4;
  int d;
};
TEST4(c3c5I0i4i)
}
{
struct b1si22s4 {
  _Bool a:1;
  short b;
  int c:22;
  short d:4;
};
TEST4(b1si22s4)
}
{
struct i9i15s14C1i {
  int a:9;
  int b:15;
  short c:14;
  char :1;
  int d;
};
TEST4(i9i15s14C1i)
}
{
struct I11s1s3I1i2b1 {
  int :11;
  short a:1;
  short b:3;
  int :1;
  int c:2;
  _Bool d:1;
};
TEST4(I11s1s3I1i2b1)
}
{
struct s5iii2 {
  short a:5;
  int b;
  int c;
  int d:2;
};
TEST4(s5iii2)
}
{
struct s14i2s9s {
  short a:14;
  int b:2;
  short c:9;
  short d;
};
TEST4(s14i2s9s)
}
{
struct sc6i29c8 {
  short a;
  char b:6;
  int c:29;
  char d:8;
};
TEST4(sc6i29c8)
}
{
struct s7c3s7i1 {
  short a:7;
  char b:3;
  short c:7;
  int d:1;
};
TEST4(s7c3s7i1)
}
{
struct i13csi10 {
  int a:13;
  char b;
  short c;
  int d:10;
};
TEST4(i13csi10)
}
{
struct i11cii11 {
  int a:11;
  char b;
  int c;
  int d:11;
};
TEST4(i11cii11)
}
{
struct b1c5c4i1 {
  _Bool a:1;
  char b:5;
  char c:4;
  int d:1;
};
TEST4(b1c5c4i1)
}
{
struct i2si7i28 {
  int a:2;
  short b;
  int c:7;
  int d:28;
};
TEST4(i2si7i28)
}
{
struct bc4i1s2 {
  _Bool a;
  char b:4;
  int c:1;
  short d:2;
};
TEST4(bc4i1s2)
}
{
struct i3i6C0cc7 {
  int a:3;
  int b:6;
  char :0;
  char c;
  char d:7;
};
TEST4(i3i6C0cc7)
}
{
struct S5b1i8iB0i23 {
  short :5;
  _Bool a:1;
  int b:8;
  int c;
  _Bool :0;
  int d:23;
};
TEST4(S5b1i8iB0i23)
}
{
struct S11ii7c6i3 {
  short :11;
  int a;
  int b:7;
  char c:6;
  int d:3;
};
TEST4(S11ii7c6i3)
}
{
struct s11ss8s {
  short a:11;
  short b;
  short c:8;
  short d;
};
TEST4(s11ss8s)
}
{
struct c5i22i3i {
  char a:5;
  int b:22;
  int c:3;
  int d;
};
TEST4(c5i22i3i)
}
{
struct i20c4i19i2 {
  int a:20;
  char b:4;
  int c:19;
  int d:2;
};
TEST4(i20c4i19i2)
}
{
struct is7s12i20 {
  int a;
  short b:7;
  short c:12;
  int d:20;
};
TEST4(is7s12i20)
}
{
struct i14i1ii7 {
  int a:14;
  int b:1;
  int c;
  int d:7;
};
TEST4(i14i1ii7)
}
{
struct S0I0ss6s1i2 {
  short :0;
  int :0;
  short a;
  short b:6;
  short c:1;
  int d:2;
};
TEST4(S0I0ss6s1i2)
}
{
struct s1s2i30i1 {
  short a:1;
  short b:2;
  int c:30;
  int d:1;
};
TEST4(s1s2i30i1)
}
{
struct si27s15s3 {
  short a;
  int b:27;
  short c:15;
  short d:3;
};
TEST4(si27s15s3)
}
{
struct s8ci7c4 {
  short a:8;
  char b;
  int c:7;
  char d:4;
};
TEST4(s8ci7c4)
}
{
struct b1ii31i7 {
  _Bool a:1;
  int b;
  int c:31;
  int d:7;
};
TEST4(b1ii31i7)
}
{
struct i16s2S2b1c {
  int a:16;
  short b:2;
  short :2;
  _Bool c:1;
  char d;
};
TEST4(i16s2S2b1c)
}
{
struct i2ib1b1 {
  int a:2;
  int b;
  _Bool c:1;
  _Bool d:1;
};
TEST4(i2ib1b1)
}
{
struct i2C1s2s12c8 {
  int a:2;
  char :1;
  short b:2;
  short c:12;
  char d:8;
};
TEST4(i2C1s2s12c8)
}
{
struct I12i2I0c2s7i25 {
  int :12;
  int a:2;
  int :0;
  char b:2;
  short c:7;
  int d:25;
};
TEST4(I12i2I0c2s7i25)
}
{
struct i31bc2s5 {
  int a:31;
  _Bool b;
  char c:2;
  short d:5;
};
TEST4(i31bc2s5)
}
{
struct i10iI15cc6 {
  int a:10;
  int b;
  int :15;
  char c;
  char d:6;
};
TEST4(i10iI15cc6)
}
{
struct i11i10I19s16i5 {
  int a:11;
  int b:10;
  int :19;
  short c:16;
  int d:5;
};
TEST4(i11i10I19s16i5)
}
{
struct s3sic4 {
  short a:3;
  short b;
  int c;
  char d:4;
};
TEST4(s3sic4)
}
{
struct i2b1s8s8 {
  int a:2;
  _Bool b:1;
  short c:8;
  short d:8;
};
TEST4(i2b1s8s8)
}
{
struct c8c8ci2 {
  char a:8;
  char b:8;
  char c;
  int d:2;
};
TEST4(c8c8ci2)
}
{
struct si21i1b1 {
  short a;
  int b:21;
  int c:1;
  _Bool d:1;
};
TEST4(si21i1b1)
}
{
struct i29c5i2b1 {
  int a:29;
  char b:5;
  int c:2;
  _Bool d:1;
};
TEST4(i29c5i2b1)
}
{
struct cs12i3i {
  char a;
  short b:12;
  int c:3;
  int d;
};
TEST4(cs12i3i)
}
{
struct ii13c1i6 {
  int a;
  int b:13;
  char c:1;
  int d:6;
};
TEST4(ii13c1i6)
}
{
struct c1iB1i19i {
  char a:1;
  int b;
  _Bool :1;
  int c:19;
  int d;
};
TEST4(c1iB1i19i)
}
{
struct c5c5bs {
  char a:5;
  char b:5;
  _Bool c;
  short d;
};
TEST4(c5c5bs)
}
{
struct b1is9I0i {
  _Bool a:1;
  int b;
  short c:9;
  int :0;
  int d;
};
TEST4(b1is9I0i)
}
{
struct ibi12I0i {
  int a;
  _Bool b;
  int c:12;
  int :0;
  int d;
};
TEST4(ibi12I0i)
}
{
struct ii14i14i {
  int a;
  int b:14;
  int c:14;
  int d;
};
TEST4(ii14i14i)
}
{
struct i2i13i5s {
  int a:2;
  int b:13;
  int c:5;
  short d;
};
TEST4(i2i13i5s)
}
{
struct c3i2i6i9 {
  char a:3;
  int b:2;
  int c:6;
  int d:9;
};
TEST4(c3i2i6i9)
}
{
struct s13s7b1c8 {
  short a:13;
  short b:7;
  _Bool c:1;
  char d:8;
};
TEST4(s13s7b1c8)
}
{
struct ii1s8i27 {
  int a;
  int b:1;
  short c:8;
  int d:27;
};
TEST4(ii1s8i27)
}
{
struct ic8s1c1 {
  int a;
  char b:8;
  short c:1;
  char d:1;
};
TEST4(ic8s1c1)
}
{
struct S2i5c5c6s3 {
  short :2;
  int a:5;
  char b:5;
  char c:6;
  short d:3;
};
TEST4(S2i5c5c6s3)
}
{
struct sc1s6c4 {
  short a;
  char b:1;
  short c:6;
  char d:4;
};
TEST4(sc1s6c4)
}
{
struct s2iss12 {
  short a:2;
  int b;
  short c;
  short d:12;
};
TEST4(s2iss12)
}
{
struct i15I17i26I1B0s8I15B1s3 {
  int a:15;
  int :17;
  int b:26;
  int :1;
  _Bool :0;
  short c:8;
  int :15;
  _Bool :1;
  short d:3;
};
TEST4(i15I17i26I1B0s8I15B1s3)
}
{
struct s4I29cci11 {
  short a:4;
  int :29;
  char b;
  char c;
  int d:11;
};
TEST4(s4I29cci11)
}
{
struct c7b1i31i13 {
  char a:7;
  _Bool b:1;
  int c:31;
  int d:13;
};
TEST4(c7b1i31i13)
}
{
struct i23i13is5 {
  int a:23;
  int b:13;
  int c;
  short d:5;
};
TEST4(i23i13is5)
}
{
struct c8ci3c {
  char a:8;
  char b;
  int c:3;
  char d;
};
TEST4(c8ci3c)
}
{
struct i1b1s13b1 {
  int a:1;
  _Bool b:1;
  short c:13;
  _Bool d:1;
};
TEST4(i1b1s13b1)
}
{
struct i1i2i15i {
  int a:1;
  int b:2;
  int c:15;
  int d;
};
TEST4(i1i2i15i)
}
{
struct i26i2i1b1 {
  int a:26;
  int b:2;
  int c:1;
  _Bool d:1;
};
TEST4(i26i2i1b1)
}
{
struct c1i14c3i1 {
  char a:1;
  int b:14;
  char c:3;
  int d:1;
};
TEST4(c1i14c3i1)
}
{
struct i31c8c4I0b {
  int a:31;
  char b:8;
  char c:4;
  int :0;
  _Bool d;
};
TEST4(i31c8c4I0b)
}
{
struct S11c1c1ci1 {
  short :11;
  char a:1;
  char b:1;
  char c;
  int d:1;
};
TEST4(S11c1c1ci1)
}
{
struct ii10c4c4 {
  int a;
  int b:10;
  char c:4;
  char d:4;
};
TEST4(ii10c4c4)
}
{
struct I30i12c6i1c1 {
  int :30;
  int a:12;
  char b:6;
  int c:1;
  char d:1;
};
TEST4(I30i12c6i1c1)
}
{
struct i3sc8i14 {
  int a:3;
  short b;
  char c:8;
  int d:14;
};
TEST4(i3sc8i14)
}
{
struct i15ic3c1 {
  int a:15;
  int b;
  char c:3;
  char d:1;
};
TEST4(i15ic3c1)
}
{
struct I4b1b1S9I3s11c1 {
  int :4;
  _Bool a:1;
  _Bool b:1;
  short :9;
  int :3;
  short c:11;
  char d:1;
};
TEST4(I4b1b1S9I3s11c1)
}
{
struct i2bc1i26 {
  int a:2;
  _Bool b;
  char c:1;
  int d:26;
};
TEST4(i2bc1i26)
}
{
struct c1c7i30c5 {
  char a:1;
  char b:7;
  int c:30;
  char d:5;
};
TEST4(c1c7i30c5)
}
{
struct s1c1i5i30 {
  short a:1;
  char b:1;
  int c:5;
  int d:30;
};
TEST4(s1c1i5i30)
}
{
struct s3i22s4i {
  short a:3;
  int b:22;
  short c:4;
  int d;
};
TEST4(s3i22s4i)
}
{
struct i7is9c7 {
  int a:7;
  int b;
  short c:9;
  char d:7;
};
TEST4(i7is9c7)
}
{
struct I10bb1i7i23 {
  int :10;
  _Bool a;
  _Bool b:1;
  int c:7;
  int d:23;
};
TEST4(I10bb1i7i23)
}
{
struct c2s5i13b1 {
  char a:2;
  short b:5;
  int c:13;
  _Bool d:1;
};
TEST4(c2s5i13b1)
}
{
struct C0c1C5c3i27c5 {
  char :0;
  char a:1;
  char :5;
  char b:3;
  int c:27;
  char d:5;
};
TEST4(C0c1C5c3i27c5)
}
{
struct c8i7i9c3 {
  char a:8;
  int b:7;
  int c:9;
  char d:3;
};
TEST4(c8i7i9c3)
}
{
struct i2i8i13s {
  int a:2;
  int b:8;
  int c:13;
  short d;
};
TEST4(i2i8i13s)
}
{
struct S6i4i8ii13 {
  short :6;
  int a:4;
  int b:8;
  int c;
  int d:13;
};
TEST4(S6i4i8ii13)
}
{
struct i2I9i5s3s8 {
  int a:2;
  int :9;
  int b:5;
  short c:3;
  short d:8;
};
TEST4(i2I9i5s3s8)
}
{
struct i8s4c5i23 {
  int a:8;
  short b:4;
  char c:5;
  int d:23;
};
TEST4(i8s4c5i23)
}
{
struct C3c3i1C0c1s1 {
  char :3;
  char a:3;
  int b:1;
  char :0;
  char c:1;
  short d:1;
};
TEST4(C3c3i1C0c1s1)
}
{
struct si17s4i18 {
  short a;
  int b:17;
  short c:4;
  int d:18;
};
TEST4(si17s4i18)
}
{
struct s2s1i17c2 {
  short a:2;
  short b:1;
  int c:17;
  char d:2;
};
TEST4(s2s1i17c2)
}
{
struct c8i5c2b1 {
  char a:8;
  int b:5;
  char c:2;
  _Bool d:1;
};
TEST4(c8i5c2b1)
}
{
struct c7s2c5c4 {
  char a:7;
  short b:2;
  char c:5;
  char d:4;
};
TEST4(c7s2c5c4)
}
{
struct s7I0c8c1b {
  short a:7;
  int :0;
  char b:8;
  char c:1;
  _Bool d;
};
TEST4(s7I0c8c1b)
}
{
struct s2i2i2I3i {
  short a:2;
  int b:2;
  int c:2;
  int :3;
  int d;
};
TEST4(s2i2i2I3i)
}
{
struct S12s2i11i10i {
  short :12;
  short a:2;
  int b:11;
  int c:10;
  int d;
};
TEST4(S12s2i11i10i)
}
{
struct I11i12bis2 {
  int :11;
  int a:12;
  _Bool b;
  int c;
  short d:2;
};
TEST4(I11i12bis2)
}
{
struct B1i29si4b1 {
  _Bool :1;
  int a:29;
  short b;
  int c:4;
  _Bool d:1;
};
TEST4(B1i29si4b1)
}
{
struct i2ssi {
  int a:2;
  short b;
  short c;
  int d;
};
TEST4(i2ssi)
}
{
struct i15s8s8i1 {
  int a:15;
  short b:8;
  short c:8;
  int d:1;
};
TEST4(i15s8s8i1)
}
{
struct I4c5B1i13iC1i {
  int :4;
  char a:5;
  _Bool :1;
  int b:13;
  int c;
  char :1;
  int d;
};
TEST4(I4c5B1i13iC1i)
}
{
struct i31c3i7s5 {
  int a:31;
  char b:3;
  int c:7;
  short d:5;
};
TEST4(i31c3i7s5)
}
{
struct ii1B1c7i1 {
  int a;
  int b:1;
  _Bool :1;
  char c:7;
  int d:1;
};
TEST4(ii1B1c7i1)
}
{
struct si9b1s {
  short a;
  int b:9;
  _Bool c:1;
  short d;
};
TEST4(si9b1s)
}
{
struct cs1c7s4 {
  char a;
  short b:1;
  char c:7;
  short d:4;
};
TEST4(cs1c7s4)
}
{
struct C0s4s9I0si3 {
  char :0;
  short a:4;
  short b:9;
  int :0;
  short c;
  int d:3;
};
TEST4(C0s4s9I0si3)
}
{
struct b1i23s11i {
  _Bool a:1;
  int b:23;
  short c:11;
  int d;
};
TEST4(b1i23s11i)
}
{
struct s13c2s16s5 {
  short a:13;
  char b:2;
  short c:16;
  short d:5;
};
TEST4(s13c2s16s5)
}
{
struct s12sic3 {
  short a:12;
  short b;
  int c;
  char d:3;
};
TEST4(s12sic3)
}
{
struct c5bsB1i {
  char a:5;
  _Bool b;
  short c;
  _Bool :1;
  int d;
};
TEST4(c5bsB1i)
}
{
struct b1s3S11i21i32 {
  _Bool a:1;
  short b:3;
  short :11;
  int c:21;
  int d:32;
};
TEST4(b1s3S11i21i32)
}
{
struct c6c2i2i6 {
  char a:6;
  char b:2;
  int c:2;
  int d:6;
};
TEST4(c6c2i2i6)
}
{
struct i7i4ii29 {
  int a:7;
  int b:4;
  int c;
  int d:29;
};
TEST4(i7i4ii29)
}
{
struct i3I13c5i25s {
  int a:3;
  int :13;
  char b:5;
  int c:25;
  short d;
};
TEST4(i3I13c5i25s)
}
{
struct c1s5si5 {
  char a:1;
  short b:5;
  short c;
  int d:5;
};
TEST4(c1s5si5)
}
{
struct sS10i1cc6 {
  short a;
  short :10;
  int b:1;
  char c;
  char d:6;
};
TEST4(sS10i1cc6)
}
{
struct S0iii10I23i11 {
  short :0;
  int a;
  int b;
  int c:10;
  int :23;
  int d:11;
};
TEST4(S0iii10I23i11)
}
{
struct c4B0c5C4i5i2 {
  char a:4;
  _Bool :0;
  char b:5;
  char :4;
  int c:5;
  int d:2;
};
TEST4(c4B0c5C4i5i2)
}
{
struct i5I1sc1i {
  int a:5;
  int :1;
  short b;
  char c:1;
  int d;
};
TEST4(i5I1sc1i)
}
{
struct i21c2i32i4 {
  int a:21;
  char b:2;
  int c:32;
  int d:4;
};
TEST4(i21c2i32i4)
}
{
struct i1s3i8i2 {
  int a:1;
  short b:3;
  int c:8;
  int d:2;
};
TEST4(i1s3i8i2)
}
{
struct i7i6i2c4 {
  int a:7;
  int b:6;
  int c:2;
  char d:4;
};
TEST4(i7i6i2c4)
}
{
struct i2i7ii {
  int a:2;
  int b:7;
  int c;
  int d;
};
TEST4(i2i7ii)
}
{
struct ii14I0c5c {
  int a;
  int b:14;
  int :0;
  char c:5;
  char d;
};
TEST4(ii14I0c5c)
}
{
struct s6c1i18i3 {
  short a:6;
  char b:1;
  int c:18;
  int d:3;
};
TEST4(s6c1i18i3)
}
{
struct c6i12s3c {
  char a:6;
  int b:12;
  short c:3;
  char d;
};
TEST4(c6i12s3c)
}
{
struct i2i13c2c {
  int a:2;
  int b:13;
  char c:2;
  char d;
};
TEST4(i2i13c2c)
}
{
struct b1i1i17c4 {
  _Bool a:1;
  int b:1;
  int c:17;
  char d:4;
};
TEST4(b1i1i17c4)
}
{
struct b1s5b1c2 {
  _Bool a:1;
  short b:5;
  _Bool c:1;
  char d:2;
};
TEST4(b1s5b1c2)
}
{
struct s6i19i1C0s1 {
  short a:6;
  int b:19;
  int c:1;
  char :0;
  short d:1;
};
TEST4(s6i19i1C0s1)
}
{
struct i6i7ii {
  int a:6;
  int b:7;
  int c;
  int d;
};
TEST4(i6i7ii)
}
{
struct s10ii2i29 {
  short a:10;
  int b;
  int c:2;
  int d:29;
};
TEST4(s10ii2i29)
}
{
struct s7i4sS14i11 {
  short a:7;
  int b:4;
  short c;
  short :14;
  int d:11;
};
TEST4(s7i4sS14i11)
}
