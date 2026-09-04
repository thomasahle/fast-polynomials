
y = (x) * (x);
z = (a12 + x + y) * (a11 + y);
w = (a10 + y + z) * (a9 + z);
v = (a8 + y + z) * (a7 + w);
u = (a6 + z + v) * (a5 + x);
t = (a4 + x + y) * (a3 + x);
s = (a2 + w + t) * (a1 + y);
P = a0 + v + u + s ;
jac test
jac good!
13 good!

y = (x) * (x);
z = (a14 + x) * (a13 + y);
w = (a12 + x + z) * (a11 + z);
v = (a10 + y + z) * (a9 + w);
u = (a8 + z) * (a7 + w);
t = (a6 + x + w) * (a5 + v);
s = (a4 + z + w) * (a3 + y);
r = (a2 + y + w) * (a1 + u);
P = a0 + z + w + v + t + s + r ;
jac test
jac good!
15 good!

y = (x) * (x);
z = (a16 + x + y) * (a15 + y);
w = (a14 + x + z) * (a13 + z);
v = (a12 + y + z) * (a11 + x);
u = (a10 + x + z) * (a9 + v);
t = (a8 + y) * (a7 + z);
s = (a6 + x + y) * (a5 + w);
r = (a4 + y + z) * (a3 + t);
q = (a2 + y + w) * (a1 + u);
P = a0 + s + r + q ;
jac test
jac good!

17 good!
y = (x) * (x);
z = (a18 + x + y) * (a17 + y);
w = (a16 + x + z) * (a15 + x);
v = (a14 + y + w) * (a13 + w);
u = (a12 + y + w) * (a11 + z);
t = (a10 + y + z) * (a9 + w);
s = (a8 + w + v) * (a7 + y);
r = (a6 + w) * (a5 + u);
q = (a4 + z + v) * (a3 + t);
p = (a2 + x + s) * (a1 + y);
P = a0 + r + q + p ;
jac test
jac good!
19 good!

y = (x) * (x);
z = (a20 + x) * (a19 + y);
w = (a18 + y + z) * (a17 + z);
v = (a16 + y + w) * (a15 + z);
u = (a14 + y) * (a13 + w);
t = (a12 + x + w) * (a11 + w);
s = (a10 + z + v) * (a9 + t);
r = (a8 + w) * (a7 + t);
q = (a6 + y + r) * (a5 + x);
p = (a4 + w + u) * (a3 + z);
o = (a2 + u + r) * (a1 + y);
P = a0 + w + s + q + p + o ;
jac test
jac good!
21 good!

