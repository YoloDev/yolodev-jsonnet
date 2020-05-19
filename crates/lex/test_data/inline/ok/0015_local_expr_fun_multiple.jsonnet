local foo(a, b = 2) = a + b,
      bar(a = 1, b = 2) = foo(a, b) + foo(a, b);
bar
