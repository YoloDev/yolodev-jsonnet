{
  local c = $,
  local a = c,
  a::5,
  k::'test',
  assert $.a == 5,
  assert a.a == 5,
}
