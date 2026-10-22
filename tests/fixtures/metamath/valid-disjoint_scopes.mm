$c wff pair $.
$v x y $.
fx $f wff x $.
fy $f wff y $.
$d x y $.
outer $a wff pair x y $.
${
  $d x y $.
  inside $p wff pair x y $= fx fy outer $.
$}
after $p wff pair x y $= fx fy outer $.
${
  $v z $.
  fz $f wff z $.
  $d x z $.
  scoped $a wff pair x z $.
$}
${
  $v z $.
  fz2 $f wff z $.
  $d y z $.
  scoped2 $a wff pair y z $.
$}
