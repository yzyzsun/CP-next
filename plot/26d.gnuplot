set terminal pdf mono font "Linux Biolinum,10" size 2.5,2
set output '26d.pdf'

set style data linespoints
set style histogram cluster gap 1
set style line 1 lc rgb 'black' lt 1 lw 1
set boxwidth 0.9
set key left top
set xlabel 'Inheritance level'
set xtics 1
set ylabel 'Execution time (ms)'
set ytics 1000
set yrange [0:6000]

# A = 10
# B = 20
# Z = 1
# f(x) = (x <= A) ? x : (x < B) ? NaN : (x - B + A + Z)
# g(x) = (x <= A) ? x : (x < A + Z) ? NaN : (x + B - A - Z)
# set nonlinear x via f(x) inverse g(x)
# set arrow 1 from A, graph 0 to B, graph 0 nohead lt B lc bgnd front
# set arrow 2 from A, graph 0 length graph  .01 angle 60 nohead front
# set arrow 3 from A, graph 0 length graph -.01 angle 60 nohead front
# set arrow 4 from B, graph 0 length graph  .01 angle 60 nohead front
# set arrow 5 from B, graph 0 length graph -.01 angle 60 nohead front

plot '26d.tsv' using 1:4 ti col ls 3 with lines, \
     '' u 1:3 ti col ls 2 with lines, \
     '' u 1:2 ti col ls 1 with lines
