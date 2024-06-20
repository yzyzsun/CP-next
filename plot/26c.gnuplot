set terminal pdf mono font "Linux Biolinum,10" size 2.5,2
set output '26c.pdf'

set style data histogram
set yrange [0.5:5]
set ytics (0.5,1,2,3,4,5)
set style histogram cluster gap 1
set style line 1 lc rgb 'black' lt 1 lw 1
set boxwidth 0.9
set key left top
set xtics scale 0
set ylabel 'Execution time ratio (slowdown)'
set logscale y
set grid ytics
plot "<awk -F'\t' 'NR==1{print $1,$3} NR>1{print $1,1}'     26c.tsv" u 2:xtic(1) ti col ls 1 fillstyle pattern 6, \
     "<awk -F'\t' 'NR==1{print $1,$2} NR>1{print $1,$2/$3}' 26c.tsv" u 2 ti col ls 1, \
     1 noti dashtype 2
