set terminal pdf mono font "Linux Biolinum,10" size 5,2
set output '25b.pdf'

set style data histogram
set yrange [0.5:1000]
set style histogram cluster gap 1
set style line 1 lc rgb 'black' lt 1 lw 1
set style fill pattern border -1
set boxwidth 0.9
set key left top
set xtics scale 0
set ylabel 'Execution time ratio (slowdown)'
set logscale y
set grid ytics
plot "<awk -F'\t' 'NR==1{print $1,$3} NR>1{print $1,1}'     25b.tsv" u 2:xtic(1) ti col ls 1, \
     "<awk -F'\t' 'NR==1{print $1,$5} NR>1{print $1,$5/$3}' 25b.tsv" u 2 ti col ls 1 fillstyle pattern 3, \
     "<awk -F'\t' 'NR==1{print $1,$4} NR>1{print $1,$4/$3}' 25b.tsv" u 2 ti col ls 1 fillstyle pattern 2, \
     "<awk -F'\t' 'NR==1{print $1,$6} NR>1{print $1,$6/$3}' 25b.tsv" u 2 ti col ls 1 fillstyle pattern 4, \
     "<awk -F'\t' 'NR==1{print $1,$7} NR>1{print $1,$7/$3}' 25b.tsv" u 2 ti col ls 1, \
     "<awk -F'\t' 'NR==1{print $1,$8} NR>1{print $1,$8/$3}' 25b.tsv" u 2 ti col ls 1 fillstyle pattern 1, \
     1 noti dashtype 2
