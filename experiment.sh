bash build.sh
#executable =("st_seq")
file_input=("wiki" "world_leaders" "dna" "coreutils")
#file_input=("test" "test2")
n_experiment=("1" "2" "3" "4")
parameters=("1000000" "2000000" "3000000" "4000000" "5000000" "6000000" "7000000" "8000000" "9000000" "10000000")
#parameters=("100" "200" "300" "400")

files=${#file_input[@]}
experiments=${#n_experiment[@]}
parameter=${#parameters[@]}
outfile2=result$(date +"%Y-%m-%d-%H:%M:%S").txt 
for ((i=0; i<${files}; i++))
do
    for ((j=0; j<${experiments}; j++))
    do
        for ((k=0; k<${parameter}; k++))
        do
            echo "./st_seq" "${file_input[i]}.par" "${n_experiment[j]}" "${parameters[k]}" 
            ./st_seq ${file_input[i]}.par ${n_experiment[j]} ${parameters[k]} >> ${outfile2}
            echo "Descanso"
            sleep 10  
        done  
    done  
done 
