#Declaracion de sets
set PUERTA;
set OBJETO;
set ESTE within PUERTA;
set OESTE within PUERTA;
set NORTE within PUERTA;
set C4 within OBJETO;
set C6 within OBJETO;
set SALAS;
set ROBOTS;
#Declaracion sets auxiliares para las restricciones
set rob_oeste within ROBOTS;
set rob_este within ROBOTS;
set SALAS_OESTE within SALAS;
set SALAS_ESTE within SALAS;
set AB within SALAS;
set CD within SALAS;

#Declaracion de los parametros necesarios
param reduccion {i in PUERTA, j in OBJETO};
param costes {i in PUERTA, j in OBJETO};
param rob_pres {j in ROBOTS};
param rob_lim {j in ROBOTS};
param rob_energia {j in ROBOTS};
param obj_salas {i in SALAS};

#Declaracion de las variables de decision

#Variable de decision de la primera parte, de enteros
var objetos_por_puerta {i in PUERTA, j in OBJETO}, integer;

#Variable de decision de la segunda parte, binaria
var robots_por_sala {i in SALAS, j in ROBOTS}, binary; /* segunda parte*/

#Funcion objetivo del problema juntando la primera parte y la segunda.
minimize Time: sum{i in SALAS, j in ROBOTS}(robots_por_sala[i,j]*obj_salas[i]*rob_pres[j])+(320 - (sum{i in PUERTA, j in OBJETO}(objetos_por_puerta[i,j] * reduccion[i,j]))/3);

#Restricciones del primer problema

#La suma del coste de todos los elementos de todas las puertas al dia no debe superar los 1000 euros
s.t. Max_coste_por_dia: (sum{i in PUERTA, j in OBJETO}(objetos_por_puerta[i,j] * costes[i,j]))*8 <= 1000;

#El coste total por dia en la entrada principal debe ser menor que el 10 por ciento de la entrada secundaria norte
s.t. Max_coste_por_dia_main1: (sum{i in ESTE, j in OBJETO}(objetos_por_puerta[i,j] * costes[i,j])) <= (sum{i in NORTE, j in OBJETO}(objetos_por_puerta[i,j] * costes[i,j]))*1.1;

#El coste total por dia de la entrada principal debe ser menor que el 10 por ciento de la entrada secundaria oeste
s.t. Max_coste_por_dia_main2: (sum{i in ESTE, j in OBJETO}(objetos_por_puerta[i,j] * costes[i,j])) <= (sum{i in OESTE, j in OBJETO}(objetos_por_puerta[i,j] * costes[i,j]))*1.1;

#La suma del numero de maquinas y tornos en la puerta Norte, definido con el set C4, no debe ser superior a la misma suma en la puerta Este
s.t. Max_numero_norte: (sum{i in NORTE, j in C4}(objetos_por_puerta[i,j])) <= (sum{i in ESTE, j in C4}(objetos_por_puerta[i,j]))-1;

#La suma del numero de maquinas y tornos de la puerta Oeste, definido en el set C4, no debe ser superior a la misma suma en la puerta Este
s.t. Max_numero_oeste: (sum{i in OESTE, j in C4}(objetos_por_puerta[i,j])) <= (sum{i in ESTE, j in C4}(objetos_por_puerta[i,j]))-1;

#El numero maximo de tornos, definido en el set C6, debe ser menor a la misma suma en la puerta Oeste
s.t. Max_torno_puerta: sum{i in NORTE, j in C6}(objetos_por_puerta[i,j]) <= (sum{i in OESTE, j in C6}(objetos_por_puerta[i,j]))-1;

#En la puerta Este debe haber como minimo dos objetos de cada tipo (maquinas, tornos y personas)
s.t. Min_objetos_este {i in ESTE, j in OBJETO}: (objetos_por_puerta[i,j]) >= 2;

#En la puerta Norte debe haber como minimo 1 objeto de cada tipo
s.t. Min_objetos_norte {i in NORTE, j in OBJETO}: (objetos_por_puerta[i,j]) >= 1;

#En la puerta oeste debe haber como minimo 1 objeto de cada tipo
s.t. Min_objetos_oeste {i in OESTE, j in OBJETO}: (objetos_por_puerta[i,j]) >= 1;

#La reduccion de tiempo en la entrada Este debe ser mayor a la reduccion llevaba a cabo en la entrada norte
s.t. Reduc_este_norte: (sum{i in ESTE, j in OBJETO}(objetos_por_puerta[i,j] * reduccion[i,j])) >= (sum{i in NORTE, j in OBJETO}(objetos_por_puerta[i,j] * reduccion[i,j]))+1;

#La reduccion de tiempo en la entrada Este debe ser mayor a la reduccion llevaba a cabo en la entrada oeste
s.t. Reduc_este_oeste: (sum{i in ESTE, j in OBJETO}(objetos_por_puerta[i,j] * reduccion[i,j])) >= (sum{i in OESTE, j in OBJETO}(objetos_por_puerta[i,j] * reduccion[i,j]))+1;

#Restriccion auxiliar para que la suma maxima de tiempo en la entrada este sea 130, en caso contrario la funcion objetivo no funciona
s.t. maxeste: sum{i in ESTE, j in OBJETO}objetos_por_puerta[i,j]<=130;

#Restriccion auxiliar para que la suma maxima de tiempo en la entrada norte sea 100, en caso contrario la funcion objetivo no funciona
s.t. maxnorte: sum{i in NORTE, j in OBJETO}objetos_por_puerta[i,j]<=100;

#Restriccion auxiliar para que la suma maxima de tiempo en la entrada oeste sea 90, en caso contrario la funcion objetivo no funciona
s.t. maxoeste: sum{i in OESTE, j in OBJETO}objetos_por_puerta[i,j]<=90;


#Restricciones de la segunda parte de la practica

#Debe haber un robot en cada sala en todo momento. Asi mismo, esta restriccion cumple tambien con que cada sala debe tener un robot en todo momento.
s.t. n_robots_salas {i in SALAS}: sum{j in ROBOTS} robots_por_sala[i,j] = 1;

#Numero de salas minimas que deben tener asignadas los robots
s.t. min_salas_robot {j in ROBOTS}: sum {i in SALAS} robots_por_sala[i,j] >=2;

#Numero de salas maximas que deben tener asignadas los robots
s.t. max_salas_robot {j in ROBOTS}: sum {i in SALAS} robots_por_sala[i,j] <=3;

#La suma de las salas del este de los robots asignados al oeste debe ser 0 para cumplir que esos robots no son asignados a salas prohibidas
s.t. robots_por_oeste_sala {j in rob_oeste}: sum{i in SALAS_ESTE} robots_por_sala[i,j]=0;

#La suma de las salas del oeste de los robots asignados al este debe ser 0 para cumplir que esos robots no son asignados a salas prohibidas
s.t. robots_por_este_sala {j in rob_este}: sum{i in SALAS_OESTE} robots_por_sala[i,j]=0;

#La suma de los robots asignados a las salas A B, definidas con el subconjunto AB en los sets, debe ser mayor a la misma suma en C y D para que puedan ser asignados a esas salas
s.t. robotsABCD {j in ROBOTS}: sum{i in AB} robots_por_sala[i,j] >= sum{i in CD} robots_por_sala[i,j];

#Los robots no deben presentar salas cuyas prestaciones sean mayores de la energia limite de cada robot
s.t. limiteEnergia {j in ROBOTS}: sum{i in SALAS}((robots_por_sala[i,j]*rob_energia[j])*obj_salas[i])<= rob_lim[j];

#El tiempo de las presentaciones del ala oeste debe ser mayor en un 10 por ciento al tiempo requerido a las presentaciones del ala este
s.t. tiempo_max_pres: (sum{i in SALAS_ESTE, j in ROBOTS} (robots_por_sala[i,j]*obj_salas[i]*rob_pres[j]))*1.1 <= (sum{i in SALAS_OESTE, j in ROBOTS} (robots_por_sala[i,j]*obj_salas[i]*rob_pres[j]))+1;


end;
