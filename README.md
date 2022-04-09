# Another-ntcc-Simulator
This is just another ntcc simulator.

Autor: Rodrigo Botero Ibarra

Sin más pretensiones que la de aprender, propongo esta versión particular de simulador para el cálculo de procesos `ntcc` (non-deterministic temporal concurrent constraint) \[1, 2\]. Esta herramienta fue desarrollada completamente en `Mozart-Oz` \[3\]. No se trata de un trabajo riguroso, tampoco único, es solo un ejercicio académico que, como tal, puede estar sujeto a errores.

#### Características:

La herramienta de simulación está conformada por seis archivos .oz no compilados, que corresponden a los seis módulos siguientes:
- Un generador de aleatorios básico y un poco rudimentario;
- Un analizador sintáctico que reconoce el lenguaje `ntcc`;
- Un intérprete que traduce el árbol de derivación;
- Un simulador `ntcc` que recoge la salida del intérprete y ejecuta las simulaciones;
- Un editor de texto elemental que actúa también como la interfaz gráfica del sistema y
- Una aplicación que dibuja el árbol de derivación del código que será simulado.

En otras palabras, son seis scripts con los procedimientos y funciones necesarios para correr el simulador.

Aunque aquí se habla del lenguaje `ntcc`, debe entenderse que el `ntcc` no es un lenguaje de programación con todo lo que ello implica. El `ntcc` es un cálculo de procesos o lenguaje mínimo que permite la descripción temporal de procesos concurrentes, no deterministas, a partir de información parcial, como por ejemplo la contenida en una desigualdad.

Para que el sistema de simulación funcione correctamente, debe especificarse desde el principio una clase de dominio para las variables. Este dominio, que es el sistema de restricciones que usará el simulador, no se puede cambiar (por ahora) y está restringido a los dominios finitos. Esto significa que las simulaciones solo se pueden ejecutar usando números naturales, incluyendo el cero. El valor mínimo que se puede asignar a una variable es cero y el máximo está dado por el máximo número natural o entero positivo que soporta la versión de `Mozart-Oz` usada para ejecutar la aplicación.

El editor de texto del simulador intenta recrear las mismas coloraciones de las palabras reservadas que emplea el `Emacs` cuando se está ejecutando el Mozart, aunque con una pequeña diferencia: todas las palabras reservadas, comentarios y símbolos especiales (diferentes a los de agrupación) aparecen, no solo coloreados según el grupo al que pertencen, sino tambien resaltados en "negrilla" (mayor grosor de la letra). Solo las funciones de cortar, copiar y pegar texto están disponibles. También existe una opción para limpiar las ventanas en caso de querer empezar desde cero.

Con el editor se pueden abrir archivos de texto con programas `ntcc` previamente guardados, también modificarlos y guardarlos. Asimismo, los resultados de las simulaciones se pueden guardar en formato texto y los resultados guardados se pueden abrir en la ventana principal. También existe una opción para visualizar los árboles sintácticos de las simulaciones.

Usted puede simular los programas que desee, las veces que quiera, solo recuerde que el `Browser` queda activo desde la primera vez que se ejecuta una simulación, a menos que se cierre el editor; esto último termina todas las ejecuciones y limpia la memoria. Se recomienda realizar de vez en cuando esta acción (cerrar el editor después de guardar los cambios), máxime si el simulador corre en una máquina vieja.

#### Limitaciones:

Esta herramienta de simulación ofrece funcionalidades limitadas a lo estrictamente necesario para ejecutar código basado en el cálculo `ntcc`. Para poner las expectativas en contexto, se mencionarán solo algunas de las limitaciones de esta herramienta.

Con el editor de texto no se puede deshacer ni rehacer una acción, tampoco soporta la búsqueda de palabras, ni permite la identación automática, esta se hace manualmente aunque no es necesaria para la correcta ejecución de los programas `ntcc`. El editor no guarda automáticamente, ni sugiere guardar los cambios hechos en el programa si este se va a cerrar. Para guardar algún cambio en algún archivo simplemente hay que guardarlo de nuevo con el mismo nombre. Por ahora no existe la opción de impresión, para imprimir se abre el archivo de texto con otro editor o procesador de texto y se imprime desde allí.

Aunque las siguientes palabras resevadas son reconocidas por el editor, el simulador, sin embargo, no reconoce ni ejecuta las instrucciones que de ellas derivan y, por el contrario, pueden generar errores. Estas son: `'fun', 'lazy', 'if', 'then', 'else', 'and'` y `'or'`. Estas operaciones podrían ser incluidas en un futuro.

El constructor del árbol de derivación es un tanto ineficiente, en cuanto que el tiempo para calcular y dibujar cada árbol crece exponencialmente con el tamaño del árbol. Por este motivo no se recomienda su uso en el caso de simulaciones muy grandes. Adicionalmente, el árbol tampoco se puede guardar como imagen, esto se debe hacer por medio de una captura de pantalla.

Todavía no existe una herramienta para la visualización de los resultados que, por el momento, se muestran como listas de variables con sus respectivos valores finales.

Como ya se mencionó, el simulador solo reconoce dominios finitos y esta es una gran desventaja. En un futuro se podría estudiar la posibilidad de incluir otros dominios soportados por `Mozart-Oz`.

La herramienta de simulación tampoco soporta la verificación de los programas `ntcc`, esta podría incluirse en un futuro.

#### Descarga y ejecución:

Para ejecutar el programa primero asegúrese de tener instalado [Mozart 1.4.0 y Oz 3](https://mozart.github.io/
), preferiblemente. Luego, se debe descargar (o clonar) la carpeta del simulador con los siguientes archivos (todos en la misma carpeta): `Aleatorio.oz, LexerParser.oz, Interpreter.oz, NtccSimulator.oz, TreeBuilder.oz` y `TextEditor.oz`. También puede descargar la carpeta con los ejemplos.

Una vez descargados los archivos en una misma carpeta, abrir `TextEditor.oz` en el `Emacs` y ejecutarlo con la opción `Feed Buffer`. Inmediatamente se abrirá el editor de texto ya mencionado. Aquí podrá escribir el código `ntcc` que desee o cargarlo desde archivo y simularlo siguiendo las instrucciones y ejemplos provistos con el programa.

##### Nota:

Todos los ejemplos, que están contenidos en la carpeta 'Ejemplos', fueron ejecutados en una Acer Aspire 4315, con procesador Intel Celeron 560 a 2,13 GHz, 2,00 GB de memoria y sistema operativo Windows 7 Ultimate de 32 bits.

#### Licencia:

El conjunto de archivos que componen el simulador son de libre uso y libres de cargo. Si por algún motivo se requiere de alguna formalidad el acuerdo de licencia `BSD`, o similar, es suficiente. Téngase en cuenta que el software aquí presentado es un ejercicio puramente académico, puede contener errores y, por lo tanto, el autor no ofrece ningún tipo de garantía sobre el mismo o sobre su uso directo o indirecto, presente o futuro.

#### Agradecimientos:

El autor agradece la ayuda de todos aquellos que le guiaron en la construcción de este simulador. Especiales gracias a los profesores Mauricio Toro Bermúdez y Gerardo M. Sarria por sus aportes y guía en el desarrollo de este proyecto. También agradece a los profesores Camilo Rueda y Carlos Olarte que, en su momento, con sus comentarios y críticas, perfilaron el camino de este proyecto. El apoyo moral del profesor Ciro Jaramillo M., también fue vital para no desfallecer. Sobra mencionar también a mi hijo Santiago y a toda mi familia por su apoyo.

#### Bibliografía:

Los siguientes trabajos son el sustento teórico y práctico del proyecto.

1. Valencia, F. D., (2002). Temporal Concurrent Constraint Programming. PhD Dissertation. University of Aarhus.
2. Olarte, C., Rueda, C. y Valencia, F. D. (2013). Models and Emerging Trends of Concurrent Constraint Programming. Constraints, Springer Verlag.
3. [Van Roy, P. y Haridi, S. (2004). Concepts, Techniques, and Models of Computer Programming. The MIT Press.](https://www.info.ucl.ac.be/~pvr/book.html)
4. Arbeláez, A., Gutiérrez, J., and Pérez, J. A. (2006). Timed concurrent constraint programming in systems biology. Newsletter of the ALP 19(4).
5. Schulte, C. (Ed.). (2002). Programming constraint services: High-level programming of standard and new constraint services. Berlin, Heidelberg: Springer Berlin Heidelberg.
6. Bermúdez, M. T., Pérez, J., & Rueda, C. (2009). Towards a correct and efficient implementation of simulation and verification tools for Probabilistic ntcc (Draft).
7. Toro-Bermúdez, M., Rueda, C., Agón, C., & Assayag, G. (2009). Ntccrt: A concurrent constraint framework for real-time interaction.
8. Müller, T. (2001). Constraint propagation in Mozart. PhD Dissertation. Saarland University, Saarbruken.
9. Smolka, G. (1995). The Oz programming model. In Computer science today (pp. 324-343). Springer, Berlin, Heidelberg.

