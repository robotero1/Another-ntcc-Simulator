# Another-ntcc-Simulator
This is just another ntcc simulator.

Autor: Rodrigo Botero Ibarra

Sin más pretensiones que la de aprender, propongo esta versión particular de simulador para el cálculo de procesos ntcc (non-deterministic temporal concurrent constraint). Esta herramienta está escrita completamente en Mozart-Oz. No se trata de un trabajo riguroso, tampoco único, es solo un ejercicio académico que, como tal, puede estar sujeto a errores.

Características:

La herramienta de simulación está conformada por seis archivos .oz no compilados, que corresponden a los seis módulos siguientes:
- Un generador de aleatorios básico y un poco rudimentario;
- Un analizador sintáctico que reconoce el lenguaje ntcc;
- Un intérprete que traduce el árbol de derivación;
- Un simulador ntcc que recoge la salida del intérprete y ejecuta las simulaciones;
- Un editor de texto elemental que actúa también como la interfaz gráfica del sistema y
- Una aplicación que dibuja el árbol de derivación del código que será simulado.

En otras palabras, son seis scripts con los procedimientos y funciones necesarios para correr el simulador.

Aunque aquí se habla del lenguaje ntcc, debe entenderse que el ntcc no es un lenguaje de programación con todo lo que ello implica. El ntcc es un cálculo de procesos o lenguaje mínimo que permite la descripción temporal de procesos concurrentes, no deterministas, a partir de información parcial, como la contenida en una desigualdad.

Para que el sistema de simulación funcione correctamente, debe especificarse desde el principio un dominio para las variables. Este dominio, que es el sistema de restricciones que usará el simulador, no se puede cambiar (por ahora) y está restringido a los dominios finitos. Esto significa que las simulaciones solo se pueden ejecutar usando números naturales, incluyendo el cero. El valor mínimo que se puede asignar a una variable es cero y el máximo está dado por el máximo número natural que soporta la versión de Mozart-Oz usada para ejecutar la aplicación.

El editor de texto del sistema intenta recrear las mismas coloraciones de las palabras reservadas que emplea el Emacs cuando se está ejecutando el Mozart, aunque con algunas pequeñas diferencias: todas las palabras reservadas, comentarios y símbolos especiales (diferentes a los de agrupación) aparecen, no solo coloreados según el grupo al que pertencen, sino tambien resaltados en "negrilla" (mayor grosor de la letra). Solo las funciones de cortar, copiar y pegar texto están disponibles; no se puede deshacer una operación, tampoco soporta la búsqueda de palabras, ni permite la identación automática, esta se hace manualmente aunque no es necesaria. Más adelante se verán otras características del editor de texto.

Descarga y ejecución:

Para ejecutar el programa primero asegúrese de tener instalado Mozart 1.4.0 y Oz 3, preferiblemente. Luego, se debe descargar (o clonar) la carpeta del simulador con los siguientes archivos (todos en la misma carpeta): Aleatorio.oz, LexerParser.oz, Interpreter.oz, NtccSimulator.oz, TreeBuilder.oz y TextEditor.oz.
Una vez descargados los archivos en una misma carpeta, abrir TextEditor.oz en el Emacs y ejecutarlo con la opción Feed Buffer. Inmediatamente se abrirá el editor de texto ya mencionado. Aquí podrá escribir el código ntcc que desee o cargarlo desde archivo y simularlo siguiendo las instrucciones y ejemplos provistos con el programa.

Licencia:

El conjunto de archivos que componen el simulador son de libre uso y libres de cargo. Si por algún motivo se requiere de alguna formalidad el acuerdo de licencia BSD es suficiente. Téngase en cuenta que el software aquí presente es un ejercicio puramente académico, puede contener errores, y por lo tanto el autor no ofrece ningún tipo de garantía sobre el mismo o sobre su uso, directo o indirecto.


En construcción...
