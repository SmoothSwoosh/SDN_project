Задача построения сети управления для SDN сети.

Выполнил задачу Новиков Сергей Александрович, студент 204 группы ВМК МГУ.

Дата выполнения: 16.04.2022

Задание описано в файле SDN_network.pdf.

Список библиотек, использующихся в реализации:
- Boost (а точнее, это собрание библиотек классов)
- std - для использования M_PI, cos, sin, sqrt, asin, pow, sort, make_pair и stringstream
- graphviz - для визуализации остовного дерева


Запуск программы:
- Для запуска программы необходимо установить boost и graphviz.
  Для этого в среде Linux (Ubuntu) нужно выполнить следующую команду:
    sudo apt-get install g++ libboost-all-dev graphviz
- После установки можно приводить программу в эксплуатацию. Делается это следующим образом:
    - Для компиляции программы используется команда: g++ sdn.cpp -std=c++1z -o sdn -lboost_graph -lboost_program_options
      где sdn.cpp - это файл, содержащий код программы (находится в архиве к заданию).
    - Далее пользователь вводит: ./sdn -t "FILENAME".graphml -k CRITERION
      где FILENAME - имя файла с топологией графа в формате .GraphML, 
      а CRITERION - число 1 или 2 в зависимости от выбранного пользователем критерия.


При запуске программы выполняется следующее:
- Генерируются два csv файла: один ("FILENAME"_topo.csv) описывает топологию исходного графа,
  а второй ("FILENAME"_routes.csv) - топологию остовного дерева, построенного по выбранному пользователем критерию.
- Также создаётся dot файл ("FILENAME"_tree.dot) с визуализацией построенного остовного дерева.


Описание визуализации графа:
- Красным цветом помечен узел контроллера, а чёрным - остальные вершины.
- Зелёным цветом помечены каналы связи, входящие в остовное дерево, а чёрным - остальные.


Дополнительные пояснения:
- Для отображения содержимого файла "FILENAME"_tree.dot используйте команду
  dot -Tx11 "FILENAME"_tree.dot
- В файле "FILENAME"_routes.csv есть также резервные (reserve) пути, которые будут использованы в случае, если
  произойдёт поломка в главном (main) пути.
- В папке tests есть csv файлы и dot файлы как для выбора критерия k1, так и для выбора критерия k2+k1.
  Критерию k1 соответствуют файлы "FILENAME"_routes1.csv и "FILENAME"_tree1.dot, 
  а k2 - "FILENAME"_routes2.csv и "FILENAME"_tree2.dot
