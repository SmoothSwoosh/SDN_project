#include <algorithm>  //sort
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graph_utility.hpp>
#include <boost/graph/graphml.hpp>
#include <boost/graph/graphviz.hpp>
#include <boost/program_options.hpp>
#include <boost/property_map/dynamic_property_map.hpp>
#include <boost/property_map/property_map.hpp>
#include <cmath>  //M_PI, cos, sin, sqrt, asin, pow
#include <fstream>
#include <iostream>  //Input/output
#include <set>
#include <sstream>
#include <string>
#include <utility>  //make_pair
#include <vector>

const int EARTH_RADIUS = 6371;   // Earth radius equals 6371 km
const double CABLE_DELAY = 4.8;  // Cable delay equals 4.8 microseconds per km
const double INF = 1000 * 1000 * 1000;  // Infimum of delays

using namespace boost;
using std::cerr;
using std::cout;
using std::endl;
using std::ifstream;
using std::ios;
using std::ofstream;
using std::pair;
using std::set;
using std::string;
using std::stringstream;
using std::swap;
using std::vector;

// Class Node which holds nodes' information
// such as latitude, longitude and ID in topology
class Node {
 private:
  string label;
  double latitude, longitude;
  int id;
  bool broken;

 public:
  Node() = default;  // Default constructor

  Node(const string &label, double latitude, double longitude, int id,
       bool broken)
      : label(label),
        latitude(latitude),
        longitude(longitude),
        id(id),
        broken(broken){};  // Node's constructor

  // Copy constructor of Node
  Node(const Node &other) {
    label = other.get_label();
    latitude = other.get_latitude();
    longitude = other.get_longitude();
    id = other.get_id();
    broken = other.is_broken();
  }

  // Getters
  string get_label() const { return label; }

  double get_latitude() const { return latitude; }

  double get_longitude() const { return longitude; }

  int get_id() const { return id; }

  bool is_broken() const { return broken; }
};

// Class Edge which holds channels' information:
// source node, target node, delay between them
class Edge {
 private:
  int source, target;
  double delay;

 public:
  // Default constructor
  Edge() = default;

  // Edge constructor
  Edge(int source, int target, double delay) {
    this->source = source;
    this->target = target;
    this->delay = delay;
  }

  // Copy constructor
  Edge(const Edge &other) {
    source = other.get_source();
    target = other.get_target();
    delay = other.get_delay();
  }

  // Getters
  int get_source() const { return source; }

  int get_target() const { return target; }

  double get_delay() const { return delay; }

  double get_distance() const { return delay / CABLE_DELAY; }
};

// Structure for holding dijkstra function output
typedef struct Dijkstra_Holder {
  int controller_node;  // Node where controller is supposed to be located
  vector<int> p;        // Vector of parents
  vector<double>
      distances;  // Vector of distances from controller node to others

  // Constructor
  Dijkstra_Holder(int controller_node, const vector<int> &p,
                  const vector<double> &distances) {
    this->controller_node = controller_node;
    this->p = p;
    this->distances = distances;
  }

  // Copy constructor
  Dijkstra_Holder(const Dijkstra_Holder &other) {
    this->controller_node = other.controller_node;
    this->p = other.p;
    this->distances = other.distances;
  }
} Dijkstra_Holder;

// Measure the distance between point A and B on Earth
// using the Great circle method (Haversine formula)
double distance_between_nodes(const Node &A, const Node &B) {
  // Take latitudes and longitudes from Nodes
  double A_latitude = A.get_latitude();
  double A_longitude = A.get_longitude();
  double B_latitude = B.get_latitude();
  double B_longitude = B.get_longitude();

  // Lambda-function that converts degrees to radians
  auto convert_to_radians = [](double degrees) { return M_PI * degrees / 180; };

  // Convert latitudes and longitudes from degrees to radians
  A_latitude = convert_to_radians(A_latitude);
  A_longitude = convert_to_radians(A_longitude);
  B_latitude = convert_to_radians(B_latitude);
  B_longitude = convert_to_radians(B_longitude);

  // Calculate an answer using Haversine formula
  // link to source: https://en.wikipedia.org/wiki/Haversine_formula

  double dist = pow(sin((B_latitude - A_latitude) / 2), 2) +
                cos(A_latitude) * cos(B_latitude) *
                    pow(sin((B_longitude - A_longitude) / 2), 2);
  dist = 2 * EARTH_RADIUS * asin(sqrt(dist));

  return dist;
}

// Calculate delays between any two nodes of topology.
// Returns a sorted vector of channels
vector<vector<pair<int, double>>> calculate_delays(
    const vector<Node> &node_holder, const vector<vector<int>> &topology) {
  vector<vector<pair<int, double>>> channels(node_holder.size());

  for (size_t v = 0; v < topology.size(); ++v) {
    // Through all nodes in topology
    for (int u : topology[v]) {
      // Through all neighbours of node v

      // Calculate a distance between v and its neighbour u
      double dist =
          distance_between_nodes(node_holder.at(v), node_holder.at(u));

      // Then calculate a delay between then
      double delay = dist * CABLE_DELAY;

      // Collect this information in channels
      channels[v].push_back(pair<int, double>(u, delay));
      channels[u].push_back(pair<int, double>(v, delay));
    }
  }

  // Sort channels by their IDs
  for (size_t v = 0; v < channels.size(); ++v) {
    sort(channels[v].begin(), channels[v].end());
  }

  return channels;
}

// Realization of Dijkstra algorithm
// which returns a controller node, vector of paths from controller to other
// nodes and distances from controller node to others. Asymptotics of this
// Dijkstra algorithm realization is O(m * logn), where n - number of nodes in
// topology and m - number of channels. This asymptotics is achieved by using
// set<distance, node_id> - logn and linear passage through all channels (i.e.
// edges) - m. And overall asymptotics of this function is O(n * m * logn)
// because of usage Dijkstra algorithm for each node.
Dijkstra_Holder dijkstra(const vector<vector<pair<int, double>>> &channels,
                         int state) {
  // NOTE: Distance between nodes v and u is a delay between them!

  vector<double> max_delays;  // Vector of maximum delays

  vector<vector<int>> parents;  // Vector of paths from one node to others

  vector<vector<double>> distances;  // Vector of distances from one to others

  // Through all nodes of topology
  for (size_t s = 0; s < channels.size(); ++s) {
    // Vector of distances between node s and other nodes
    vector<double> dist(channels.size(), INF);

    vector<int> p(channels.size(), -1);  // Path between node s and others

    if (channels[s].size() == 0) {
      // If this vertex is isolated
      max_delays.push_back(INF);
      distances.push_back(dist);
      parents.push_back(p);
      continue;
    }

    set<pair<double, int>> q;  // Set of nodes in order to sort them by
                               // distances

    dist[s] = 0;  // Distance between s ans s is obviously 0
    q.insert(pair<double, int>(dist[s], s));

    // Through all channels
    while (!q.empty()) {
      // Take next node and remove it from the set
      int v = q.begin()->second;
      q.erase(q.begin());

      // Through all neighbours of this node
      for (auto edge : channels[v]) {
        int u = edge.first;          // Neighbour
        double delay = edge.second;  // Delay between v and u

        if (dist[v] + delay < dist[u]) {
          // If we can decrease the delay between v and u (relaxation)
          // we will do it
          q.erase(pair<double, int>(dist[u], u));
          dist[u] = dist[v] + delay;
          p[u] = v;
          q.insert(pair<double, int>(dist[u], u));
        }
      }
    }
    // Collect gathered information in our vectors
    double mx = 0.0;
    for (auto elem : dist) {
      if (elem != INF && elem > mx) {
        mx = elem;
      }
    }
    max_delays.push_back(mx);
    distances.push_back(dist);
    parents.push_back(p);
  }

  // Find the node which would be a controller
  int controller_node =
      (state != -1) ? state
                    : min_element(max_delays.begin(), max_delays.end()) -
                          max_delays.begin();

  return Dijkstra_Holder(controller_node, parents[controller_node],
                         distances[controller_node]);
}

// DSU(disjoint set union) realization:
// Get a parent of node
int get(int x, vector<int> &parent) {
  if (parent[x] != x) {
    parent[x] = get(parent[x], parent);
  }
  return parent[x];
}

// Join nodes x and y into one union
void join(int x, int y, vector<int> &parent, vector<int> &ranks) {
  x = get(x, parent);
  y = get(y, parent);

  if (x == y) {
    // If x and y have common parent
    return;
  }

  if (ranks[x] < ranks[y]) {
    swap(x, y);
  }

  parent[y] = x;  // Parent of y is now node x

  ranks[x] += ranks[y];
}

// Find minimum spanning tree
// using Kruskal's algorithm.
// This realization uses DSU (disjoint set union)
// to reach asymptotics of O(m * alpha(mn)) except sorting edges which is O(m *
// logm), where n - number of nodes in topology, m - number of channels and alpha
// is an inverse Ackermann's function whose value grows very slowly. With sorting
// edges by their weights (delays) the overall asymptotics is O(m * logm)
vector<vector<pair<int, double>>> minimum_spanning_tree(
    const vector<vector<pair<int, double>>> &channels) {
  // NOTE: edge between nodes v and u is channel between them!

  // Make up a vector of edges from channels
  vector<Edge> edges;

  // Through all nodes
  for (size_t v = 0; v < channels.size(); ++v) {
    // Through all neighbours of v
    for (auto edge : channels[v]) {
      int u = edge.first;          // Neighbour of v
      double delay = edge.second;  // Delay between v and u

      edges.push_back(Edge(v, u, delay));
    }
  }

  // Lambda-function comparator for edges
  auto cmp = [](const Edge &a, const Edge &b) {
    return a.get_delay() < b.get_delay();
  };

  // Sort edges using comparator cmp
  sort(edges.begin(), edges.end(), cmp);

  // Vector which holds minimum spanning tree
  vector<vector<pair<int, double>>> min_span_tree(channels.size());
  vector<int> parent(channels.size());  // Vector which holds parent of each
                                        // node
  vector<int> ranks(
      channels.size());  // Vector which holds rank of each union in DSU

  for (size_t v = 0; v < channels.size(); ++v) {
    parent[v] = v;
    ranks[v] = 1;
  }

  for (const Edge &edge : edges) {
    int v = edge.get_source();        // Source
    int u = edge.get_target();        // Target
    double delay = edge.get_delay();  // Delay between source and target

    if (get(u, parent) != get(v, parent)) {
      // If nodes u and v are not in the same union
      // then add edge between them into spanning tree
      min_span_tree[v].push_back(pair<int, double>(u, delay));
      min_span_tree[u].push_back(pair<int, double>(v, delay));
      // and join nodes u and v
      join(u, v, parent, ranks);
    }
  }

  return min_span_tree;
}

// K1 criterion realization
Dijkstra_Holder first_criterion(
    const vector<vector<pair<int, double>>> &channels) {
  // Use Dijkstra algorithm to find controller node
  return dijkstra(channels, -1);  // since C++17
}

// K2 criterion realization
Dijkstra_Holder second_criterion(
    const vector<vector<pair<int, double>>> &channels) {
  // Firstly take a minimum spanning tree
  vector<vector<pair<int, double>>> min_span_tree;
  min_span_tree = minimum_spanning_tree(channels);

  // Then using it with Dijkstra algorithm
  // calculate controller node, vector of paths and distances
  return dijkstra(min_span_tree, -1);  // since C++17
}

// Structure for holding vertices' properties
typedef struct VertexProperty {
  int id;
  double latitude, longitude;
  string label;
} VertexProperty;

typedef adjacency_list<vecS, vecS, undirectedS, VertexProperty> Graph;
typedef graph_traits<Graph>::edge_iterator edge_iterator;

// Parse a graph
Graph ReadGraph(const string &filename) {
  ifstream is(filename);

  if (!is.is_open()) {
    cerr << "Topology's filename is wrong!" << endl;
    exit(1);
  }

  Graph graph;
  // Add needed properties to the graph
  dynamic_properties dp(ignore_other_properties);
  dp.property("label", get(&VertexProperty::label, graph));
  dp.property("id", get(&VertexProperty::id, graph));
  dp.property("Latitude", get(&VertexProperty::latitude, graph));
  dp.property("Longitude", get(&VertexProperty::longitude, graph));

  // And try to parse graph
  try {
    read_graphml(is, graph, dp);
  } catch (const std::exception &e) {
    cerr << "Cannot parse the graph: " << e.what() << endl;
    exit(1);
  }

  is.close();

  return graph;
}

// Returns a vector of Nodes(vertices) for our needs
vector<Node> get_node_holder(const Graph &g) {
  vector<Node> node_holder;

  Graph::vertex_iterator v, vend;
  for (tie(v, vend) = vertices(g); v != vend; ++v) {
    // Through all vertices of graph

    // Get all needed properties of node
    string label = g[*v].label;
    int id = g[*v].id;
    double latitude = g[*v].latitude;
    double longitude = g[*v].longitude;

    bool broken = false;
    if (latitude == 0 && longitude == 0) {
      // Vertex is incorrect
      broken = true;
      cerr << "Graph is incorrect. It has broken vertex with id = " << id << "!"
           << endl;
      cerr << "So the program removed this vertex and continued its work"
           << endl;
    }

    // Add node
    node_holder.push_back(Node(label, latitude, longitude, id, broken));
  }

  auto cmp = [](const Node &a, const Node &b) {
    return a.get_id() < b.get_id();
  };

  // Sort nodes by their indices
  sort(node_holder.begin(), node_holder.end(), cmp);

  return node_holder;
}

// Returns topology of graph
//(topology is represented as adjacent list
vector<vector<int>> get_topology(const vector<Node> &node_holder,
                                 const Graph &g) {
  vector<vector<int>> topology(node_holder.size());

  pair<edge_iterator, edge_iterator> ei = edges(g);
  for (auto it = ei.first; it != ei.second; ++it) {
    // Throught all edges of graph

    // Get source and target vertices
    int a_node = source(*it, g);
    int b_node = target(*it, g);

    if (node_holder[a_node].is_broken() || node_holder[b_node].is_broken()) {
      // If one of nodes is broken then we should skip this edge
      continue;
    }

    if (a_node != b_node &&
        find(topology[a_node].begin(), topology[a_node].end(), b_node) ==
            topology[a_node].end()) {
      // Add them into topology if they are not already there
      topology[a_node].push_back(b_node);
    }
  }

  return topology;
}

// Returns a new vector of channels
// except for vertices (and their edges) which are contained in vector path
vector<vector<pair<int, double>>> reserve_channels(
    const vector<Node> &node_holder, const vector<vector<int>> &topology,
    const vector<int> &path) {
  vector<int> deleted_path;
  for (size_t v = 0; v < path.size(); ++v) {
    if (v != 0 && (v + 1 < path.size())) {
      deleted_path.push_back(path[v]);
    }
  }

  vector<vector<int>> new_topology(node_holder.size());
  for (size_t v = 0; v < topology.size(); ++v) {
    for (size_t u : topology[v]) {
      if (find(deleted_path.begin(), deleted_path.end(), v) ==
              deleted_path.end() &&
          find(deleted_path.begin(), deleted_path.end(), u) ==
              deleted_path.end()) {
        new_topology[v].push_back(u);
      }
    }
  }

  return calculate_delays(node_holder, new_topology);
}

// Make a first csv-file which represents topology
void first_csv(const string &filename, const vector<Node> &node_holder,
               const vector<vector<pair<int, double>>> &channels) {
  ofstream input;
  input.open(filename, ios::ate | ios::trunc);

  if (!input.is_open()) {
    cerr << "Oops! Something wrong occured while creating a csv-file!" << endl;
    return;
  }

  string in =
      "Node 1(id), Node 1(label), Node 1(longitude), Node 1(latitude),"
      "Node 2(id), Node 2(label), Node 2(longitude), Node 2(latitude),"
      "Distance (km), Delay (mks)\n";
  input << in;

  for (size_t v = 0; v < channels.size(); ++v) {
    for (size_t u = 0; u < channels[v].size(); ++u) {
      int id1 = v;
      string label1 = node_holder[id1].get_label();
      double longitude1 = node_holder[id1].get_longitude();
      double latitude1 = node_holder[id1].get_latitude();

      int id2 = channels[v][u].first;
      string label2 = node_holder[id2].get_label();
      double longitude2 = node_holder[id2].get_longitude();
      double latitude2 = node_holder[id2].get_latitude();

      int delay = static_cast<int>(channels[v][u].second);
      int dist = delay / CABLE_DELAY;

      stringstream ss;
      ss << id1 << ",\"" << label1 << "\"," << longitude1 << ',' << latitude1
         << ',' << id2 << ",\"" << label2 << "\"," << longitude2 << ','
         << latitude2 << ',' << dist << ',' << delay << '\n';

      input << ss.str();
    }
  }

  input.close();
}

// Make a second csv-file which represents
// the results of Dijkstra and Kruskall algorithms' work
void second_csv(const string &filename, int node_controller,
                const vector<int> &p, const vector<double> &distances,
                const vector<Node> &node_holder,
                const vector<vector<int>> &topology,
                const vector<vector<pair<int, double>>> &channels) {
  ofstream routes_input;
  routes_input.open(filename, ios::ate | ios::trunc);

  if (!routes_input.is_open()) {
    cerr << "Oops! Something wrong occured while creating a csv-file!" << endl;
    return;
  }

  string columns = "Node 1(id), Node 2(id), Path type, Path, Delay (mks)\n";
  routes_input << columns;

  for (int s = 0; s < static_cast<int>(node_holder.size()); ++s) {
    if (node_controller != s) {
      vector<int> path;
      //--------main----------
      int t;
      for (t = s; t != node_controller && t != -1; t = p[t]) {
        path.push_back(t);
      }
      path.push_back(node_controller);
      reverse(path.begin(), path.end());

      if (t == -1) {
        // If there is no way from vertex node_controller to s
        routes_input << node_controller << ',' << s << ',' << "main" << ','
                     << "no" << '\n';
      } else {
        stringstream route;

        route << "\"[";
        for (size_t v = 0; v < path.size(); ++v) {
          route << path[v];
          if (v + 1 != path.size()) {
            route << ", ";
          }
        }
        route << "]\"";

        // Output the way and distance between node_controller and s
        routes_input << node_controller << ',' << s << ',' << "main" << ','
                     << route.str() << ',' << static_cast<int>(distances[s])
                     << '\n';
      }

      //---------reserve---------
      vector<vector<pair<int, double>>> new_channels;
      new_channels = reserve_channels(node_holder, topology,
                                      path);  // Delete broken vertices

      auto [_, parent, reserve_distances] =
          dijkstra(new_channels, node_controller);  // Find new paths
      path.clear();

      for (t = s; t != node_controller && t != -1; t = parent[t]) {
        path.push_back(t);
      }
      path.push_back(node_controller);
      reverse(path.begin(), path.end());

      if (t == -1 || path.size() <= 2) {
        // If there is no way from s to node_controller
        routes_input << node_controller << ',' << s << ',' << "reserve" << ','
                     << "no" << '\n';
      } else {
        stringstream route1;
        route1 << "\"[";
        for (size_t v = 0; v < path.size(); ++v) {
          route1 << path[v];
          if (v + 1 != path.size()) {
            route1 << ", ";
          }
        }
        route1 << "]\"";

        // Output the way from s to node_controller
        routes_input << node_controller << ',' << s << ',' << "reserve" << ','
                     << route1.str() << ','
                     << static_cast<int>(reserve_distances[s]) << '\n';
      }
    }
  }

  routes_input.close();
}

// Created for transforming default_olor_type into real
inline char const *color_to_string(default_color_type c) {
  switch (c) {
    case default_color_type::red_color:
      return "red";
    case default_color_type::green_color:
      return "green";
    case default_color_type::gray_color:
      return "gray";
    case default_color_type::white_color:
      return "white";
    case default_color_type::black_color:
      return "black";
  }
  return "";
}

// Draw a tree
// Red vertex is a node controller
// and green edges are included into spanning tree
void draw_graph(const string &filename, const vector<Node> &node_holder,
                const vector<vector<int>> &topology, const vector<int> &p,
                int node_controller) {
  typedef property<edge_name_t, std::string,
                   property<edge_color_t, default_color_type>>
      EdgeProperties;
  typedef property<vertex_name_t, std::string,
                   property<vertex_color_t, default_color_type>>
      VertexProperties;
  typedef adjacency_list<vecS, vecS, undirectedS, VertexProperties,
                         EdgeProperties>
      OutGraph;
  typedef graph_traits<OutGraph>::vertex_descriptor Vertex;
  typedef graph_traits<OutGraph>::edge_descriptor Edge;

  OutGraph g_out;
  // Create property maps
  property_map<OutGraph, vertex_name_t>::type vertex_label =
      get(vertex_name, g_out);
  property_map<OutGraph, vertex_color_t>::type color_map =
      get(vertex_color, g_out);
  property_map<OutGraph, edge_name_t>::type edge_label = get(edge_name, g_out);
  property_map<OutGraph, edge_color_t>::type color_edges =
      get(edge_color, g_out);

  set<pair<int, int>> edges;

  // Make a set of edges in the graph
  for (size_t v = 0; v < node_holder.size(); ++v) {
    if (v != static_cast<size_t>(node_controller)) {
      int u;
      for (u = static_cast<int>(v); u != node_controller && u != -1; u = p[u]) {
        pair<int, int> pair1 = {p[u], u}, pair2 = {u, p[u]};
        if (edges.find(pair1) == edges.end() &&
            edges.find(pair2) == edges.end()) {
          edges.insert(pair1);
        }
      }
    }
  }

  vector<Vertex> nodes(node_holder.size());

  // Create a vector to keep OutGraph's vertices
  for (size_t v = 0; v < node_holder.size(); ++v) {
    nodes[v] = add_vertex(g_out);
    put(color_map, nodes[v], boost::black_color);
    stringstream ss;
    ss << v;
    vertex_label[nodes[v]] = ss.str();
  }

  // Coloring node controller and edges in a spanning tree
  for (int v = 0; v < static_cast<int>(topology.size()); ++v) {
    Vertex v1 = nodes[v];  // Vertex for node v
    if (v == node_controller) {
      put(color_map, v1, boost::red_color);
    }
    for (auto u : topology[v]) {
      Vertex v2 = nodes[u];  // Vertex for node u
      Edge e =
          add_edge(v1, v2, g_out).first;  // Add edge between vertices v1 and v2
      pair<int, int> pair1 = {v, u}, pair2 = {u, v};
      if (edges.find(pair1) == edges.end() &&
          edges.find(pair2) == edges.end()) {
        // If edge is not in a spanning tree
        put(color_edges, e, boost::black_color);  // Color it black
      } else {
        // If it is in a spanning tree
        put(color_edges, e, boost::green_color);  // Color it green
      }
    }
  }

  dynamic_properties dp;
  dp.property("node_id", get(vertex_index, g_out));
  dp.property("label", vertex_label);
  dp.property("label", edge_label);
  dp.property("color",
              make_transform_value_property_map(&color_to_string, color_map));
  dp.property("color",
              make_transform_value_property_map(&color_to_string, color_edges));

  ofstream out_graph(filename);

  write_graphviz_dp(
      out_graph, g_out,
      dp);  // Write a graphml representation of a graph into file .dot

  out_graph.close();
}

int main(int argc, char *argv[]) {
  // Preparation in order to hold cmd input
  namespace po = boost::program_options;
  string graph_filename = "";
  int criterion = 0;
  po::options_description desc("Program usage");
  desc.add_options()("topology_filename,t",
                     po::value<string>(&graph_filename)->required(),
                     "topology filename")(
      "criterion_number,k", po::value<int>(&criterion)->required(),
      "criterion number");
  po::variables_map vm;
  po::store(po::parse_command_line(argc, argv, desc), vm);
  try {
    po::notify(vm);
  } catch (po::required_option) {
    cout << desc << endl;
    return 1;
  }

  if (criterion != 1 && criterion != 2) {
    cerr << "Bad criterion was given!" << endl;
    return 1;
  }

  // Read a graph
  Graph g = ReadGraph(graph_filename);

  // Get a node_holder for our purposes
  vector<Node> node_holder = get_node_holder(g);

  // Get a topology for our needs as well
  vector<vector<int>> topology = get_topology(node_holder, g);

  // Calculate delays and store them into channels
  vector<vector<pair<int, double>>> channels;
  channels = calculate_delays(node_holder, topology);

  // Make a first csv representing topology
  string filename = graph_filename + "_topo.csv";
  first_csv(filename, node_holder, channels);

  // Make a second csv representing a tree with controller node.
  // And then draw a graph of tree
  string routes_name = graph_filename + "_routes.csv";
  string tree_name = graph_filename + "_tree.dot";
  if (criterion == 1) {
    // If first criterion is chosen
    auto [controller_node, p, distances] = first_criterion(channels);
    second_csv(routes_name, controller_node, p, distances, node_holder,
               topology, channels);
    draw_graph(tree_name, node_holder, topology, p, controller_node);
  } else {
    // If second criterion is chosen
    auto [controller_node, p, distances] = second_criterion(channels);
    second_csv(routes_name, controller_node, p, distances, node_holder,
               topology, channels);
    draw_graph(tree_name, node_holder, topology, p, controller_node);
  }

  return 0;
}
