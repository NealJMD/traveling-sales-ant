/****************************************
* this is an implementation of the ant colony system TSP algorithm described 
*  in this paper http://www.idsia.ch/~luca/acs-bio97.pdf from 1996 by Marco Dorigo
*  and Luca Gambardella. It does not run within the specified time limit but has the 
*  same order of growth as the greedy algorithm.
*****************************************/
function AntSalesman() {
  
  this.get_point = function(point_id) {
    return this.points_by_id[point_id]
  }
  
  this.get_surrounding_points = function(point_id) {
    return _.clone(this.connected_points_by_id[point_id])
  }
  
  
  this.get_dist = function(point1, point2) {
    return Math.sqrt(Math.pow(point2.x - point1.x, 2) + Math.pow(point2.y - point1.y, 2));
  }
  
  
  this.init_graph = function(graph) {
    
    // The graph, as given, isn't very friendly for processing. Let's extract
    // points and arcs so we can do super-fast look ups
    
    this.points_by_id = {};
    this.connected_points_by_id = {};
    this.pheromone = {};
    this.graph = graph;
    self = this;
    self.node_count = 0;
 
    _(graph.points).each(function(p) {
      self.points_by_id[p.id] = p;
      self.connected_points_by_id[p.id] = []
      self.node_count++;
    });
    
    _(graph.arcs).each(function(a) {
      self.connected_points_by_id[a[0]].push( self.get_point(a[1]) );
      self.connected_points_by_id[a[1]].push( self.get_point(a[0]) );
      if(self.pheromone[a[0]] == null){ self.pheromone[a[0]] = {} };
      if(self.pheromone[a[1]] == null){ self.pheromone[a[1]] = {} };
      self.pheromone[a[0]][a[1]] = 1;
      self.pheromone[a[1]][a[0]] = 1;
    });
    
  }
  
  
  this.compute_plan = function(graph, start_point_id) {
    
    // My implementation

    this.visited = {}
    this.visited[start_point_id] = true;
    this.init_graph(graph);
    
    // constant parameters
    var ANT_COUNT = 15;         // number of ants
    var WALK_COUNT = 5;        // number of trials
    var EVAP_RATE = 0.85;       // each time an ant takes a path, lift a bit of pheromone
                                // so that path doesn't dominate entirely
    var DETERMINISM = 0.2;      // rate to choose the best path instead of a random path 
    var BETA = 3;               // weighting exponent between importance of closeness v. pheromone
    var PHEROMONE_SCALAR = 4;   // proportionality constant between inverse of path length and 
                                // base pheromone level of 1

    var self = this;
    var start_point = this.get_point(start_point_id);
    // var complete_path = [start_point];
    var champ_path_length = Number.POSITIVE_INFINITY;
    var closest_point, champ_path;

    function pick_starting_point() {
        // unless its the last round, start at a random point
        var random_id = "pt_"+Math.floor(Math.random() * self.node_count);
        var current_point = self.points_by_id[random_id];
        return current_point
    }

    function get_available_surrounding(current_point) {
        // compile an array of all unvisited points surrounding current_point
        available = [];
        _(self.get_surrounding_points(current_point.id)).each(function(p) {
          if (!self.visited[p.id]){
            available.push(p);
          } 
        });
        return available;
    }

    // pick the best path as determined by the distance and pheromone
    // see the paper linked above for details. takes the point to move from and the list of surrounding
    // available points. returns an object with 
    //    point: best possible point
    //    dist: distance to that point
    function pick_next_point_deterministically(current_point, available) {
      var champ_point = null;
      var champ_strength = -1;
      var champ_dist;

      _(available).each(function(p){
        var strength = Math.pow(self.get_dist(current_point, p), -1 * BETA) * self.pheromone[current_point.id][p.id];
        if (strength > champ_strength || champ_point == null) {
          champ_strength = strength;
          champ_point = p;
          champ_dist = self.get_dist(current_point, champ_point);
        }
      });

      return {point: champ_point, dist: champ_dist};

    }

    // pick a path at random from those available. Likelihood of being chosen is propotional
    // to the path strength, calculated from the proximity and strength of pheromone signal
    // returns an object with 
    //    point: best possible point
    //    dist: distance to that point
    function pick_next_point_probabilistically (current_point, available) {
      var sum = 0;
      var probs = {};
      var pids = {};
      var random = Math.random();
      var distribution_counter = 0;

      // calculate strengths
      _(available).each(function(p, i){
        var strength = Math.pow(self.get_dist(current_point, p), -1 * BETA) * self.pheromone[current_point.id][p.id];
        sum += strength;
        probs[i] = strength;
        pids[i] = p.id
      });

      // normalize probabilities
      probs = _(probs).map(function(p){
        return p / sum
      });

      // pick one from the distribution
      _(probs).each(function(pr, i){
        distribution_counter += pr;
        if (random < distribution_counter) {
          champ_point = self.get_point(pids[i]);
          champ_dist = self.get_dist(current_point, champ_point);
        }
      });

      return {point: champ_point, dist: champ_dist};      
    }

    // walk one ant all the way through the graph from starting_point
    // returns an object with properties
    //    complete_path: an array of point objects
    //    dist: numerical lenght of the path.
    function walk_entire_graph(starting_point) {
      var unvisited_count = self.node_count;
      var current_point = starting_point;
      var complete_path = [];
      
      // for each ant, reset variables 
      var path_length = 0;
      _(self.visited).each(function(b, i){ self.visited[i] = false; });

      // walk through the entire graph
      while(unvisited_count > 0){
        
        // reset vars for each step
        var available = get_available_surrounding(current_point);
        var trapped = (available.length < 1);
        var champ_point = null;
        var champ_strength = -1;
        var path, champ_dist;

        // if all surrounding points have been visited then use the greedy algo
        if(trapped){
          closest_point = self.get_closest_unvisited_point(current_point);
          // if ALL points have been visited, wrap it up with this ant
          if(closest_point == null) {
            path = self.get_path_to_point(current_point, start_point);
            complete_path = complete_path.concat(path);
            current_point = start_point;
            break;
          } else { // otherwise just use greedy
            path = self.get_path_to_point(current_point, closest_point);
            _(path).each(function(pt) {
              self.visited[pt.id] = true
            });
            current_point = closest_point;
            complete_path = complete_path.concat(path);
            unvisited_count--;
            continue;
          }
        }

        // randomly choose whether to take the best path or a weighted random path
        if(Math.random() < DETERMINISM){
          champ = pick_next_point_deterministically(current_point, available);
        } else {
          champ = pick_next_point_probabilistically(current_point, available);
        }

        // add new point to path and do bookkeeping
        path = self.get_path_to_point(current_point, champ.point);
        _(path).each(function(p) {
          self.visited[p.id] = true
        });
        complete_path = complete_path.concat(path);

        // we only learn from the best ant each round, so if it's already worse than
        // the best, squash this ant
        path_length += champ.dist;
        if (path_length > champ_path_length) { break; } 

        // take a little pheromone off this path so that other paths have a chance to be followed
        self.pheromone[current_point.id][champ.point.id] *= EVAP_RATE;
        self.pheromone[champ.point.id][current_point.id] *= EVAP_RATE;

        current_point = champ.point;
        unvisited_count--;
      }
      return {complete_path:complete_path, dist:path_length};
    }


    function walk_all_ants () {
      var champ_ant_path_length = Number.POSITIVE_INFINITY;
      var current_point, champ_path;      

      for(var ant = 0; ant < ANT_COUNT; ant++){

        first_point = pick_starting_point();
        walked = walk_entire_graph(first_point);
        last_point = walked.complete_path[walked.complete_path.length-1];

        // Go back to the start
        if(last_point != first_point){
          path = self.get_path_to_point(last_point, first_point);
          walked.complete_path = walked.complete_path.concat(path);
          walked.dist += self.get_dist(last_point, first_point);
        }

        // keep track of the best path found by an ant so far
        if(walked.dist < champ_ant_path_length) {
          champ_ant_path_length = walked.dist;
          champ_path = walked.complete_path;
        }
      }

      // lay down pheromone on shortest path
      var last_point = null;
      var pheromone_strength = Math.pow(champ_ant_path_length, -1) * PHEROMONE_SCALAR;
      _(walked.complete_path).each(function(p) {
        if(last_point != null){
          self.pheromone[last_point.id][p.id] += pheromone_strength;
          self.pheromone[p.id][last_point.id] += pheromone_strength;
        }
        last_point = p;
      });
      return {complete_path: champ_path, dist: champ_ant_path_length};
    }

    // Remove any sequential identicals from array a, return the deduped array.
    function sequential_dedupe (a) {
      final_ary = [a[0]]
      for(i=1;i<a.length;i++) {
        if (a[i] != a[i-1]) {
          final_ary.push(a[i]);
        }
      }
      return final_ary;
    }

    // find the shortest path through TSP using ant search algorithm
    function run_ant_search () {

      // we simulate a series of rounds, each round allowing a number of ants to walk through the 
      // graph loosely guided by pheromone signals. 
      for(var walk = 0; walk < WALK_COUNT; walk++){
        best = walk_all_ants(walk);
        if (best.dist < champ_path_length){
          champ_path = best.complete_path;
          champ_path_length = best.dist;
        }
      }
      
      // We need make sure we just return the IDs 
      formatted = _(champ_path).map(function(p) {
        return p.id
      });

      return sequential_dedupe(formatted);
    }

    return run_ant_search();
  }
  

  
  
  
  this.get_closest_unvisited_point = function(start_point) {
    
    // Init 
    var self = this;
    var closest_dist = 9999999;
    var closest_point = null;
    var processed = {}
    var queue = this.get_surrounding_points(start_point.id);
    var max_checks = 10;
    var checks = 0; 

    // Breadth first search
    while(queue.length > 0) {
      var point = queue.shift();
      if (processed[point.id]) continue;
      if (!self.visited[point.id]) {
        var this_dist = self.get_dist(start_point, point);
        if (this_dist < closest_dist) {
          closest_dist = this_dist;
          closest_point = point;
          if (checks > max_checks) break;
          checks += 1;
        }
      }
      processed[point.id] = true;
      _(this.get_surrounding_points(point.id)).each(function(p) {
        if (!processed[p.id]) queue.push(p);
      })
    }
    
    return closest_point; 
  }
  
  
  
  
  this.get_path_to_point = function(start_point, end_point) {
    
    // Breadth First Search. 
    // The 'visit_queue' consists of the current point, and a 'breadcrumb' path back to the start point.
    visit_queue = [[start_point, [start_point], 0]]
    visited = {}
    max_hits = 5;
    hits = 0;
    closest_path = null;
    closest_dist = 10000000;
    
    // We're going to BFS for the end_point.  It's not guaranteed to be the shortest path. 
    // Is there a better way that is computationally fast enough?
    while(visit_queue.length > 0) {
      
      a = visit_queue.shift();
      this_point = a[0];
      this_path = a[1];
      this_dist = a[2];
      visited[this_point.id] = true
      
      if (this_point.id == end_point.id) {
        
        // We've arrived, return the breadcrumb path that took us here...
        if (this_dist < closest_dist) {
          closest_dist = this_dist
          closest_path = this_path
        }
        hits += 1;
        if (hits > max_hits) {
          break;
        }
        
      } else {
        
        // Otherwise, explore all the surrounding points...
        new_points = self.get_surrounding_points(this_point.id)
        _(new_points).each(function(p) {
          if (!visited[p.id]) {
            dist = self.get_dist(this_point, p)
            visit_queue.push([p, this_path.concat(p), this_dist + dist])
          }
        }); 
      }  
    }
    
    // Otherwise, a path doesn't exist
    if (closest_path == null)
      throw "Could not compute path from start_point to end_point! " + start_point.id + " -> " + end_point.id;
    return closest_path;
  }
  
  

  
  
  
}