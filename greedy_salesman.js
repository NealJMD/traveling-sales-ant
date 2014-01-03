/***
* Our baseline implementation of the TSP. As the name implies, we greedily select
* nodes to visit.  There are far more efficient ways to win the TSP. Remember, the
* scoring algorithm is based on total distance travelled. 
**/
function GreedySalesman() {
  
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
    
    this.points_by_id = {}
    this.connected_points_by_id = {}
    this.graph = graph;
    self = this;
    
    _(graph.points).each(function(p) {
      self.points_by_id[p.id] = p;
      self.connected_points_by_id[p.id] = []
    });
    
    _(graph.arcs).each(function(a) {
      self.connected_points_by_id[a[0]].push( self.get_point(a[1]) )
      self.connected_points_by_id[a[1]].push( self.get_point(a[0]) )
    });
    
  }
  
  
  this.compute_plan = function(graph, start_point_id) {
    
    this.visited = {}
    this.visited[start_point_id] = true;
    this.init_graph(graph);
    
    var self = this;
    var start_point = this.get_point(start_point_id);
    var last_point = start_point;
    var closest_point;
    var complete_path = [start_point]
    
    // Greedily find the closest points...
    while(closest_point = this.get_closest_unvisited_point(last_point)) {
      path = this.get_path_to_point(last_point, closest_point);
      _(path).each(function(pt) {
        self.visited[pt.id] = true
      })
      last_point = closest_point;
      complete_path = complete_path.concat(path)
    }
    
    // Go back to the start
    path = this.get_path_to_point(last_point, start_point);
    complete_path = complete_path.concat(path)
    
    // We need make sure we just return the IDs 
    a = _(complete_path).map(function(p) {
      return p.id
    });
    
    // Remove any sequential identicals..
    final_ary = [a[0]]
    for(i=1;i<a.length;i++) {
      if (a[i] != a[i-1]) {
        final_ary.push(a[i]);
      }
    }
    return final_ary;
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
    
    // We're going to BFS for the end_point.  It's not gauranteed to be the shortest path. 
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