/** 
* The 'sequential salesman' traverses all the points in the order they are given
* in the graph. Not efficient, but easy to implement. 
*/
function SequentialSalesman() {
  
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

    // Init
    this.init_graph(graph);    
    var self = this;
    var start_point = this.get_point(start_point_id);
    var last_point = this.get_point(start_point_id)
    var complete_path = [last_point];
    
    
    // Just sequentially visit each point
    _(graph.points).each(function(point) { 
      path = self.get_path_to_point(last_point, point);
      complete_path = complete_path.concat(path)
      last_point = point;
    });
    
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
      if (a[i] != a[i-1]) final_ary.push(a[i]);
    }
    
    // Done 
    return final_ary;
    
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