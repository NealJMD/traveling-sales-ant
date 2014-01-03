/***
* Handles rendering the graph and showing the TSP animation
**/
function Renderer(container, graph) { 
  
  // Some constants
  MARGIN = 2; 
  WINWIDTH = $(window).width(); 
  WIDTH = (WINWIDTH - 2 * MARGIN), 
  WINHEIGHT = $(window).height()
  HEIGHT = (WINHEIGHT - 2 * MARGIN), 
  COLOR_1 = "#a8ff9a",
  COLOR_2 = "#ff4242",
  COLOR_START = "#3cb79c",
  ZILLA = "M-5.085,7.617c0,0,0.93-2.283,1.606-3.213c0,0-1.634-2.001-1.606-3.945c0.028-1.945,0.62-4.988,1.353-5.891  C-3-6.334-0.801-8.476,2.102-8.279c2.903,0.198,3.861,1.522,3.974,1.635c0.113,0.112-0.553,0.366-0.563,2.025  c0,0-0.983,0.021-1.079,0.158c0,0-0.74-1.986-2.642-1.976c0,0-1.159-0.185-1.934,0.94c-0.561,0.813-0.613,1.627-0.561,2.061  c0,0-3.371,0.856-3.572,1.564s0.243,1.3,0.243,1.3s-0.666-0.634-0.084-1.374c0.582-0.74,3.403-1.353,3.467-1.374  c0,0,0.401,1.427,1.585,1.712c1.184,0.285,2.758,0.338,3.16-0.951c0.402-1.29,0.359-1.839,0.359-1.839l1.131-0.127  c0,0,0.127,0.919,0.296,1.025c0,0-0.275,0.296-0.306,0.433c0,0,1.722-1.141,3.403-1.067c0,0,0.222-1.829-0.74-2.378  c0,0-0.624-1.194-2.072-0.169c0,0-0.792,0.898-0.539,1.828c0,0,0.032,1.353,0.423,1.395c0,0,2.674-0.729,3.794-0.719  c1.12,0.011,2.822,0.053,3.34,1.596c0,0,0.655,0.782,0.423,2.029c-0.233,1.247-1.839,2.938-8.223,5.08l1.527-0.536  c0,0,0.827,4.754,0.893,5.309C7.807,9.326,7.809,9.342,7.809,9.35c0,0-0.55,1.24-2.48,2.296c0,0-4.833,0.254-6.017-0.479  C-1.873,10.435-5.113,9.364-5.085,7.617z"; 
  X_GRID_LINES = 20;
  Y_GRID_LINES = 20;
  
  NODE_RADIUS = 10
  INITIAL_ANIM_DURATION = 2000
  NODE_DELAY = 700


  /**
  * Initializes the D3 object, etc
  **/
  this.initialize = function() {
    
    this.svg = d3.select( container || "#graph" ) 
      .append( "svg:svg" )
        .attr( "width", WIDTH + (2 * MARGIN) )
        .attr( "height", HEIGHT + (2 * MARGIN) )
      .append( "g" ) 
        .attr( "transform", "translate(" + MARGIN + "," + MARGIN + ")" );

    x = d3.scale.linear()
      .domain( [0, 100] )
      .range( [0, WIDTH] );

    y = d3.scale.linear()
      .domain( [100, 0] )
      .range( [0, HEIGHT ] ); 

    xrule = this.svg.selectAll( "g.x" )
      .data( x.ticks( X_GRID_LINES ) )
      .enter().append( "g" ) 
      .attr( "class", "x" ); 

    xrule.append( "line" ) 
      .attr( "x1", x )
      .attr( "y1", 0 ) 
      .attr( "x2", x ) 
      .attr( "y2", HEIGHT ); 

    yrule = this.svg.selectAll( "g.y" )
      .data( x.ticks( Y_GRID_LINES ) )
      .enter().append( "g" )
      .attr( "class", "y" );

    yrule.append( "line" )
      .attr( "x1", 0) 
      .attr( "y1", y ) 
      .attr( "x2", WIDTH ) 
      .attr( "y2", y );
    
  }


  /**
  * Sets and Renders the graph
  **/
  this.set_graph = function(graph) {
    this.graph = graph;
    this.create_arcs(); 
    this.create_nodes(); 
  }

  
  /**
  * Starts executing a plan
  **/
  this.start_plan = function(plan, player_id) {
    this.animate(plan, player_id);
  }


  /**
  * Renders arcs in D3
  **/
  this.create_arcs = function() { 
    s = this
    line = this.svg.selectAll( "line.arcs" ) 
      .data( this.graph.arcs )
      .enter()
      .append( "line" ) 
      .attr( "class", "arcs" )
      
      // The initial positions:
      .attr( "x1", function(d){ return WIDTH/2 })
      .attr( "x2", function(d){ return WIDTH/2 })
      .attr( "y1", function(d){ return HEIGHT/2 })
      .attr( "y2", function(d){ return HEIGHT/2 })
      
      // The actual positions:
      .transition()
      .duration( INITIAL_ANIM_DURATION ) 
      .attr( "x1", function(d){ 
        var one_point = s.find_single_point( d[0] );
        var x1 = one_point.x; 
        return x(x1);
      })

      .attr( "y1", function(d){ 
        var one_point = s.find_single_point( d[0] );
        var y1 = one_point.y; 
        return y(y1); 
      })

      .attr( "x2", function(d){ 
        var one_point = s.find_single_point( d[1] ); 
        var x2 = one_point.x;
        return x(x2); 
      })

      .attr( "y2", function(d){ 
        var one_point = s.find_single_point( d[1] );
        var y2 = one_point.y; 
        return y(y2); 
      }); 

  }


  /**
  * Finds a given point
  **/
  this.find_single_point = function( d  ) { 
    for( i=0;i<this.graph.points.length;i++ ) { 
      if (this.graph.points[i].id === d) { return this.graph.points[i] } 
    }
  }


  /**
  * Renders the nodes in D3
  **/
  this.create_nodes = function() { 

    node = this.svg.selectAll("circle.node") 
      .data( this.graph.points, function(d){ return d.id }); 
    
    node
      .enter()
      .append( "svg:circle" )
      .attr( "class", "node" )
      .attr( "id", function( d, i ) { 
        return d.id; 
      })
      
      // The initial positions:
      .attr( "cx", function(d){ return WIDTH/2 })
      .attr( "cy", function(d){ return HEIGHT/2 })
      .attr( "r", function(d){ return 0 })
      
      // The actual positions
      .transition()
      .duration( INITIAL_ANIM_DURATION )
      .attr( "r", NODE_RADIUS )
      .attr( "cx", function( d, i ) { 
        return x( d.x );
      })
      .attr( "cy", function( d, i ) { 
        return y( d.y ); 
      })
      .style( "fill", COLOR_1);

    return node;
  }

  
  
 
  /**
  * Kicks off an animation of a given plan.  We can color the 'bob' by supplying
  * an extra CSS class 
  **/
  this.animate = function(plan, player_id) { 

    var player_id = player_id || "bob";
    var self = this;
    var i = 0;
    var bob = create_bobzilla(); 
    var animate_bob = _(plan).map(function(pt) {
      p = self.find_single_point(pt);
      return [x(p.x), y(p.y), p.id]
    });
    var visited_points = {}

    function create_bobzilla() {   
      var bob = self.svg.selectAll( "#" + player_id ) 
        .data( [1] ) // create one bobzilla
        .enter()
        .append( "path" ) 
          .attr( "id", player_id )
          .attr( "class", "st0" )
          .attr( "d", ZILLA );

      return bob; 
    }

    function animate_first_step( animation, target, i, player_id) { 
      var l = animation.length; 
      var current_point = animation[i][2]; 
      d3.select("#" + current_point)
        .transition()
        .style("fill", COLOR_START); 

      target
        .transition()
        .attr(  "transform", "translate(" + animation[i][0] + "," + animation[i][1] + ")" ) 
        .each( "end", function() { 
          visited_points[current_point] = true
          return animate_second_step( animation, i, target, l, player_id ); 
        }); 
    }
    
    function highlight_next_unvisited_point(animation, i, player_id) {
      for(j=i; j<animation.length; j++) {
        current_point = animation[j][2];
        if (visited_points[current_point]) continue;  // we've visited this point
        //$('#'+visited_points[animation[j].id]).addClass("node_selected")
        // we haven't visted... highlight
        d3.select("#" + current_point).classed("node_selected", true)
        return;
      }
    }
    
    function highlight_this_point(animation, i, player_id) {
      current_point = animation[i][2];
      d3.select("#" + current_point).classed("node_visited_"+player_id, true)
    }

    function animate_second_step( animation, i, target, l, player_id ) { 
      
      highlight_next_unvisited_point(animation, i, player_id);
      
      if ( i < l ) { 

        var current_point = animation[i][2]; 

        target        
          .transition()
          .delay(NODE_DELAY)
          .duration(500)
          .ease( "linear" )
          .attr( "transform", "translate(" + animation[i][0] + "," + animation[i][1] + ")" )
          .each( "end", function() { 
            window.setTimeout(function() {
              highlight_this_point(animation, i, player_id);
              i++;
              visited_points[current_point] = true
              animate_second_step( animation, i, target, l, player_id );       
            }, 0)
            
          });

      } else { 
        target
          .transition()
          .delay(NODE_DELAY)
          .duration(500)
          .ease( "linear" )
            .attr( "transform", "scale( 50, 50 )"  ) 
            .attr( "opacity", "0.8")
            .remove(); 
        }
      }
      
    animate_first_step( animate_bob, bob, i, player_id ); 
  }



  // Initialize
  this.initialize();
  if (graph) this.set_graph(graph);
}

