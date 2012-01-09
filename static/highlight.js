function highlight(argName) {
  // First, remove all highlighting since we are about to highlight something else
  $('.highlight').removeClass('highlight');
  // Now just highlight what we find in the code section
  $('code').highlight(argName, false, 'highlight');
}

function linkCalledFunctions(fnames) {
  $.map(fnames, function (fname, ix) { $('code').makeFunctionLink(fname); });
}

function initializeHighlighting() {
  var linkFunc = function(fname) {
    var regex = new RegExp('(<[^>]*>)|(\\b'+ fname.replace(/([-.*+?^${}()|[\]\/\\])/g,"\\$1") +')', 'g');
    return this.html(this.html().replace(regex, function(a, b, c){
      var url = fname + ".html";
      return (a.charAt(0) == '<') ? a : '<a href="'+ url +'">' + c + '</a>';
    }));
  };

  var highlightFunc = function(search, insensitive, klass) {
    var regex = new RegExp('(<[^>]*>)|(\\b'+ search.replace(/([-.*+?^${}()|[\]\/\\])/g,"\\$1") +')', insensitive ? 'ig' : 'g');
    return this.html(this.html().replace(regex, function(a, b, c){
      return (a.charAt(0) == '<') ? a : '<strong class="'+ klass +'">' + c + '</strong>';
    }));
	};

  jQuery.fn.extend({ makeFunctionLink: linkFunc, highlight: highlightFunc });
}