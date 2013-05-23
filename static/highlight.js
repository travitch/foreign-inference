// function highlight(argName) {
//   // First, remove all highlighting since we are about to highlight something else
//   $('.highlight').removeClass('highlight');
//   $('.witness-reason').remove();

//   // Now just highlight what we find in the code section
//   $('code').highlight(argName, false, 'highlight');
// }

function highlightLines(startLine, witnessLines) {
  if(witnessLines.length == 0) return;

  // Clear old witnesses
  $('.witness-reason').remove();

  // Find the code listing and append a witness to each
  // line (wrapped helpfully in a <li></li>)
  var codeChildren = $("pre ol.codelist").children();
  for(var i = 0; i < witnessLines.length; ++ i) {
    var lineNo = witnessLines[i][0] - startLine;
    var lineItem = codeChildren[lineNo];
    var witness = '<span class="witness-reason code-comment"> /* ' +
    witnessLines[i][1] + ' */</span>';
      $(lineItem).append(witness);
  }
}

function linkCalledFunctions(fnames) {
   $.map(fnames, function (fname, ix) { $('body').makeFunctionLink(fname[0], fname[1]); });
}

function initializeHighlighting() {
  var linkFunc = function(txtName, fname) {
    var target = txtName.replace(/([-.*+?^${}()|[\]\/\\])/g, "\\$1");
    var regex = new RegExp('(<[^>]*>)|(\\b'+ target +'\\b)', 'g');
    return this.html(this.html().replace(regex, function(a, b, c){
      var url = fname + ".html";
      return (a.charAt(0) == '<') ? a : '<a href="'+ url +'">' + c + '</a>';
    }));
  };

  // var highlightFunc = function(search, insensitive, klass) {
  //   var regex = new RegExp('(<[^>]*>)|(\\b'+ search.replace(/([-.*+?^${}()|[\]\/\\])/g,"\\$1") +')', insensitive ? 'ig' : 'g');
  //   return this.html(this.html().replace(regex, function(a, b, c){
  //     return (a.charAt(0) == '<') ? a : '<strong class="'+ klass +'">' + c + '</strong>';
  //   }));
	// };

  jQuery.fn.extend({ makeFunctionLink: linkFunc });
}
