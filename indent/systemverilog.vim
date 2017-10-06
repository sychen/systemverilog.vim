" Language:     SystemVerilog
" Maintainer:   Sung-Yu Chen <eesonyu@gmail.com>
" Last Change:  January 6th, 2016

if exists("b:did_indent")
  finish
else
  let b:did_indent = 1
endif

setlocal indentexpr=GetSystemVerilogIndent()

setlocal indentkeys=!^F,o,O,0),0}
setlocal indentkeys+==begin,=end,=join,=endcase,=join_any,=join_none
setlocal indentkeys+==endmodule,=endfunction,=endtask,=endspecify
setlocal indentkeys+==endclass,=endpackage,=endsequence,=endclocking
setlocal indentkeys+==endinterface,=endgroup,=endprogram,=endproperty,=endchecker
setlocal indentkeys+==endgenerate
setlocal indentkeys+==`else,=`endif

if exists("*GetSystemVerilogIndent")
  finish
endif

let s:cpo_cache = &cpo
set cpo&vim  " Reset cpo to Vim default

function GetSystemVerilogIndent()

  if exists('b:systemverilog_indent_width')
    let offset = b:systemverilog_indent_width
  else
    let offset = &sw  " shiftwidth
  endif

  let old_line_number = prevnonblank(v:lnum - 1)
  if old_line_number == 0
      return 0
  endif

  " Prepare variables
  let older_line_number = prevnonblank(old_line_number - 1)

  let this_line = getline(v:lnum)
  let old_line = getline(old_line_number)
  let older_line = getline(older_line_number)

  let old_indent = indent(old_line_number)
  let older_indent = indent(older_line_number)
  let real_old_indent = old_indent

  let offset_comment = 1

  let re_comment ='\(//.*\|/\*.*\*/\s*\)'


  " Extract the indent level of the last line
  if old_line =~ '\*/\s*$' && old_line !~ '/\*.\{-}\*/'
    let real_old_indent = old_indent - offset_comment

  " Indent after if/else/for/case/always/initial/specify/fork blocks
  elseif
    \ old_line =~ '`\@<!\<\(if\|else\)\>' ||
    \ old_line =~ '^\s*\<\(for\|case\%[[zx]]\|do\|foreach\|randcase\)\>' ||
    \ old_line =~ '^\s*\<\(always\|always_comb\|always_ff\|always_latch\)\>' ||
    \ old_line =~ '^\s*\<\(initial\|specify\|fork\|final\)\>'
    if old_line !~ '\(;\|\<end\>\)\s*' . re_comment . '*$' ||
      \ old_line =~ '\(//\|/\*\).*\(;\|\<end\>\)\s*' . re_comment . '*$'
      let real_old_indent = old_indent + offset
    endif

endfunction

let &cpo = s:cpo_cache
unlet s:cpo_cache

