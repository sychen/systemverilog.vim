" Vim Syntax File for SystemVerilog
" Language:     SystemVerilog
" Maintainer:   Sung-Yu Chen <sychen@realtek.com>
" Last Update:  Fri Jul 13 18:06:48 CST 2012
" Requires:     Vim 7.0 or later

" Quit when a syntax file was already loaded
" TODO: this is added for Vim 6.x, is this still needed?
if exists("b:current_syntax")
    finish
endif

" TODO: any modification?
setlocal iskeyword=@,48-57,_,192-255

syn match       systemverilogOperator           "[&|~><!)(*#%@+/=?:;}{,.\^\-\[\]]"
syn keyword     systemverilogOperator           begin end
syn region      systemverilogComment            start="/\*" end="\*/"
syn match       systemverilogComment            "//.*$"

syn match       systemverilogString             "\"[^\"]*\""

syn match       systemverilogPreCondition       "^\s*`\(ifdef\|ifndef\|else\|elsif\|endif\)\>"
syn match       systemverilogDefine             "^\s*`\(define\)\>"
syn match       systemverilogDefine             "^\s*`\(include\)\>"

"syn match       systemverilogConstant           "`\?\<[A-Z][A-Z0-9_]\+\>"
syn match       systemverilogConstant           "`\?\<[A-Z][A-Z0-9_]*\>"

syn keyword     systemverilogStatement          class endclass
syn keyword     systemverilogStatement          function endfunction
syn keyword     systemverilogStatement          task endtask
syn keyword     systemverilogStatement          package endpackage
syn keyword     systemverilogStatement          module endmodule
syn keyword     systemverilogStatement          interface endinterface
syn keyword     systemverilogStatement          property endproperty
syn keyword     systemverilogStatement          case endcase default
syn keyword     systemverilogStatement          import
syn keyword     systemverilogStatement          new
syn keyword     systemverilogStatement          parameter
syn keyword     systemverilogStatement          force
syn keyword     systemverilogStatement          assign
syn keyword     systemverilogStatement          repeat
syn keyword     systemverilogStatement          posedge assert

syn keyword     systemverilogConditional        if else while foreach for do
syn keyword     systemverilogConditional        fork join disable join_any join_none wait
syn keyword     systemverilogStatement          initial forever

" OOP keywords
syn keyword     systemverilogStatement          virtual extends public local protected pure
syn keyword     systemverilogStatement          extern static unsigned ref inout input output const
syn keyword     systemverilogStatement          return
syn keyword     systemverilogIdentifier         super this
syn keyword     systemverilogStorageClass       rand

syn keyword     systemverilogTypeStatement      void
syn keyword     systemverilogTypeStatement      automatic
syn keyword     systemverilogTypeStatement      int integer
syn keyword     systemverilogTypeStatement      string
syn keyword     systemverilogTypeStatement      logic bit byte
syn keyword     systemverilogTypeStatement      event time
syn keyword     systemverilogTypeStatement      process
syn match       systemverilogFunction           "\(process::\)\@<=self"
syn keyword     systemverilogTypeStatement      reg
syn keyword     systemverilogStatement          type
syn keyword     systemverilogStatement          enum

syn keyword     systemverilogTypeDefStatement   typedef

" 6.16 String Data Type

syn match       systemverilogFunction           "\(\.\)\@<=\(len\|puts\|getc\)"
syn match       systemverilogFunction           "\(\.\)\@<=\(toupper\|tolower\)"
syn match       systemverilogFunction           "\(\.\)\@<=\(compare\|icompare\|substr\)"
syn match       systemverilogFunction           "\(\.\)\@<=\(atoi\|atohex\|atooct\|atobin\|atoreal\)"
syn match       systemverilogFunction           "\(\.\)\@<=\(itoa\|hextoa\|octtoa\|bintoa\|realtoa\)"

" 6.19 Enumeration

syn match       systemverilogFunction           "\(\.\)\@<=\(first\|last\|next\|prev\|num\|name\)"

" 7 Aggregation Data Types

syn match       systemverilogFunction           "\(\.\)\@<=\(size\|delete\|exists\|insert\)"
syn match       systemverilogFunction           "\(\.\)\@<=\(pop\|push\)_\(front\|back\)"
syn match       systemverilogFunction           "\(\.\)\@<=find\(_first\|_last\)\?\(_index\)\?\>"

syn match  systemverilogFunction       "\.index\>"
syn match  systemverilogFunction       "\.min\>"
syn match  systemverilogFunction       "\.max\>"
syn match  systemverilogFunction       "\.unique\>"
syn match  systemverilogFunction       "\.unique_index\>"
syn match  systemverilogFunction       "\.sort\>"
syn match  systemverilogFunction       "\.rsort\>"
syn match  systemverilogFunction       "\.shuffle\>"
syn match  systemverilogFunction       "\.reverse\>"
syn match  systemverilogFunction       "\.sum\>"
syn match  systemverilogFunction       "\.product\>"
syn match  systemverilogFunction       "\.xor\>"
syn match  systemverilogFunction       "\.status\>"
syn match  systemverilogFunction       "\.kill\>"
syn match  systemverilogFunction       "\.self\>"
syn match  systemverilogFunction       "\.await\>"
syn match  systemverilogFunction       "\.suspend\>"
syn match  systemverilogFunction       "\.resume\>"
syn match  systemverilogFunction       "\.get\>"
syn match  systemverilogFunction       "\.put\>"
syn match  systemverilogFunction       "\.peek\>"
syn match  systemverilogFunction       "\.try_get\>"
syn match  systemverilogFunction       "\.try_peek\>"
syn match  systemverilogFunction       "\.try_put\>"
syn match  systemverilogFunction       "\.data\>"
syn match  systemverilogFunction       "\.eq\>"
syn match  systemverilogFunction       "\.neq\>"
syn match  systemverilogFunction       "\.new\>"
syn match  systemverilogFunction       "\.empty\>"
syn match  systemverilogFunction       "\.front\>"
syn match  systemverilogFunction       "\.back\>"
syn match  systemverilogFunction       "\.insert\>"
syn match  systemverilogFunction       "\.insert_range\>"
syn match  systemverilogFunction       "\.erase\>"
syn match  systemverilogFunction       "\.erase_range\>"
syn match  systemverilogFunction       "\.set\>"
syn match  systemverilogFunction       "\.swap\>"
syn match  systemverilogFunction       "\.clear\>"
syn match  systemverilogFunction       "\.purge\>"
syn match  systemverilogFunction       "\.start\>"
syn match  systemverilogFunction       "\.finish\>"

syn match       systemverilogClass              "vmm_[a-z_]\+\>"

syn keyword     systemverilogStatement          null

syn match       systemverilogSystemTask         "\$sformatf\>"
syn match       systemverilogSystemTask         "\$sformat\>"
syn match       systemverilogSystemTask         "\$swrite\>"
syn match       systemverilogSystemTask         "\$bits"
syn match       systemverilogSystemTask         "\$cast"
syn match       systemverilogSystemTask         "\$urandom"
syn match       systemverilogSystemTask         "\$isunknown"
syn match       systemverilogSystemTask         "\$realtime"
syn match       systemverilogSystemTask         "\$f\(display\|open\|close\)"
syn match       systemverilogSystemTask         "\$time"
syn match       systemverilogSystemTask         "\$error"

syn match       systemverilogCompilerDirective "`celldefine"
syn match       systemverilogCompilerDirective "`default_nettype"
syn match       systemverilogCompilerDirective "`define"
syn match       systemverilogCompilerDirective "`else"
syn match       systemverilogCompilerDirective "`elsif"
syn match       systemverilogCompilerDirective "`endcelldefine"
syn match       systemverilogCompilerDirective "`endif"
syn match       systemverilogCompilerDirective "`ifdef"
syn match       systemverilogCompilerDirective "`ifndef"
syn match       systemverilogCompilerDirective "`line"
syn match       systemverilogCompilerDirective "`nounconnected_drive"
syn match       systemverilogCompilerDirective "`resetall"
syn match       systemverilogCompilerDirective "`timescale"
syn match       systemverilogCompilerDirective "`unconnected_drive"
syn match       systemverilogCompilerDirective "`undef"

" UVM syntax
runtime syntax/systemverilog-uvm.vim

" Stuff can not be published
runtime syntax/systemverilog-local.vim

" Modify the following as needed.
" The trade-off is performance versus functionality
" TODO: fine-tune this value
syn sync lines=80

" Default the default highlighting
hi def link systemverilogComment            Comment
hi def link systemverilogPreCondition       PreCondit
hi def link systemverilogDefine             Define
hi def link systemverilogConstant           Constant
hi def link systemverilogStatement          Statement
hi def link systemverilogConditional        Conditional
hi def link systemverilogTypeStatement      Type
" hi def link systemverilogTypeDefStatement   TypeDef
hi def link systemverilogTypeDefStatement   Statement
hi def link systemverilogClass              Type
hi def link systemverilogStorageClass       Type
" hi def link systemverilogOperator           Operator
hi def link systemverilogOperator           Special
hi def link systemverilogString             String
hi def link systemverilogIdentifier         Identifier
hi def link systemverilogSystemTask         Macro
hi def link systemverilogCompilerDirective  Define
hi def link systemverilogFunction           Function
let b:current_syntax = "systemverilog"
