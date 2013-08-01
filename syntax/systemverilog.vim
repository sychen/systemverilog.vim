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
syn keyword     systemverilogStatement          new

syn keyword     systemverilogConditional        if else while foreach for
syn keyword     systemverilogConditional        fork join disable join_any join_none wait
syn keyword     systemverilogStatement          initial forever

" OOP keywords
syn keyword     systemverilogStatement          virtual extends public local protected pure
syn keyword     systemverilogStatement          extern static unsigned ref inout input output const
syn keyword     systemverilogStatement          return
syn keyword     systemverilogIdentifier         super this

syn keyword     systemverilogTypeStatement      void
syn keyword     systemverilogTypeStatement      int integer
syn keyword     systemverilogTypeStatement      string
syn keyword     systemverilogTypeStatement      logic bit
syn keyword     systemverilogTypeStatement      event time
syn keyword     systemverilogTypeStatement      process
syn keyword     systemverilogStatement          type
syn keyword     systemverilogStatement          enum

syn keyword     systemverilogTypeDefStatement   typedef

syn match       systemverilogClass              "vmm_[a-z_]\+\>"

syn keyword     systemverilogStatement          null

syn match       systemverilogSystemTask         "\$sformatf\>"
syn match       systemverilogSystemTask         "\$sformat\>"
syn match       systemverilogSystemTask         "\$bits"
syn match       systemverilogSystemTask         "\$cast"

" uvm_pkg.sv

syn keyword     uvmPackage                      uvm_pkg

" base/uvm_component.svh
syn keyword     uvmClass                        uvm_component

    syn keyword uvmClass                        uvm_sequence_base
    syn keyword uvmClass                        uvm_objection
    syn keyword uvmClass                        uvm_severity
    syn keyword uvmClass                        uvm_action
    syn keyword uvmClass                        uvm_transaction
    syn keyword uvmClass                        uvm_recorder
    syn keyword uvmClass                        uvm_event_pool
    syn keyword uvmClass                        uvm_printer
    syn keyword uvmClass                        uvm_verbosity
    syn keyword uvmIdentifier                   uvm_build_phase
    syn keyword uvmFunction                     uvm_report_fatal


" base/uvm_root.svh

    syn keyword uvmClass                        uvm_test_done_objection
    syn keyword uvmClass                        uvm_cmdline_processor

syn keyword     uvmClass                        uvm_root

syn keyword     uvmIdentifier                   uvm_top

" base/uvm_resource.svh

syn keyword     uvmClass                        uvm_resource_base
syn keyword     uvmClass                        uvm_resource_types
syn keyword     uvmClass                        uvm_resource_options
    syn keyword     uvmFunction                     uvm_glob_to_re
    syn keyword     uvmFunction                     uvm_re_match

" base/uvm_config_db.svh

    syn keyword     uvmClass                        uvm_config_db_options

syn keyword     uvmClass                        uvm_config_db

    syn keyword     uvmClass                    uvm_resource_db
    syn keyword     uvmClass                    uvm_resource
    syn keyword     uvmClass                    uvm_queue
    syn keyword     uvmClass                    uvm_resource_pool
    syn keyword     uvmClass                    uvm_resource_types

syn keyword     uvmClass                        uvm_config_wrapper

" base/uvm_object.svh

syn keyword     uvmClass                        uvm_object

    syn keyword uvmFunction                     uvm_report_warning

" macros/uvm_callback.svh

syn keyword     uvmClass                        uvm_callback
syn keyword     uvmClass                        uvm_callbacks
syn keyword     uvmClass                        uvm_typed_callbacks
syn keyword     uvmClass                        uvm_derived_callbacks
syn keyword     uvmClass                        uvm_callbacks_base
syn keyword     uvmClass                        uvm_typeid_base
syn keyword     uvmClass                        uvm_typeid

" macros/uvm_callback_defines.svh

syn match       uvmFunction                     "\`uvm_register_cb"

" base/uvm_pool.svh
syn keyword     uvmClass                        uvm_pool

" seq/uvm_sequence_item.svh

syn keyword     uvmClass                        uvm_sequence_item
    syn match   uvmMacro                        "\`uvm_object_registry"
    syn keyword uvmClass                        uvm_report_handler

" seq/uvm_sequence.svh

syn keyword     uvmClass                        uvm_sequence

" seq/uvm_sequencer_base.svh

syn keyword uvmClass                        uvm_sequencer_base
    syn keyword uvmClass                        uvm_sequence_request
    syn keyword uvmClass                        uvm_sequencer_arb_mode
    syn match   uvmMacro                        "\`uvm_warning"


" seq/uvm_sequencer_param_base.svh

syn keyword     uvmClass                        uvm_sequencer_param_base
    syn keyword uvmClass                        uvm_sequencer_analysis_fifo
    syn keyword uvmClass                        uvm_analysis_export
    syn keyword uvmClass                        uvm_tlm_fifo

" seq/uvm_sequencer.svh

syn keyword     uvmClass                        uvm_sequencer
    syn match   uvmMacro                        "\`uvm_component_param_utils"
    syn keyword uvmClass                        uvm_seq_item_pull_imp
    syn keyword uvmFunction                     uvm_report_info
    syn keyword uvmFunction                     uvm_report_error
    syn keyword uvmClass                        uvm_port_component_base


" comp/uvm_driver.svh

syn keyword     uvmClass                        uvm_driver

    syn keyword uvmClass                        uvm_seq_item_pull_port
    syn keyword uvmClass                        uvm_analysis_port

" macros/uvm_sequence_defines.svh

syn match       uvmMacro                        "\`uvm_create"
syn match       uvmMacro                        "\`uvm_create_on"
syn match       uvmMacro                        "\`uvm_do"
syn match       uvmMacro                        "\`uvm_do_with"
syn match       uvmMacro                        "\`uvm_do_pri"
syn match       uvmMacro                        "\`uvm_do_pri_with"
syn match       uvmMacro                        "\`uvm_do_on_pri_with"
syn match       uvmMacro                        "\`uvm_do_on"
syn match       uvmMacro                        "\`uvm_do_on_pri"
syn match       uvmMacro                        "\`uvm_do_on_with"

syn match       uvmMacro                        "\`uvm_send"
syn match       uvmMacro                        "\`uvm_send_pri"
syn match       uvmMacro                        "\`uvm_rand_send"
syn match       uvmMacro                        "\`uvm_rand_send_pri"
syn match       uvmMacro                        "\`uvm_rand_send_pri_with"

syn match       uvmMacro                        "\`uvm_add_to_seq_lib"
syn match       uvmMacro                        "\`uvm_sequence_library_utils"

syn match       uvmMacro                        "\`uvm_declare_p_sequencer"

" others
syn keyword     uvmClass                        uvm_blocking_put_port
syn keyword     uvmClass                        uvm_void
syn keyword     uvmClass                        uvm_report_object
syn keyword     uvmClass                        uvm_object_wrapper
syn keyword     uvmClass                        uvm_phase
syn keyword     uvmClass                        uvm_domain
syn keyword     uvmClass                        uvm_bitstream_t
syn keyword     uvmFunction                     get_config_int


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
" hi def link systemverilogOperator           Operator
hi def link systemverilogOperator           Special
hi def link systemverilogString             String
hi def link systemverilogIdentifier         Identifier
hi def link systemverilogSystemTask         Macro
hi def link uvmMacro                        Macro
hi def link uvmClass                        Type
hi def link uvmPackage                      Identifier
hi def link uvmFunction                     Function
hi def link uvmIdentifier                   Identifier
let b:current_syntax = "systemverilog"
