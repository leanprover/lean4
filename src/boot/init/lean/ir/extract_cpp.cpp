// Lean compiler output
// Module: init.lean.ir.extract_cpp
// Imports: init.lean.name_mangling init.lean.config init.lean.ir.type_check
#include "runtime/object.h"
#include "runtime/apply.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s4_lean_s2_ir_s13_mk__fnid__set;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__34;
obj* _l_s4_lean_s2_ir_s3_cpp_s9_is__const(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__terminator(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__2;
obj* _l_s3_int_s4_repr_s6___main_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s15_emit__def__core(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s24_emit__global__var__decls(obj*, obj*, obj*);
obj* _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__2;
obj* _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__1(obj*, obj*);
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s24_emit__global__var__decls_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__9;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__2;
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__3_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s7___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__terminator_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__4;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__1(obj*, obj*, obj*);
obj* _l_s3_int_s4_repr_s6___main(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__35;
unsigned char _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__2(unsigned short, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__8;
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__6(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__6;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main(unsigned char, unsigned char);
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(obj*, obj*);
obj* _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s9___spec__1_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__33;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__16;
obj* _l_s2_id_s5_monad_s11___lambda__2(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s10_global2cpp_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s18_initialize__prefix;
obj* _l_s4_lean_s2_ir_s3_cpp_s7_fid2cpp_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__14;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s7___boxed(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s13_collect__used(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__9;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__7;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__type__size_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__8;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s9_emit__sep_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp(unsigned char);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith(unsigned char, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s19_monad__state__trans_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__2_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__39;
obj* _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__4;
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__38;
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__2;
obj* _l_s4_lean_s2_ir_s12_extract__cpp_s11___closed__1;
obj* _l_s4_lean_s2_ir_s5_instr_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main(unsigned char);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__5;
obj* _l_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main_s9___spec__2(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__4;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__18;
obj* _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__2_s7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__5;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__type(unsigned char, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__13;
unsigned char _l_s4_list_s5_empty_s6___main_s6___rarg(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__1;
obj* _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
obj* _l_s10_uint32__sz;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s12_extract__cpp_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s12_file__header(obj*);
obj* _l_s6_rbnode_s14_balance2__node_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__19;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__6;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__1;
obj* _l_s2_id_s5_monad_s11___lambda__3(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s7___boxed(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__block_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_finalize__prefix;
obj* _l_s4_lean_s2_ir_s12_extract__cpp_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__4;
obj* _l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header_s11___closed__2;
obj* _l_s6_rbnode_s14_balance1__node_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__3;
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__2(obj*, obj*, unsigned char);
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__5;
obj* _l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s12___closed__10;
obj* _l_s4_lean_s2_ir_s3_cpp_s21_emit__template__param_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s12_infer__types(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__9;
obj* _l_s4_lean_s2_ir_s7_type2id_s6___main(unsigned char);
obj* _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1(obj*, obj*, unsigned char, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__big__binop(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s5_paren(obj*);
obj* _l_s9_reader__t_s4_pure_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__2_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__3(unsigned short, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__1(size_t, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__fnid(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__4;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__21;
obj* _l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__1;
obj* _l_s9___private_1205956357__s4_name_s11_mangle__aux_s6___main(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__3;
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__3(obj*, obj*, unsigned char);
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__28;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__2;
obj* _l_s8_state__t_s12_monad__state_s6___rarg(obj*);
obj* _l_s9_reader__t_s4_pure_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__2(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__3;
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__5(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__4;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__12;
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__8;
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__4;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__15;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__1_s11___closed__1;
obj* _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__23;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__18;
obj* _l_s4_lean_s2_ir_s6_header_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__17;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s20_emit__logical__arith(unsigned char, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s12_decl__locals(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__5;
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s10_monad__run;
obj* _l_s9_reader__t_s5_monad_s6___rarg(obj*);
obj* _l_s9_except__t_s13_monad__except_s6___rarg(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__8;
obj* _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main(obj*);
obj* _l_s9_reader__t_s4_lift(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__11;
obj* _l_s6_uint16_s7_to__nat_s6___main(unsigned short);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__37;
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__7;
obj* _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__26;
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__40;
obj* _l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__1;
obj* _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_need__uncurry_s9___spec__1(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__13;
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__7;
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s12_emit__global(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__7;
obj* _l_s8_state__t_s5_monad_s6___rarg(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__8;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s13_monad__reader;
obj* _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__2(obj*, obj*, unsigned char, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__4;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__30;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__22;
obj* _l_s4_lean_s2_ir_s3_cpp_s12_emit__header_s11___closed__1;
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(obj*, obj*);
obj* _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__type_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main(unsigned char, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__7;
obj* _l_s2_id_s3_run(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s10_global2cpp(obj*, obj*, obj*);
obj* _l_s3_nat_s6_repeat_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__3_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__7;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__20;
obj* _l_s4_lean_s4_name_s9_quick__lt_s6___main(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix(unsigned char, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit(obj*, unsigned char, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s15_emit__arg__list(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params(obj*, obj*, obj*);
obj* _l_s2_id_s5_monad_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s9_is__const_s11___closed__1;
obj* _l_s9_reader__t_s10_monad__run_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__2;
obj* _l_s9___private_3255790009__s6_string_s11_mangle__aux_s6___main_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__6;
obj* _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s18_emit__assign__unop(obj*, unsigned char, unsigned char, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__25;
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__type__size_s11___closed__1;
obj* _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s9_emit__def(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s12_emit__header(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith_s7___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s11_mk__context;
obj* _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__6;
obj* _l_s4_lean_s2_ir_s2_id_s10_to__string_s6___main(obj*);
obj* _l_s9_reader__t_s4_read_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__7;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__31;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_decl__local(obj*, unsigned char, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__4;
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__1_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__41;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s12_monad__state;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__9;
obj* _l_s4_lean_s2_ir_s10_terminator_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__4;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__3;
obj* _l_s4_lean_s18_closure__max__args;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__3;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s15_emit__def__core_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s13_monad__except;
obj* _l_s4_lean_s2_ir_s3_cpp_s5_paren_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s5_monad;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__6;
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__9;
obj* _l_s4_lean_s2_ir_s3_cpp_s7_fid2cpp(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__1;
obj* _l_s4_lean_s6_format_s2_be_s6___main_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__27;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_decl__local_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__case(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__7;
obj* _l_s4_lean_s2_ir_s3_cpp_s15_emit__var__list(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__op__x(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s10_terminator_s10_to__format_s6___main(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg_s11___closed__1;
obj* _l_s9_reader__t_s13_monad__except_s6___rarg(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__unop(unsigned char, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__4;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__29;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__9;
obj* _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s9___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply(obj*, obj*, obj*, obj*);
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__1(obj*, obj*, unsigned char);
obj* _l_s4_lean_s2_ir_s3_cpp_s20_emit__logical__arith_s7___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__8;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__5;
obj* _l_s4_lean_s2_ir_s3_cpp_s14_emit__x__op__y(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__17;
obj* _l_s3_nat_s7_mrepeat_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__unop_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s3_nat_s4_repr(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__5;
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp(unsigned char);
obj* _l_s4_lean_s2_ir_s3_cpp_s15_emit__arg__list_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__1_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__24;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__16;
obj* _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__7;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__block_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s12___closed__11;
obj* _l_s9_except__t_s10_monad__run_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s5_comma(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp(unsigned char, unsigned char);
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__1;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__2;
obj* _l_s4_lean_s2_ir_s12_extract__cpp(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__4;
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop(obj*, unsigned char, unsigned char, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__block(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__12;
obj* _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__9;
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__3;
obj* _l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__4;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__6;
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__6;
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__1;
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__2;
obj* _l_s2_id(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__32;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__10;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__36;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__6;
obj* _l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__line(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__15;
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__type__size(unsigned char, obj*, obj*);
obj* _l_s8_state__t_s10_monad__run_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__5;
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__2_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__3_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__4;
obj* _l_s3_nat_s6_repeat_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__3(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__11;
obj* _l_s5_usize_s7_to__nat_s6___main(size_t);
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__6;
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__block_s11___closed__1;
obj* _l_s9_except__t_s4_lift_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__8;
obj* _l_s4_lean_s2_ir_s3_cpp_s10_extract__m;
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main(unsigned char);
obj* _l_s9_except__t_s5_monad_s6___rarg(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__2;
obj* _l_s2_id_s4_bind(obj*, obj*);
obj* _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__1;
obj* _l_s6_rbnode_s18_mk__insert__result_s6___main_s6___rarg(unsigned char, obj*);
obj* _l_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s18_emit__assign__unop_s7___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__5;
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s7___boxed(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__10;
obj* _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos_s11___closed__1;
obj* _l_s4_list_s6_length_s6___main_s6___rarg(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s13_need__uncurry(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid(obj*, obj*, obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s9_emit__sep(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__4;
obj* _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_string_s5_quote(obj*);
obj* _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__1;
obj* _l_s4_lean_s2_ir_s13_is__arith__ty_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s21_emit__template__param(unsigned char, obj*, obj*);
obj* _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__14;
obj* _init__l_s4_lean_s2_ir_s3_cpp_s18_initialize__prefix() {
{
obj* x_0; 
x_0 = lean::mk_string("_lean_initialize_");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_finalize__prefix() {
{
obj* x_0; 
x_0 = lean::mk_string("_lean_finalize_");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s12_file__header(obj* x_0) {
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_1 = _l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__1;
lean::inc(x_1);
x_3 = lean::string_append(x_1, x_0);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__2;
x_5 = lean::string_append(x_3, x_4);
x_6 = lean::string_append(x_5, x_1);
x_7 = lean::string_append(x_6, x_0);
lean::dec(x_0);
x_9 = _l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__3;
x_10 = lean::string_append(x_7, x_9);
x_11 = _l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__4;
x_12 = lean::string_append(x_10, x_11);
return x_12;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("#include <");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("/object.h>\n");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string("/apply.h>\n");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string("typedef lean::object obj;");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_extract__m() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s10_monad__run() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s3_run), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_state__t_s10_monad__run_s6___rarg), 5, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s10_monad__run_s6___rarg), 3, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s10_monad__run_s6___rarg), 4, 1);
lean::closure_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s13_monad__reader() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_5 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_0);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set(x_5, 4, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = _l_s8_state__t_s5_monad_s6___rarg(x_7);
x_9 = _l_s9_except__t_s5_monad_s6___rarg(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_read_s6___rarg), 2, 1);
lean::closure_set(x_10, 0, x_9);
return x_10;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s12_monad__state() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_5 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_0);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set(x_5, 4, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
lean::inc(x_7);
x_9 = _l_s8_state__t_s5_monad_s6___rarg(x_7);
lean::inc(x_9);
x_11 = _l_s9_except__t_s5_monad_s6___rarg(x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_lift), 4, 3);
lean::closure_set(x_12, 0, lean::box(0));
lean::closure_set(x_12, 1, lean::box(0));
lean::closure_set(x_12, 2, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s4_lift_s6___rarg), 3, 1);
lean::closure_set(x_13, 0, x_9);
x_14 = _l_s8_state__t_s12_monad__state_s6___rarg(x_7);
x_15 = _l_s19_monad__state__trans_s6___rarg(x_13, x_14);
x_16 = _l_s19_monad__state__trans_s6___rarg(x_12, x_15);
return x_16;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s13_monad__except() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_5 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_0);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set(x_5, 4, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = _l_s8_state__t_s5_monad_s6___rarg(x_7);
x_9 = _l_s9_except__t_s13_monad__except_s6___rarg(x_8);
x_10 = _l_s9_reader__t_s13_monad__except_s6___rarg(x_9);
return x_10;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s5_monad() {
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_5 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_0);
lean::cnstr_set(x_5, 3, x_1);
lean::cnstr_set(x_5, 4, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = _l_s8_state__t_s5_monad_s6___rarg(x_7);
x_9 = _l_s9_except__t_s5_monad_s6___rarg(x_8);
x_10 = _l_s9_reader__t_s5_monad_s6___rarg(x_9);
return x_10;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::dec(x_2);
x_5 = lean::apply_1(x_0, x_1);
x_6 = lean::string_append(x_3, x_5);
lean::dec(x_5);
x_8 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s3_cpp_s4_emit_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__line(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; 
x_2 = _l_s4_lean_s6_format_s2_be_s6___main_s11___closed__1;
lean::inc(x_2);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_2, x_0, x_1);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_6; obj* x_8; 
lean::dec(x_1);
x_4 = lean::string_append(x_2, x_0);
lean::dec(x_0);
x_6 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s5_paren_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_3);
x_6 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_3, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_0);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_16 = x_7;
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
if (lean::is_scalar(x_11)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_11;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_9);
return x_18;
}
else
{
obj* x_19; obj* x_21; obj* x_22; obj* x_24; 
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_19 = x_7;
}
lean::inc(x_1);
x_21 = lean::apply_2(x_0, x_1, x_9);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_28; obj* x_31; obj* x_32; 
lean::dec(x_1);
x_28 = lean::cnstr_get(x_22, 0);
lean::inc(x_28);
lean::dec(x_22);
if (lean::is_scalar(x_19)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_19;
}
lean::cnstr_set(x_31, 0, x_28);
if (lean::is_scalar(x_11)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_11;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_24);
return x_32;
}
else
{
obj* x_33; obj* x_36; obj* x_38; obj* x_39; obj* x_41; 
x_33 = lean::cnstr_get(x_22, 0);
lean::inc(x_33);
lean::dec(x_22);
x_36 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_36);
x_38 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_36, x_1, x_24);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
if (lean::obj_tag(x_39) == 0)
{
obj* x_45; obj* x_48; obj* x_49; 
lean::dec(x_33);
x_45 = lean::cnstr_get(x_39, 0);
lean::inc(x_45);
lean::dec(x_39);
if (lean::is_scalar(x_19)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_19;
}
lean::cnstr_set(x_48, 0, x_45);
if (lean::is_scalar(x_11)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_11;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_41);
return x_49;
}
else
{
obj* x_51; obj* x_52; 
lean::dec(x_39);
if (lean::is_scalar(x_19)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_19;
}
lean::cnstr_set(x_51, 0, x_33);
if (lean::is_scalar(x_11)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_11;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_41);
return x_52;
}
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s5_paren(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s3_cpp_s5_paren_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s5_comma(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::inc(x_2);
x_5 = lean::apply_2(x_0, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_25; 
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
}
x_19 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_2);
lean::inc(x_19);
x_22 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_19, x_2, x_8);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_33; obj* x_34; 
lean::dec(x_1);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
if (lean::is_scalar(x_18)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_18;
}
lean::cnstr_set(x_33, 0, x_30);
if (lean::is_scalar(x_10)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_10;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_25);
return x_34;
}
else
{
obj* x_38; 
lean::dec(x_10);
lean::dec(x_18);
lean::dec(x_23);
x_38 = lean::apply_2(x_1, x_2, x_25);
return x_38;
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = _l_s9___private_3255790009__s6_string_s11_mangle__aux_s6___main_s11___closed__2;
lean::inc(x_3);
x_5 = _l_s9___private_1205956357__s4_name_s11_mangle__aux_s6___main(x_3, x_0);
x_6 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_5, x_1, x_2);
return x_6;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid_s11___closed__1;
lean::inc(x_3);
x_5 = _l_s9___private_1205956357__s4_name_s11_mangle__aux_s6___main(x_3, x_0);
x_6 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_5, x_1, x_2);
return x_6;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("_lbl");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s7_fid2cpp(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 4);
lean::inc(x_6);
lean::dec(x_3);
lean::inc(x_0);
x_10 = lean::apply_1(x_6, x_0);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_10);
x_12 = _l_s4_lean_s2_ir_s3_cpp_s7_fid2cpp_s11___closed__1;
lean::inc(x_12);
x_14 = _l_s9___private_1205956357__s4_name_s11_mangle__aux_s6___main(x_12, x_0);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_2);
return x_16;
}
else
{
obj* x_18; obj* x_21; obj* x_22; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_10, 0);
lean::inc(x_18);
lean::dec(x_10);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_18);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_2);
return x_22;
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s7_fid2cpp_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("_l");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__fnid(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
lean::inc(x_1);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s7_fid2cpp(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
}
if (lean::obj_tag(x_5) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_13 = x_5;
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_7);
return x_15;
}
else
{
obj* x_17; obj* x_20; 
lean::dec(x_9);
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
lean::dec(x_5);
x_20 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_17, x_1, x_7);
return x_20;
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s9_is__const(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 3);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::apply_1(x_6, x_0);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; 
lean::dec(x_9);
x_11 = _l_s4_lean_s2_ir_s3_cpp_s9_is__const_s11___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_17; unsigned char x_18; obj* x_20; obj* x_21; obj* x_22; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
x_17 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_14);
x_18 = lean::cnstr_get_scalar<unsigned char>(x_17, sizeof(void*)*3);
lean::dec(x_17);
x_20 = lean::box(x_18);
x_21 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_2);
return x_22;
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s9_is__const_s11___closed__1() {
{
unsigned char x_0; obj* x_1; obj* x_2; 
x_0 = 0;
x_1 = lean::box(x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s10_global2cpp(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; 
x_3 = _l_s4_lean_s2_ir_s3_cpp_s7_fid2cpp(x_0, x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_8 = x_3;
}
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_11 = x_4;
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_9);
if (lean::is_scalar(x_8)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_8;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_6);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_22; 
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_16 = x_4;
}
x_17 = _l_s4_lean_s2_ir_s3_cpp_s10_global2cpp_s11___closed__1;
lean::inc(x_17);
x_19 = lean::string_append(x_17, x_14);
lean::dec(x_14);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_19);
if (lean::is_scalar(x_8)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_8;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_6);
return x_22;
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_global2cpp_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("_g");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s12_emit__global(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
lean::inc(x_1);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s10_global2cpp(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
}
if (lean::obj_tag(x_5) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_13 = x_5;
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_7);
return x_15;
}
else
{
obj* x_17; obj* x_20; 
lean::dec(x_9);
x_17 = lean::cnstr_get(x_5, 0);
lean::inc(x_17);
lean::dec(x_5);
x_20 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_17, x_1, x_7);
return x_20;
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main(unsigned char x_0) {
{

switch (x_0) {
case 0:
{
obj* x_1; 
x_1 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__1;
lean::inc(x_1);
return x_1;
}
case 1:
{
obj* x_3; 
x_3 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__1;
lean::inc(x_3);
return x_3;
}
case 2:
{
obj* x_5; 
x_5 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__2;
lean::inc(x_5);
return x_5;
}
case 3:
{
obj* x_7; 
x_7 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__3;
lean::inc(x_7);
return x_7;
}
case 4:
{
obj* x_9; 
x_9 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__4;
lean::inc(x_9);
return x_9;
}
case 5:
{
obj* x_11; 
x_11 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__5;
lean::inc(x_11);
return x_11;
}
case 6:
{
obj* x_13; 
x_13 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__6;
lean::inc(x_13);
return x_13;
}
case 7:
{
obj* x_15; 
x_15 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__7;
lean::inc(x_15);
return x_15;
}
case 8:
{
obj* x_17; 
x_17 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__8;
lean::inc(x_17);
return x_17;
}
case 9:
{
obj* x_19; 
x_19 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__9;
lean::inc(x_19);
return x_19;
}
case 10:
{
obj* x_21; 
x_21 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s12___closed__10;
lean::inc(x_21);
return x_21;
}
default:
{
obj* x_23; 
x_23 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s12___closed__11;
lean::inc(x_23);
return x_23;
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("unsigned char");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("unsigned short");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string("unsigned");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string("unsigned long long");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__5() {
{
obj* x_0; 
x_0 = lean::mk_string("size_t");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__6() {
{
obj* x_0; 
x_0 = lean::mk_string("short");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__7() {
{
obj* x_0; 
x_0 = lean::mk_string("int");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__8() {
{
obj* x_0; 
x_0 = lean::mk_string("long long");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__9() {
{
obj* x_0; 
x_0 = lean::mk_string("float");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s12___closed__10() {
{
obj* x_0; 
x_0 = lean::mk_string("double");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s12___closed__11() {
{
obj* x_0; 
x_0 = lean::mk_string("obj*");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main(x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp(unsigned char x_0) {
{
obj* x_1; 
x_1 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp(x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__type(unsigned char x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main(x_0);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_3, x_1, x_2);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__type_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__type(x_3, x_1, x_2);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{

if (lean::obj_tag(x_2) == 0)
{
obj* x_9; obj* x_11; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_9 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_4);
return x_11;
}
else
{
obj* x_12; obj* x_14; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
lean::dec(x_2);
if (lean::obj_tag(x_14) == 0)
{
obj* x_19; 
lean::dec(x_14);
lean::dec(x_1);
x_19 = lean::apply_3(x_0, x_12, x_3, x_4);
return x_19;
}
else
{
obj* x_22; obj* x_23; obj* x_25; obj* x_27; 
lean::inc(x_3);
lean::inc(x_0);
x_22 = lean::apply_3(x_0, x_12, x_3, x_4);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 x_27 = x_22;
}
if (lean::obj_tag(x_23) == 0)
{
obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
x_32 = lean::cnstr_get(x_23, 0);
lean::inc(x_32);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_34 = x_23;
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
if (lean::is_scalar(x_27)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_27;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_25);
return x_36;
}
else
{
obj* x_37; obj* x_40; obj* x_41; obj* x_43; 
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_37 = x_23;
}
lean::inc(x_3);
lean::inc(x_1);
x_40 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1, x_3, x_25);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_50; obj* x_53; obj* x_54; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
x_50 = lean::cnstr_get(x_41, 0);
lean::inc(x_50);
lean::dec(x_41);
if (lean::is_scalar(x_37)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_37;
}
lean::cnstr_set(x_53, 0, x_50);
if (lean::is_scalar(x_27)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_27;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_43);
return x_54;
}
else
{
obj* x_56; obj* x_59; obj* x_60; obj* x_62; 
lean::dec(x_41);
x_56 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_3);
lean::inc(x_56);
x_59 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_56, x_3, x_43);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_60) == 0)
{
obj* x_69; obj* x_72; obj* x_73; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
x_69 = lean::cnstr_get(x_60, 0);
lean::inc(x_69);
lean::dec(x_60);
if (lean::is_scalar(x_37)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_37;
}
lean::cnstr_set(x_72, 0, x_69);
if (lean::is_scalar(x_27)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_27;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_62);
return x_73;
}
else
{
obj* x_77; 
lean::dec(x_60);
lean::dec(x_27);
lean::dec(x_37);
x_77 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg(x_0, x_1, x_14, x_3, x_62);
return x_77;
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string(" ");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; 
x_5 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s9_emit__sep_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; 
x_5 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg(x_1, x_2, x_0, x_3, x_4);
return x_5;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s9_emit__sep(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s3_cpp_s9_emit__sep_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s15_emit__var__list(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s3_cpp_s9_emit__var), 3, 0);
x_4 = lean::mk_string(",");
x_5 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__1;
lean::inc(x_1);
lean::inc(x_3);
x_6 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_3, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_0);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_16 = x_7;
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
if (lean::is_scalar(x_11)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_11;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_9);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_25; obj* x_26; obj* x_28; 
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_19 = x_7;
}
x_20 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__2;
x_21 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__3;
lean::inc(x_1);
lean::inc(x_21);
lean::inc(x_20);
x_25 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg(x_20, x_21, x_0, x_1, x_9);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_32; obj* x_35; obj* x_36; 
lean::dec(x_1);
x_32 = lean::cnstr_get(x_26, 0);
lean::inc(x_32);
lean::dec(x_26);
if (lean::is_scalar(x_19)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_19;
}
lean::cnstr_set(x_35, 0, x_32);
if (lean::is_scalar(x_11)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_11;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_28);
return x_36;
}
else
{
obj* x_40; obj* x_42; 
lean::dec(x_11);
lean::dec(x_19);
lean::dec(x_26);
x_40 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__4;
lean::inc(x_40);
x_42 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_40, x_1, x_28);
return x_42;
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("<");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s3_cpp_s10_emit__type_s7___boxed), 3, 0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string(",");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string(">");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s21_emit__template__param(unsigned char x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_cnstr(0, 0, 0);
;
x_4 = lean::box(x_0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params(x_5, x_1, x_2);
return x_6;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s21_emit__template__param_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s21_emit__template__param(x_3, x_1, x_2);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s15_emit__arg__list(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s3_cpp_s15_emit__arg__list_s11___lambda__1), 3, 0);
x_4 = lean::mk_string(",");
x_5 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s15_emit__arg__list_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_3 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*1);
lean::inc(x_1);
x_5 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__type(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_0);
lean::dec(x_1);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_25; 
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
}
x_19 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_19);
x_22 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_19, x_1, x_8);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_33; obj* x_34; 
lean::dec(x_0);
lean::dec(x_1);
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
if (lean::is_scalar(x_18)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_18;
}
lean::cnstr_set(x_33, 0, x_30);
if (lean::is_scalar(x_10)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_10;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_25);
return x_34;
}
else
{
obj* x_38; obj* x_41; 
lean::dec(x_10);
lean::dec(x_18);
lean::dec(x_23);
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
lean::dec(x_0);
x_41 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_38, x_1, x_25);
return x_41;
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_2 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos_s11___closed__1;
lean::inc(x_0);
lean::inc(x_2);
x_5 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_2, x_0, x_1);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_0);
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_14 = x_6;
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_12);
if (lean::is_scalar(x_10)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_10;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_8);
return x_16;
}
else
{
obj* x_19; obj* x_21; 
lean::dec(x_6);
lean::dec(x_10);
x_19 = _l_s4_lean_s6_format_s2_be_s6___main_s11___closed__1;
lean::inc(x_19);
x_21 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_19, x_0, x_8);
return x_21;
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s9_emit__eos_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string(";");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_7; obj* x_9; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
x_7 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__1;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
lean::dec(x_0);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_20; obj* x_21; obj* x_23; obj* x_25; 
lean::dec(x_12);
lean::dec(x_1);
x_17 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__2;
lean::inc(x_2);
lean::inc(x_17);
x_20 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_17, x_2, x_3);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_release(x_20, 1);
 x_25 = x_20;
}
if (lean::obj_tag(x_21) == 0)
{
obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_10);
lean::dec(x_2);
x_28 = lean::cnstr_get(x_21, 0);
lean::inc(x_28);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_30 = x_21;
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
if (lean::is_scalar(x_25)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_25;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_23);
return x_32;
}
else
{
obj* x_33; obj* x_35; obj* x_36; obj* x_38; 
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_33 = x_21;
}
lean::inc(x_2);
x_35 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid(x_10, x_2, x_23);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_35, 1);
lean::inc(x_38);
lean::dec(x_35);
if (lean::obj_tag(x_36) == 0)
{
obj* x_42; obj* x_45; obj* x_46; 
lean::dec(x_2);
x_42 = lean::cnstr_get(x_36, 0);
lean::inc(x_42);
lean::dec(x_36);
if (lean::is_scalar(x_33)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_33;
}
lean::cnstr_set(x_45, 0, x_42);
if (lean::is_scalar(x_25)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_25;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_38);
return x_46;
}
else
{
obj* x_50; 
lean::dec(x_25);
lean::dec(x_36);
lean::dec(x_33);
x_50 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos(x_2, x_38);
return x_50;
}
}
}
else
{
obj* x_51; obj* x_54; obj* x_55; obj* x_57; obj* x_59; 
x_51 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__3;
lean::inc(x_2);
lean::inc(x_51);
x_54 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_51, x_2, x_3);
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_59 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 lean::cnstr_release(x_54, 1);
 x_59 = x_54;
}
if (lean::obj_tag(x_55) == 0)
{
obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_2);
x_64 = lean::cnstr_get(x_55, 0);
lean::inc(x_64);
if (lean::is_shared(x_55)) {
 lean::dec(x_55);
 x_66 = lean::box(0);
} else {
 lean::cnstr_release(x_55, 0);
 x_66 = x_55;
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_64);
if (lean::is_scalar(x_59)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_59;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_57);
return x_68;
}
else
{
obj* x_69; obj* x_72; obj* x_73; obj* x_75; 
if (lean::is_shared(x_55)) {
 lean::dec(x_55);
 x_69 = lean::box(0);
} else {
 lean::cnstr_release(x_55, 0);
 x_69 = x_55;
}
lean::inc(x_2);
lean::inc(x_1);
x_72 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s9___spec__1(x_1, x_2, x_57);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
lean::dec(x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_82; obj* x_85; obj* x_86; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_2);
x_82 = lean::cnstr_get(x_73, 0);
lean::inc(x_82);
lean::dec(x_73);
if (lean::is_scalar(x_69)) {
 x_85 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_85 = x_69;
}
lean::cnstr_set(x_85, 0, x_82);
if (lean::is_scalar(x_59)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_59;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_75);
return x_86;
}
else
{
obj* x_88; obj* x_89; obj* x_92; obj* x_95; obj* x_96; obj* x_98; 
lean::dec(x_73);
x_88 = lean::mk_nat_obj(1u);
x_89 = lean::nat_add(x_1, x_88);
lean::dec(x_88);
lean::dec(x_1);
x_92 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__4;
lean::inc(x_2);
lean::inc(x_92);
x_95 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_92, x_2, x_75);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_95, 1);
lean::inc(x_98);
lean::dec(x_95);
if (lean::obj_tag(x_96) == 0)
{
obj* x_105; obj* x_108; obj* x_109; 
lean::dec(x_12);
lean::dec(x_89);
lean::dec(x_10);
lean::dec(x_2);
x_105 = lean::cnstr_get(x_96, 0);
lean::inc(x_105);
lean::dec(x_96);
if (lean::is_scalar(x_69)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_69;
}
lean::cnstr_set(x_108, 0, x_105);
if (lean::is_scalar(x_59)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_59;
}
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_98);
return x_109;
}
else
{
obj* x_112; obj* x_113; obj* x_115; 
lean::dec(x_96);
lean::inc(x_2);
x_112 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid(x_10, x_2, x_98);
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_112, 1);
lean::inc(x_115);
lean::dec(x_112);
if (lean::obj_tag(x_113) == 0)
{
obj* x_121; obj* x_124; obj* x_125; 
lean::dec(x_12);
lean::dec(x_89);
lean::dec(x_2);
x_121 = lean::cnstr_get(x_113, 0);
lean::inc(x_121);
lean::dec(x_113);
if (lean::is_scalar(x_69)) {
 x_124 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_124 = x_69;
}
lean::cnstr_set(x_124, 0, x_121);
if (lean::is_scalar(x_59)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_59;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_115);
return x_125;
}
else
{
obj* x_128; obj* x_129; obj* x_131; 
lean::dec(x_113);
lean::inc(x_2);
x_128 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos(x_2, x_115);
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_128, 1);
lean::inc(x_131);
lean::dec(x_128);
if (lean::obj_tag(x_129) == 0)
{
obj* x_137; obj* x_140; obj* x_141; 
lean::dec(x_12);
lean::dec(x_89);
lean::dec(x_2);
x_137 = lean::cnstr_get(x_129, 0);
lean::inc(x_137);
lean::dec(x_129);
if (lean::is_scalar(x_69)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_69;
}
lean::cnstr_set(x_140, 0, x_137);
if (lean::is_scalar(x_59)) {
 x_141 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_141 = x_59;
}
lean::cnstr_set(x_141, 0, x_140);
lean::cnstr_set(x_141, 1, x_131);
return x_141;
}
else
{
obj* x_145; 
lean::dec(x_129);
lean::dec(x_69);
lean::dec(x_59);
x_145 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main(x_12, x_89, x_2, x_131);
return x_145;
}
}
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__1() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("ill-formed case terminator");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("default: goto ");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string("case ");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string(": goto ");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
lean::dec(x_1);
x_4 = _l_s3_nat_s4_repr(x_0);
x_5 = lean::string_append(x_2, x_4);
lean::dec(x_4);
x_7 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_5);
return x_9;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; 
x_4 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; obj* x_5; unsigned char x_7; 
if (lean::obj_tag(x_1) == 0)
{
unsigned char x_9; 
x_9 = 0;
x_7 = x_9;
goto lbl_8;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_20; obj* x_21; obj* x_23; obj* x_25; 
lean::dec(x_12);
lean::dec(x_0);
lean::dec(x_1);
x_17 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__4;
lean::inc(x_2);
lean::inc(x_17);
x_20 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_17, x_2, x_3);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_release(x_20, 1);
 x_25 = x_20;
}
if (lean::obj_tag(x_21) == 0)
{
obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_10);
lean::dec(x_2);
x_28 = lean::cnstr_get(x_21, 0);
lean::inc(x_28);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_30 = x_21;
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
if (lean::is_scalar(x_25)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_25;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_23);
return x_32;
}
else
{
obj* x_33; obj* x_35; obj* x_36; obj* x_38; 
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_33 = x_21;
}
lean::inc(x_2);
x_35 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid(x_10, x_2, x_23);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_35, 1);
lean::inc(x_38);
lean::dec(x_35);
if (lean::obj_tag(x_36) == 0)
{
obj* x_42; obj* x_45; obj* x_46; 
lean::dec(x_2);
x_42 = lean::cnstr_get(x_36, 0);
lean::inc(x_42);
lean::dec(x_36);
if (lean::is_scalar(x_33)) {
 x_45 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_45 = x_33;
}
lean::cnstr_set(x_45, 0, x_42);
if (lean::is_scalar(x_25)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_25;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_38);
return x_46;
}
else
{
obj* x_50; 
lean::dec(x_25);
lean::dec(x_36);
lean::dec(x_33);
x_50 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos(x_2, x_38);
return x_50;
}
}
}
else
{
obj* x_51; obj* x_53; 
x_51 = lean::cnstr_get(x_12, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_12, 1);
lean::inc(x_53);
lean::dec(x_12);
if (lean::obj_tag(x_53) == 0)
{
obj* x_58; obj* x_59; obj* x_61; obj* x_64; 
lean::dec(x_53);
lean::dec(x_1);
x_61 = lean::cnstr_get(x_2, 1);
lean::inc(x_61);
lean::inc(x_0);
x_64 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(x_61, x_0);
if (lean::obj_tag(x_64) == 0)
{
obj* x_69; 
lean::dec(x_51);
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_64);
x_69 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5;
lean::inc(x_69);
x_58 = x_69;
x_59 = x_3;
goto lbl_60;
}
else
{
obj* x_71; unsigned char x_74; 
x_71 = lean::cnstr_get(x_64, 0);
lean::inc(x_71);
lean::dec(x_64);
x_74 = lean::unbox(x_71);
lean::dec(x_71);
switch (x_74) {
case 0:
{
obj* x_76; obj* x_79; obj* x_80; obj* x_82; 
x_76 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__6;
lean::inc(x_2);
lean::inc(x_76);
x_79 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_76, x_2, x_3);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
if (lean::obj_tag(x_80) == 0)
{
obj* x_88; obj* x_90; obj* x_91; 
lean::dec(x_51);
lean::dec(x_10);
lean::dec(x_0);
x_88 = lean::cnstr_get(x_80, 0);
lean::inc(x_88);
if (lean::is_shared(x_80)) {
 lean::dec(x_80);
 x_90 = lean::box(0);
} else {
 lean::cnstr_release(x_80, 0);
 x_90 = x_80;
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_88);
x_58 = x_91;
x_59 = x_82;
goto lbl_60;
}
else
{
obj* x_92; obj* x_94; obj* x_95; obj* x_97; 
if (lean::is_shared(x_80)) {
 lean::dec(x_80);
 x_92 = lean::box(0);
} else {
 lean::cnstr_release(x_80, 0);
 x_92 = x_80;
}
lean::inc(x_2);
x_94 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_2, x_82);
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_94, 1);
lean::inc(x_97);
lean::dec(x_94);
if (lean::obj_tag(x_95) == 0)
{
obj* x_102; obj* x_105; 
lean::dec(x_51);
lean::dec(x_10);
x_102 = lean::cnstr_get(x_95, 0);
lean::inc(x_102);
lean::dec(x_95);
if (lean::is_scalar(x_92)) {
 x_105 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_105 = x_92;
}
lean::cnstr_set(x_105, 0, x_102);
x_58 = x_105;
x_59 = x_97;
goto lbl_60;
}
else
{
obj* x_107; obj* x_110; obj* x_111; obj* x_113; 
lean::dec(x_95);
x_107 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__7;
lean::inc(x_2);
lean::inc(x_107);
x_110 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_107, x_2, x_97);
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_110, 1);
lean::inc(x_113);
lean::dec(x_110);
if (lean::obj_tag(x_111) == 0)
{
obj* x_118; obj* x_121; 
lean::dec(x_51);
lean::dec(x_10);
x_118 = lean::cnstr_get(x_111, 0);
lean::inc(x_118);
lean::dec(x_111);
if (lean::is_scalar(x_92)) {
 x_121 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_121 = x_92;
}
lean::cnstr_set(x_121, 0, x_118);
x_58 = x_121;
x_59 = x_113;
goto lbl_60;
}
else
{
obj* x_124; obj* x_125; obj* x_127; 
lean::dec(x_111);
lean::inc(x_2);
x_124 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid(x_51, x_2, x_113);
x_125 = lean::cnstr_get(x_124, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_124, 1);
lean::inc(x_127);
lean::dec(x_124);
if (lean::obj_tag(x_125) == 0)
{
obj* x_131; obj* x_134; 
lean::dec(x_10);
x_131 = lean::cnstr_get(x_125, 0);
lean::inc(x_131);
lean::dec(x_125);
if (lean::is_scalar(x_92)) {
 x_134 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_134 = x_92;
}
lean::cnstr_set(x_134, 0, x_131);
x_58 = x_134;
x_59 = x_127;
goto lbl_60;
}
else
{
obj* x_136; obj* x_139; obj* x_140; obj* x_142; 
lean::dec(x_125);
x_136 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__8;
lean::inc(x_2);
lean::inc(x_136);
x_139 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_136, x_2, x_127);
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_139, 1);
lean::inc(x_142);
lean::dec(x_139);
if (lean::obj_tag(x_140) == 0)
{
obj* x_146; obj* x_149; 
lean::dec(x_10);
x_146 = lean::cnstr_get(x_140, 0);
lean::inc(x_146);
lean::dec(x_140);
if (lean::is_scalar(x_92)) {
 x_149 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_149 = x_92;
}
lean::cnstr_set(x_149, 0, x_146);
x_58 = x_149;
x_59 = x_142;
goto lbl_60;
}
else
{
obj* x_153; obj* x_154; obj* x_156; 
lean::dec(x_140);
lean::dec(x_92);
lean::inc(x_2);
x_153 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid(x_10, x_2, x_142);
x_154 = lean::cnstr_get(x_153, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_153, 1);
lean::inc(x_156);
lean::dec(x_153);
x_58 = x_154;
x_59 = x_156;
goto lbl_60;
}
}
}
}
}
}
case 1:
{
obj* x_162; 
lean::dec(x_51);
lean::dec(x_10);
lean::dec(x_0);
x_162 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5;
lean::inc(x_162);
x_58 = x_162;
x_59 = x_3;
goto lbl_60;
}
case 2:
{
obj* x_167; 
lean::dec(x_51);
lean::dec(x_10);
lean::dec(x_0);
x_167 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5;
lean::inc(x_167);
x_58 = x_167;
x_59 = x_3;
goto lbl_60;
}
case 3:
{
obj* x_169; obj* x_172; obj* x_173; obj* x_175; 
x_169 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__6;
lean::inc(x_2);
lean::inc(x_169);
x_172 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_169, x_2, x_3);
x_173 = lean::cnstr_get(x_172, 0);
lean::inc(x_173);
x_175 = lean::cnstr_get(x_172, 1);
lean::inc(x_175);
lean::dec(x_172);
if (lean::obj_tag(x_173) == 0)
{
obj* x_181; obj* x_183; obj* x_184; 
lean::dec(x_51);
lean::dec(x_10);
lean::dec(x_0);
x_181 = lean::cnstr_get(x_173, 0);
lean::inc(x_181);
if (lean::is_shared(x_173)) {
 lean::dec(x_173);
 x_183 = lean::box(0);
} else {
 lean::cnstr_release(x_173, 0);
 x_183 = x_173;
}
if (lean::is_scalar(x_183)) {
 x_184 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_184 = x_183;
}
lean::cnstr_set(x_184, 0, x_181);
x_58 = x_184;
x_59 = x_175;
goto lbl_60;
}
else
{
obj* x_185; obj* x_187; obj* x_188; obj* x_190; 
if (lean::is_shared(x_173)) {
 lean::dec(x_173);
 x_185 = lean::box(0);
} else {
 lean::cnstr_release(x_173, 0);
 x_185 = x_173;
}
lean::inc(x_2);
x_187 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_2, x_175);
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
x_190 = lean::cnstr_get(x_187, 1);
lean::inc(x_190);
lean::dec(x_187);
if (lean::obj_tag(x_188) == 0)
{
obj* x_195; obj* x_198; 
lean::dec(x_51);
lean::dec(x_10);
x_195 = lean::cnstr_get(x_188, 0);
lean::inc(x_195);
lean::dec(x_188);
if (lean::is_scalar(x_185)) {
 x_198 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_198 = x_185;
}
lean::cnstr_set(x_198, 0, x_195);
x_58 = x_198;
x_59 = x_190;
goto lbl_60;
}
else
{
obj* x_200; obj* x_203; obj* x_204; obj* x_206; 
lean::dec(x_188);
x_200 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__9;
lean::inc(x_2);
lean::inc(x_200);
x_203 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_200, x_2, x_190);
x_204 = lean::cnstr_get(x_203, 0);
lean::inc(x_204);
x_206 = lean::cnstr_get(x_203, 1);
lean::inc(x_206);
lean::dec(x_203);
if (lean::obj_tag(x_204) == 0)
{
obj* x_211; obj* x_214; 
lean::dec(x_51);
lean::dec(x_10);
x_211 = lean::cnstr_get(x_204, 0);
lean::inc(x_211);
lean::dec(x_204);
if (lean::is_scalar(x_185)) {
 x_214 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_214 = x_185;
}
lean::cnstr_set(x_214, 0, x_211);
x_58 = x_214;
x_59 = x_206;
goto lbl_60;
}
else
{
obj* x_217; obj* x_218; obj* x_220; 
lean::dec(x_204);
lean::inc(x_2);
x_217 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid(x_10, x_2, x_206);
x_218 = lean::cnstr_get(x_217, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get(x_217, 1);
lean::inc(x_220);
lean::dec(x_217);
if (lean::obj_tag(x_218) == 0)
{
obj* x_224; obj* x_227; 
lean::dec(x_51);
x_224 = lean::cnstr_get(x_218, 0);
lean::inc(x_224);
lean::dec(x_218);
if (lean::is_scalar(x_185)) {
 x_227 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_227 = x_185;
}
lean::cnstr_set(x_227, 0, x_224);
x_58 = x_227;
x_59 = x_220;
goto lbl_60;
}
else
{
obj* x_229; obj* x_232; obj* x_233; obj* x_235; 
lean::dec(x_218);
x_229 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__8;
lean::inc(x_2);
lean::inc(x_229);
x_232 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_229, x_2, x_220);
x_233 = lean::cnstr_get(x_232, 0);
lean::inc(x_233);
x_235 = lean::cnstr_get(x_232, 1);
lean::inc(x_235);
lean::dec(x_232);
if (lean::obj_tag(x_233) == 0)
{
obj* x_239; obj* x_242; 
lean::dec(x_51);
x_239 = lean::cnstr_get(x_233, 0);
lean::inc(x_239);
lean::dec(x_233);
if (lean::is_scalar(x_185)) {
 x_242 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_242 = x_185;
}
lean::cnstr_set(x_242, 0, x_239);
x_58 = x_242;
x_59 = x_235;
goto lbl_60;
}
else
{
obj* x_246; obj* x_247; obj* x_249; 
lean::dec(x_233);
lean::dec(x_185);
lean::inc(x_2);
x_246 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid(x_51, x_2, x_235);
x_247 = lean::cnstr_get(x_246, 0);
lean::inc(x_247);
x_249 = lean::cnstr_get(x_246, 1);
lean::inc(x_249);
lean::dec(x_246);
x_58 = x_247;
x_59 = x_249;
goto lbl_60;
}
}
}
}
}
}
case 4:
{
obj* x_255; 
lean::dec(x_51);
lean::dec(x_10);
lean::dec(x_0);
x_255 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5;
lean::inc(x_255);
x_58 = x_255;
x_59 = x_3;
goto lbl_60;
}
case 5:
{
obj* x_260; 
lean::dec(x_51);
lean::dec(x_10);
lean::dec(x_0);
x_260 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5;
lean::inc(x_260);
x_58 = x_260;
x_59 = x_3;
goto lbl_60;
}
case 6:
{
obj* x_265; 
lean::dec(x_51);
lean::dec(x_10);
lean::dec(x_0);
x_265 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5;
lean::inc(x_265);
x_58 = x_265;
x_59 = x_3;
goto lbl_60;
}
case 7:
{
obj* x_270; 
lean::dec(x_51);
lean::dec(x_10);
lean::dec(x_0);
x_270 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5;
lean::inc(x_270);
x_58 = x_270;
x_59 = x_3;
goto lbl_60;
}
case 8:
{
obj* x_275; 
lean::dec(x_51);
lean::dec(x_10);
lean::dec(x_0);
x_275 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5;
lean::inc(x_275);
x_58 = x_275;
x_59 = x_3;
goto lbl_60;
}
case 9:
{
obj* x_280; 
lean::dec(x_51);
lean::dec(x_10);
lean::dec(x_0);
x_280 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5;
lean::inc(x_280);
x_58 = x_280;
x_59 = x_3;
goto lbl_60;
}
case 10:
{
obj* x_285; 
lean::dec(x_51);
lean::dec(x_10);
lean::dec(x_0);
x_285 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5;
lean::inc(x_285);
x_58 = x_285;
x_59 = x_3;
goto lbl_60;
}
default:
{
obj* x_290; 
lean::dec(x_51);
lean::dec(x_10);
lean::dec(x_0);
x_290 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5;
lean::inc(x_290);
x_58 = x_290;
x_59 = x_3;
goto lbl_60;
}
}
}
lbl_60:
{

if (lean::obj_tag(x_58) == 0)
{
obj* x_293; obj* x_295; obj* x_296; obj* x_297; 
lean::dec(x_2);
x_293 = lean::cnstr_get(x_58, 0);
lean::inc(x_293);
if (lean::is_shared(x_58)) {
 lean::dec(x_58);
 x_295 = lean::box(0);
} else {
 lean::cnstr_release(x_58, 0);
 x_295 = x_58;
}
if (lean::is_scalar(x_295)) {
 x_296 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_296 = x_295;
}
lean::cnstr_set(x_296, 0, x_293);
x_297 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_297, 0, x_296);
lean::cnstr_set(x_297, 1, x_59);
return x_297;
}
else
{
obj* x_299; 
lean::dec(x_58);
x_299 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos(x_2, x_59);
return x_299;
}
}
}
else
{
unsigned char x_303; 
lean::dec(x_51);
lean::dec(x_53);
lean::dec(x_10);
x_303 = 0;
x_7 = x_303;
goto lbl_8;
}
}
}
lbl_6:
{

if (lean::obj_tag(x_4) == 0)
{
obj* x_306; obj* x_308; obj* x_309; obj* x_310; 
lean::dec(x_1);
lean::dec(x_2);
x_306 = lean::cnstr_get(x_4, 0);
lean::inc(x_306);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_308 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_308 = x_4;
}
if (lean::is_scalar(x_308)) {
 x_309 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_309 = x_308;
}
lean::cnstr_set(x_309, 0, x_306);
x_310 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_310, 0, x_309);
lean::cnstr_set(x_310, 1, x_5);
return x_310;
}
else
{
obj* x_311; obj* x_312; obj* x_315; obj* x_316; obj* x_318; obj* x_320; 
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_311 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_311 = x_4;
}
x_312 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__1;
lean::inc(x_2);
lean::inc(x_312);
x_315 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_312, x_2, x_5);
x_316 = lean::cnstr_get(x_315, 0);
lean::inc(x_316);
x_318 = lean::cnstr_get(x_315, 1);
lean::inc(x_318);
if (lean::is_shared(x_315)) {
 lean::dec(x_315);
 x_320 = lean::box(0);
} else {
 lean::cnstr_release(x_315, 0);
 lean::cnstr_release(x_315, 1);
 x_320 = x_315;
}
if (lean::obj_tag(x_316) == 0)
{
obj* x_323; obj* x_326; obj* x_327; 
lean::dec(x_1);
lean::dec(x_2);
x_323 = lean::cnstr_get(x_316, 0);
lean::inc(x_323);
lean::dec(x_316);
if (lean::is_scalar(x_311)) {
 x_326 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_326 = x_311;
}
lean::cnstr_set(x_326, 0, x_323);
if (lean::is_scalar(x_320)) {
 x_327 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_327 = x_320;
}
lean::cnstr_set(x_327, 0, x_326);
lean::cnstr_set(x_327, 1, x_318);
return x_327;
}
else
{
obj* x_329; obj* x_332; obj* x_333; obj* x_335; 
lean::dec(x_316);
x_329 = _l_s4_lean_s6_format_s2_be_s6___main_s11___closed__1;
lean::inc(x_2);
lean::inc(x_329);
x_332 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_329, x_2, x_318);
x_333 = lean::cnstr_get(x_332, 0);
lean::inc(x_333);
x_335 = lean::cnstr_get(x_332, 1);
lean::inc(x_335);
lean::dec(x_332);
if (lean::obj_tag(x_333) == 0)
{
obj* x_341; obj* x_344; obj* x_345; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_329);
x_341 = lean::cnstr_get(x_333, 0);
lean::inc(x_341);
lean::dec(x_333);
if (lean::is_scalar(x_311)) {
 x_344 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_344 = x_311;
}
lean::cnstr_set(x_344, 0, x_341);
if (lean::is_scalar(x_320)) {
 x_345 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_345 = x_320;
}
lean::cnstr_set(x_345, 0, x_344);
lean::cnstr_set(x_345, 1, x_335);
return x_345;
}
else
{
obj* x_347; obj* x_349; obj* x_350; obj* x_352; 
lean::dec(x_333);
x_347 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_349 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main(x_1, x_347, x_2, x_335);
x_350 = lean::cnstr_get(x_349, 0);
lean::inc(x_350);
x_352 = lean::cnstr_get(x_349, 1);
lean::inc(x_352);
lean::dec(x_349);
if (lean::obj_tag(x_350) == 0)
{
obj* x_357; obj* x_360; obj* x_361; 
lean::dec(x_2);
lean::dec(x_329);
x_357 = lean::cnstr_get(x_350, 0);
lean::inc(x_357);
lean::dec(x_350);
if (lean::is_scalar(x_311)) {
 x_360 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_360 = x_311;
}
lean::cnstr_set(x_360, 0, x_357);
if (lean::is_scalar(x_320)) {
 x_361 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_361 = x_320;
}
lean::cnstr_set(x_361, 0, x_360);
lean::cnstr_set(x_361, 1, x_352);
return x_361;
}
else
{
obj* x_363; obj* x_366; obj* x_367; obj* x_369; 
lean::dec(x_350);
x_363 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__2;
lean::inc(x_2);
lean::inc(x_363);
x_366 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_363, x_2, x_352);
x_367 = lean::cnstr_get(x_366, 0);
lean::inc(x_367);
x_369 = lean::cnstr_get(x_366, 1);
lean::inc(x_369);
lean::dec(x_366);
if (lean::obj_tag(x_367) == 0)
{
obj* x_374; obj* x_377; obj* x_378; 
lean::dec(x_2);
lean::dec(x_329);
x_374 = lean::cnstr_get(x_367, 0);
lean::inc(x_374);
lean::dec(x_367);
if (lean::is_scalar(x_311)) {
 x_377 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_377 = x_311;
}
lean::cnstr_set(x_377, 0, x_374);
if (lean::is_scalar(x_320)) {
 x_378 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_378 = x_320;
}
lean::cnstr_set(x_378, 0, x_377);
lean::cnstr_set(x_378, 1, x_369);
return x_378;
}
else
{
obj* x_383; 
lean::dec(x_320);
lean::dec(x_367);
lean::dec(x_311);
lean::inc(x_329);
x_383 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_329, x_2, x_369);
return x_383;
}
}
}
}
}
}
lbl_8:
{
obj* x_384; obj* x_387; obj* x_388; obj* x_390; obj* x_392; 
x_384 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__3;
lean::inc(x_2);
lean::inc(x_384);
x_387 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_384, x_2, x_3);
x_388 = lean::cnstr_get(x_387, 0);
lean::inc(x_388);
x_390 = lean::cnstr_get(x_387, 1);
lean::inc(x_390);
if (lean::is_shared(x_387)) {
 lean::dec(x_387);
 x_392 = lean::box(0);
} else {
 lean::cnstr_release(x_387, 0);
 lean::cnstr_release(x_387, 1);
 x_392 = x_387;
}
if (lean::obj_tag(x_388) == 0)
{
obj* x_396; obj* x_398; obj* x_399; obj* x_400; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
x_396 = lean::cnstr_get(x_388, 0);
lean::inc(x_396);
if (lean::is_shared(x_388)) {
 lean::dec(x_388);
 x_398 = lean::box(0);
} else {
 lean::cnstr_release(x_388, 0);
 x_398 = x_388;
}
if (lean::is_scalar(x_398)) {
 x_399 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_399 = x_398;
}
lean::cnstr_set(x_399, 0, x_396);
if (lean::is_scalar(x_392)) {
 x_400 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_400 = x_392;
}
lean::cnstr_set(x_400, 0, x_399);
lean::cnstr_set(x_400, 1, x_390);
return x_400;
}
else
{
obj* x_402; obj* x_403; obj* x_406; obj* x_407; obj* x_409; 
lean::dec(x_392);
if (lean::is_shared(x_388)) {
 lean::dec(x_388);
 x_402 = lean::box(0);
} else {
 lean::cnstr_release(x_388, 0);
 x_402 = x_388;
}
x_403 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_2);
lean::inc(x_403);
x_406 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_403, x_2, x_390);
x_407 = lean::cnstr_get(x_406, 0);
lean::inc(x_407);
x_409 = lean::cnstr_get(x_406, 1);
lean::inc(x_409);
lean::dec(x_406);
if (lean::obj_tag(x_407) == 0)
{
obj* x_413; obj* x_416; 
lean::dec(x_0);
x_413 = lean::cnstr_get(x_407, 0);
lean::inc(x_413);
lean::dec(x_407);
if (lean::is_scalar(x_402)) {
 x_416 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_416 = x_402;
}
lean::cnstr_set(x_416, 0, x_413);
x_4 = x_416;
x_5 = x_409;
goto lbl_6;
}
else
{
obj* x_419; obj* x_420; obj* x_422; 
lean::dec(x_407);
lean::inc(x_2);
x_419 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_2, x_409);
x_420 = lean::cnstr_get(x_419, 0);
lean::inc(x_420);
x_422 = lean::cnstr_get(x_419, 1);
lean::inc(x_422);
lean::dec(x_419);
if (lean::obj_tag(x_420) == 0)
{
obj* x_425; obj* x_428; 
x_425 = lean::cnstr_get(x_420, 0);
lean::inc(x_425);
lean::dec(x_420);
if (lean::is_scalar(x_402)) {
 x_428 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_428 = x_402;
}
lean::cnstr_set(x_428, 0, x_425);
x_4 = x_428;
x_5 = x_422;
goto lbl_6;
}
else
{
obj* x_429; obj* x_432; obj* x_435; obj* x_436; obj* x_438; 
x_429 = lean::cnstr_get(x_420, 0);
lean::inc(x_429);
lean::dec(x_420);
x_432 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_2);
lean::inc(x_432);
x_435 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_432, x_2, x_422);
x_436 = lean::cnstr_get(x_435, 0);
lean::inc(x_436);
x_438 = lean::cnstr_get(x_435, 1);
lean::inc(x_438);
lean::dec(x_435);
if (lean::obj_tag(x_436) == 0)
{
obj* x_442; obj* x_445; 
lean::dec(x_429);
x_442 = lean::cnstr_get(x_436, 0);
lean::inc(x_442);
lean::dec(x_436);
if (lean::is_scalar(x_402)) {
 x_445 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_445 = x_402;
}
lean::cnstr_set(x_445, 0, x_442);
x_4 = x_445;
x_5 = x_438;
goto lbl_6;
}
else
{
obj* x_447; 
lean::dec(x_436);
if (lean::is_scalar(x_402)) {
 x_447 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_447 = x_402;
}
lean::cnstr_set(x_447, 0, x_429);
x_4 = x_447;
x_5 = x_438;
goto lbl_6;
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string(" {");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("}");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string("switch ");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string("goto ");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("ill-formed case");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__6() {
{
obj* x_0; 
x_0 = lean::mk_string("if (");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__7() {
{
obj* x_0; 
x_0 = lean::mk_string(") goto ");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__8() {
{
obj* x_0; 
x_0 = lean::mk_string("; else goto ");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__9() {
{
obj* x_0; 
x_0 = lean::mk_string(" == 0) goto ");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__case(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; 
x_4 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__terminator(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_14; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__terminator_s11___closed__1;
lean::inc(x_1);
lean::inc(x_8);
x_11 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_8, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_6);
lean::dec(x_1);
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_21 = x_12;
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_19);
x_3 = x_22;
x_4 = x_14;
goto lbl_5;
}
else
{
obj* x_23; obj* x_25; obj* x_26; obj* x_28; 
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_23 = x_12;
}
lean::inc(x_1);
x_25 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_6, x_1, x_14);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_32; obj* x_35; 
lean::dec(x_1);
x_32 = lean::cnstr_get(x_26, 0);
lean::inc(x_32);
lean::dec(x_26);
if (lean::is_scalar(x_23)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_23;
}
lean::cnstr_set(x_35, 0, x_32);
x_3 = x_35;
x_4 = x_28;
goto lbl_5;
}
else
{
obj* x_38; obj* x_39; obj* x_41; 
lean::dec(x_26);
lean::dec(x_23);
x_38 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos(x_1, x_28);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
x_3 = x_39;
x_4 = x_41;
goto lbl_5;
}
}
}
case 1:
{
obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_51; 
x_44 = lean::cnstr_get(x_0, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_0, 1);
lean::inc(x_46);
x_48 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main(x_44, x_46, x_1, x_2);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
x_3 = x_49;
x_4 = x_51;
goto lbl_5;
}
default:
{
obj* x_54; obj* x_56; obj* x_59; obj* x_60; obj* x_62; 
x_54 = lean::cnstr_get(x_0, 0);
lean::inc(x_54);
x_56 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__4;
lean::inc(x_1);
lean::inc(x_56);
x_59 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_56, x_1, x_2);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_60) == 0)
{
obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_1);
lean::dec(x_54);
x_67 = lean::cnstr_get(x_60, 0);
lean::inc(x_67);
if (lean::is_shared(x_60)) {
 lean::dec(x_60);
 x_69 = lean::box(0);
} else {
 lean::cnstr_release(x_60, 0);
 x_69 = x_60;
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_67);
x_3 = x_70;
x_4 = x_62;
goto lbl_5;
}
else
{
obj* x_71; obj* x_73; obj* x_74; obj* x_76; 
if (lean::is_shared(x_60)) {
 lean::dec(x_60);
 x_71 = lean::box(0);
} else {
 lean::cnstr_release(x_60, 0);
 x_71 = x_60;
}
lean::inc(x_1);
x_73 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid(x_54, x_1, x_62);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_80; obj* x_83; 
lean::dec(x_1);
x_80 = lean::cnstr_get(x_74, 0);
lean::inc(x_80);
lean::dec(x_74);
if (lean::is_scalar(x_71)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_71;
}
lean::cnstr_set(x_83, 0, x_80);
x_3 = x_83;
x_4 = x_76;
goto lbl_5;
}
else
{
obj* x_86; obj* x_87; obj* x_89; 
lean::dec(x_71);
lean::dec(x_74);
x_86 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos(x_1, x_76);
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_86, 1);
lean::inc(x_89);
lean::dec(x_86);
x_3 = x_87;
x_4 = x_89;
goto lbl_5;
}
}
}
}
lbl_5:
{

if (lean::obj_tag(x_3) == 0)
{
obj* x_92; obj* x_94; obj* x_95; unsigned char x_96; obj* x_97; obj* x_99; obj* x_100; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_92 = lean::cnstr_get(x_3, 0);
lean::inc(x_92);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_94 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_94 = x_3;
}
x_95 = _l_s4_lean_s2_ir_s10_terminator_s10_to__format_s6___main(x_0);
x_96 = 0;
x_97 = _l_s4_lean_s2_ir_s10_terminator_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_97);
x_99 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_99, 0, x_97);
lean::cnstr_set(x_99, 1, x_95);
lean::cnstr_set_scalar(x_99, sizeof(void*)*2, x_96);
x_100 = x_99;
x_101 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_101);
x_103 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_103, 0, x_100);
lean::cnstr_set(x_103, 1, x_101);
lean::cnstr_set_scalar(x_103, sizeof(void*)*2, x_96);
x_104 = x_103;
x_105 = lean::alloc_cnstr(1, 0, 0);
;
x_106 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_106, 0, x_104);
lean::cnstr_set(x_106, 1, x_105);
lean::cnstr_set_scalar(x_106, sizeof(void*)*2, x_96);
x_107 = x_106;
x_108 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_92);
lean::cnstr_set_scalar(x_108, sizeof(void*)*2, x_96);
x_109 = x_108;
if (lean::is_scalar(x_94)) {
 x_110 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_110 = x_94;
}
lean::cnstr_set(x_110, 0, x_109);
x_111 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_4);
return x_111;
}
else
{
obj* x_113; 
lean::dec(x_0);
x_113 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_113, 0, x_3);
lean::cnstr_set(x_113, 1, x_4);
return x_113;
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__terminator_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("return ");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__type__size(unsigned char x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__type__size_s11___closed__1;
lean::inc(x_1);
lean::inc(x_3);
x_6 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_3, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
x_13 = lean::cnstr_get(x_7, 0);
lean::inc(x_13);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_15 = x_7;
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
if (lean::is_scalar(x_11)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_11;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_9);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_25; 
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_18 = x_7;
}
x_19 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_19);
x_22 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_19, x_1, x_9);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_29 = lean::cnstr_get(x_23, 0);
lean::inc(x_29);
lean::dec(x_23);
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_18;
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_11)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_11;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_25);
return x_33;
}
else
{
obj* x_36; obj* x_37; obj* x_39; 
lean::dec(x_23);
lean::inc(x_1);
x_36 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__type(x_0, x_1, x_25);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
if (lean::obj_tag(x_37) == 0)
{
obj* x_43; obj* x_46; obj* x_47; 
lean::dec(x_1);
x_43 = lean::cnstr_get(x_37, 0);
lean::inc(x_43);
lean::dec(x_37);
if (lean::is_scalar(x_18)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_18;
}
lean::cnstr_set(x_46, 0, x_43);
if (lean::is_scalar(x_11)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_11;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_39);
return x_47;
}
else
{
obj* x_48; obj* x_51; obj* x_53; obj* x_54; obj* x_56; 
x_48 = lean::cnstr_get(x_37, 0);
lean::inc(x_48);
lean::dec(x_37);
x_51 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_51);
x_53 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_51, x_1, x_39);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
lean::dec(x_53);
if (lean::obj_tag(x_54) == 0)
{
obj* x_60; obj* x_63; obj* x_64; 
lean::dec(x_48);
x_60 = lean::cnstr_get(x_54, 0);
lean::inc(x_60);
lean::dec(x_54);
if (lean::is_scalar(x_18)) {
 x_63 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_63 = x_18;
}
lean::cnstr_set(x_63, 0, x_60);
if (lean::is_scalar(x_11)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_11;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_56);
return x_64;
}
else
{
obj* x_66; obj* x_67; 
lean::dec(x_54);
if (lean::is_scalar(x_18)) {
 x_66 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_66 = x_18;
}
lean::cnstr_set(x_66, 0, x_48);
if (lean::is_scalar(x_11)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_11;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_56);
return x_67;
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__type__size_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("sizeof");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__type__size_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__type__size(x_3, x_1, x_2);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__op__x(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::inc(x_2);
x_5 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_0, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_25; 
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
}
x_19 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_2);
lean::inc(x_19);
x_22 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_19, x_2, x_8);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_33; obj* x_34; 
lean::dec(x_1);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
if (lean::is_scalar(x_18)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_18;
}
lean::cnstr_set(x_33, 0, x_30);
if (lean::is_scalar(x_10)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_10;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_25);
return x_34;
}
else
{
obj* x_37; obj* x_38; obj* x_40; 
lean::dec(x_23);
lean::inc(x_2);
x_37 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_1, x_2, x_25);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_44; obj* x_47; obj* x_48; 
lean::dec(x_2);
x_44 = lean::cnstr_get(x_38, 0);
lean::inc(x_44);
lean::dec(x_38);
if (lean::is_scalar(x_18)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_18;
}
lean::cnstr_set(x_47, 0, x_44);
if (lean::is_scalar(x_10)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_10;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_40);
return x_48;
}
else
{
obj* x_49; obj* x_52; obj* x_54; obj* x_55; obj* x_57; 
x_49 = lean::cnstr_get(x_38, 0);
lean::inc(x_49);
lean::dec(x_38);
x_52 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_52);
x_54 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_52, x_2, x_40);
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
if (lean::obj_tag(x_55) == 0)
{
obj* x_61; obj* x_64; obj* x_65; 
lean::dec(x_49);
x_61 = lean::cnstr_get(x_55, 0);
lean::inc(x_61);
lean::dec(x_55);
if (lean::is_scalar(x_18)) {
 x_64 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_64 = x_18;
}
lean::cnstr_set(x_64, 0, x_61);
if (lean::is_scalar(x_10)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_10;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_57);
return x_65;
}
else
{
obj* x_67; obj* x_68; 
lean::dec(x_55);
if (lean::is_scalar(x_18)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_18;
}
lean::cnstr_set(x_67, 0, x_49);
if (lean::is_scalar(x_10)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_10;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_57);
return x_68;
}
}
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_13; 
lean::inc(x_4);
x_10 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_4, x_5);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_18 = x_11;
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
x_6 = x_19;
x_7 = x_13;
goto lbl_8;
}
else
{
obj* x_21; obj* x_24; obj* x_25; obj* x_27; 
lean::dec(x_11);
x_21 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1;
lean::inc(x_4);
lean::inc(x_21);
x_24 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_21, x_4, x_13);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_6 = x_25;
x_7 = x_27;
goto lbl_8;
}
lbl_8:
{

if (lean::obj_tag(x_6) == 0)
{
obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_34 = lean::cnstr_get(x_6, 0);
lean::inc(x_34);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_36 = x_6;
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_7);
return x_38;
}
else
{
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; 
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_39 = x_6;
}
lean::inc(x_4);
x_41 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_1, x_4, x_7);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
if (lean::is_shared(x_41)) {
 lean::dec(x_41);
 x_46 = lean::box(0);
} else {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 x_46 = x_41;
}
if (lean::obj_tag(x_42) == 0)
{
obj* x_50; obj* x_53; obj* x_54; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_3);
x_50 = lean::cnstr_get(x_42, 0);
lean::inc(x_50);
lean::dec(x_42);
if (lean::is_scalar(x_39)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_39;
}
lean::cnstr_set(x_53, 0, x_50);
if (lean::is_scalar(x_46)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_46;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_44);
return x_54;
}
else
{
obj* x_56; obj* x_59; obj* x_60; obj* x_62; 
lean::dec(x_42);
x_56 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_4);
lean::inc(x_56);
x_59 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_56, x_4, x_44);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_60) == 0)
{
obj* x_69; obj* x_72; obj* x_73; 
lean::dec(x_56);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_3);
x_69 = lean::cnstr_get(x_60, 0);
lean::inc(x_69);
lean::dec(x_60);
if (lean::is_scalar(x_39)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_39;
}
lean::cnstr_set(x_72, 0, x_69);
if (lean::is_scalar(x_46)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_46;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_62);
return x_73;
}
else
{
obj* x_76; obj* x_77; obj* x_79; 
lean::dec(x_60);
lean::inc(x_4);
x_76 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_3, x_4, x_62);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
if (lean::obj_tag(x_77) == 0)
{
obj* x_85; obj* x_88; obj* x_89; 
lean::dec(x_56);
lean::dec(x_4);
lean::dec(x_2);
x_85 = lean::cnstr_get(x_77, 0);
lean::inc(x_85);
lean::dec(x_77);
if (lean::is_scalar(x_39)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_39;
}
lean::cnstr_set(x_88, 0, x_85);
if (lean::is_scalar(x_46)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_46;
}
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_79);
return x_89;
}
else
{
obj* x_93; obj* x_94; obj* x_96; 
lean::dec(x_77);
lean::inc(x_4);
lean::inc(x_56);
x_93 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_56, x_4, x_79);
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_93, 1);
lean::inc(x_96);
lean::dec(x_93);
if (lean::obj_tag(x_94) == 0)
{
obj* x_101; obj* x_104; obj* x_105; 
lean::dec(x_4);
lean::dec(x_2);
x_101 = lean::cnstr_get(x_94, 0);
lean::inc(x_101);
lean::dec(x_94);
if (lean::is_scalar(x_39)) {
 x_104 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_104 = x_39;
}
lean::cnstr_set(x_104, 0, x_101);
if (lean::is_scalar(x_46)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_46;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_96);
return x_105;
}
else
{
obj* x_109; 
lean::dec(x_94);
lean::dec(x_46);
lean::dec(x_39);
x_109 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_2, x_4, x_96);
return x_109;
}
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string(" = ");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__big__binop(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_13; 
lean::inc(x_4);
x_10 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_4, x_5);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_3);
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_19 = x_11;
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
x_6 = x_20;
x_7 = x_13;
goto lbl_8;
}
else
{
obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_28; 
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_21 = x_11;
}
x_22 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1;
lean::inc(x_4);
lean::inc(x_22);
x_25 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_22, x_4, x_13);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_32; obj* x_35; 
lean::dec(x_3);
x_32 = lean::cnstr_get(x_26, 0);
lean::inc(x_32);
lean::dec(x_26);
if (lean::is_scalar(x_21)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_21;
}
lean::cnstr_set(x_35, 0, x_32);
x_6 = x_35;
x_7 = x_28;
goto lbl_8;
}
else
{
obj* x_39; obj* x_40; obj* x_42; 
lean::dec(x_21);
lean::dec(x_26);
lean::inc(x_4);
x_39 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_3, x_4, x_28);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
x_6 = x_40;
x_7 = x_42;
goto lbl_8;
}
}
lbl_8:
{

if (lean::obj_tag(x_6) == 0)
{
obj* x_48; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
x_48 = lean::cnstr_get(x_6, 0);
lean::inc(x_48);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_50 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_50 = x_6;
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_7);
return x_52;
}
else
{
obj* x_53; obj* x_54; obj* x_57; obj* x_58; obj* x_60; obj* x_62; 
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_53 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_53 = x_6;
}
x_54 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_4);
lean::inc(x_54);
x_57 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_54, x_4, x_7);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
if (lean::is_shared(x_57)) {
 lean::dec(x_57);
 x_62 = lean::box(0);
} else {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_62 = x_57;
}
if (lean::obj_tag(x_58) == 0)
{
obj* x_66; obj* x_69; obj* x_70; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
x_66 = lean::cnstr_get(x_58, 0);
lean::inc(x_66);
lean::dec(x_58);
if (lean::is_scalar(x_53)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_53;
}
lean::cnstr_set(x_69, 0, x_66);
if (lean::is_scalar(x_62)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_62;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_60);
return x_70;
}
else
{
obj* x_73; obj* x_74; obj* x_76; 
lean::dec(x_58);
lean::inc(x_4);
x_73 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_1, x_4, x_60);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_81; obj* x_84; obj* x_85; 
lean::dec(x_4);
lean::dec(x_2);
x_81 = lean::cnstr_get(x_74, 0);
lean::inc(x_81);
lean::dec(x_74);
if (lean::is_scalar(x_53)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_53;
}
lean::cnstr_set(x_84, 0, x_81);
if (lean::is_scalar(x_62)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_62;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_76);
return x_85;
}
else
{
obj* x_87; obj* x_90; obj* x_91; obj* x_93; 
lean::dec(x_74);
x_87 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_4);
lean::inc(x_87);
x_90 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_87, x_4, x_76);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
if (lean::obj_tag(x_91) == 0)
{
obj* x_98; obj* x_101; obj* x_102; 
lean::dec(x_4);
lean::dec(x_2);
x_98 = lean::cnstr_get(x_91, 0);
lean::inc(x_98);
lean::dec(x_91);
if (lean::is_scalar(x_53)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_53;
}
lean::cnstr_set(x_101, 0, x_98);
if (lean::is_scalar(x_62)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_62;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_93);
return x_102;
}
else
{
obj* x_105; obj* x_106; obj* x_108; 
lean::dec(x_91);
lean::inc(x_4);
x_105 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_2, x_4, x_93);
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_105, 1);
lean::inc(x_108);
lean::dec(x_105);
if (lean::obj_tag(x_106) == 0)
{
obj* x_112; obj* x_115; obj* x_116; 
lean::dec(x_4);
x_112 = lean::cnstr_get(x_106, 0);
lean::inc(x_112);
lean::dec(x_106);
if (lean::is_scalar(x_53)) {
 x_115 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_115 = x_53;
}
lean::cnstr_set(x_115, 0, x_112);
if (lean::is_scalar(x_62)) {
 x_116 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_116 = x_62;
}
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_108);
return x_116;
}
else
{
obj* x_117; obj* x_120; obj* x_122; obj* x_123; obj* x_125; 
x_117 = lean::cnstr_get(x_106, 0);
lean::inc(x_117);
lean::dec(x_106);
x_120 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_120);
x_122 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_120, x_4, x_108);
x_123 = lean::cnstr_get(x_122, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_122, 1);
lean::inc(x_125);
lean::dec(x_122);
if (lean::obj_tag(x_123) == 0)
{
obj* x_129; obj* x_132; obj* x_133; 
lean::dec(x_117);
x_129 = lean::cnstr_get(x_123, 0);
lean::inc(x_129);
lean::dec(x_123);
if (lean::is_scalar(x_53)) {
 x_132 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_132 = x_53;
}
lean::cnstr_set(x_132, 0, x_129);
if (lean::is_scalar(x_62)) {
 x_133 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_133 = x_62;
}
lean::cnstr_set(x_133, 0, x_132);
lean::cnstr_set(x_133, 1, x_125);
return x_133;
}
else
{
obj* x_135; obj* x_136; 
lean::dec(x_123);
if (lean::is_scalar(x_53)) {
 x_135 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_135 = x_53;
}
lean::cnstr_set(x_135, 0, x_117);
if (lean::is_scalar(x_62)) {
 x_136 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_136 = x_62;
}
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_125);
return x_136;
}
}
}
}
}
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith(unsigned char x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
{

switch (x_0) {
case 0:
{
obj* x_9; 
lean::dec(x_5);
x_9 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_9;
}
case 1:
{
obj* x_11; 
lean::dec(x_5);
x_11 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_11;
}
case 2:
{
obj* x_13; 
lean::dec(x_5);
x_13 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_13;
}
case 3:
{
obj* x_15; 
lean::dec(x_5);
x_15 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_15;
}
case 4:
{
obj* x_17; 
lean::dec(x_5);
x_17 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_17;
}
case 5:
{
obj* x_19; 
lean::dec(x_5);
x_19 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_19;
}
case 6:
{
obj* x_21; 
lean::dec(x_5);
x_21 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_21;
}
case 7:
{
obj* x_23; 
lean::dec(x_5);
x_23 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_23;
}
case 8:
{
obj* x_25; 
lean::dec(x_5);
x_25 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_25;
}
case 9:
{
obj* x_27; 
lean::dec(x_5);
x_27 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_27;
}
case 10:
{
obj* x_29; 
lean::dec(x_5);
x_29 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_29;
}
default:
{
obj* x_31; 
lean::dec(x_4);
x_31 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__big__binop(x_1, x_2, x_3, x_5, x_6, x_7);
return x_31;
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
{
unsigned char x_8; obj* x_9; 
x_8 = lean::unbox(x_0);
x_9 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s20_emit__logical__arith(unsigned char x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
{

switch (x_0) {
case 0:
{
obj* x_11; 
lean::dec(x_5);
lean::dec(x_6);
x_11 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_4, x_7, x_8);
return x_11;
}
case 1:
{
obj* x_14; 
lean::dec(x_4);
lean::dec(x_6);
x_14 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_14;
}
case 2:
{
obj* x_17; 
lean::dec(x_4);
lean::dec(x_6);
x_17 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_17;
}
case 3:
{
obj* x_20; 
lean::dec(x_4);
lean::dec(x_6);
x_20 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_20;
}
case 4:
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_6);
x_23 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_23;
}
case 5:
{
obj* x_26; 
lean::dec(x_4);
lean::dec(x_6);
x_26 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_26;
}
case 6:
{
obj* x_29; 
lean::dec(x_4);
lean::dec(x_6);
x_29 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_29;
}
case 7:
{
obj* x_32; 
lean::dec(x_4);
lean::dec(x_6);
x_32 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_32;
}
case 8:
{
obj* x_35; 
lean::dec(x_4);
lean::dec(x_6);
x_35 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_35;
}
case 9:
{
obj* x_38; 
lean::dec(x_4);
lean::dec(x_6);
x_38 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_38;
}
case 10:
{
obj* x_41; 
lean::dec(x_4);
lean::dec(x_6);
x_41 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_41;
}
default:
{
obj* x_44; 
lean::dec(x_4);
lean::dec(x_5);
x_44 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__big__binop(x_1, x_2, x_3, x_6, x_7, x_8);
return x_44;
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s20_emit__logical__arith_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
{
unsigned char x_9; obj* x_10; 
x_9 = lean::unbox(x_0);
x_10 = _l_s4_lean_s2_ir_s3_cpp_s20_emit__logical__arith(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop(obj* x_0, unsigned char x_1, unsigned char x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
unsigned char x_7; obj* x_9; obj* x_10; 
switch (x_2) {
case 0:
{
obj* x_12; obj* x_13; obj* x_16; 
x_12 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__2;
x_13 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__3;
lean::inc(x_13);
lean::inc(x_12);
x_16 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith(x_1, x_0, x_3, x_4, x_12, x_13, x_5, x_6);
return x_16;
}
case 1:
{
obj* x_17; obj* x_18; obj* x_21; 
x_17 = _l_s3_int_s4_repr_s6___main_s11___closed__1;
x_18 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__4;
lean::inc(x_18);
lean::inc(x_17);
x_21 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith(x_1, x_0, x_3, x_4, x_17, x_18, x_5, x_6);
return x_21;
}
case 2:
{
obj* x_22; obj* x_23; obj* x_26; 
x_22 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__5;
x_23 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__6;
lean::inc(x_23);
lean::inc(x_22);
x_26 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith(x_1, x_0, x_3, x_4, x_22, x_23, x_5, x_6);
return x_26;
}
case 3:
{
obj* x_27; obj* x_28; obj* x_31; 
x_27 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__7;
x_28 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__8;
lean::inc(x_28);
lean::inc(x_27);
x_31 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith(x_1, x_0, x_3, x_4, x_27, x_28, x_5, x_6);
return x_31;
}
case 4:
{
obj* x_32; obj* x_33; obj* x_36; 
x_32 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__9;
x_33 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__10;
lean::inc(x_33);
lean::inc(x_32);
x_36 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith(x_1, x_0, x_3, x_4, x_32, x_33, x_5, x_6);
return x_36;
}
case 5:
{
obj* x_37; obj* x_39; 
x_37 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__11;
lean::inc(x_37);
x_39 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__big__binop(x_0, x_3, x_4, x_37, x_5, x_6);
return x_39;
}
case 6:
{
obj* x_40; obj* x_42; 
x_40 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__12;
lean::inc(x_40);
x_42 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__big__binop(x_0, x_3, x_4, x_40, x_5, x_6);
return x_42;
}
case 7:
{
obj* x_43; obj* x_45; 
x_43 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__13;
lean::inc(x_43);
x_45 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__big__binop(x_0, x_3, x_4, x_43, x_5, x_6);
return x_45;
}
case 8:
{
obj* x_46; obj* x_48; 
x_46 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__14;
lean::inc(x_46);
x_48 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__big__binop(x_0, x_3, x_4, x_46, x_5, x_6);
return x_48;
}
case 9:
{
obj* x_49; obj* x_51; 
x_49 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__15;
lean::inc(x_49);
x_51 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__big__binop(x_0, x_3, x_4, x_49, x_5, x_6);
return x_51;
}
case 10:
{
obj* x_52; obj* x_54; 
x_52 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__16;
lean::inc(x_52);
x_54 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_0, x_3, x_4, x_52, x_5, x_6);
return x_54;
}
case 11:
{
obj* x_55; obj* x_57; 
x_55 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__17;
lean::inc(x_55);
x_57 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix(x_0, x_3, x_4, x_55, x_5, x_6);
return x_57;
}
case 12:
{
obj* x_58; obj* x_59; obj* x_60; obj* x_64; 
x_58 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__18;
x_59 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__19;
x_60 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__20;
lean::inc(x_60);
lean::inc(x_59);
lean::inc(x_58);
x_64 = _l_s4_lean_s2_ir_s3_cpp_s20_emit__logical__arith(x_1, x_0, x_3, x_4, x_58, x_59, x_60, x_5, x_6);
return x_64;
}
case 13:
{
obj* x_65; obj* x_66; obj* x_67; obj* x_71; 
x_65 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__21;
x_66 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__22;
x_67 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__23;
lean::inc(x_67);
lean::inc(x_66);
lean::inc(x_65);
x_71 = _l_s4_lean_s2_ir_s3_cpp_s20_emit__logical__arith(x_1, x_0, x_3, x_4, x_65, x_66, x_67, x_5, x_6);
return x_71;
}
case 14:
{
obj* x_72; obj* x_73; obj* x_74; obj* x_78; 
x_72 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__24;
x_73 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__25;
x_74 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__26;
lean::inc(x_74);
lean::inc(x_73);
lean::inc(x_72);
x_78 = _l_s4_lean_s2_ir_s3_cpp_s20_emit__logical__arith(x_1, x_0, x_3, x_4, x_72, x_73, x_74, x_5, x_6);
return x_78;
}
case 15:
{
obj* x_79; obj* x_80; obj* x_83; 
x_79 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__27;
x_80 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__28;
lean::inc(x_80);
lean::inc(x_79);
x_83 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith(x_1, x_0, x_3, x_4, x_79, x_80, x_5, x_6);
return x_83;
}
case 16:
{
obj* x_84; obj* x_85; obj* x_88; 
x_84 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__1;
x_85 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__29;
lean::inc(x_85);
lean::inc(x_84);
x_88 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith(x_1, x_0, x_3, x_4, x_84, x_85, x_5, x_6);
return x_88;
}
case 17:
{
obj* x_89; obj* x_90; obj* x_93; 
x_89 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__30;
x_90 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__31;
lean::inc(x_90);
lean::inc(x_89);
x_93 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith(x_1, x_0, x_3, x_4, x_89, x_90, x_5, x_6);
return x_93;
}
case 18:
{
obj* x_94; obj* x_95; obj* x_98; 
x_94 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__24;
x_95 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__32;
lean::inc(x_95);
lean::inc(x_94);
x_98 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__arith(x_1, x_0, x_3, x_4, x_94, x_95, x_5, x_6);
return x_98;
}
case 19:
{
obj* x_99; obj* x_101; 
x_99 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__33;
lean::inc(x_99);
x_101 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__big__binop(x_0, x_3, x_4, x_99, x_5, x_6);
return x_101;
}
case 20:
{
obj* x_102; obj* x_104; 
x_102 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__34;
lean::inc(x_102);
x_104 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__big__binop(x_0, x_3, x_4, x_102, x_5, x_6);
return x_104;
}
case 21:
{
obj* x_105; obj* x_107; 
x_105 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__35;
lean::inc(x_105);
x_107 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__big__binop(x_0, x_3, x_4, x_105, x_5, x_6);
return x_107;
}
case 22:
{
obj* x_108; obj* x_110; 
x_108 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__36;
lean::inc(x_108);
x_110 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__big__binop(x_0, x_3, x_4, x_108, x_5, x_6);
return x_110;
}
case 23:
{

switch (x_1) {
case 0:
{
unsigned char x_111; 
x_111 = 0;
x_7 = x_111;
goto lbl_8;
}
case 1:
{
unsigned char x_112; 
x_112 = 0;
x_7 = x_112;
goto lbl_8;
}
case 2:
{
unsigned char x_113; 
x_113 = 0;
x_7 = x_113;
goto lbl_8;
}
case 3:
{
unsigned char x_114; 
x_114 = 0;
x_7 = x_114;
goto lbl_8;
}
case 4:
{
unsigned char x_115; 
x_115 = 0;
x_7 = x_115;
goto lbl_8;
}
case 5:
{
unsigned char x_116; 
x_116 = 0;
x_7 = x_116;
goto lbl_8;
}
case 6:
{
unsigned char x_117; 
x_117 = 0;
x_7 = x_117;
goto lbl_8;
}
case 7:
{
unsigned char x_118; 
x_118 = 0;
x_7 = x_118;
goto lbl_8;
}
case 8:
{
unsigned char x_119; 
x_119 = 0;
x_7 = x_119;
goto lbl_8;
}
case 9:
{
unsigned char x_120; 
x_120 = 0;
x_7 = x_120;
goto lbl_8;
}
case 10:
{
unsigned char x_121; 
x_121 = 0;
x_7 = x_121;
goto lbl_8;
}
default:
{
obj* x_123; obj* x_124; obj* x_126; 
lean::inc(x_5);
x_123 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_5, x_6);
x_124 = lean::cnstr_get(x_123, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_123, 1);
lean::inc(x_126);
lean::dec(x_123);
if (lean::obj_tag(x_124) == 0)
{
obj* x_129; obj* x_131; obj* x_132; 
x_129 = lean::cnstr_get(x_124, 0);
lean::inc(x_129);
if (lean::is_shared(x_124)) {
 lean::dec(x_124);
 x_131 = lean::box(0);
} else {
 lean::cnstr_release(x_124, 0);
 x_131 = x_124;
}
if (lean::is_scalar(x_131)) {
 x_132 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_132 = x_131;
}
lean::cnstr_set(x_132, 0, x_129);
x_9 = x_132;
x_10 = x_126;
goto lbl_11;
}
else
{
obj* x_134; obj* x_137; obj* x_138; obj* x_140; 
lean::dec(x_124);
x_134 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__37;
lean::inc(x_5);
lean::inc(x_134);
x_137 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_134, x_5, x_126);
x_138 = lean::cnstr_get(x_137, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_137, 1);
lean::inc(x_140);
lean::dec(x_137);
x_9 = x_138;
x_10 = x_140;
goto lbl_11;
}
}
}
}
case 24:
{
obj* x_144; obj* x_145; obj* x_147; obj* x_149; 
lean::inc(x_5);
x_144 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_5, x_6);
x_145 = lean::cnstr_get(x_144, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_144, 1);
lean::inc(x_147);
if (lean::is_shared(x_144)) {
 lean::dec(x_144);
 x_149 = lean::box(0);
} else {
 lean::cnstr_release(x_144, 0);
 lean::cnstr_release(x_144, 1);
 x_149 = x_144;
}
if (lean::obj_tag(x_145) == 0)
{
obj* x_153; obj* x_155; obj* x_156; obj* x_157; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_3);
x_153 = lean::cnstr_get(x_145, 0);
lean::inc(x_153);
if (lean::is_shared(x_145)) {
 lean::dec(x_145);
 x_155 = lean::box(0);
} else {
 lean::cnstr_release(x_145, 0);
 x_155 = x_145;
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
if (lean::is_scalar(x_149)) {
 x_157 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_157 = x_149;
}
lean::cnstr_set(x_157, 0, x_156);
lean::cnstr_set(x_157, 1, x_147);
return x_157;
}
else
{
obj* x_158; obj* x_159; obj* x_162; obj* x_163; obj* x_165; 
if (lean::is_shared(x_145)) {
 lean::dec(x_145);
 x_158 = lean::box(0);
} else {
 lean::cnstr_release(x_145, 0);
 x_158 = x_145;
}
x_159 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1;
lean::inc(x_5);
lean::inc(x_159);
x_162 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_159, x_5, x_147);
x_163 = lean::cnstr_get(x_162, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_162, 1);
lean::inc(x_165);
lean::dec(x_162);
if (lean::obj_tag(x_163) == 0)
{
obj* x_171; obj* x_174; obj* x_175; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_3);
x_171 = lean::cnstr_get(x_163, 0);
lean::inc(x_171);
lean::dec(x_163);
if (lean::is_scalar(x_158)) {
 x_174 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_174 = x_158;
}
lean::cnstr_set(x_174, 0, x_171);
if (lean::is_scalar(x_149)) {
 x_175 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_175 = x_149;
}
lean::cnstr_set(x_175, 0, x_174);
lean::cnstr_set(x_175, 1, x_165);
return x_175;
}
else
{
obj* x_179; obj* x_182; 
lean::dec(x_163);
lean::dec(x_158);
lean::dec(x_149);
x_179 = lean::cnstr_get(x_5, 1);
lean::inc(x_179);
lean::inc(x_4);
x_182 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(x_179, x_4);
if (lean::obj_tag(x_182) == 0)
{
obj* x_184; obj* x_187; obj* x_188; obj* x_190; 
lean::dec(x_182);
x_184 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__38;
lean::inc(x_5);
lean::inc(x_184);
x_187 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_184, x_5, x_165);
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
x_190 = lean::cnstr_get(x_187, 1);
lean::inc(x_190);
lean::dec(x_187);
x_9 = x_188;
x_10 = x_190;
goto lbl_11;
}
else
{
obj* x_193; unsigned char x_196; obj* x_198; obj* x_199; obj* x_200; 
x_193 = lean::cnstr_get(x_182, 0);
lean::inc(x_193);
lean::dec(x_182);
x_196 = lean::unbox(x_193);
lean::dec(x_193);
x_198 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_196);
x_199 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_200 = lean::nat_dec_eq(x_198, x_199);
lean::dec(x_198);
if (lean::obj_tag(x_200) == 0)
{
obj* x_203; obj* x_206; obj* x_207; obj* x_209; 
lean::dec(x_200);
x_203 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__38;
lean::inc(x_5);
lean::inc(x_203);
x_206 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_203, x_5, x_165);
x_207 = lean::cnstr_get(x_206, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_206, 1);
lean::inc(x_209);
lean::dec(x_206);
x_9 = x_207;
x_10 = x_209;
goto lbl_11;
}
else
{
obj* x_213; obj* x_216; obj* x_217; obj* x_219; 
lean::dec(x_200);
x_213 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__39;
lean::inc(x_5);
lean::inc(x_213);
x_216 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_213, x_5, x_165);
x_217 = lean::cnstr_get(x_216, 0);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_216, 1);
lean::inc(x_219);
lean::dec(x_216);
x_9 = x_217;
x_10 = x_219;
goto lbl_11;
}
}
}
}
}
case 25:
{
obj* x_223; obj* x_224; obj* x_226; 
lean::inc(x_5);
x_223 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_5, x_6);
x_224 = lean::cnstr_get(x_223, 0);
lean::inc(x_224);
x_226 = lean::cnstr_get(x_223, 1);
lean::inc(x_226);
lean::dec(x_223);
if (lean::obj_tag(x_224) == 0)
{
obj* x_229; obj* x_231; obj* x_232; 
x_229 = lean::cnstr_get(x_224, 0);
lean::inc(x_229);
if (lean::is_shared(x_224)) {
 lean::dec(x_224);
 x_231 = lean::box(0);
} else {
 lean::cnstr_release(x_224, 0);
 x_231 = x_224;
}
if (lean::is_scalar(x_231)) {
 x_232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_232 = x_231;
}
lean::cnstr_set(x_232, 0, x_229);
x_9 = x_232;
x_10 = x_226;
goto lbl_11;
}
else
{
obj* x_234; obj* x_237; obj* x_238; obj* x_240; 
lean::dec(x_224);
x_234 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__40;
lean::inc(x_5);
lean::inc(x_234);
x_237 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_234, x_5, x_226);
x_238 = lean::cnstr_get(x_237, 0);
lean::inc(x_238);
x_240 = lean::cnstr_get(x_237, 1);
lean::inc(x_240);
lean::dec(x_237);
x_9 = x_238;
x_10 = x_240;
goto lbl_11;
}
}
default:
{
obj* x_244; obj* x_245; obj* x_247; 
lean::inc(x_5);
x_244 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_5, x_6);
x_245 = lean::cnstr_get(x_244, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_244, 1);
lean::inc(x_247);
lean::dec(x_244);
if (lean::obj_tag(x_245) == 0)
{
obj* x_250; obj* x_252; obj* x_253; 
x_250 = lean::cnstr_get(x_245, 0);
lean::inc(x_250);
if (lean::is_shared(x_245)) {
 lean::dec(x_245);
 x_252 = lean::box(0);
} else {
 lean::cnstr_release(x_245, 0);
 x_252 = x_245;
}
if (lean::is_scalar(x_252)) {
 x_253 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_253 = x_252;
}
lean::cnstr_set(x_253, 0, x_250);
x_9 = x_253;
x_10 = x_247;
goto lbl_11;
}
else
{
obj* x_255; obj* x_258; obj* x_259; obj* x_261; 
lean::dec(x_245);
x_255 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__41;
lean::inc(x_5);
lean::inc(x_255);
x_258 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_255, x_5, x_247);
x_259 = lean::cnstr_get(x_258, 0);
lean::inc(x_259);
x_261 = lean::cnstr_get(x_258, 1);
lean::inc(x_261);
lean::dec(x_258);
x_9 = x_259;
x_10 = x_261;
goto lbl_11;
}
}
}
lbl_8:
{
obj* x_264; obj* x_265; obj* x_268; obj* x_269; obj* x_271; 
lean::inc(x_5);
x_268 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_5, x_6);
x_269 = lean::cnstr_get(x_268, 0);
lean::inc(x_269);
x_271 = lean::cnstr_get(x_268, 1);
lean::inc(x_271);
lean::dec(x_268);
if (lean::obj_tag(x_269) == 0)
{
obj* x_274; obj* x_276; obj* x_277; 
x_274 = lean::cnstr_get(x_269, 0);
lean::inc(x_274);
if (lean::is_shared(x_269)) {
 lean::dec(x_269);
 x_276 = lean::box(0);
} else {
 lean::cnstr_release(x_269, 0);
 x_276 = x_269;
}
if (lean::is_scalar(x_276)) {
 x_277 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_277 = x_276;
}
lean::cnstr_set(x_277, 0, x_274);
x_264 = x_277;
x_265 = x_271;
goto lbl_266;
}
else
{
obj* x_278; obj* x_279; obj* x_282; obj* x_283; obj* x_285; 
if (lean::is_shared(x_269)) {
 lean::dec(x_269);
 x_278 = lean::box(0);
} else {
 lean::cnstr_release(x_269, 0);
 x_278 = x_269;
}
x_279 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__1;
lean::inc(x_5);
lean::inc(x_279);
x_282 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_279, x_5, x_271);
x_283 = lean::cnstr_get(x_282, 0);
lean::inc(x_283);
x_285 = lean::cnstr_get(x_282, 1);
lean::inc(x_285);
lean::dec(x_282);
if (lean::obj_tag(x_283) == 0)
{
obj* x_288; obj* x_291; 
x_288 = lean::cnstr_get(x_283, 0);
lean::inc(x_288);
lean::dec(x_283);
if (lean::is_scalar(x_278)) {
 x_291 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_291 = x_278;
}
lean::cnstr_set(x_291, 0, x_288);
x_264 = x_291;
x_265 = x_285;
goto lbl_266;
}
else
{
obj* x_295; obj* x_296; obj* x_298; 
lean::dec(x_283);
lean::dec(x_278);
lean::inc(x_5);
x_295 = _l_s4_lean_s2_ir_s3_cpp_s21_emit__template__param(x_1, x_5, x_285);
x_296 = lean::cnstr_get(x_295, 0);
lean::inc(x_296);
x_298 = lean::cnstr_get(x_295, 1);
lean::inc(x_298);
lean::dec(x_295);
x_264 = x_296;
x_265 = x_298;
goto lbl_266;
}
}
lbl_266:
{

if (lean::obj_tag(x_264) == 0)
{
obj* x_304; obj* x_306; obj* x_307; obj* x_308; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_3);
x_304 = lean::cnstr_get(x_264, 0);
lean::inc(x_304);
if (lean::is_shared(x_264)) {
 lean::dec(x_264);
 x_306 = lean::box(0);
} else {
 lean::cnstr_release(x_264, 0);
 x_306 = x_264;
}
if (lean::is_scalar(x_306)) {
 x_307 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_307 = x_306;
}
lean::cnstr_set(x_307, 0, x_304);
x_308 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_308, 0, x_307);
lean::cnstr_set(x_308, 1, x_265);
return x_308;
}
else
{
obj* x_309; obj* x_310; obj* x_313; obj* x_314; obj* x_316; obj* x_318; 
if (lean::is_shared(x_264)) {
 lean::dec(x_264);
 x_309 = lean::box(0);
} else {
 lean::cnstr_release(x_264, 0);
 x_309 = x_264;
}
x_310 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_5);
lean::inc(x_310);
x_313 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_310, x_5, x_265);
x_314 = lean::cnstr_get(x_313, 0);
lean::inc(x_314);
x_316 = lean::cnstr_get(x_313, 1);
lean::inc(x_316);
if (lean::is_shared(x_313)) {
 lean::dec(x_313);
 x_318 = lean::box(0);
} else {
 lean::cnstr_release(x_313, 0);
 lean::cnstr_release(x_313, 1);
 x_318 = x_313;
}
if (lean::obj_tag(x_314) == 0)
{
obj* x_322; obj* x_325; obj* x_326; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_3);
x_322 = lean::cnstr_get(x_314, 0);
lean::inc(x_322);
lean::dec(x_314);
if (lean::is_scalar(x_309)) {
 x_325 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_325 = x_309;
}
lean::cnstr_set(x_325, 0, x_322);
if (lean::is_scalar(x_318)) {
 x_326 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_326 = x_318;
}
lean::cnstr_set(x_326, 0, x_325);
lean::cnstr_set(x_326, 1, x_316);
return x_326;
}
else
{
obj* x_329; obj* x_330; obj* x_332; 
lean::dec(x_314);
lean::inc(x_5);
x_329 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_3, x_5, x_316);
x_330 = lean::cnstr_get(x_329, 0);
lean::inc(x_330);
x_332 = lean::cnstr_get(x_329, 1);
lean::inc(x_332);
lean::dec(x_329);
if (lean::obj_tag(x_330) == 0)
{
obj* x_337; obj* x_340; obj* x_341; 
lean::dec(x_4);
lean::dec(x_5);
x_337 = lean::cnstr_get(x_330, 0);
lean::inc(x_337);
lean::dec(x_330);
if (lean::is_scalar(x_309)) {
 x_340 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_340 = x_309;
}
lean::cnstr_set(x_340, 0, x_337);
if (lean::is_scalar(x_318)) {
 x_341 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_341 = x_318;
}
lean::cnstr_set(x_341, 0, x_340);
lean::cnstr_set(x_341, 1, x_332);
return x_341;
}
else
{
obj* x_343; obj* x_346; obj* x_347; obj* x_349; 
lean::dec(x_330);
x_343 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_5);
lean::inc(x_343);
x_346 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_343, x_5, x_332);
x_347 = lean::cnstr_get(x_346, 0);
lean::inc(x_347);
x_349 = lean::cnstr_get(x_346, 1);
lean::inc(x_349);
lean::dec(x_346);
if (lean::obj_tag(x_347) == 0)
{
obj* x_354; obj* x_357; obj* x_358; 
lean::dec(x_4);
lean::dec(x_5);
x_354 = lean::cnstr_get(x_347, 0);
lean::inc(x_354);
lean::dec(x_347);
if (lean::is_scalar(x_309)) {
 x_357 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_357 = x_309;
}
lean::cnstr_set(x_357, 0, x_354);
if (lean::is_scalar(x_318)) {
 x_358 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_358 = x_318;
}
lean::cnstr_set(x_358, 0, x_357);
lean::cnstr_set(x_358, 1, x_349);
return x_358;
}
else
{
obj* x_361; obj* x_362; obj* x_364; 
lean::dec(x_347);
lean::inc(x_5);
x_361 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_4, x_5, x_349);
x_362 = lean::cnstr_get(x_361, 0);
lean::inc(x_362);
x_364 = lean::cnstr_get(x_361, 1);
lean::inc(x_364);
lean::dec(x_361);
if (lean::obj_tag(x_362) == 0)
{
obj* x_368; obj* x_371; obj* x_372; 
lean::dec(x_5);
x_368 = lean::cnstr_get(x_362, 0);
lean::inc(x_368);
lean::dec(x_362);
if (lean::is_scalar(x_309)) {
 x_371 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_371 = x_309;
}
lean::cnstr_set(x_371, 0, x_368);
if (lean::is_scalar(x_318)) {
 x_372 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_372 = x_318;
}
lean::cnstr_set(x_372, 0, x_371);
lean::cnstr_set(x_372, 1, x_364);
return x_372;
}
else
{
obj* x_373; obj* x_376; obj* x_378; obj* x_379; obj* x_381; 
x_373 = lean::cnstr_get(x_362, 0);
lean::inc(x_373);
lean::dec(x_362);
x_376 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_376);
x_378 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_376, x_5, x_364);
x_379 = lean::cnstr_get(x_378, 0);
lean::inc(x_379);
x_381 = lean::cnstr_get(x_378, 1);
lean::inc(x_381);
lean::dec(x_378);
if (lean::obj_tag(x_379) == 0)
{
obj* x_385; obj* x_388; obj* x_389; 
lean::dec(x_373);
x_385 = lean::cnstr_get(x_379, 0);
lean::inc(x_385);
lean::dec(x_379);
if (lean::is_scalar(x_309)) {
 x_388 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_388 = x_309;
}
lean::cnstr_set(x_388, 0, x_385);
if (lean::is_scalar(x_318)) {
 x_389 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_389 = x_318;
}
lean::cnstr_set(x_389, 0, x_388);
lean::cnstr_set(x_389, 1, x_381);
return x_389;
}
else
{
obj* x_391; obj* x_392; 
lean::dec(x_379);
if (lean::is_scalar(x_309)) {
 x_391 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_391 = x_309;
}
lean::cnstr_set(x_391, 0, x_373);
if (lean::is_scalar(x_318)) {
 x_392 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_392 = x_318;
}
lean::cnstr_set(x_392, 0, x_391);
lean::cnstr_set(x_392, 1, x_381);
return x_392;
}
}
}
}
}
}
}
}
lbl_11:
{

if (lean::obj_tag(x_9) == 0)
{
obj* x_396; obj* x_398; obj* x_399; obj* x_400; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_3);
x_396 = lean::cnstr_get(x_9, 0);
lean::inc(x_396);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_398 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_398 = x_9;
}
if (lean::is_scalar(x_398)) {
 x_399 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_399 = x_398;
}
lean::cnstr_set(x_399, 0, x_396);
x_400 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_400, 0, x_399);
lean::cnstr_set(x_400, 1, x_10);
return x_400;
}
else
{
obj* x_401; obj* x_402; obj* x_405; obj* x_406; obj* x_408; obj* x_410; 
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_401 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_401 = x_9;
}
x_402 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_5);
lean::inc(x_402);
x_405 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_402, x_5, x_10);
x_406 = lean::cnstr_get(x_405, 0);
lean::inc(x_406);
x_408 = lean::cnstr_get(x_405, 1);
lean::inc(x_408);
if (lean::is_shared(x_405)) {
 lean::dec(x_405);
 x_410 = lean::box(0);
} else {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 x_410 = x_405;
}
if (lean::obj_tag(x_406) == 0)
{
obj* x_414; obj* x_417; obj* x_418; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_3);
x_414 = lean::cnstr_get(x_406, 0);
lean::inc(x_414);
lean::dec(x_406);
if (lean::is_scalar(x_401)) {
 x_417 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_417 = x_401;
}
lean::cnstr_set(x_417, 0, x_414);
if (lean::is_scalar(x_410)) {
 x_418 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_418 = x_410;
}
lean::cnstr_set(x_418, 0, x_417);
lean::cnstr_set(x_418, 1, x_408);
return x_418;
}
else
{
obj* x_421; obj* x_422; obj* x_424; 
lean::dec(x_406);
lean::inc(x_5);
x_421 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_3, x_5, x_408);
x_422 = lean::cnstr_get(x_421, 0);
lean::inc(x_422);
x_424 = lean::cnstr_get(x_421, 1);
lean::inc(x_424);
lean::dec(x_421);
if (lean::obj_tag(x_422) == 0)
{
obj* x_429; obj* x_432; obj* x_433; 
lean::dec(x_4);
lean::dec(x_5);
x_429 = lean::cnstr_get(x_422, 0);
lean::inc(x_429);
lean::dec(x_422);
if (lean::is_scalar(x_401)) {
 x_432 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_432 = x_401;
}
lean::cnstr_set(x_432, 0, x_429);
if (lean::is_scalar(x_410)) {
 x_433 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_433 = x_410;
}
lean::cnstr_set(x_433, 0, x_432);
lean::cnstr_set(x_433, 1, x_424);
return x_433;
}
else
{
obj* x_435; obj* x_438; obj* x_439; obj* x_441; 
lean::dec(x_422);
x_435 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_5);
lean::inc(x_435);
x_438 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_435, x_5, x_424);
x_439 = lean::cnstr_get(x_438, 0);
lean::inc(x_439);
x_441 = lean::cnstr_get(x_438, 1);
lean::inc(x_441);
lean::dec(x_438);
if (lean::obj_tag(x_439) == 0)
{
obj* x_446; obj* x_449; obj* x_450; 
lean::dec(x_4);
lean::dec(x_5);
x_446 = lean::cnstr_get(x_439, 0);
lean::inc(x_446);
lean::dec(x_439);
if (lean::is_scalar(x_401)) {
 x_449 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_449 = x_401;
}
lean::cnstr_set(x_449, 0, x_446);
if (lean::is_scalar(x_410)) {
 x_450 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_450 = x_410;
}
lean::cnstr_set(x_450, 0, x_449);
lean::cnstr_set(x_450, 1, x_441);
return x_450;
}
else
{
obj* x_453; obj* x_454; obj* x_456; 
lean::dec(x_439);
lean::inc(x_5);
x_453 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_4, x_5, x_441);
x_454 = lean::cnstr_get(x_453, 0);
lean::inc(x_454);
x_456 = lean::cnstr_get(x_453, 1);
lean::inc(x_456);
lean::dec(x_453);
if (lean::obj_tag(x_454) == 0)
{
obj* x_460; obj* x_463; obj* x_464; 
lean::dec(x_5);
x_460 = lean::cnstr_get(x_454, 0);
lean::inc(x_460);
lean::dec(x_454);
if (lean::is_scalar(x_401)) {
 x_463 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_463 = x_401;
}
lean::cnstr_set(x_463, 0, x_460);
if (lean::is_scalar(x_410)) {
 x_464 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_464 = x_410;
}
lean::cnstr_set(x_464, 0, x_463);
lean::cnstr_set(x_464, 1, x_456);
return x_464;
}
else
{
obj* x_465; obj* x_468; obj* x_470; obj* x_471; obj* x_473; 
x_465 = lean::cnstr_get(x_454, 0);
lean::inc(x_465);
lean::dec(x_454);
x_468 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_468);
x_470 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_468, x_5, x_456);
x_471 = lean::cnstr_get(x_470, 0);
lean::inc(x_471);
x_473 = lean::cnstr_get(x_470, 1);
lean::inc(x_473);
lean::dec(x_470);
if (lean::obj_tag(x_471) == 0)
{
obj* x_477; obj* x_480; obj* x_481; 
lean::dec(x_465);
x_477 = lean::cnstr_get(x_471, 0);
lean::inc(x_477);
lean::dec(x_471);
if (lean::is_scalar(x_401)) {
 x_480 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_480 = x_401;
}
lean::cnstr_set(x_480, 0, x_477);
if (lean::is_scalar(x_410)) {
 x_481 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_481 = x_410;
}
lean::cnstr_set(x_481, 0, x_480);
lean::cnstr_set(x_481, 1, x_473);
return x_481;
}
else
{
obj* x_483; obj* x_484; 
lean::dec(x_471);
if (lean::is_scalar(x_401)) {
 x_483 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_483 = x_401;
}
lean::cnstr_set(x_483, 0, x_465);
if (lean::is_scalar(x_410)) {
 x_484 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_484 = x_410;
}
lean::cnstr_set(x_484, 0, x_483);
lean::cnstr_set(x_484, 1, x_473);
return x_484;
}
}
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::sarray_data");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("+");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_add");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_sub");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__5() {
{
obj* x_0; 
x_0 = lean::mk_string("*");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__6() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_mul");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__7() {
{
obj* x_0; 
x_0 = lean::mk_string("/");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__8() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_div");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__9() {
{
obj* x_0; 
x_0 = lean::mk_string("%");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__10() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_mod");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__11() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_add");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__12() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_sub");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__13() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_mul");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__14() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_div");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__15() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_mod");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__16() {
{
obj* x_0; 
x_0 = lean::mk_string("<<");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__17() {
{
obj* x_0; 
x_0 = lean::mk_string(">>");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__18() {
{
obj* x_0; 
x_0 = lean::mk_string("&&");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__19() {
{
obj* x_0; 
x_0 = lean::mk_string("&");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__20() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_land");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__21() {
{
obj* x_0; 
x_0 = lean::mk_string("||");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__22() {
{
obj* x_0; 
x_0 = lean::mk_string("|");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__23() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_lor");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__24() {
{
obj* x_0; 
x_0 = lean::mk_string("!=");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__25() {
{
obj* x_0; 
x_0 = lean::mk_string("^");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__26() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_lxor");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__27() {
{
obj* x_0; 
x_0 = lean::mk_string("<=");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__28() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_le");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__29() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_lt");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__30() {
{
obj* x_0; 
x_0 = lean::mk_string("==");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__31() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_eq");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__32() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_ne");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__33() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_le");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__34() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_lt");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__35() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_eq");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__36() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_ne");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__37() {
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::array_obj");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__38() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::sarray_push");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__39() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::array_push");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__40() {
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::string_push");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__41() {
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::string_append");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
unsigned char x_7; unsigned char x_8; obj* x_9; 
x_7 = lean::unbox(x_1);
x_8 = lean::unbox(x_2);
x_9 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop(x_0, x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s14_emit__x__op__y(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_12; 
lean::inc(x_3);
x_9 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_3, x_4);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_17 = x_10;
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_15);
x_5 = x_18;
x_6 = x_12;
goto lbl_7;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_26; 
lean::dec(x_10);
x_20 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1;
lean::inc(x_3);
lean::inc(x_20);
x_23 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_20, x_3, x_12);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
x_5 = x_24;
x_6 = x_26;
goto lbl_7;
}
lbl_7:
{

if (lean::obj_tag(x_5) == 0)
{
obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_32 = lean::cnstr_get(x_5, 0);
lean::inc(x_32);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_34 = x_5;
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_6);
return x_36;
}
else
{
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_44; 
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_37 = x_5;
}
lean::inc(x_3);
x_39 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1, x_3, x_6);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
if (lean::is_shared(x_39)) {
 lean::dec(x_39);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_39, 0);
 lean::cnstr_release(x_39, 1);
 x_44 = x_39;
}
if (lean::obj_tag(x_40) == 0)
{
obj* x_47; obj* x_50; obj* x_51; 
lean::dec(x_2);
lean::dec(x_3);
x_47 = lean::cnstr_get(x_40, 0);
lean::inc(x_47);
lean::dec(x_40);
if (lean::is_scalar(x_37)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_37;
}
lean::cnstr_set(x_50, 0, x_47);
if (lean::is_scalar(x_44)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_44;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_42);
return x_51;
}
else
{
obj* x_53; obj* x_56; obj* x_57; obj* x_59; 
lean::dec(x_40);
x_53 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_3);
lean::inc(x_53);
x_56 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_53, x_3, x_42);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
if (lean::obj_tag(x_57) == 0)
{
obj* x_64; obj* x_67; obj* x_68; 
lean::dec(x_2);
lean::dec(x_3);
x_64 = lean::cnstr_get(x_57, 0);
lean::inc(x_64);
lean::dec(x_57);
if (lean::is_scalar(x_37)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_37;
}
lean::cnstr_set(x_67, 0, x_64);
if (lean::is_scalar(x_44)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_44;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_59);
return x_68;
}
else
{
obj* x_71; obj* x_72; obj* x_74; 
lean::dec(x_57);
lean::inc(x_3);
x_71 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_2, x_3, x_59);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
lean::dec(x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_78; obj* x_81; obj* x_82; 
lean::dec(x_3);
x_78 = lean::cnstr_get(x_72, 0);
lean::inc(x_78);
lean::dec(x_72);
if (lean::is_scalar(x_37)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_37;
}
lean::cnstr_set(x_81, 0, x_78);
if (lean::is_scalar(x_44)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_44;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_74);
return x_82;
}
else
{
obj* x_83; obj* x_86; obj* x_88; obj* x_89; obj* x_91; 
x_83 = lean::cnstr_get(x_72, 0);
lean::inc(x_83);
lean::dec(x_72);
x_86 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_86);
x_88 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_86, x_3, x_74);
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_88, 1);
lean::inc(x_91);
lean::dec(x_88);
if (lean::obj_tag(x_89) == 0)
{
obj* x_95; obj* x_98; obj* x_99; 
lean::dec(x_83);
x_95 = lean::cnstr_get(x_89, 0);
lean::inc(x_95);
lean::dec(x_89);
if (lean::is_scalar(x_37)) {
 x_98 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_98 = x_37;
}
lean::cnstr_set(x_98, 0, x_95);
if (lean::is_scalar(x_44)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_44;
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_91);
return x_99;
}
else
{
obj* x_101; obj* x_102; 
lean::dec(x_89);
if (lean::is_scalar(x_37)) {
 x_101 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_101 = x_37;
}
lean::cnstr_set(x_101, 0, x_83);
if (lean::is_scalar(x_44)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_44;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_91);
return x_102;
}
}
}
}
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main(unsigned char x_0, unsigned char x_1) {
{

switch (x_1) {
case 0:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_0);
x_3 = _l_s4_lean_s2_ir_s13_is__arith__ty_s11___closed__1;
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; 
lean::dec(x_4);
x_7 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__1;
lean::inc(x_7);
return x_7;
}
else
{
obj* x_10; 
lean::dec(x_4);
x_10 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__2;
lean::inc(x_10);
return x_10;
}
}
case 1:
{
obj* x_12; 
x_12 = _l_s3_int_s4_repr_s6___main_s11___closed__1;
lean::inc(x_12);
return x_12;
}
case 2:
{
obj* x_14; 
x_14 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__3;
lean::inc(x_14);
return x_14;
}
case 3:
{
obj* x_16; 
x_16 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__4;
lean::inc(x_16);
return x_16;
}
case 4:
{
obj* x_18; 
x_18 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__5;
lean::inc(x_18);
return x_18;
}
case 5:
{
obj* x_20; 
x_20 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__6;
lean::inc(x_20);
return x_20;
}
case 6:
{
obj* x_22; 
x_22 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__7;
lean::inc(x_22);
return x_22;
}
case 7:
{
obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
x_24 = _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main(x_0);
x_25 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__8;
lean::inc(x_25);
x_27 = lean::string_append(x_25, x_24);
lean::dec(x_24);
x_29 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__4;
x_30 = lean::string_append(x_27, x_29);
return x_30;
}
case 8:
{
obj* x_31; 
x_31 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__9;
lean::inc(x_31);
return x_31;
}
case 9:
{
obj* x_33; 
x_33 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__10;
lean::inc(x_33);
return x_33;
}
case 10:
{
obj* x_35; 
x_35 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__11;
lean::inc(x_35);
return x_35;
}
case 11:
{
obj* x_37; 
x_37 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__12;
lean::inc(x_37);
return x_37;
}
case 12:
{
obj* x_39; 
x_39 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__13;
lean::inc(x_39);
return x_39;
}
case 13:
{
obj* x_41; 
x_41 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__14;
lean::inc(x_41);
return x_41;
}
case 14:
{
obj* x_43; 
x_43 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__15;
lean::inc(x_43);
return x_43;
}
case 15:
{
obj* x_45; 
x_45 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__16;
lean::inc(x_45);
return x_45;
}
case 16:
{
obj* x_47; 
x_47 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__17;
lean::inc(x_47);
return x_47;
}
default:
{
obj* x_49; 
x_49 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__18;
lean::inc(x_49);
return x_49;
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("~");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("!");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_neg");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat2int");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__5() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::is_scalar");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__6() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::is_shared");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__7() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::is_null");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__8() {
{
obj* x_0; 
x_0 = lean::mk_string("static_cast<");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__9() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::box");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__10() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::unbox");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__11() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::array_copy");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__12() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::sarray_copy");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__13() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::array_size");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__14() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::sarray_size");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__15() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::string_len");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__16() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_succ");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__17() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::obj_tag");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__18() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::cnstr_tag");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main(x_2, x_3);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp(unsigned char x_0, unsigned char x_1) {
{
obj* x_2; 
x_2 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main(x_0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp(x_2, x_3);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s18_emit__assign__unop(obj* x_0, unsigned char x_1, unsigned char x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_14; 
x_6 = _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main(x_1, x_2);
lean::inc(x_4);
x_11 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_4, x_5);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_12, 0);
lean::inc(x_17);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
x_7 = x_20;
x_8 = x_14;
goto lbl_9;
}
else
{
obj* x_22; obj* x_25; obj* x_26; obj* x_28; 
lean::dec(x_12);
x_22 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1;
lean::inc(x_4);
lean::inc(x_22);
x_25 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_22, x_4, x_14);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_7 = x_26;
x_8 = x_28;
goto lbl_9;
}
lbl_9:
{

if (lean::obj_tag(x_7) == 0)
{
obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
x_34 = lean::cnstr_get(x_7, 0);
lean::inc(x_34);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_36 = x_7;
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_8);
return x_38;
}
else
{
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; 
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_39 = x_7;
}
lean::inc(x_4);
x_41 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_6, x_4, x_8);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
if (lean::is_shared(x_41)) {
 lean::dec(x_41);
 x_46 = lean::box(0);
} else {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 x_46 = x_41;
}
if (lean::obj_tag(x_42) == 0)
{
obj* x_49; obj* x_52; obj* x_53; 
lean::dec(x_4);
lean::dec(x_3);
x_49 = lean::cnstr_get(x_42, 0);
lean::inc(x_49);
lean::dec(x_42);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_49);
if (lean::is_scalar(x_46)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_46;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_44);
return x_53;
}
else
{
obj* x_55; obj* x_58; obj* x_59; obj* x_61; 
lean::dec(x_42);
x_55 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_4);
lean::inc(x_55);
x_58 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_55, x_4, x_44);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
if (lean::obj_tag(x_59) == 0)
{
obj* x_66; obj* x_69; obj* x_70; 
lean::dec(x_4);
lean::dec(x_3);
x_66 = lean::cnstr_get(x_59, 0);
lean::inc(x_66);
lean::dec(x_59);
if (lean::is_scalar(x_39)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_39;
}
lean::cnstr_set(x_69, 0, x_66);
if (lean::is_scalar(x_46)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_46;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_61);
return x_70;
}
else
{
obj* x_73; obj* x_74; obj* x_76; 
lean::dec(x_59);
lean::inc(x_4);
x_73 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_3, x_4, x_61);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_80; obj* x_83; obj* x_84; 
lean::dec(x_4);
x_80 = lean::cnstr_get(x_74, 0);
lean::inc(x_80);
lean::dec(x_74);
if (lean::is_scalar(x_39)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_39;
}
lean::cnstr_set(x_83, 0, x_80);
if (lean::is_scalar(x_46)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_46;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_76);
return x_84;
}
else
{
obj* x_85; obj* x_88; obj* x_90; obj* x_91; obj* x_93; 
x_85 = lean::cnstr_get(x_74, 0);
lean::inc(x_85);
lean::dec(x_74);
x_88 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_88);
x_90 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_88, x_4, x_76);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
if (lean::obj_tag(x_91) == 0)
{
obj* x_97; obj* x_100; obj* x_101; 
lean::dec(x_85);
x_97 = lean::cnstr_get(x_91, 0);
lean::inc(x_97);
lean::dec(x_91);
if (lean::is_scalar(x_39)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_39;
}
lean::cnstr_set(x_100, 0, x_97);
if (lean::is_scalar(x_46)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_46;
}
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_93);
return x_101;
}
else
{
obj* x_103; obj* x_104; 
lean::dec(x_91);
if (lean::is_scalar(x_39)) {
 x_103 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_103 = x_39;
}
lean::cnstr_set(x_103, 0, x_85);
if (lean::is_scalar(x_46)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_46;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_93);
return x_104;
}
}
}
}
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s18_emit__assign__unop_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
unsigned char x_6; unsigned char x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
x_7 = lean::unbox(x_2);
x_8 = _l_s4_lean_s2_ir_s3_cpp_s18_emit__assign__unop(x_0, x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main(unsigned char x_0, obj* x_1, obj* x_2) {
{

switch (x_0) {
case 0:
{
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
case 1:
{
obj* x_8; obj* x_10; 
lean::dec(x_1);
x_8 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_2);
return x_10;
}
case 2:
{
obj* x_12; obj* x_14; 
lean::dec(x_1);
x_12 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_2);
return x_14;
}
case 3:
{
obj* x_15; obj* x_17; 
x_15 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__1;
lean::inc(x_15);
x_17 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_15, x_1, x_2);
return x_17;
}
case 4:
{
obj* x_18; obj* x_20; 
x_18 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__2;
lean::inc(x_18);
x_20 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_18, x_1, x_2);
return x_20;
}
case 5:
{
obj* x_22; obj* x_24; 
lean::dec(x_1);
x_22 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_2);
return x_24;
}
case 6:
{
obj* x_26; obj* x_28; 
lean::dec(x_1);
x_26 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_26);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_2);
return x_28;
}
case 7:
{
obj* x_30; obj* x_32; 
lean::dec(x_1);
x_30 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_2);
return x_32;
}
case 8:
{
obj* x_33; obj* x_35; 
x_33 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__3;
lean::inc(x_33);
x_35 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_33, x_1, x_2);
return x_35;
}
case 9:
{
obj* x_37; obj* x_39; 
lean::dec(x_1);
x_37 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_2);
return x_39;
}
case 10:
{
obj* x_41; obj* x_43; 
lean::dec(x_1);
x_41 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_41);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_2);
return x_43;
}
default:
{
obj* x_45; obj* x_47; 
lean::dec(x_1);
x_45 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_2);
return x_47;
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("u");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("ull");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string("ll");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main(x_3, x_1, x_2);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix(unsigned char x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix(x_3, x_1, x_2);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit(obj* x_0, unsigned char x_1, obj* x_2, obj* x_3, obj* x_4) {
{

switch (lean::obj_tag(x_2)) {
case 0:
{
unsigned char x_5; 
x_5 = lean::cnstr_get_scalar<unsigned char>(x_2, 0);
lean::dec(x_2);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
lean::inc(x_3);
x_8 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_3, x_4);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_3);
x_15 = lean::cnstr_get(x_9, 0);
lean::inc(x_15);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_17 = x_9;
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_15);
if (lean::is_scalar(x_13)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_13;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_11);
return x_19;
}
else
{
obj* x_22; obj* x_24; 
lean::dec(x_13);
lean::dec(x_9);
x_22 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__1;
lean::inc(x_22);
x_24 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_22, x_3, x_11);
return x_24;
}
}
else
{
obj* x_26; obj* x_27; obj* x_29; obj* x_31; 
lean::inc(x_3);
x_26 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_3, x_4);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 x_31 = x_26;
}
if (lean::obj_tag(x_27) == 0)
{
obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_3);
x_33 = lean::cnstr_get(x_27, 0);
lean::inc(x_33);
if (lean::is_shared(x_27)) {
 lean::dec(x_27);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_27, 0);
 x_35 = x_27;
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
if (lean::is_scalar(x_31)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_31;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_29);
return x_37;
}
else
{
obj* x_40; obj* x_42; 
lean::dec(x_31);
lean::dec(x_27);
x_40 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__2;
lean::inc(x_40);
x_42 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_40, x_3, x_29);
return x_42;
}
}
}
case 1:
{
obj* x_43; obj* x_47; obj* x_48; obj* x_50; obj* x_52; 
x_43 = lean::cnstr_get(x_2, 0);
lean::inc(x_43);
lean::dec(x_2);
lean::inc(x_3);
x_47 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_3, x_4);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
if (lean::is_shared(x_47)) {
 lean::dec(x_47);
 x_52 = lean::box(0);
} else {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_52 = x_47;
}
if (lean::obj_tag(x_48) == 0)
{
obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_43);
lean::dec(x_3);
x_55 = lean::cnstr_get(x_48, 0);
lean::inc(x_55);
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_57 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 x_57 = x_48;
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
if (lean::is_scalar(x_52)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_52;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_50);
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_64; obj* x_65; obj* x_67; 
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_60 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 x_60 = x_48;
}
x_61 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__3;
lean::inc(x_3);
lean::inc(x_61);
x_64 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_61, x_3, x_50);
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_64, 1);
lean::inc(x_67);
lean::dec(x_64);
if (lean::obj_tag(x_65) == 0)
{
obj* x_72; obj* x_75; obj* x_76; 
lean::dec(x_43);
lean::dec(x_3);
x_72 = lean::cnstr_get(x_65, 0);
lean::inc(x_72);
lean::dec(x_65);
if (lean::is_scalar(x_60)) {
 x_75 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_75 = x_60;
}
lean::cnstr_set(x_75, 0, x_72);
if (lean::is_scalar(x_52)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_52;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_67);
return x_76;
}
else
{
obj* x_78; obj* x_79; obj* x_82; obj* x_83; obj* x_85; 
lean::dec(x_65);
x_78 = _l_s6_string_s5_quote(x_43);
x_79 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_3);
lean::inc(x_79);
x_82 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_79, x_3, x_67);
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
if (lean::obj_tag(x_83) == 0)
{
obj* x_90; obj* x_93; obj* x_94; 
lean::dec(x_78);
lean::dec(x_3);
x_90 = lean::cnstr_get(x_83, 0);
lean::inc(x_90);
lean::dec(x_83);
if (lean::is_scalar(x_60)) {
 x_93 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_93 = x_60;
}
lean::cnstr_set(x_93, 0, x_90);
if (lean::is_scalar(x_52)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_52;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_85);
return x_94;
}
else
{
obj* x_97; obj* x_98; obj* x_100; 
lean::dec(x_83);
lean::inc(x_3);
x_97 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_78, x_3, x_85);
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_97, 1);
lean::inc(x_100);
lean::dec(x_97);
if (lean::obj_tag(x_98) == 0)
{
obj* x_104; obj* x_107; obj* x_108; 
lean::dec(x_3);
x_104 = lean::cnstr_get(x_98, 0);
lean::inc(x_104);
lean::dec(x_98);
if (lean::is_scalar(x_60)) {
 x_107 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_107 = x_60;
}
lean::cnstr_set(x_107, 0, x_104);
if (lean::is_scalar(x_52)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_52;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_100);
return x_108;
}
else
{
obj* x_109; obj* x_112; obj* x_114; obj* x_115; obj* x_117; 
x_109 = lean::cnstr_get(x_98, 0);
lean::inc(x_109);
lean::dec(x_98);
x_112 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_112);
x_114 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_112, x_3, x_100);
x_115 = lean::cnstr_get(x_114, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_114, 1);
lean::inc(x_117);
lean::dec(x_114);
if (lean::obj_tag(x_115) == 0)
{
obj* x_121; obj* x_124; obj* x_125; 
lean::dec(x_109);
x_121 = lean::cnstr_get(x_115, 0);
lean::inc(x_121);
lean::dec(x_115);
if (lean::is_scalar(x_60)) {
 x_124 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_124 = x_60;
}
lean::cnstr_set(x_124, 0, x_121);
if (lean::is_scalar(x_52)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_52;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_117);
return x_125;
}
else
{
obj* x_127; obj* x_128; 
lean::dec(x_115);
if (lean::is_scalar(x_60)) {
 x_127 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_127 = x_60;
}
lean::cnstr_set(x_127, 0, x_109);
if (lean::is_scalar(x_52)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_52;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_117);
return x_128;
}
}
}
}
}
}
case 2:
{
obj* x_129; unsigned char x_132; 
x_129 = lean::cnstr_get(x_2, 0);
lean::inc(x_129);
lean::dec(x_2);
switch (x_1) {
case 0:
{
unsigned char x_134; 
x_134 = 0;
x_132 = x_134;
goto lbl_133;
}
case 1:
{
unsigned char x_135; 
x_135 = 0;
x_132 = x_135;
goto lbl_133;
}
case 2:
{
unsigned char x_136; 
x_136 = 0;
x_132 = x_136;
goto lbl_133;
}
case 3:
{
unsigned char x_137; 
x_137 = 0;
x_132 = x_137;
goto lbl_133;
}
case 4:
{
unsigned char x_138; 
x_138 = 0;
x_132 = x_138;
goto lbl_133;
}
case 5:
{
unsigned char x_139; 
x_139 = 0;
x_132 = x_139;
goto lbl_133;
}
case 6:
{
unsigned char x_140; 
x_140 = 0;
x_132 = x_140;
goto lbl_133;
}
case 7:
{
unsigned char x_141; 
x_141 = 0;
x_132 = x_141;
goto lbl_133;
}
case 8:
{
unsigned char x_142; 
x_142 = 0;
x_132 = x_142;
goto lbl_133;
}
case 9:
{
unsigned char x_143; 
x_143 = 0;
x_132 = x_143;
goto lbl_133;
}
case 10:
{
unsigned char x_144; 
x_144 = 0;
x_132 = x_144;
goto lbl_133;
}
default:
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_151; obj* x_152; obj* x_154; 
x_145 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__4;
x_146 = lean::int_dec_lt(x_129, x_145);
lean::inc(x_3);
x_151 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_3, x_4);
x_152 = lean::cnstr_get(x_151, 0);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_151, 1);
lean::inc(x_154);
lean::dec(x_151);
if (lean::obj_tag(x_152) == 0)
{
obj* x_157; obj* x_159; obj* x_160; 
x_157 = lean::cnstr_get(x_152, 0);
lean::inc(x_157);
if (lean::is_shared(x_152)) {
 lean::dec(x_152);
 x_159 = lean::box(0);
} else {
 lean::cnstr_release(x_152, 0);
 x_159 = x_152;
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_157);
x_147 = x_160;
x_148 = x_154;
goto lbl_149;
}
else
{
obj* x_162; obj* x_165; obj* x_166; obj* x_168; 
lean::dec(x_152);
x_162 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1;
lean::inc(x_3);
lean::inc(x_162);
x_165 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_162, x_3, x_154);
x_166 = lean::cnstr_get(x_165, 0);
lean::inc(x_166);
x_168 = lean::cnstr_get(x_165, 1);
lean::inc(x_168);
lean::dec(x_165);
x_147 = x_166;
x_148 = x_168;
goto lbl_149;
}
lbl_149:
{

if (lean::obj_tag(x_147) == 0)
{
obj* x_174; obj* x_176; obj* x_177; obj* x_178; 
lean::dec(x_146);
lean::dec(x_129);
lean::dec(x_3);
x_174 = lean::cnstr_get(x_147, 0);
lean::inc(x_174);
if (lean::is_shared(x_147)) {
 lean::dec(x_147);
 x_176 = lean::box(0);
} else {
 lean::cnstr_release(x_147, 0);
 x_176 = x_147;
}
if (lean::is_scalar(x_176)) {
 x_177 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_177 = x_176;
}
lean::cnstr_set(x_177, 0, x_174);
x_178 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set(x_178, 1, x_148);
return x_178;
}
else
{
obj* x_179; 
if (lean::is_shared(x_147)) {
 lean::dec(x_147);
 x_179 = lean::box(0);
} else {
 lean::cnstr_release(x_147, 0);
 x_179 = x_147;
}
if (lean::obj_tag(x_146) == 0)
{
obj* x_181; obj* x_184; obj* x_185; obj* x_187; obj* x_189; 
lean::dec(x_146);
x_181 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__5;
lean::inc(x_3);
lean::inc(x_181);
x_184 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_181, x_3, x_148);
x_185 = lean::cnstr_get(x_184, 0);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_184, 1);
lean::inc(x_187);
if (lean::is_shared(x_184)) {
 lean::dec(x_184);
 x_189 = lean::box(0);
} else {
 lean::cnstr_release(x_184, 0);
 lean::cnstr_release(x_184, 1);
 x_189 = x_184;
}
if (lean::obj_tag(x_185) == 0)
{
obj* x_192; obj* x_195; obj* x_196; 
lean::dec(x_129);
lean::dec(x_3);
x_192 = lean::cnstr_get(x_185, 0);
lean::inc(x_192);
lean::dec(x_185);
if (lean::is_scalar(x_179)) {
 x_195 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_195 = x_179;
}
lean::cnstr_set(x_195, 0, x_192);
if (lean::is_scalar(x_189)) {
 x_196 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_196 = x_189;
}
lean::cnstr_set(x_196, 0, x_195);
lean::cnstr_set(x_196, 1, x_187);
return x_196;
}
else
{
obj* x_199; obj* x_200; obj* x_202; 
lean::dec(x_185);
lean::inc(x_3);
x_199 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s9___spec__1(x_129, x_3, x_187);
x_200 = lean::cnstr_get(x_199, 0);
lean::inc(x_200);
x_202 = lean::cnstr_get(x_199, 1);
lean::inc(x_202);
lean::dec(x_199);
if (lean::obj_tag(x_200) == 0)
{
obj* x_206; obj* x_209; obj* x_210; 
lean::dec(x_3);
x_206 = lean::cnstr_get(x_200, 0);
lean::inc(x_206);
lean::dec(x_200);
if (lean::is_scalar(x_179)) {
 x_209 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_209 = x_179;
}
lean::cnstr_set(x_209, 0, x_206);
if (lean::is_scalar(x_189)) {
 x_210 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_210 = x_189;
}
lean::cnstr_set(x_210, 0, x_209);
lean::cnstr_set(x_210, 1, x_202);
return x_210;
}
else
{
obj* x_214; obj* x_216; 
lean::dec(x_200);
lean::dec(x_189);
lean::dec(x_179);
x_214 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__6;
lean::inc(x_214);
x_216 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_214, x_3, x_202);
return x_216;
}
}
}
else
{
obj* x_218; obj* x_221; obj* x_222; obj* x_224; obj* x_226; 
lean::dec(x_146);
x_218 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__7;
lean::inc(x_3);
lean::inc(x_218);
x_221 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_218, x_3, x_148);
x_222 = lean::cnstr_get(x_221, 0);
lean::inc(x_222);
x_224 = lean::cnstr_get(x_221, 1);
lean::inc(x_224);
if (lean::is_shared(x_221)) {
 lean::dec(x_221);
 x_226 = lean::box(0);
} else {
 lean::cnstr_release(x_221, 0);
 lean::cnstr_release(x_221, 1);
 x_226 = x_221;
}
if (lean::obj_tag(x_222) == 0)
{
obj* x_229; obj* x_232; obj* x_233; 
lean::dec(x_129);
lean::dec(x_3);
x_229 = lean::cnstr_get(x_222, 0);
lean::inc(x_229);
lean::dec(x_222);
if (lean::is_scalar(x_179)) {
 x_232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_232 = x_179;
}
lean::cnstr_set(x_232, 0, x_229);
if (lean::is_scalar(x_226)) {
 x_233 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_233 = x_226;
}
lean::cnstr_set(x_233, 0, x_232);
lean::cnstr_set(x_233, 1, x_224);
return x_233;
}
else
{
obj* x_235; obj* x_238; obj* x_239; obj* x_241; 
lean::dec(x_222);
x_235 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_3);
lean::inc(x_235);
x_238 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_235, x_3, x_224);
x_239 = lean::cnstr_get(x_238, 0);
lean::inc(x_239);
x_241 = lean::cnstr_get(x_238, 1);
lean::inc(x_241);
lean::dec(x_238);
if (lean::obj_tag(x_239) == 0)
{
obj* x_246; obj* x_249; obj* x_250; 
lean::dec(x_129);
lean::dec(x_3);
x_246 = lean::cnstr_get(x_239, 0);
lean::inc(x_246);
lean::dec(x_239);
if (lean::is_scalar(x_179)) {
 x_249 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_249 = x_179;
}
lean::cnstr_set(x_249, 0, x_246);
if (lean::is_scalar(x_226)) {
 x_250 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_250 = x_226;
}
lean::cnstr_set(x_250, 0, x_249);
lean::cnstr_set(x_250, 1, x_241);
return x_250;
}
else
{
obj* x_253; obj* x_254; obj* x_256; 
lean::dec(x_239);
lean::inc(x_3);
x_253 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s9___spec__1(x_129, x_3, x_241);
x_254 = lean::cnstr_get(x_253, 0);
lean::inc(x_254);
x_256 = lean::cnstr_get(x_253, 1);
lean::inc(x_256);
lean::dec(x_253);
if (lean::obj_tag(x_254) == 0)
{
obj* x_260; obj* x_263; obj* x_264; 
lean::dec(x_3);
x_260 = lean::cnstr_get(x_254, 0);
lean::inc(x_260);
lean::dec(x_254);
if (lean::is_scalar(x_179)) {
 x_263 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_263 = x_179;
}
lean::cnstr_set(x_263, 0, x_260);
if (lean::is_scalar(x_226)) {
 x_264 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_264 = x_226;
}
lean::cnstr_set(x_264, 0, x_263);
lean::cnstr_set(x_264, 1, x_256);
return x_264;
}
else
{
obj* x_266; obj* x_269; obj* x_270; obj* x_272; 
lean::dec(x_254);
x_266 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__1;
lean::inc(x_3);
lean::inc(x_266);
x_269 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_266, x_3, x_256);
x_270 = lean::cnstr_get(x_269, 0);
lean::inc(x_270);
x_272 = lean::cnstr_get(x_269, 1);
lean::inc(x_272);
lean::dec(x_269);
if (lean::obj_tag(x_270) == 0)
{
obj* x_276; obj* x_279; obj* x_280; 
lean::dec(x_3);
x_276 = lean::cnstr_get(x_270, 0);
lean::inc(x_276);
lean::dec(x_270);
if (lean::is_scalar(x_179)) {
 x_279 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_279 = x_179;
}
lean::cnstr_set(x_279, 0, x_276);
if (lean::is_scalar(x_226)) {
 x_280 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_280 = x_226;
}
lean::cnstr_set(x_280, 0, x_279);
lean::cnstr_set(x_280, 1, x_272);
return x_280;
}
else
{
obj* x_281; obj* x_284; obj* x_286; obj* x_287; obj* x_289; 
x_281 = lean::cnstr_get(x_270, 0);
lean::inc(x_281);
lean::dec(x_270);
x_284 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_284);
x_286 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_284, x_3, x_272);
x_287 = lean::cnstr_get(x_286, 0);
lean::inc(x_287);
x_289 = lean::cnstr_get(x_286, 1);
lean::inc(x_289);
lean::dec(x_286);
if (lean::obj_tag(x_287) == 0)
{
obj* x_293; obj* x_296; obj* x_297; 
lean::dec(x_281);
x_293 = lean::cnstr_get(x_287, 0);
lean::inc(x_293);
lean::dec(x_287);
if (lean::is_scalar(x_179)) {
 x_296 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_296 = x_179;
}
lean::cnstr_set(x_296, 0, x_293);
if (lean::is_scalar(x_226)) {
 x_297 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_297 = x_226;
}
lean::cnstr_set(x_297, 0, x_296);
lean::cnstr_set(x_297, 1, x_289);
return x_297;
}
else
{
obj* x_299; obj* x_300; 
lean::dec(x_287);
if (lean::is_scalar(x_179)) {
 x_299 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_299 = x_179;
}
lean::cnstr_set(x_299, 0, x_281);
if (lean::is_scalar(x_226)) {
 x_300 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_300 = x_226;
}
lean::cnstr_set(x_300, 0, x_299);
lean::cnstr_set(x_300, 1, x_289);
return x_300;
}
}
}
}
}
}
}
}
}
}
lbl_133:
{
obj* x_302; obj* x_303; obj* x_305; obj* x_307; 
lean::inc(x_3);
x_302 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_3, x_4);
x_303 = lean::cnstr_get(x_302, 0);
lean::inc(x_303);
x_305 = lean::cnstr_get(x_302, 1);
lean::inc(x_305);
if (lean::is_shared(x_302)) {
 lean::dec(x_302);
 x_307 = lean::box(0);
} else {
 lean::cnstr_release(x_302, 0);
 lean::cnstr_release(x_302, 1);
 x_307 = x_302;
}
if (lean::obj_tag(x_303) == 0)
{
obj* x_310; obj* x_312; obj* x_313; obj* x_314; 
lean::dec(x_129);
lean::dec(x_3);
x_310 = lean::cnstr_get(x_303, 0);
lean::inc(x_310);
if (lean::is_shared(x_303)) {
 lean::dec(x_303);
 x_312 = lean::box(0);
} else {
 lean::cnstr_release(x_303, 0);
 x_312 = x_303;
}
if (lean::is_scalar(x_312)) {
 x_313 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_313 = x_312;
}
lean::cnstr_set(x_313, 0, x_310);
if (lean::is_scalar(x_307)) {
 x_314 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_314 = x_307;
}
lean::cnstr_set(x_314, 0, x_313);
lean::cnstr_set(x_314, 1, x_305);
return x_314;
}
else
{
obj* x_315; obj* x_316; obj* x_319; obj* x_320; obj* x_322; 
if (lean::is_shared(x_303)) {
 lean::dec(x_303);
 x_315 = lean::box(0);
} else {
 lean::cnstr_release(x_303, 0);
 x_315 = x_303;
}
x_316 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1;
lean::inc(x_3);
lean::inc(x_316);
x_319 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_316, x_3, x_305);
x_320 = lean::cnstr_get(x_319, 0);
lean::inc(x_320);
x_322 = lean::cnstr_get(x_319, 1);
lean::inc(x_322);
lean::dec(x_319);
if (lean::obj_tag(x_320) == 0)
{
obj* x_327; obj* x_330; obj* x_331; 
lean::dec(x_129);
lean::dec(x_3);
x_327 = lean::cnstr_get(x_320, 0);
lean::inc(x_327);
lean::dec(x_320);
if (lean::is_scalar(x_315)) {
 x_330 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_330 = x_315;
}
lean::cnstr_set(x_330, 0, x_327);
if (lean::is_scalar(x_307)) {
 x_331 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_331 = x_307;
}
lean::cnstr_set(x_331, 0, x_330);
lean::cnstr_set(x_331, 1, x_322);
return x_331;
}
else
{
obj* x_334; obj* x_335; obj* x_337; 
lean::dec(x_320);
lean::inc(x_3);
x_334 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s9___spec__1(x_129, x_3, x_322);
x_335 = lean::cnstr_get(x_334, 0);
lean::inc(x_335);
x_337 = lean::cnstr_get(x_334, 1);
lean::inc(x_337);
lean::dec(x_334);
if (lean::obj_tag(x_335) == 0)
{
obj* x_341; obj* x_344; obj* x_345; 
lean::dec(x_3);
x_341 = lean::cnstr_get(x_335, 0);
lean::inc(x_341);
lean::dec(x_335);
if (lean::is_scalar(x_315)) {
 x_344 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_344 = x_315;
}
lean::cnstr_set(x_344, 0, x_341);
if (lean::is_scalar(x_307)) {
 x_345 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_345 = x_307;
}
lean::cnstr_set(x_345, 0, x_344);
lean::cnstr_set(x_345, 1, x_337);
return x_345;
}
else
{
obj* x_349; 
lean::dec(x_315);
lean::dec(x_307);
lean::dec(x_335);
x_349 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main(x_1, x_3, x_337);
return x_349;
}
}
}
}
}
default:
{
obj* x_350; obj* x_354; obj* x_355; obj* x_357; obj* x_359; 
x_350 = lean::cnstr_get(x_2, 0);
lean::inc(x_350);
lean::dec(x_2);
lean::inc(x_3);
x_354 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_3, x_4);
x_355 = lean::cnstr_get(x_354, 0);
lean::inc(x_355);
x_357 = lean::cnstr_get(x_354, 1);
lean::inc(x_357);
if (lean::is_shared(x_354)) {
 lean::dec(x_354);
 x_359 = lean::box(0);
} else {
 lean::cnstr_release(x_354, 0);
 lean::cnstr_release(x_354, 1);
 x_359 = x_354;
}
if (lean::obj_tag(x_355) == 0)
{
obj* x_362; obj* x_364; obj* x_365; obj* x_366; 
lean::dec(x_350);
lean::dec(x_3);
x_362 = lean::cnstr_get(x_355, 0);
lean::inc(x_362);
if (lean::is_shared(x_355)) {
 lean::dec(x_355);
 x_364 = lean::box(0);
} else {
 lean::cnstr_release(x_355, 0);
 x_364 = x_355;
}
if (lean::is_scalar(x_364)) {
 x_365 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_365 = x_364;
}
lean::cnstr_set(x_365, 0, x_362);
if (lean::is_scalar(x_359)) {
 x_366 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_366 = x_359;
}
lean::cnstr_set(x_366, 0, x_365);
lean::cnstr_set(x_366, 1, x_357);
return x_366;
}
else
{
obj* x_367; obj* x_368; obj* x_371; obj* x_372; obj* x_374; 
if (lean::is_shared(x_355)) {
 lean::dec(x_355);
 x_367 = lean::box(0);
} else {
 lean::cnstr_release(x_355, 0);
 x_367 = x_355;
}
x_368 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1;
lean::inc(x_3);
lean::inc(x_368);
x_371 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_368, x_3, x_357);
x_372 = lean::cnstr_get(x_371, 0);
lean::inc(x_372);
x_374 = lean::cnstr_get(x_371, 1);
lean::inc(x_374);
lean::dec(x_371);
if (lean::obj_tag(x_372) == 0)
{
obj* x_379; obj* x_382; obj* x_383; 
lean::dec(x_350);
lean::dec(x_3);
x_379 = lean::cnstr_get(x_372, 0);
lean::inc(x_379);
lean::dec(x_372);
if (lean::is_scalar(x_367)) {
 x_382 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_382 = x_367;
}
lean::cnstr_set(x_382, 0, x_379);
if (lean::is_scalar(x_359)) {
 x_383 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_383 = x_359;
}
lean::cnstr_set(x_383, 0, x_382);
lean::cnstr_set(x_383, 1, x_374);
return x_383;
}
else
{
obj* x_387; 
lean::dec(x_367);
lean::dec(x_372);
lean::dec(x_359);
x_387 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_350, x_3, x_374);
return x_387;
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string(" = false");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string(" = true");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::mk_string");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__4() {
{
obj* x_0; obj* x_1; 
x_0 = _l_s10_uint32__sz;
x_1 = lean::nat2int(x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__5() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::mk_mpz_core(lean::mpz(\"");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__6() {
{
obj* x_0; 
x_0 = lean::mk_string("\"))");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__7() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::mk_nat_obj");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
lean::dec(x_1);
x_4 = _l_s3_int_s4_repr_s6___main(x_0);
x_5 = lean::string_append(x_2, x_4);
lean::dec(x_4);
x_7 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_5);
return x_9;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
unsigned char x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
x_6 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit(x_0, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main(unsigned char x_0) {
{

switch (x_0) {
case 0:
{
obj* x_1; 
x_1 = _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__1;
lean::inc(x_1);
return x_1;
}
case 1:
{
obj* x_3; 
x_3 = _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__2;
lean::inc(x_3);
return x_3;
}
case 2:
{
obj* x_5; 
x_5 = _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__3;
lean::inc(x_5);
return x_5;
}
case 3:
{
obj* x_7; 
x_7 = _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__4;
lean::inc(x_7);
return x_7;
}
case 4:
{
obj* x_9; 
x_9 = _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__5;
lean::inc(x_9);
return x_9;
}
case 5:
{
obj* x_11; 
x_11 = _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__6;
lean::inc(x_11);
return x_11;
}
case 6:
{
obj* x_13; 
x_13 = _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__7;
lean::inc(x_13);
return x_13;
}
case 7:
{
obj* x_15; 
x_15 = _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__8;
lean::inc(x_15);
return x_15;
}
default:
{
obj* x_17; 
x_17 = _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__9;
lean::inc(x_17);
return x_17;
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::inc_ref");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::dec_ref");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::dec_shared_ref");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::inc");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__5() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::dec");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__6() {
{
obj* x_0; 
x_0 = lean::mk_string("free");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__7() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::dealloc");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__8() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::array_pop");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__9() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::sarray_pop");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main(x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp(unsigned char x_0) {
{
obj* x_1; 
x_1 = _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s7___boxed(obj* x_0) {
{
unsigned char x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp(x_1);
return x_2;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__unop(unsigned char x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_4 = _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main(x_0);
lean::inc(x_2);
x_6 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_4, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_1);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_16 = x_7;
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
if (lean::is_scalar(x_11)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_11;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_9);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_26; 
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_19 = x_7;
}
x_20 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_2);
lean::inc(x_20);
x_23 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_20, x_2, x_9);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_31; obj* x_34; obj* x_35; 
lean::dec(x_1);
lean::dec(x_2);
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
lean::dec(x_24);
if (lean::is_scalar(x_19)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_19;
}
lean::cnstr_set(x_34, 0, x_31);
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_26);
return x_35;
}
else
{
obj* x_38; obj* x_39; obj* x_41; 
lean::dec(x_24);
lean::inc(x_2);
x_38 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_1, x_2, x_26);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
if (lean::obj_tag(x_39) == 0)
{
obj* x_45; obj* x_48; obj* x_49; 
lean::dec(x_2);
x_45 = lean::cnstr_get(x_39, 0);
lean::inc(x_45);
lean::dec(x_39);
if (lean::is_scalar(x_19)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_19;
}
lean::cnstr_set(x_48, 0, x_45);
if (lean::is_scalar(x_11)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_11;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_41);
return x_49;
}
else
{
obj* x_50; obj* x_53; obj* x_55; obj* x_56; obj* x_58; 
x_50 = lean::cnstr_get(x_39, 0);
lean::inc(x_50);
lean::dec(x_39);
x_53 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_53);
x_55 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_53, x_2, x_41);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_62; obj* x_65; obj* x_66; 
lean::dec(x_50);
x_62 = lean::cnstr_get(x_56, 0);
lean::inc(x_62);
lean::dec(x_56);
if (lean::is_scalar(x_19)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_19;
}
lean::cnstr_set(x_65, 0, x_62);
if (lean::is_scalar(x_11)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_11;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_58);
return x_66;
}
else
{
obj* x_68; obj* x_69; 
lean::dec(x_56);
if (lean::is_scalar(x_19)) {
 x_68 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_68 = x_19;
}
lean::cnstr_set(x_68, 0, x_50);
if (lean::is_scalar(x_11)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_11;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_58);
return x_69;
}
}
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s10_emit__unop_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__unop(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_9; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
x_7 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__1;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::inc(x_12);
x_15 = _l_s4_list_s6_length_s6___main_s6___rarg(x_12);
x_16 = _l_s4_lean_s18_closure__max__args;
x_17 = lean::nat_dec_lt(x_16, x_15);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_28; 
lean::dec(x_12);
lean::dec(x_17);
lean::dec(x_10);
lean::inc(x_2);
x_25 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_2, x_3);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_31; obj* x_33; obj* x_34; 
x_31 = lean::cnstr_get(x_26, 0);
lean::inc(x_31);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_33 = x_26;
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_31);
x_21 = x_34;
x_22 = x_28;
goto lbl_23;
}
else
{
obj* x_36; obj* x_39; obj* x_40; obj* x_42; 
lean::dec(x_26);
x_36 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__3;
lean::inc(x_2);
lean::inc(x_36);
x_39 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_36, x_2, x_28);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
x_21 = x_40;
x_22 = x_42;
goto lbl_23;
}
lbl_23:
{

if (lean::obj_tag(x_21) == 0)
{
obj* x_48; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_15);
lean::dec(x_1);
lean::dec(x_2);
x_48 = lean::cnstr_get(x_21, 0);
lean::inc(x_48);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_50 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_50 = x_21;
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_22);
return x_52;
}
else
{
obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_60; 
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_53 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_53 = x_21;
}
lean::inc(x_2);
x_55 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s9___spec__1(x_15, x_2, x_22);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
if (lean::is_shared(x_55)) {
 lean::dec(x_55);
 x_60 = lean::box(0);
} else {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 1);
 x_60 = x_55;
}
if (lean::obj_tag(x_56) == 0)
{
obj* x_63; obj* x_66; obj* x_67; 
lean::dec(x_1);
lean::dec(x_2);
x_63 = lean::cnstr_get(x_56, 0);
lean::inc(x_63);
lean::dec(x_56);
if (lean::is_scalar(x_53)) {
 x_66 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_66 = x_53;
}
lean::cnstr_set(x_66, 0, x_63);
if (lean::is_scalar(x_60)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_60;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_58);
return x_67;
}
else
{
obj* x_69; obj* x_72; obj* x_73; obj* x_75; 
lean::dec(x_56);
x_69 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_2);
lean::inc(x_69);
x_72 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_69, x_2, x_58);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
lean::dec(x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_80; obj* x_83; obj* x_84; 
lean::dec(x_1);
lean::dec(x_2);
x_80 = lean::cnstr_get(x_73, 0);
lean::inc(x_80);
lean::dec(x_73);
if (lean::is_scalar(x_53)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_53;
}
lean::cnstr_set(x_83, 0, x_80);
if (lean::is_scalar(x_60)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_60;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_75);
return x_84;
}
else
{
obj* x_86; obj* x_87; obj* x_91; obj* x_92; obj* x_94; 
lean::dec(x_73);
x_86 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__2;
x_87 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__3;
lean::inc(x_2);
lean::inc(x_87);
lean::inc(x_86);
x_91 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg(x_86, x_87, x_1, x_2, x_75);
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_91, 1);
lean::inc(x_94);
lean::dec(x_91);
if (lean::obj_tag(x_92) == 0)
{
obj* x_98; obj* x_101; obj* x_102; 
lean::dec(x_2);
x_98 = lean::cnstr_get(x_92, 0);
lean::inc(x_98);
lean::dec(x_92);
if (lean::is_scalar(x_53)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_53;
}
lean::cnstr_set(x_101, 0, x_98);
if (lean::is_scalar(x_60)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_60;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_94);
return x_102;
}
else
{
obj* x_103; obj* x_106; obj* x_108; obj* x_109; obj* x_111; 
x_103 = lean::cnstr_get(x_92, 0);
lean::inc(x_103);
lean::dec(x_92);
x_106 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_106);
x_108 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_106, x_2, x_94);
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_108, 1);
lean::inc(x_111);
lean::dec(x_108);
if (lean::obj_tag(x_109) == 0)
{
obj* x_115; obj* x_118; obj* x_119; 
lean::dec(x_103);
x_115 = lean::cnstr_get(x_109, 0);
lean::inc(x_115);
lean::dec(x_109);
if (lean::is_scalar(x_53)) {
 x_118 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_118 = x_53;
}
lean::cnstr_set(x_118, 0, x_115);
if (lean::is_scalar(x_60)) {
 x_119 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_119 = x_60;
}
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_111);
return x_119;
}
else
{
obj* x_121; obj* x_122; 
lean::dec(x_109);
if (lean::is_scalar(x_53)) {
 x_121 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_121 = x_53;
}
lean::cnstr_set(x_121, 0, x_103);
if (lean::is_scalar(x_60)) {
 x_122 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_122 = x_60;
}
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_111);
return x_122;
}
}
}
}
}
}
}
else
{
obj* x_125; obj* x_126; obj* x_128; obj* x_129; obj* x_131; obj* x_132; obj* x_134; obj* x_135; obj* x_137; obj* x_140; obj* x_141; obj* x_143; 
lean::dec(x_17);
lean::dec(x_1);
x_137 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__8;
lean::inc(x_2);
lean::inc(x_137);
x_140 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_137, x_2, x_3);
x_141 = lean::cnstr_get(x_140, 0);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_140, 1);
lean::inc(x_143);
lean::dec(x_140);
if (lean::obj_tag(x_141) == 0)
{
obj* x_146; obj* x_148; obj* x_149; 
x_146 = lean::cnstr_get(x_141, 0);
lean::inc(x_146);
if (lean::is_shared(x_141)) {
 lean::dec(x_141);
 x_148 = lean::box(0);
} else {
 lean::cnstr_release(x_141, 0);
 x_148 = x_141;
}
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_146);
x_134 = x_149;
x_135 = x_143;
goto lbl_136;
}
else
{
obj* x_150; obj* x_153; obj* x_154; obj* x_156; 
if (lean::is_shared(x_141)) {
 lean::dec(x_141);
 x_150 = lean::box(0);
} else {
 lean::cnstr_release(x_141, 0);
 x_150 = x_141;
}
lean::inc(x_2);
lean::inc(x_15);
x_153 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s9___spec__1(x_15, x_2, x_143);
x_154 = lean::cnstr_get(x_153, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_153, 1);
lean::inc(x_156);
lean::dec(x_153);
if (lean::obj_tag(x_154) == 0)
{
obj* x_159; obj* x_162; 
x_159 = lean::cnstr_get(x_154, 0);
lean::inc(x_159);
lean::dec(x_154);
if (lean::is_scalar(x_150)) {
 x_162 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_162 = x_150;
}
lean::cnstr_set(x_162, 0, x_159);
x_134 = x_162;
x_135 = x_156;
goto lbl_136;
}
else
{
obj* x_165; obj* x_168; obj* x_169; obj* x_171; 
lean::dec(x_150);
lean::dec(x_154);
x_165 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__9;
lean::inc(x_2);
lean::inc(x_165);
x_168 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_165, x_2, x_156);
x_169 = lean::cnstr_get(x_168, 0);
lean::inc(x_169);
x_171 = lean::cnstr_get(x_168, 1);
lean::inc(x_171);
lean::dec(x_168);
x_134 = x_169;
x_135 = x_171;
goto lbl_136;
}
}
lbl_127:
{

if (lean::obj_tag(x_125) == 0)
{
obj* x_175; obj* x_177; obj* x_178; obj* x_179; 
lean::dec(x_2);
x_175 = lean::cnstr_get(x_125, 0);
lean::inc(x_175);
if (lean::is_shared(x_125)) {
 lean::dec(x_125);
 x_177 = lean::box(0);
} else {
 lean::cnstr_release(x_125, 0);
 x_177 = x_125;
}
if (lean::is_scalar(x_177)) {
 x_178 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_178 = x_177;
}
lean::cnstr_set(x_178, 0, x_175);
x_179 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_179, 0, x_178);
lean::cnstr_set(x_179, 1, x_126);
return x_179;
}
else
{
obj* x_181; obj* x_183; 
lean::dec(x_125);
x_181 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__4;
lean::inc(x_181);
x_183 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_181, x_2, x_126);
return x_183;
}
}
lbl_130:
{

if (lean::obj_tag(x_128) == 0)
{
obj* x_184; obj* x_186; obj* x_187; 
x_184 = lean::cnstr_get(x_128, 0);
lean::inc(x_184);
if (lean::is_shared(x_128)) {
 lean::dec(x_128);
 x_186 = lean::box(0);
} else {
 lean::cnstr_release(x_128, 0);
 x_186 = x_128;
}
if (lean::is_scalar(x_186)) {
 x_187 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_187 = x_186;
}
lean::cnstr_set(x_187, 0, x_184);
x_125 = x_187;
x_126 = x_129;
goto lbl_127;
}
else
{
obj* x_188; obj* x_189; obj* x_192; obj* x_193; obj* x_195; 
if (lean::is_shared(x_128)) {
 lean::dec(x_128);
 x_188 = lean::box(0);
} else {
 lean::cnstr_release(x_128, 0);
 x_188 = x_128;
}
x_189 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_2);
lean::inc(x_189);
x_192 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_189, x_2, x_129);
x_193 = lean::cnstr_get(x_192, 0);
lean::inc(x_193);
x_195 = lean::cnstr_get(x_192, 1);
lean::inc(x_195);
lean::dec(x_192);
if (lean::obj_tag(x_193) == 0)
{
obj* x_198; obj* x_201; 
x_198 = lean::cnstr_get(x_193, 0);
lean::inc(x_198);
lean::dec(x_193);
if (lean::is_scalar(x_188)) {
 x_201 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_201 = x_188;
}
lean::cnstr_set(x_201, 0, x_198);
x_125 = x_201;
x_126 = x_195;
goto lbl_127;
}
else
{
obj* x_203; obj* x_206; obj* x_207; obj* x_209; 
lean::dec(x_193);
x_203 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__5;
lean::inc(x_2);
lean::inc(x_203);
x_206 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_203, x_2, x_195);
x_207 = lean::cnstr_get(x_206, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_206, 1);
lean::inc(x_209);
lean::dec(x_206);
if (lean::obj_tag(x_207) == 0)
{
obj* x_212; obj* x_215; 
x_212 = lean::cnstr_get(x_207, 0);
lean::inc(x_212);
lean::dec(x_207);
if (lean::is_scalar(x_188)) {
 x_215 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_215 = x_188;
}
lean::cnstr_set(x_215, 0, x_212);
x_125 = x_215;
x_126 = x_209;
goto lbl_127;
}
else
{
obj* x_216; obj* x_219; obj* x_222; obj* x_223; obj* x_225; 
x_216 = lean::cnstr_get(x_207, 0);
lean::inc(x_216);
lean::dec(x_207);
x_219 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_2);
lean::inc(x_219);
x_222 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_219, x_2, x_209);
x_223 = lean::cnstr_get(x_222, 0);
lean::inc(x_223);
x_225 = lean::cnstr_get(x_222, 1);
lean::inc(x_225);
lean::dec(x_222);
if (lean::obj_tag(x_223) == 0)
{
obj* x_229; obj* x_232; 
lean::dec(x_216);
x_229 = lean::cnstr_get(x_223, 0);
lean::inc(x_229);
lean::dec(x_223);
if (lean::is_scalar(x_188)) {
 x_232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_232 = x_188;
}
lean::cnstr_set(x_232, 0, x_229);
x_125 = x_232;
x_126 = x_225;
goto lbl_127;
}
else
{
obj* x_234; 
lean::dec(x_223);
if (lean::is_scalar(x_188)) {
 x_234 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_234 = x_188;
}
lean::cnstr_set(x_234, 0, x_216);
x_125 = x_234;
x_126 = x_225;
goto lbl_127;
}
}
}
}
}
lbl_133:
{

if (lean::obj_tag(x_131) == 0)
{
obj* x_237; obj* x_239; obj* x_240; 
lean::dec(x_15);
lean::dec(x_10);
x_237 = lean::cnstr_get(x_131, 0);
lean::inc(x_237);
if (lean::is_shared(x_131)) {
 lean::dec(x_131);
 x_239 = lean::box(0);
} else {
 lean::cnstr_release(x_131, 0);
 x_239 = x_131;
}
if (lean::is_scalar(x_239)) {
 x_240 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_240 = x_239;
}
lean::cnstr_set(x_240, 0, x_237);
x_125 = x_240;
x_126 = x_132;
goto lbl_127;
}
else
{
obj* x_241; obj* x_242; obj* x_245; obj* x_246; obj* x_248; 
if (lean::is_shared(x_131)) {
 lean::dec(x_131);
 x_241 = lean::box(0);
} else {
 lean::cnstr_release(x_131, 0);
 x_241 = x_131;
}
x_242 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_2);
lean::inc(x_242);
x_245 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_242, x_2, x_132);
x_246 = lean::cnstr_get(x_245, 0);
lean::inc(x_246);
x_248 = lean::cnstr_get(x_245, 1);
lean::inc(x_248);
lean::dec(x_245);
if (lean::obj_tag(x_246) == 0)
{
obj* x_253; obj* x_256; 
lean::dec(x_15);
lean::dec(x_10);
x_253 = lean::cnstr_get(x_246, 0);
lean::inc(x_253);
lean::dec(x_246);
if (lean::is_scalar(x_241)) {
 x_256 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_256 = x_241;
}
lean::cnstr_set(x_256, 0, x_253);
x_125 = x_256;
x_126 = x_248;
goto lbl_127;
}
else
{
obj* x_259; obj* x_260; obj* x_262; 
lean::dec(x_246);
lean::inc(x_2);
x_259 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_10, x_2, x_248);
x_260 = lean::cnstr_get(x_259, 0);
lean::inc(x_260);
x_262 = lean::cnstr_get(x_259, 1);
lean::inc(x_262);
lean::dec(x_259);
if (lean::obj_tag(x_260) == 0)
{
obj* x_266; obj* x_269; 
lean::dec(x_15);
x_266 = lean::cnstr_get(x_260, 0);
lean::inc(x_266);
lean::dec(x_260);
if (lean::is_scalar(x_241)) {
 x_269 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_269 = x_241;
}
lean::cnstr_set(x_269, 0, x_266);
x_128 = x_269;
x_129 = x_262;
goto lbl_130;
}
else
{
obj* x_271; obj* x_274; obj* x_275; obj* x_277; 
lean::dec(x_260);
x_271 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_2);
lean::inc(x_271);
x_274 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_271, x_2, x_262);
x_275 = lean::cnstr_get(x_274, 0);
lean::inc(x_275);
x_277 = lean::cnstr_get(x_274, 1);
lean::inc(x_277);
lean::dec(x_274);
if (lean::obj_tag(x_275) == 0)
{
obj* x_281; obj* x_284; 
lean::dec(x_15);
x_281 = lean::cnstr_get(x_275, 0);
lean::inc(x_281);
lean::dec(x_275);
if (lean::is_scalar(x_241)) {
 x_284 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_284 = x_241;
}
lean::cnstr_set(x_284, 0, x_281);
x_128 = x_284;
x_129 = x_277;
goto lbl_130;
}
else
{
obj* x_288; obj* x_289; obj* x_291; 
lean::dec(x_241);
lean::dec(x_275);
lean::inc(x_2);
x_288 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s9___spec__1(x_15, x_2, x_277);
x_289 = lean::cnstr_get(x_288, 0);
lean::inc(x_289);
x_291 = lean::cnstr_get(x_288, 1);
lean::inc(x_291);
lean::dec(x_288);
x_128 = x_289;
x_129 = x_291;
goto lbl_130;
}
}
}
}
}
lbl_136:
{

if (lean::obj_tag(x_134) == 0)
{
obj* x_296; obj* x_298; obj* x_299; 
lean::dec(x_12);
lean::dec(x_0);
x_296 = lean::cnstr_get(x_134, 0);
lean::inc(x_296);
if (lean::is_shared(x_134)) {
 lean::dec(x_134);
 x_298 = lean::box(0);
} else {
 lean::cnstr_release(x_134, 0);
 x_298 = x_134;
}
if (lean::is_scalar(x_298)) {
 x_299 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_299 = x_298;
}
lean::cnstr_set(x_299, 0, x_296);
x_131 = x_299;
x_132 = x_135;
goto lbl_133;
}
else
{
obj* x_300; obj* x_301; obj* x_302; obj* x_306; obj* x_307; obj* x_309; 
if (lean::is_shared(x_134)) {
 lean::dec(x_134);
 x_300 = lean::box(0);
} else {
 lean::cnstr_release(x_134, 0);
 x_300 = x_134;
}
x_301 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__2;
x_302 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__3;
lean::inc(x_2);
lean::inc(x_302);
lean::inc(x_301);
x_306 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg(x_301, x_302, x_12, x_2, x_135);
x_307 = lean::cnstr_get(x_306, 0);
lean::inc(x_307);
x_309 = lean::cnstr_get(x_306, 1);
lean::inc(x_309);
lean::dec(x_306);
if (lean::obj_tag(x_307) == 0)
{
obj* x_313; obj* x_316; 
lean::dec(x_0);
x_313 = lean::cnstr_get(x_307, 0);
lean::inc(x_313);
lean::dec(x_307);
if (lean::is_scalar(x_300)) {
 x_316 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_316 = x_300;
}
lean::cnstr_set(x_316, 0, x_313);
x_131 = x_316;
x_132 = x_309;
goto lbl_133;
}
else
{
obj* x_318; obj* x_321; obj* x_322; obj* x_324; 
lean::dec(x_307);
x_318 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__6;
lean::inc(x_2);
lean::inc(x_318);
x_321 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_318, x_2, x_309);
x_322 = lean::cnstr_get(x_321, 0);
lean::inc(x_322);
x_324 = lean::cnstr_get(x_321, 1);
lean::inc(x_324);
lean::dec(x_321);
if (lean::obj_tag(x_322) == 0)
{
obj* x_328; obj* x_331; 
lean::dec(x_0);
x_328 = lean::cnstr_get(x_322, 0);
lean::inc(x_328);
lean::dec(x_322);
if (lean::is_scalar(x_300)) {
 x_331 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_331 = x_300;
}
lean::cnstr_set(x_331, 0, x_328);
x_131 = x_331;
x_132 = x_324;
goto lbl_133;
}
else
{
obj* x_334; obj* x_335; obj* x_337; 
lean::dec(x_322);
lean::inc(x_2);
x_334 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_2, x_324);
x_335 = lean::cnstr_get(x_334, 0);
lean::inc(x_335);
x_337 = lean::cnstr_get(x_334, 1);
lean::inc(x_337);
lean::dec(x_334);
if (lean::obj_tag(x_335) == 0)
{
obj* x_340; obj* x_343; 
x_340 = lean::cnstr_get(x_335, 0);
lean::inc(x_340);
lean::dec(x_335);
if (lean::is_scalar(x_300)) {
 x_343 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_343 = x_300;
}
lean::cnstr_set(x_343, 0, x_340);
x_131 = x_343;
x_132 = x_337;
goto lbl_133;
}
else
{
obj* x_346; obj* x_349; obj* x_350; obj* x_352; 
lean::dec(x_335);
lean::dec(x_300);
x_346 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__7;
lean::inc(x_2);
lean::inc(x_346);
x_349 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_346, x_2, x_337);
x_350 = lean::cnstr_get(x_349, 0);
lean::inc(x_350);
x_352 = lean::cnstr_get(x_349, 1);
lean::inc(x_352);
lean::dec(x_349);
x_131 = x_350;
x_132 = x_352;
goto lbl_133;
}
}
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__1() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("ill-formed apply");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s3_cpp_s9_emit__var), 3, 0);
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string(" = apply_");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string("; }");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__5() {
{
obj* x_0; 
x_0 = lean::mk_string("as");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__6() {
{
obj* x_0; 
x_0 = lean::mk_string("}; ");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__7() {
{
obj* x_0; 
x_0 = lean::mk_string(" = apply_m");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__8() {
{
obj* x_0; 
x_0 = lean::mk_string("{ obj * as[");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__9() {
{
obj* x_0; 
x_0 = lean::mk_string("] = {");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; obj* x_7; obj* x_11; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 3);
lean::inc(x_7);
lean::dec(x_5);
lean::inc(x_1);
x_11 = lean::apply_1(x_7, x_1);
if (lean::obj_tag(x_11) == 0)
{
obj* x_17; obj* x_19; 
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_17 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__1;
lean::inc(x_17);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_4);
return x_19;
}
else
{
obj* x_20; obj* x_25; obj* x_26; obj* x_28; obj* x_30; 
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
lean::dec(x_11);
lean::inc(x_3);
lean::inc(x_0);
x_25 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_3, x_4);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 x_30 = x_25;
}
if (lean::obj_tag(x_26) == 0)
{
obj* x_36; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_20);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_36 = lean::cnstr_get(x_26, 0);
lean::inc(x_36);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_38 = x_26;
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
if (lean::is_scalar(x_30)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_30;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_28);
return x_40;
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_51; obj* x_53; 
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_41 = x_26;
}
x_45 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__2;
lean::inc(x_3);
lean::inc(x_45);
x_48 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_45, x_3, x_28);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_53 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_53 = x_48;
}
if (lean::obj_tag(x_49) == 0)
{
obj* x_61; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_30);
lean::dec(x_20);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_41);
x_61 = lean::cnstr_get(x_49, 0);
lean::inc(x_61);
if (lean::is_shared(x_49)) {
 lean::dec(x_49);
 x_63 = lean::box(0);
} else {
 lean::cnstr_release(x_49, 0);
 x_63 = x_49;
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_61);
if (lean::is_scalar(x_53)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_53;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_51);
return x_65;
}
else
{
obj* x_66; obj* x_68; obj* x_69; obj* x_71; 
if (lean::is_shared(x_49)) {
 lean::dec(x_49);
 x_66 = lean::box(0);
} else {
 lean::cnstr_release(x_49, 0);
 x_66 = x_49;
}
lean::inc(x_3);
x_68 = _l_s4_lean_s2_ir_s3_cpp_s7_fid2cpp(x_1, x_3, x_51);
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_68, 1);
lean::inc(x_71);
lean::dec(x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_80; obj* x_83; obj* x_84; 
lean::dec(x_30);
lean::dec(x_20);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_41);
x_80 = lean::cnstr_get(x_69, 0);
lean::inc(x_80);
lean::dec(x_69);
if (lean::is_scalar(x_66)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_66;
}
lean::cnstr_set(x_83, 0, x_80);
if (lean::is_scalar(x_53)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_53;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_71);
return x_84;
}
else
{
obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_93; obj* x_94; obj* x_95; obj* x_97; obj* x_98; obj* x_101; obj* x_102; obj* x_103; 
lean::dec(x_53);
x_86 = lean::cnstr_get(x_69, 0);
lean::inc(x_86);
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_88 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 x_88 = x_69;
}
x_89 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_20);
x_90 = lean::cnstr_get(x_89, 1);
lean::inc(x_90);
lean::dec(x_89);
x_93 = _l_s4_list_s6_length_s6___main_s6___rarg(x_90);
x_94 = _l_s4_lean_s18_closure__max__args;
x_95 = lean::nat_dec_lt(x_94, x_93);
lean::inc(x_2);
x_97 = _l_s4_list_s6_length_s6___main_s6___rarg(x_2);
x_98 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__3;
lean::inc(x_3);
lean::inc(x_98);
x_101 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_98, x_3, x_71);
if (lean::obj_tag(x_95) == 0)
{
obj* x_106; obj* x_108; 
lean::dec(x_95);
x_106 = lean::cnstr_get(x_101, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_101, 1);
lean::inc(x_108);
lean::dec(x_101);
if (lean::obj_tag(x_106) == 0)
{
obj* x_112; obj* x_115; 
lean::dec(x_86);
x_112 = lean::cnstr_get(x_106, 0);
lean::inc(x_112);
lean::dec(x_106);
if (lean::is_scalar(x_88)) {
 x_115 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_115 = x_88;
}
lean::cnstr_set(x_115, 0, x_112);
x_102 = x_115;
x_103 = x_108;
goto lbl_104;
}
else
{
obj* x_119; obj* x_120; obj* x_122; 
lean::dec(x_106);
lean::dec(x_88);
lean::inc(x_3);
x_119 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_86, x_3, x_108);
x_120 = lean::cnstr_get(x_119, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_119, 1);
lean::inc(x_122);
lean::dec(x_119);
x_102 = x_120;
x_103 = x_122;
goto lbl_104;
}
}
else
{
obj* x_126; obj* x_128; 
lean::dec(x_95);
x_126 = lean::cnstr_get(x_101, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_101, 1);
lean::inc(x_128);
lean::dec(x_101);
if (lean::obj_tag(x_126) == 0)
{
obj* x_132; obj* x_135; 
lean::dec(x_86);
x_132 = lean::cnstr_get(x_126, 0);
lean::inc(x_132);
lean::dec(x_126);
if (lean::is_scalar(x_88)) {
 x_135 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_135 = x_88;
}
lean::cnstr_set(x_135, 0, x_132);
x_102 = x_135;
x_103 = x_128;
goto lbl_104;
}
else
{
obj* x_138; obj* x_140; obj* x_143; obj* x_144; obj* x_146; 
lean::dec(x_126);
lean::dec(x_88);
x_138 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__4;
lean::inc(x_138);
x_140 = lean::string_append(x_138, x_86);
lean::dec(x_86);
lean::inc(x_3);
x_143 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_140, x_3, x_128);
x_144 = lean::cnstr_get(x_143, 0);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_143, 1);
lean::inc(x_146);
lean::dec(x_143);
x_102 = x_144;
x_103 = x_146;
goto lbl_104;
}
}
lbl_104:
{

if (lean::obj_tag(x_102) == 0)
{
obj* x_151; obj* x_154; 
lean::dec(x_93);
lean::dec(x_97);
x_151 = lean::cnstr_get(x_102, 0);
lean::inc(x_151);
lean::dec(x_102);
if (lean::is_scalar(x_66)) {
 x_154 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_154 = x_66;
}
lean::cnstr_set(x_154, 0, x_151);
x_42 = x_154;
x_43 = x_103;
goto lbl_44;
}
else
{
obj* x_156; obj* x_159; obj* x_160; obj* x_162; 
lean::dec(x_102);
x_156 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_3);
lean::inc(x_156);
x_159 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_156, x_3, x_103);
x_160 = lean::cnstr_get(x_159, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_159, 1);
lean::inc(x_162);
lean::dec(x_159);
if (lean::obj_tag(x_160) == 0)
{
obj* x_167; obj* x_170; 
lean::dec(x_93);
lean::dec(x_97);
x_167 = lean::cnstr_get(x_160, 0);
lean::inc(x_167);
lean::dec(x_160);
if (lean::is_scalar(x_66)) {
 x_170 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_170 = x_66;
}
lean::cnstr_set(x_170, 0, x_167);
x_42 = x_170;
x_43 = x_162;
goto lbl_44;
}
else
{
obj* x_172; obj* x_175; obj* x_176; obj* x_178; 
lean::dec(x_160);
x_172 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_3);
lean::inc(x_172);
x_175 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_172, x_3, x_162);
x_176 = lean::cnstr_get(x_175, 0);
lean::inc(x_176);
x_178 = lean::cnstr_get(x_175, 1);
lean::inc(x_178);
lean::dec(x_175);
if (lean::obj_tag(x_176) == 0)
{
obj* x_184; obj* x_187; 
lean::dec(x_172);
lean::dec(x_93);
lean::dec(x_97);
x_184 = lean::cnstr_get(x_176, 0);
lean::inc(x_184);
lean::dec(x_176);
if (lean::is_scalar(x_66)) {
 x_187 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_187 = x_66;
}
lean::cnstr_set(x_187, 0, x_184);
x_42 = x_187;
x_43 = x_178;
goto lbl_44;
}
else
{
obj* x_190; obj* x_191; obj* x_193; 
lean::dec(x_176);
lean::inc(x_3);
x_190 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s9___spec__1(x_93, x_3, x_178);
x_191 = lean::cnstr_get(x_190, 0);
lean::inc(x_191);
x_193 = lean::cnstr_get(x_190, 1);
lean::inc(x_193);
lean::dec(x_190);
if (lean::obj_tag(x_191) == 0)
{
obj* x_198; obj* x_201; 
lean::dec(x_172);
lean::dec(x_97);
x_198 = lean::cnstr_get(x_191, 0);
lean::inc(x_198);
lean::dec(x_191);
if (lean::is_scalar(x_66)) {
 x_201 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_201 = x_66;
}
lean::cnstr_set(x_201, 0, x_198);
x_42 = x_201;
x_43 = x_193;
goto lbl_44;
}
else
{
obj* x_205; obj* x_206; obj* x_208; 
lean::dec(x_191);
lean::inc(x_3);
lean::inc(x_172);
x_205 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_172, x_3, x_193);
x_206 = lean::cnstr_get(x_205, 0);
lean::inc(x_206);
x_208 = lean::cnstr_get(x_205, 1);
lean::inc(x_208);
lean::dec(x_205);
if (lean::obj_tag(x_206) == 0)
{
obj* x_212; obj* x_215; 
lean::dec(x_97);
x_212 = lean::cnstr_get(x_206, 0);
lean::inc(x_212);
lean::dec(x_206);
if (lean::is_scalar(x_66)) {
 x_215 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_215 = x_66;
}
lean::cnstr_set(x_215, 0, x_212);
x_42 = x_215;
x_43 = x_208;
goto lbl_44;
}
else
{
obj* x_219; obj* x_220; obj* x_222; 
lean::dec(x_206);
lean::dec(x_66);
lean::inc(x_3);
x_219 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s9___spec__1(x_97, x_3, x_208);
x_220 = lean::cnstr_get(x_219, 0);
lean::inc(x_220);
x_222 = lean::cnstr_get(x_219, 1);
lean::inc(x_222);
lean::dec(x_219);
x_42 = x_220;
x_43 = x_222;
goto lbl_44;
}
}
}
}
}
}
}
}
lbl_44:
{

if (lean::obj_tag(x_42) == 0)
{
obj* x_228; obj* x_231; obj* x_232; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
x_228 = lean::cnstr_get(x_42, 0);
lean::inc(x_228);
lean::dec(x_42);
if (lean::is_scalar(x_41)) {
 x_231 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_231 = x_41;
}
lean::cnstr_set(x_231, 0, x_228);
if (lean::is_scalar(x_30)) {
 x_232 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_232 = x_30;
}
lean::cnstr_set(x_232, 0, x_231);
lean::cnstr_set(x_232, 1, x_43);
return x_232;
}
else
{
obj* x_234; obj* x_237; obj* x_238; obj* x_240; 
lean::dec(x_42);
x_234 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_3);
lean::inc(x_234);
x_237 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_234, x_3, x_43);
x_238 = lean::cnstr_get(x_237, 0);
lean::inc(x_238);
x_240 = lean::cnstr_get(x_237, 1);
lean::inc(x_240);
lean::dec(x_237);
if (lean::obj_tag(x_238) == 0)
{
obj* x_246; obj* x_249; obj* x_250; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
x_246 = lean::cnstr_get(x_238, 0);
lean::inc(x_246);
lean::dec(x_238);
if (lean::is_scalar(x_41)) {
 x_249 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_249 = x_41;
}
lean::cnstr_set(x_249, 0, x_246);
if (lean::is_scalar(x_30)) {
 x_250 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_250 = x_30;
}
lean::cnstr_set(x_250, 0, x_249);
lean::cnstr_set(x_250, 1, x_240);
return x_250;
}
else
{
obj* x_252; obj* x_253; obj* x_254; obj* x_256; 
lean::dec(x_238);
x_252 = lean::mk_nat_obj(0u);
x_253 = _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s9___spec__1(x_0, x_252, x_2, x_3, x_240);
x_254 = lean::cnstr_get(x_253, 0);
lean::inc(x_254);
x_256 = lean::cnstr_get(x_253, 1);
lean::inc(x_256);
lean::dec(x_253);
if (lean::obj_tag(x_254) == 0)
{
obj* x_259; obj* x_262; obj* x_263; 
x_259 = lean::cnstr_get(x_254, 0);
lean::inc(x_259);
lean::dec(x_254);
if (lean::is_scalar(x_41)) {
 x_262 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_262 = x_41;
}
lean::cnstr_set(x_262, 0, x_259);
if (lean::is_scalar(x_30)) {
 x_263 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_263 = x_30;
}
lean::cnstr_set(x_263, 0, x_262);
lean::cnstr_set(x_263, 1, x_256);
return x_263;
}
else
{
obj* x_266; obj* x_268; 
lean::dec(x_254);
lean::dec(x_41);
x_266 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_266);
if (lean::is_scalar(x_30)) {
 x_268 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_268 = x_30;
}
lean::cnstr_set(x_268, 0, x_266);
lean::cnstr_set(x_268, 1, x_256);
return x_268;
}
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__1() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("invalid closure");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::alloc_closure(");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string("reinterpret_cast<lean::lean_cfun>(");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string("uncurry");
return x_0;
}
}
obj* _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s9___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{

if (lean::obj_tag(x_2) == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_1);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_27; obj* x_28; obj* x_30; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::dec(x_2);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_1, x_15);
lean::dec(x_15);
x_24 = _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s9___spec__1_s11___closed__1;
lean::inc(x_3);
lean::inc(x_24);
x_27 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_24, x_3, x_4);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_10);
lean::dec(x_1);
x_35 = lean::cnstr_get(x_28, 0);
lean::inc(x_35);
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 x_37 = x_28;
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_35);
x_18 = x_38;
x_19 = x_30;
goto lbl_20;
}
else
{
obj* x_39; obj* x_40; obj* x_43; obj* x_44; obj* x_46; 
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 x_39 = x_28;
}
x_40 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_3);
lean::inc(x_40);
x_43 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_40, x_3, x_30);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_51; obj* x_54; 
lean::dec(x_10);
lean::dec(x_1);
x_51 = lean::cnstr_get(x_44, 0);
lean::inc(x_51);
lean::dec(x_44);
if (lean::is_scalar(x_39)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_39;
}
lean::cnstr_set(x_54, 0, x_51);
x_18 = x_54;
x_19 = x_46;
goto lbl_20;
}
else
{
obj* x_58; obj* x_59; obj* x_61; 
lean::dec(x_44);
lean::inc(x_3);
lean::inc(x_0);
x_58 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_3, x_46);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
if (lean::obj_tag(x_59) == 0)
{
obj* x_65; obj* x_68; 
lean::dec(x_1);
x_65 = lean::cnstr_get(x_59, 0);
lean::inc(x_65);
lean::dec(x_59);
if (lean::is_scalar(x_39)) {
 x_68 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_68 = x_39;
}
lean::cnstr_set(x_68, 0, x_65);
x_21 = x_68;
x_22 = x_61;
goto lbl_23;
}
else
{
obj* x_70; obj* x_73; obj* x_74; obj* x_76; 
lean::dec(x_59);
x_70 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_3);
lean::inc(x_70);
x_73 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_70, x_3, x_61);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_80; obj* x_83; 
lean::dec(x_1);
x_80 = lean::cnstr_get(x_74, 0);
lean::inc(x_80);
lean::dec(x_74);
if (lean::is_scalar(x_39)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_39;
}
lean::cnstr_set(x_83, 0, x_80);
x_21 = x_83;
x_22 = x_76;
goto lbl_23;
}
else
{
obj* x_87; obj* x_88; obj* x_90; 
lean::dec(x_74);
lean::dec(x_39);
lean::inc(x_3);
x_87 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s9___spec__1(x_1, x_3, x_76);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_87, 1);
lean::inc(x_90);
lean::dec(x_87);
x_21 = x_88;
x_22 = x_90;
goto lbl_23;
}
}
}
}
lbl_20:
{

if (lean::obj_tag(x_18) == 0)
{
obj* x_97; obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_12);
lean::dec(x_16);
lean::dec(x_0);
lean::dec(x_3);
x_97 = lean::cnstr_get(x_18, 0);
lean::inc(x_97);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_99 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 x_99 = x_18;
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_97);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_19);
return x_101;
}
else
{
obj* x_103; 
lean::dec(x_18);
x_103 = _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s9___spec__1(x_0, x_16, x_12, x_3, x_19);
return x_103;
}
}
lbl_23:
{

if (lean::obj_tag(x_21) == 0)
{
obj* x_105; obj* x_107; obj* x_108; 
lean::dec(x_10);
x_105 = lean::cnstr_get(x_21, 0);
lean::inc(x_105);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_107 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_107 = x_21;
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
x_18 = x_108;
x_19 = x_22;
goto lbl_20;
}
else
{
obj* x_109; obj* x_110; obj* x_113; obj* x_114; obj* x_116; 
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_109 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_109 = x_21;
}
x_110 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_3);
lean::inc(x_110);
x_113 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_110, x_3, x_22);
x_114 = lean::cnstr_get(x_113, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_113, 1);
lean::inc(x_116);
lean::dec(x_113);
if (lean::obj_tag(x_114) == 0)
{
obj* x_120; obj* x_123; 
lean::dec(x_10);
x_120 = lean::cnstr_get(x_114, 0);
lean::inc(x_120);
lean::dec(x_114);
if (lean::is_scalar(x_109)) {
 x_123 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_123 = x_109;
}
lean::cnstr_set(x_123, 0, x_120);
x_18 = x_123;
x_19 = x_116;
goto lbl_20;
}
else
{
obj* x_126; obj* x_127; obj* x_129; 
lean::dec(x_114);
lean::inc(x_3);
x_126 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_10, x_3, x_116);
x_127 = lean::cnstr_get(x_126, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_126, 1);
lean::inc(x_129);
lean::dec(x_126);
if (lean::obj_tag(x_127) == 0)
{
obj* x_132; obj* x_135; 
x_132 = lean::cnstr_get(x_127, 0);
lean::inc(x_132);
lean::dec(x_127);
if (lean::is_scalar(x_109)) {
 x_135 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_135 = x_109;
}
lean::cnstr_set(x_135, 0, x_132);
x_18 = x_135;
x_19 = x_129;
goto lbl_20;
}
else
{
obj* x_136; obj* x_139; obj* x_142; obj* x_143; obj* x_145; 
x_136 = lean::cnstr_get(x_127, 0);
lean::inc(x_136);
lean::dec(x_127);
x_139 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_3);
lean::inc(x_139);
x_142 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_139, x_3, x_129);
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_142, 1);
lean::inc(x_145);
lean::dec(x_142);
if (lean::obj_tag(x_143) == 0)
{
obj* x_149; obj* x_152; 
lean::dec(x_136);
x_149 = lean::cnstr_get(x_143, 0);
lean::inc(x_149);
lean::dec(x_143);
if (lean::is_scalar(x_109)) {
 x_152 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_152 = x_109;
}
lean::cnstr_set(x_152, 0, x_149);
x_18 = x_152;
x_19 = x_145;
goto lbl_20;
}
else
{
obj* x_154; 
lean::dec(x_143);
if (lean::is_scalar(x_109)) {
 x_154 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_154 = x_109;
}
lean::cnstr_set(x_154, 0, x_136);
x_18 = x_154;
x_19 = x_145;
goto lbl_20;
}
}
}
}
}
}
}
}
obj* _init__l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s9___spec__1_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string(";\nlean::closure_set_arg");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::inc(x_1);
x_10 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_5, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
if (lean::obj_tag(x_11) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_19 = x_11;
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
if (lean::is_scalar(x_15)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_15;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_13);
x_3 = x_21;
goto lbl_4;
}
else
{
obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_29; 
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_22 = x_11;
}
x_23 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1;
lean::inc(x_1);
lean::inc(x_23);
x_26 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_23, x_1, x_13);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_33; obj* x_36; obj* x_37; 
lean::dec(x_7);
x_33 = lean::cnstr_get(x_27, 0);
lean::inc(x_33);
lean::dec(x_27);
if (lean::is_scalar(x_22)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_22;
}
lean::cnstr_set(x_36, 0, x_33);
if (lean::is_scalar(x_15)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_15;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_29);
x_3 = x_37;
goto lbl_4;
}
else
{
obj* x_42; 
lean::dec(x_22);
lean::dec(x_15);
lean::dec(x_27);
lean::inc(x_1);
x_42 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_7, x_1, x_29);
x_3 = x_42;
goto lbl_4;
}
}
}
case 1:
{
obj* x_43; unsigned char x_45; obj* x_46; obj* x_49; 
x_43 = lean::cnstr_get(x_0, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*2);
x_46 = lean::cnstr_get(x_0, 1);
lean::inc(x_46);
lean::inc(x_1);
x_49 = _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit(x_43, x_45, x_46, x_1, x_2);
x_3 = x_49;
goto lbl_4;
}
case 2:
{
obj* x_50; unsigned char x_52; unsigned char x_53; obj* x_54; obj* x_57; 
x_50 = lean::cnstr_get(x_0, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*2);
x_53 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*2 + 1);
x_54 = lean::cnstr_get(x_0, 1);
lean::inc(x_54);
lean::inc(x_1);
x_57 = _l_s4_lean_s2_ir_s3_cpp_s18_emit__assign__unop(x_50, x_52, x_53, x_54, x_1, x_2);
x_3 = x_57;
goto lbl_4;
}
case 3:
{
obj* x_58; unsigned char x_60; unsigned char x_61; obj* x_62; obj* x_64; obj* x_67; 
x_58 = lean::cnstr_get(x_0, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*3);
x_61 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*3 + 1);
x_62 = lean::cnstr_get(x_0, 1);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_0, 2);
lean::inc(x_64);
lean::inc(x_1);
x_67 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop(x_58, x_60, x_61, x_62, x_64, x_1, x_2);
x_3 = x_67;
goto lbl_4;
}
case 4:
{
unsigned char x_68; obj* x_69; obj* x_72; 
x_68 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*1);
x_69 = lean::cnstr_get(x_0, 0);
lean::inc(x_69);
lean::inc(x_1);
x_72 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__unop(x_68, x_69, x_1, x_2);
x_3 = x_72;
goto lbl_4;
}
case 5:
{
obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_80; obj* x_83; obj* x_84; obj* x_86; 
x_73 = lean::cnstr_get(x_0, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_0, 1);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_0, 2);
lean::inc(x_77);
lean::inc(x_1);
x_83 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_73, x_1, x_2);
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
lean::dec(x_83);
if (lean::obj_tag(x_84) == 0)
{
obj* x_89; obj* x_91; obj* x_92; 
x_89 = lean::cnstr_get(x_84, 0);
lean::inc(x_89);
if (lean::is_shared(x_84)) {
 lean::dec(x_84);
 x_91 = lean::box(0);
} else {
 lean::cnstr_release(x_84, 0);
 x_91 = x_84;
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_89);
x_79 = x_92;
x_80 = x_86;
goto lbl_81;
}
else
{
obj* x_94; obj* x_97; obj* x_98; obj* x_100; 
lean::dec(x_84);
x_94 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1;
lean::inc(x_1);
lean::inc(x_94);
x_97 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_94, x_1, x_86);
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_97, 1);
lean::inc(x_100);
lean::dec(x_97);
x_79 = x_98;
x_80 = x_100;
goto lbl_81;
}
lbl_81:
{

if (lean::obj_tag(x_79) == 0)
{
obj* x_105; obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_75);
lean::dec(x_77);
x_105 = lean::cnstr_get(x_79, 0);
lean::inc(x_105);
if (lean::is_shared(x_79)) {
 lean::dec(x_79);
 x_107 = lean::box(0);
} else {
 lean::cnstr_release(x_79, 0);
 x_107 = x_79;
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
x_109 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_80);
x_3 = x_109;
goto lbl_4;
}
else
{
obj* x_110; obj* x_113; obj* x_114; obj* x_116; obj* x_118; unsigned char x_119; 
if (lean::is_shared(x_79)) {
 lean::dec(x_79);
 x_110 = lean::box(0);
} else {
 lean::cnstr_release(x_79, 0);
 x_110 = x_79;
}
lean::inc(x_1);
lean::inc(x_75);
x_113 = _l_s4_lean_s2_ir_s3_cpp_s9_is__const(x_75, x_1, x_80);
x_114 = lean::cnstr_get(x_113, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_113, 1);
lean::inc(x_116);
if (lean::is_shared(x_113)) {
 lean::dec(x_113);
 x_118 = lean::box(0);
} else {
 lean::cnstr_release(x_113, 0);
 lean::cnstr_release(x_113, 1);
 x_118 = x_113;
}
if (lean::obj_tag(x_114) == 0)
{
obj* x_125; obj* x_127; obj* x_128; obj* x_129; 
lean::dec(x_110);
lean::dec(x_75);
lean::dec(x_77);
lean::dec(x_118);
x_125 = lean::cnstr_get(x_114, 0);
lean::inc(x_125);
if (lean::is_shared(x_114)) {
 lean::dec(x_114);
 x_127 = lean::box(0);
} else {
 lean::cnstr_release(x_114, 0);
 x_127 = x_114;
}
if (lean::is_scalar(x_127)) {
 x_128 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_128 = x_127;
}
lean::cnstr_set(x_128, 0, x_125);
x_129 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_129, 0, x_128);
lean::cnstr_set(x_129, 1, x_116);
x_3 = x_129;
goto lbl_4;
}
else
{
obj* x_130; unsigned char x_133; 
x_130 = lean::cnstr_get(x_114, 0);
lean::inc(x_130);
lean::dec(x_114);
x_133 = lean::unbox(x_130);
lean::dec(x_130);
if (x_133 == 0)
{
unsigned char x_135; 
x_135 = 0;
x_119 = x_135;
goto lbl_120;
}
else
{
obj* x_140; 
lean::dec(x_110);
lean::dec(x_77);
lean::dec(x_118);
lean::inc(x_1);
x_140 = _l_s4_lean_s2_ir_s3_cpp_s12_emit__global(x_75, x_1, x_116);
x_3 = x_140;
goto lbl_4;
}
}
lbl_120:
{
obj* x_142; obj* x_143; obj* x_145; 
lean::inc(x_1);
x_142 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__fnid(x_75, x_1, x_116);
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_142, 1);
lean::inc(x_145);
lean::dec(x_142);
if (lean::obj_tag(x_143) == 0)
{
obj* x_149; obj* x_152; obj* x_153; 
lean::dec(x_77);
x_149 = lean::cnstr_get(x_143, 0);
lean::inc(x_149);
lean::dec(x_143);
if (lean::is_scalar(x_110)) {
 x_152 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_152 = x_110;
}
lean::cnstr_set(x_152, 0, x_149);
if (lean::is_scalar(x_118)) {
 x_153 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_153 = x_118;
}
lean::cnstr_set(x_153, 0, x_152);
lean::cnstr_set(x_153, 1, x_145);
x_3 = x_153;
goto lbl_4;
}
else
{
obj* x_155; obj* x_158; obj* x_159; obj* x_161; 
lean::dec(x_143);
x_155 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_155);
x_158 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_155, x_1, x_145);
x_159 = lean::cnstr_get(x_158, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_158, 1);
lean::inc(x_161);
lean::dec(x_158);
if (lean::obj_tag(x_159) == 0)
{
obj* x_165; obj* x_168; obj* x_169; 
lean::dec(x_77);
x_165 = lean::cnstr_get(x_159, 0);
lean::inc(x_165);
lean::dec(x_159);
if (lean::is_scalar(x_110)) {
 x_168 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_168 = x_110;
}
lean::cnstr_set(x_168, 0, x_165);
if (lean::is_scalar(x_118)) {
 x_169 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_169 = x_118;
}
lean::cnstr_set(x_169, 0, x_168);
lean::cnstr_set(x_169, 1, x_161);
x_3 = x_169;
goto lbl_4;
}
else
{
obj* x_171; obj* x_172; obj* x_176; obj* x_177; obj* x_179; 
lean::dec(x_159);
x_171 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__2;
x_172 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__3;
lean::inc(x_1);
lean::inc(x_172);
lean::inc(x_171);
x_176 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg(x_171, x_172, x_77, x_1, x_161);
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_176, 1);
lean::inc(x_179);
lean::dec(x_176);
if (lean::obj_tag(x_177) == 0)
{
obj* x_182; obj* x_185; obj* x_186; 
x_182 = lean::cnstr_get(x_177, 0);
lean::inc(x_182);
lean::dec(x_177);
if (lean::is_scalar(x_110)) {
 x_185 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_185 = x_110;
}
lean::cnstr_set(x_185, 0, x_182);
if (lean::is_scalar(x_118)) {
 x_186 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_186 = x_118;
}
lean::cnstr_set(x_186, 0, x_185);
lean::cnstr_set(x_186, 1, x_179);
x_3 = x_186;
goto lbl_4;
}
else
{
obj* x_187; obj* x_190; obj* x_193; obj* x_194; obj* x_196; 
x_187 = lean::cnstr_get(x_177, 0);
lean::inc(x_187);
lean::dec(x_177);
x_190 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_1);
lean::inc(x_190);
x_193 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_190, x_1, x_179);
x_194 = lean::cnstr_get(x_193, 0);
lean::inc(x_194);
x_196 = lean::cnstr_get(x_193, 1);
lean::inc(x_196);
lean::dec(x_193);
if (lean::obj_tag(x_194) == 0)
{
obj* x_200; obj* x_203; obj* x_204; 
lean::dec(x_187);
x_200 = lean::cnstr_get(x_194, 0);
lean::inc(x_200);
lean::dec(x_194);
if (lean::is_scalar(x_110)) {
 x_203 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_203 = x_110;
}
lean::cnstr_set(x_203, 0, x_200);
if (lean::is_scalar(x_118)) {
 x_204 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_204 = x_118;
}
lean::cnstr_set(x_204, 0, x_203);
lean::cnstr_set(x_204, 1, x_196);
x_3 = x_204;
goto lbl_4;
}
else
{
obj* x_206; obj* x_207; 
lean::dec(x_194);
if (lean::is_scalar(x_110)) {
 x_206 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_206 = x_110;
}
lean::cnstr_set(x_206, 0, x_187);
if (lean::is_scalar(x_118)) {
 x_207 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_207 = x_118;
}
lean::cnstr_set(x_207, 0, x_206);
lean::cnstr_set(x_207, 1, x_196);
x_3 = x_207;
goto lbl_4;
}
}
}
}
}
}
}
}
case 6:
{
obj* x_208; unsigned short x_210; unsigned short x_211; size_t x_212; obj* x_213; obj* x_214; obj* x_216; obj* x_217; obj* x_220; obj* x_221; obj* x_223; 
x_208 = lean::cnstr_get(x_0, 0);
lean::inc(x_208);
x_210 = lean::cnstr_get_scalar<unsigned short>(x_0, sizeof(void*)*2);
x_211 = lean::cnstr_get_scalar<unsigned short>(x_0, sizeof(void*)*2 + 2);
x_212 = lean::cnstr_get_scalar<size_t>(x_0, sizeof(void*)*1);
lean::inc(x_1);
x_220 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_208, x_1, x_2);
x_221 = lean::cnstr_get(x_220, 0);
lean::inc(x_221);
x_223 = lean::cnstr_get(x_220, 1);
lean::inc(x_223);
lean::dec(x_220);
if (lean::obj_tag(x_221) == 0)
{
obj* x_226; obj* x_228; obj* x_229; 
x_226 = lean::cnstr_get(x_221, 0);
lean::inc(x_226);
if (lean::is_shared(x_221)) {
 lean::dec(x_221);
 x_228 = lean::box(0);
} else {
 lean::cnstr_release(x_221, 0);
 x_228 = x_221;
}
if (lean::is_scalar(x_228)) {
 x_229 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_229 = x_228;
}
lean::cnstr_set(x_229, 0, x_226);
x_216 = x_229;
x_217 = x_223;
goto lbl_218;
}
else
{
obj* x_231; obj* x_234; obj* x_235; obj* x_237; 
lean::dec(x_221);
x_231 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__1;
lean::inc(x_1);
lean::inc(x_231);
x_234 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_231, x_1, x_223);
x_235 = lean::cnstr_get(x_234, 0);
lean::inc(x_235);
x_237 = lean::cnstr_get(x_234, 1);
lean::inc(x_237);
lean::dec(x_234);
x_216 = x_235;
x_217 = x_237;
goto lbl_218;
}
lbl_215:
{

if (lean::obj_tag(x_213) == 0)
{
obj* x_240; obj* x_242; obj* x_243; obj* x_244; 
x_240 = lean::cnstr_get(x_213, 0);
lean::inc(x_240);
if (lean::is_shared(x_213)) {
 lean::dec(x_213);
 x_242 = lean::box(0);
} else {
 lean::cnstr_release(x_213, 0);
 x_242 = x_213;
}
if (lean::is_scalar(x_242)) {
 x_243 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_243 = x_242;
}
lean::cnstr_set(x_243, 0, x_240);
x_244 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_244, 0, x_243);
lean::cnstr_set(x_244, 1, x_214);
x_3 = x_244;
goto lbl_4;
}
else
{
obj* x_245; obj* x_246; obj* x_249; obj* x_250; obj* x_252; obj* x_254; 
if (lean::is_shared(x_213)) {
 lean::dec(x_213);
 x_245 = lean::box(0);
} else {
 lean::cnstr_release(x_213, 0);
 x_245 = x_213;
}
x_246 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_246);
x_249 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_246, x_1, x_214);
x_250 = lean::cnstr_get(x_249, 0);
lean::inc(x_250);
x_252 = lean::cnstr_get(x_249, 1);
lean::inc(x_252);
if (lean::is_shared(x_249)) {
 lean::dec(x_249);
 x_254 = lean::box(0);
} else {
 lean::cnstr_release(x_249, 0);
 lean::cnstr_release(x_249, 1);
 x_254 = x_249;
}
if (lean::obj_tag(x_250) == 0)
{
obj* x_255; obj* x_258; obj* x_259; 
x_255 = lean::cnstr_get(x_250, 0);
lean::inc(x_255);
lean::dec(x_250);
if (lean::is_scalar(x_245)) {
 x_258 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_258 = x_245;
}
lean::cnstr_set(x_258, 0, x_255);
if (lean::is_scalar(x_254)) {
 x_259 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_259 = x_254;
}
lean::cnstr_set(x_259, 0, x_258);
lean::cnstr_set(x_259, 1, x_252);
x_3 = x_259;
goto lbl_4;
}
else
{
obj* x_262; obj* x_263; obj* x_265; 
lean::dec(x_250);
lean::inc(x_1);
x_262 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__1(x_212, x_1, x_252);
x_263 = lean::cnstr_get(x_262, 0);
lean::inc(x_263);
x_265 = lean::cnstr_get(x_262, 1);
lean::inc(x_265);
lean::dec(x_262);
if (lean::obj_tag(x_263) == 0)
{
obj* x_268; obj* x_271; obj* x_272; 
x_268 = lean::cnstr_get(x_263, 0);
lean::inc(x_268);
lean::dec(x_263);
if (lean::is_scalar(x_245)) {
 x_271 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_271 = x_245;
}
lean::cnstr_set(x_271, 0, x_268);
if (lean::is_scalar(x_254)) {
 x_272 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_272 = x_254;
}
lean::cnstr_set(x_272, 0, x_271);
lean::cnstr_set(x_272, 1, x_265);
x_3 = x_272;
goto lbl_4;
}
else
{
obj* x_273; obj* x_276; obj* x_279; obj* x_280; obj* x_282; 
x_273 = lean::cnstr_get(x_263, 0);
lean::inc(x_273);
lean::dec(x_263);
x_276 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_1);
lean::inc(x_276);
x_279 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_276, x_1, x_265);
x_280 = lean::cnstr_get(x_279, 0);
lean::inc(x_280);
x_282 = lean::cnstr_get(x_279, 1);
lean::inc(x_282);
lean::dec(x_279);
if (lean::obj_tag(x_280) == 0)
{
obj* x_286; obj* x_289; obj* x_290; 
lean::dec(x_273);
x_286 = lean::cnstr_get(x_280, 0);
lean::inc(x_286);
lean::dec(x_280);
if (lean::is_scalar(x_245)) {
 x_289 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_289 = x_245;
}
lean::cnstr_set(x_289, 0, x_286);
if (lean::is_scalar(x_254)) {
 x_290 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_290 = x_254;
}
lean::cnstr_set(x_290, 0, x_289);
lean::cnstr_set(x_290, 1, x_282);
x_3 = x_290;
goto lbl_4;
}
else
{
obj* x_292; obj* x_293; 
lean::dec(x_280);
if (lean::is_scalar(x_245)) {
 x_292 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_292 = x_245;
}
lean::cnstr_set(x_292, 0, x_273);
if (lean::is_scalar(x_254)) {
 x_293 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_293 = x_254;
}
lean::cnstr_set(x_293, 0, x_292);
lean::cnstr_set(x_293, 1, x_282);
x_3 = x_293;
goto lbl_4;
}
}
}
}
}
lbl_218:
{

if (lean::obj_tag(x_216) == 0)
{
obj* x_294; obj* x_296; obj* x_297; obj* x_298; 
x_294 = lean::cnstr_get(x_216, 0);
lean::inc(x_294);
if (lean::is_shared(x_216)) {
 lean::dec(x_216);
 x_296 = lean::box(0);
} else {
 lean::cnstr_release(x_216, 0);
 x_296 = x_216;
}
if (lean::is_scalar(x_296)) {
 x_297 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_297 = x_296;
}
lean::cnstr_set(x_297, 0, x_294);
x_298 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_298, 0, x_297);
lean::cnstr_set(x_298, 1, x_217);
x_3 = x_298;
goto lbl_4;
}
else
{
obj* x_299; obj* x_300; obj* x_303; obj* x_304; obj* x_306; obj* x_308; 
if (lean::is_shared(x_216)) {
 lean::dec(x_216);
 x_299 = lean::box(0);
} else {
 lean::cnstr_release(x_216, 0);
 x_299 = x_216;
}
x_300 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_300);
x_303 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_300, x_1, x_217);
x_304 = lean::cnstr_get(x_303, 0);
lean::inc(x_304);
x_306 = lean::cnstr_get(x_303, 1);
lean::inc(x_306);
if (lean::is_shared(x_303)) {
 lean::dec(x_303);
 x_308 = lean::box(0);
} else {
 lean::cnstr_release(x_303, 0);
 lean::cnstr_release(x_303, 1);
 x_308 = x_303;
}
if (lean::obj_tag(x_304) == 0)
{
obj* x_309; obj* x_312; obj* x_313; 
x_309 = lean::cnstr_get(x_304, 0);
lean::inc(x_309);
lean::dec(x_304);
if (lean::is_scalar(x_299)) {
 x_312 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_312 = x_299;
}
lean::cnstr_set(x_312, 0, x_309);
if (lean::is_scalar(x_308)) {
 x_313 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_313 = x_308;
}
lean::cnstr_set(x_313, 0, x_312);
lean::cnstr_set(x_313, 1, x_306);
x_3 = x_313;
goto lbl_4;
}
else
{
obj* x_317; obj* x_318; obj* x_320; 
lean::dec(x_308);
lean::dec(x_304);
lean::inc(x_1);
x_317 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__2(x_210, x_1, x_306);
x_318 = lean::cnstr_get(x_317, 0);
lean::inc(x_318);
x_320 = lean::cnstr_get(x_317, 1);
lean::inc(x_320);
lean::dec(x_317);
if (lean::obj_tag(x_318) == 0)
{
obj* x_323; obj* x_326; 
x_323 = lean::cnstr_get(x_318, 0);
lean::inc(x_323);
lean::dec(x_318);
if (lean::is_scalar(x_299)) {
 x_326 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_326 = x_299;
}
lean::cnstr_set(x_326, 0, x_323);
x_213 = x_326;
x_214 = x_320;
goto lbl_215;
}
else
{
obj* x_328; obj* x_331; obj* x_332; obj* x_334; 
lean::dec(x_318);
x_328 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_328);
x_331 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_328, x_1, x_320);
x_332 = lean::cnstr_get(x_331, 0);
lean::inc(x_332);
x_334 = lean::cnstr_get(x_331, 1);
lean::inc(x_334);
lean::dec(x_331);
if (lean::obj_tag(x_332) == 0)
{
obj* x_337; obj* x_340; 
x_337 = lean::cnstr_get(x_332, 0);
lean::inc(x_337);
lean::dec(x_332);
if (lean::is_scalar(x_299)) {
 x_340 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_340 = x_299;
}
lean::cnstr_set(x_340, 0, x_337);
x_213 = x_340;
x_214 = x_334;
goto lbl_215;
}
else
{
obj* x_344; obj* x_345; obj* x_347; 
lean::dec(x_299);
lean::dec(x_332);
lean::inc(x_1);
x_344 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__3(x_211, x_1, x_334);
x_345 = lean::cnstr_get(x_344, 0);
lean::inc(x_345);
x_347 = lean::cnstr_get(x_344, 1);
lean::inc(x_347);
lean::dec(x_344);
x_213 = x_345;
x_214 = x_347;
goto lbl_215;
}
}
}
}
}
}
case 7:
{
obj* x_350; unsigned short x_352; obj* x_353; obj* x_355; obj* x_356; obj* x_358; obj* x_361; obj* x_362; obj* x_364; obj* x_366; 
x_350 = lean::cnstr_get(x_0, 0);
lean::inc(x_350);
x_352 = lean::cnstr_get_scalar<unsigned short>(x_0, sizeof(void*)*2);
x_353 = lean::cnstr_get(x_0, 1);
lean::inc(x_353);
x_358 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__2;
lean::inc(x_1);
lean::inc(x_358);
x_361 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_358, x_1, x_2);
x_362 = lean::cnstr_get(x_361, 0);
lean::inc(x_362);
x_364 = lean::cnstr_get(x_361, 1);
lean::inc(x_364);
if (lean::is_shared(x_361)) {
 lean::dec(x_361);
 x_366 = lean::box(0);
} else {
 lean::cnstr_release(x_361, 0);
 lean::cnstr_release(x_361, 1);
 x_366 = x_361;
}
if (lean::obj_tag(x_362) == 0)
{
obj* x_369; obj* x_371; obj* x_372; obj* x_373; 
lean::dec(x_353);
lean::dec(x_350);
x_369 = lean::cnstr_get(x_362, 0);
lean::inc(x_369);
if (lean::is_shared(x_362)) {
 lean::dec(x_362);
 x_371 = lean::box(0);
} else {
 lean::cnstr_release(x_362, 0);
 x_371 = x_362;
}
if (lean::is_scalar(x_371)) {
 x_372 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_372 = x_371;
}
lean::cnstr_set(x_372, 0, x_369);
if (lean::is_scalar(x_366)) {
 x_373 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_373 = x_366;
}
lean::cnstr_set(x_373, 0, x_372);
lean::cnstr_set(x_373, 1, x_364);
x_3 = x_373;
goto lbl_4;
}
else
{
obj* x_374; obj* x_375; obj* x_378; obj* x_379; obj* x_381; 
if (lean::is_shared(x_362)) {
 lean::dec(x_362);
 x_374 = lean::box(0);
} else {
 lean::cnstr_release(x_362, 0);
 x_374 = x_362;
}
x_375 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_375);
x_378 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_375, x_1, x_364);
x_379 = lean::cnstr_get(x_378, 0);
lean::inc(x_379);
x_381 = lean::cnstr_get(x_378, 1);
lean::inc(x_381);
lean::dec(x_378);
if (lean::obj_tag(x_379) == 0)
{
obj* x_386; obj* x_389; obj* x_390; 
lean::dec(x_353);
lean::dec(x_350);
x_386 = lean::cnstr_get(x_379, 0);
lean::inc(x_386);
lean::dec(x_379);
if (lean::is_scalar(x_374)) {
 x_389 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_389 = x_374;
}
lean::cnstr_set(x_389, 0, x_386);
if (lean::is_scalar(x_366)) {
 x_390 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_390 = x_366;
}
lean::cnstr_set(x_390, 0, x_389);
lean::cnstr_set(x_390, 1, x_381);
x_3 = x_390;
goto lbl_4;
}
else
{
obj* x_394; obj* x_395; obj* x_397; 
lean::dec(x_366);
lean::dec(x_379);
lean::inc(x_1);
x_394 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_350, x_1, x_381);
x_395 = lean::cnstr_get(x_394, 0);
lean::inc(x_395);
x_397 = lean::cnstr_get(x_394, 1);
lean::inc(x_397);
lean::dec(x_394);
if (lean::obj_tag(x_395) == 0)
{
obj* x_400; obj* x_403; 
x_400 = lean::cnstr_get(x_395, 0);
lean::inc(x_400);
lean::dec(x_395);
if (lean::is_scalar(x_374)) {
 x_403 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_403 = x_374;
}
lean::cnstr_set(x_403, 0, x_400);
x_355 = x_403;
x_356 = x_397;
goto lbl_357;
}
else
{
obj* x_405; obj* x_408; obj* x_409; obj* x_411; 
lean::dec(x_395);
x_405 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_405);
x_408 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_405, x_1, x_397);
x_409 = lean::cnstr_get(x_408, 0);
lean::inc(x_409);
x_411 = lean::cnstr_get(x_408, 1);
lean::inc(x_411);
lean::dec(x_408);
if (lean::obj_tag(x_409) == 0)
{
obj* x_414; obj* x_417; 
x_414 = lean::cnstr_get(x_409, 0);
lean::inc(x_414);
lean::dec(x_409);
if (lean::is_scalar(x_374)) {
 x_417 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_417 = x_374;
}
lean::cnstr_set(x_417, 0, x_414);
x_355 = x_417;
x_356 = x_411;
goto lbl_357;
}
else
{
obj* x_421; obj* x_422; obj* x_424; 
lean::dec(x_409);
lean::dec(x_374);
lean::inc(x_1);
x_421 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__3(x_352, x_1, x_411);
x_422 = lean::cnstr_get(x_421, 0);
lean::inc(x_422);
x_424 = lean::cnstr_get(x_421, 1);
lean::inc(x_424);
lean::dec(x_421);
x_355 = x_422;
x_356 = x_424;
goto lbl_357;
}
}
}
}
lbl_357:
{

if (lean::obj_tag(x_355) == 0)
{
obj* x_428; obj* x_430; obj* x_431; obj* x_432; 
lean::dec(x_353);
x_428 = lean::cnstr_get(x_355, 0);
lean::inc(x_428);
if (lean::is_shared(x_355)) {
 lean::dec(x_355);
 x_430 = lean::box(0);
} else {
 lean::cnstr_release(x_355, 0);
 x_430 = x_355;
}
if (lean::is_scalar(x_430)) {
 x_431 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_431 = x_430;
}
lean::cnstr_set(x_431, 0, x_428);
x_432 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_432, 0, x_431);
lean::cnstr_set(x_432, 1, x_356);
x_3 = x_432;
goto lbl_4;
}
else
{
obj* x_433; obj* x_434; obj* x_437; obj* x_438; obj* x_440; obj* x_442; 
if (lean::is_shared(x_355)) {
 lean::dec(x_355);
 x_433 = lean::box(0);
} else {
 lean::cnstr_release(x_355, 0);
 x_433 = x_355;
}
x_434 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_434);
x_437 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_434, x_1, x_356);
x_438 = lean::cnstr_get(x_437, 0);
lean::inc(x_438);
x_440 = lean::cnstr_get(x_437, 1);
lean::inc(x_440);
if (lean::is_shared(x_437)) {
 lean::dec(x_437);
 x_442 = lean::box(0);
} else {
 lean::cnstr_release(x_437, 0);
 lean::cnstr_release(x_437, 1);
 x_442 = x_437;
}
if (lean::obj_tag(x_438) == 0)
{
obj* x_444; obj* x_447; obj* x_448; 
lean::dec(x_353);
x_444 = lean::cnstr_get(x_438, 0);
lean::inc(x_444);
lean::dec(x_438);
if (lean::is_scalar(x_433)) {
 x_447 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_447 = x_433;
}
lean::cnstr_set(x_447, 0, x_444);
if (lean::is_scalar(x_442)) {
 x_448 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_448 = x_442;
}
lean::cnstr_set(x_448, 0, x_447);
lean::cnstr_set(x_448, 1, x_440);
x_3 = x_448;
goto lbl_4;
}
else
{
obj* x_451; obj* x_452; obj* x_454; 
lean::dec(x_438);
lean::inc(x_1);
x_451 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_353, x_1, x_440);
x_452 = lean::cnstr_get(x_451, 0);
lean::inc(x_452);
x_454 = lean::cnstr_get(x_451, 1);
lean::inc(x_454);
lean::dec(x_451);
if (lean::obj_tag(x_452) == 0)
{
obj* x_457; obj* x_460; obj* x_461; 
x_457 = lean::cnstr_get(x_452, 0);
lean::inc(x_457);
lean::dec(x_452);
if (lean::is_scalar(x_433)) {
 x_460 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_460 = x_433;
}
lean::cnstr_set(x_460, 0, x_457);
if (lean::is_scalar(x_442)) {
 x_461 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_461 = x_442;
}
lean::cnstr_set(x_461, 0, x_460);
lean::cnstr_set(x_461, 1, x_454);
x_3 = x_461;
goto lbl_4;
}
else
{
obj* x_462; obj* x_465; obj* x_468; obj* x_469; obj* x_471; 
x_462 = lean::cnstr_get(x_452, 0);
lean::inc(x_462);
lean::dec(x_452);
x_465 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_1);
lean::inc(x_465);
x_468 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_465, x_1, x_454);
x_469 = lean::cnstr_get(x_468, 0);
lean::inc(x_469);
x_471 = lean::cnstr_get(x_468, 1);
lean::inc(x_471);
lean::dec(x_468);
if (lean::obj_tag(x_469) == 0)
{
obj* x_475; obj* x_478; obj* x_479; 
lean::dec(x_462);
x_475 = lean::cnstr_get(x_469, 0);
lean::inc(x_475);
lean::dec(x_469);
if (lean::is_scalar(x_433)) {
 x_478 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_478 = x_433;
}
lean::cnstr_set(x_478, 0, x_475);
if (lean::is_scalar(x_442)) {
 x_479 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_479 = x_442;
}
lean::cnstr_set(x_479, 0, x_478);
lean::cnstr_set(x_479, 1, x_471);
x_3 = x_479;
goto lbl_4;
}
else
{
obj* x_481; obj* x_482; 
lean::dec(x_469);
if (lean::is_scalar(x_433)) {
 x_481 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_481 = x_433;
}
lean::cnstr_set(x_481, 0, x_462);
if (lean::is_scalar(x_442)) {
 x_482 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_482 = x_442;
}
lean::cnstr_set(x_482, 0, x_481);
lean::cnstr_set(x_482, 1, x_471);
x_3 = x_482;
goto lbl_4;
}
}
}
}
}
}
case 8:
{
obj* x_483; obj* x_485; unsigned short x_487; obj* x_488; obj* x_489; obj* x_492; obj* x_493; obj* x_495; 
x_483 = lean::cnstr_get(x_0, 0);
lean::inc(x_483);
x_485 = lean::cnstr_get(x_0, 1);
lean::inc(x_485);
x_487 = lean::cnstr_get_scalar<unsigned short>(x_0, sizeof(void*)*2);
lean::inc(x_1);
x_492 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_483, x_1, x_2);
x_493 = lean::cnstr_get(x_492, 0);
lean::inc(x_493);
x_495 = lean::cnstr_get(x_492, 1);
lean::inc(x_495);
lean::dec(x_492);
if (lean::obj_tag(x_493) == 0)
{
obj* x_498; obj* x_500; obj* x_501; 
x_498 = lean::cnstr_get(x_493, 0);
lean::inc(x_498);
if (lean::is_shared(x_493)) {
 lean::dec(x_493);
 x_500 = lean::box(0);
} else {
 lean::cnstr_release(x_493, 0);
 x_500 = x_493;
}
if (lean::is_scalar(x_500)) {
 x_501 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_501 = x_500;
}
lean::cnstr_set(x_501, 0, x_498);
x_488 = x_501;
x_489 = x_495;
goto lbl_490;
}
else
{
obj* x_503; obj* x_506; obj* x_507; obj* x_509; 
lean::dec(x_493);
x_503 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__3;
lean::inc(x_1);
lean::inc(x_503);
x_506 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_503, x_1, x_495);
x_507 = lean::cnstr_get(x_506, 0);
lean::inc(x_507);
x_509 = lean::cnstr_get(x_506, 1);
lean::inc(x_509);
lean::dec(x_506);
x_488 = x_507;
x_489 = x_509;
goto lbl_490;
}
lbl_490:
{

if (lean::obj_tag(x_488) == 0)
{
obj* x_513; obj* x_515; obj* x_516; obj* x_517; 
lean::dec(x_485);
x_513 = lean::cnstr_get(x_488, 0);
lean::inc(x_513);
if (lean::is_shared(x_488)) {
 lean::dec(x_488);
 x_515 = lean::box(0);
} else {
 lean::cnstr_release(x_488, 0);
 x_515 = x_488;
}
if (lean::is_scalar(x_515)) {
 x_516 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_516 = x_515;
}
lean::cnstr_set(x_516, 0, x_513);
x_517 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_517, 0, x_516);
lean::cnstr_set(x_517, 1, x_489);
x_3 = x_517;
goto lbl_4;
}
else
{
obj* x_518; obj* x_519; obj* x_522; obj* x_523; obj* x_525; obj* x_527; 
if (lean::is_shared(x_488)) {
 lean::dec(x_488);
 x_518 = lean::box(0);
} else {
 lean::cnstr_release(x_488, 0);
 x_518 = x_488;
}
x_519 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_519);
x_522 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_519, x_1, x_489);
x_523 = lean::cnstr_get(x_522, 0);
lean::inc(x_523);
x_525 = lean::cnstr_get(x_522, 1);
lean::inc(x_525);
if (lean::is_shared(x_522)) {
 lean::dec(x_522);
 x_527 = lean::box(0);
} else {
 lean::cnstr_release(x_522, 0);
 lean::cnstr_release(x_522, 1);
 x_527 = x_522;
}
if (lean::obj_tag(x_523) == 0)
{
obj* x_529; obj* x_532; obj* x_533; 
lean::dec(x_485);
x_529 = lean::cnstr_get(x_523, 0);
lean::inc(x_529);
lean::dec(x_523);
if (lean::is_scalar(x_518)) {
 x_532 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_532 = x_518;
}
lean::cnstr_set(x_532, 0, x_529);
if (lean::is_scalar(x_527)) {
 x_533 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_533 = x_527;
}
lean::cnstr_set(x_533, 0, x_532);
lean::cnstr_set(x_533, 1, x_525);
x_3 = x_533;
goto lbl_4;
}
else
{
obj* x_536; obj* x_537; obj* x_539; 
lean::dec(x_523);
lean::inc(x_1);
x_536 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_485, x_1, x_525);
x_537 = lean::cnstr_get(x_536, 0);
lean::inc(x_537);
x_539 = lean::cnstr_get(x_536, 1);
lean::inc(x_539);
lean::dec(x_536);
if (lean::obj_tag(x_537) == 0)
{
obj* x_542; obj* x_545; obj* x_546; 
x_542 = lean::cnstr_get(x_537, 0);
lean::inc(x_542);
lean::dec(x_537);
if (lean::is_scalar(x_518)) {
 x_545 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_545 = x_518;
}
lean::cnstr_set(x_545, 0, x_542);
if (lean::is_scalar(x_527)) {
 x_546 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_546 = x_527;
}
lean::cnstr_set(x_546, 0, x_545);
lean::cnstr_set(x_546, 1, x_539);
x_3 = x_546;
goto lbl_4;
}
else
{
obj* x_548; obj* x_551; obj* x_552; obj* x_554; 
lean::dec(x_537);
x_548 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_548);
x_551 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_548, x_1, x_539);
x_552 = lean::cnstr_get(x_551, 0);
lean::inc(x_552);
x_554 = lean::cnstr_get(x_551, 1);
lean::inc(x_554);
lean::dec(x_551);
if (lean::obj_tag(x_552) == 0)
{
obj* x_557; obj* x_560; obj* x_561; 
x_557 = lean::cnstr_get(x_552, 0);
lean::inc(x_557);
lean::dec(x_552);
if (lean::is_scalar(x_518)) {
 x_560 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_560 = x_518;
}
lean::cnstr_set(x_560, 0, x_557);
if (lean::is_scalar(x_527)) {
 x_561 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_561 = x_527;
}
lean::cnstr_set(x_561, 0, x_560);
lean::cnstr_set(x_561, 1, x_554);
x_3 = x_561;
goto lbl_4;
}
else
{
obj* x_564; obj* x_565; obj* x_567; 
lean::dec(x_552);
lean::inc(x_1);
x_564 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__3(x_487, x_1, x_554);
x_565 = lean::cnstr_get(x_564, 0);
lean::inc(x_565);
x_567 = lean::cnstr_get(x_564, 1);
lean::inc(x_567);
lean::dec(x_564);
if (lean::obj_tag(x_565) == 0)
{
obj* x_570; obj* x_573; obj* x_574; 
x_570 = lean::cnstr_get(x_565, 0);
lean::inc(x_570);
lean::dec(x_565);
if (lean::is_scalar(x_518)) {
 x_573 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_573 = x_518;
}
lean::cnstr_set(x_573, 0, x_570);
if (lean::is_scalar(x_527)) {
 x_574 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_574 = x_527;
}
lean::cnstr_set(x_574, 0, x_573);
lean::cnstr_set(x_574, 1, x_567);
x_3 = x_574;
goto lbl_4;
}
else
{
obj* x_575; obj* x_578; obj* x_581; obj* x_582; obj* x_584; 
x_575 = lean::cnstr_get(x_565, 0);
lean::inc(x_575);
lean::dec(x_565);
x_578 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_1);
lean::inc(x_578);
x_581 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_578, x_1, x_567);
x_582 = lean::cnstr_get(x_581, 0);
lean::inc(x_582);
x_584 = lean::cnstr_get(x_581, 1);
lean::inc(x_584);
lean::dec(x_581);
if (lean::obj_tag(x_582) == 0)
{
obj* x_588; obj* x_591; obj* x_592; 
lean::dec(x_575);
x_588 = lean::cnstr_get(x_582, 0);
lean::inc(x_588);
lean::dec(x_582);
if (lean::is_scalar(x_518)) {
 x_591 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_591 = x_518;
}
lean::cnstr_set(x_591, 0, x_588);
if (lean::is_scalar(x_527)) {
 x_592 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_592 = x_527;
}
lean::cnstr_set(x_592, 0, x_591);
lean::cnstr_set(x_592, 1, x_584);
x_3 = x_592;
goto lbl_4;
}
else
{
obj* x_594; obj* x_595; 
lean::dec(x_582);
if (lean::is_scalar(x_518)) {
 x_594 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_594 = x_518;
}
lean::cnstr_set(x_594, 0, x_575);
if (lean::is_scalar(x_527)) {
 x_595 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_595 = x_527;
}
lean::cnstr_set(x_595, 0, x_594);
lean::cnstr_set(x_595, 1, x_584);
x_3 = x_595;
goto lbl_4;
}
}
}
}
}
}
}
}
case 9:
{
obj* x_596; size_t x_598; obj* x_599; obj* x_601; obj* x_602; obj* x_604; obj* x_607; obj* x_608; obj* x_610; obj* x_612; 
x_596 = lean::cnstr_get(x_0, 0);
lean::inc(x_596);
x_598 = lean::cnstr_get_scalar<size_t>(x_0, sizeof(void*)*2);
x_599 = lean::cnstr_get(x_0, 1);
lean::inc(x_599);
x_604 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__4;
lean::inc(x_1);
lean::inc(x_604);
x_607 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_604, x_1, x_2);
x_608 = lean::cnstr_get(x_607, 0);
lean::inc(x_608);
x_610 = lean::cnstr_get(x_607, 1);
lean::inc(x_610);
if (lean::is_shared(x_607)) {
 lean::dec(x_607);
 x_612 = lean::box(0);
} else {
 lean::cnstr_release(x_607, 0);
 lean::cnstr_release(x_607, 1);
 x_612 = x_607;
}
if (lean::obj_tag(x_608) == 0)
{
obj* x_615; obj* x_617; obj* x_618; obj* x_619; 
lean::dec(x_599);
lean::dec(x_596);
x_615 = lean::cnstr_get(x_608, 0);
lean::inc(x_615);
if (lean::is_shared(x_608)) {
 lean::dec(x_608);
 x_617 = lean::box(0);
} else {
 lean::cnstr_release(x_608, 0);
 x_617 = x_608;
}
if (lean::is_scalar(x_617)) {
 x_618 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_618 = x_617;
}
lean::cnstr_set(x_618, 0, x_615);
if (lean::is_scalar(x_612)) {
 x_619 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_619 = x_612;
}
lean::cnstr_set(x_619, 0, x_618);
lean::cnstr_set(x_619, 1, x_610);
x_3 = x_619;
goto lbl_4;
}
else
{
obj* x_620; obj* x_621; obj* x_624; obj* x_625; obj* x_627; 
if (lean::is_shared(x_608)) {
 lean::dec(x_608);
 x_620 = lean::box(0);
} else {
 lean::cnstr_release(x_608, 0);
 x_620 = x_608;
}
x_621 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_621);
x_624 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_621, x_1, x_610);
x_625 = lean::cnstr_get(x_624, 0);
lean::inc(x_625);
x_627 = lean::cnstr_get(x_624, 1);
lean::inc(x_627);
lean::dec(x_624);
if (lean::obj_tag(x_625) == 0)
{
obj* x_632; obj* x_635; obj* x_636; 
lean::dec(x_599);
lean::dec(x_596);
x_632 = lean::cnstr_get(x_625, 0);
lean::inc(x_632);
lean::dec(x_625);
if (lean::is_scalar(x_620)) {
 x_635 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_635 = x_620;
}
lean::cnstr_set(x_635, 0, x_632);
if (lean::is_scalar(x_612)) {
 x_636 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_636 = x_612;
}
lean::cnstr_set(x_636, 0, x_635);
lean::cnstr_set(x_636, 1, x_627);
x_3 = x_636;
goto lbl_4;
}
else
{
obj* x_640; obj* x_641; obj* x_643; 
lean::dec(x_612);
lean::dec(x_625);
lean::inc(x_1);
x_640 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_596, x_1, x_627);
x_641 = lean::cnstr_get(x_640, 0);
lean::inc(x_641);
x_643 = lean::cnstr_get(x_640, 1);
lean::inc(x_643);
lean::dec(x_640);
if (lean::obj_tag(x_641) == 0)
{
obj* x_646; obj* x_649; 
x_646 = lean::cnstr_get(x_641, 0);
lean::inc(x_646);
lean::dec(x_641);
if (lean::is_scalar(x_620)) {
 x_649 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_649 = x_620;
}
lean::cnstr_set(x_649, 0, x_646);
x_601 = x_649;
x_602 = x_643;
goto lbl_603;
}
else
{
obj* x_651; obj* x_654; obj* x_655; obj* x_657; 
lean::dec(x_641);
x_651 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_651);
x_654 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_651, x_1, x_643);
x_655 = lean::cnstr_get(x_654, 0);
lean::inc(x_655);
x_657 = lean::cnstr_get(x_654, 1);
lean::inc(x_657);
lean::dec(x_654);
if (lean::obj_tag(x_655) == 0)
{
obj* x_660; obj* x_663; 
x_660 = lean::cnstr_get(x_655, 0);
lean::inc(x_660);
lean::dec(x_655);
if (lean::is_scalar(x_620)) {
 x_663 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_663 = x_620;
}
lean::cnstr_set(x_663, 0, x_660);
x_601 = x_663;
x_602 = x_657;
goto lbl_603;
}
else
{
obj* x_667; obj* x_668; obj* x_670; 
lean::dec(x_655);
lean::dec(x_620);
lean::inc(x_1);
x_667 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__1(x_598, x_1, x_657);
x_668 = lean::cnstr_get(x_667, 0);
lean::inc(x_668);
x_670 = lean::cnstr_get(x_667, 1);
lean::inc(x_670);
lean::dec(x_667);
x_601 = x_668;
x_602 = x_670;
goto lbl_603;
}
}
}
}
lbl_603:
{

if (lean::obj_tag(x_601) == 0)
{
obj* x_674; obj* x_676; obj* x_677; obj* x_678; 
lean::dec(x_599);
x_674 = lean::cnstr_get(x_601, 0);
lean::inc(x_674);
if (lean::is_shared(x_601)) {
 lean::dec(x_601);
 x_676 = lean::box(0);
} else {
 lean::cnstr_release(x_601, 0);
 x_676 = x_601;
}
if (lean::is_scalar(x_676)) {
 x_677 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_677 = x_676;
}
lean::cnstr_set(x_677, 0, x_674);
x_678 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_678, 0, x_677);
lean::cnstr_set(x_678, 1, x_602);
x_3 = x_678;
goto lbl_4;
}
else
{
obj* x_679; obj* x_680; obj* x_683; obj* x_684; obj* x_686; obj* x_688; 
if (lean::is_shared(x_601)) {
 lean::dec(x_601);
 x_679 = lean::box(0);
} else {
 lean::cnstr_release(x_601, 0);
 x_679 = x_601;
}
x_680 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_680);
x_683 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_680, x_1, x_602);
x_684 = lean::cnstr_get(x_683, 0);
lean::inc(x_684);
x_686 = lean::cnstr_get(x_683, 1);
lean::inc(x_686);
if (lean::is_shared(x_683)) {
 lean::dec(x_683);
 x_688 = lean::box(0);
} else {
 lean::cnstr_release(x_683, 0);
 lean::cnstr_release(x_683, 1);
 x_688 = x_683;
}
if (lean::obj_tag(x_684) == 0)
{
obj* x_690; obj* x_693; obj* x_694; 
lean::dec(x_599);
x_690 = lean::cnstr_get(x_684, 0);
lean::inc(x_690);
lean::dec(x_684);
if (lean::is_scalar(x_679)) {
 x_693 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_693 = x_679;
}
lean::cnstr_set(x_693, 0, x_690);
if (lean::is_scalar(x_688)) {
 x_694 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_694 = x_688;
}
lean::cnstr_set(x_694, 0, x_693);
lean::cnstr_set(x_694, 1, x_686);
x_3 = x_694;
goto lbl_4;
}
else
{
obj* x_697; obj* x_698; obj* x_700; 
lean::dec(x_684);
lean::inc(x_1);
x_697 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_599, x_1, x_686);
x_698 = lean::cnstr_get(x_697, 0);
lean::inc(x_698);
x_700 = lean::cnstr_get(x_697, 1);
lean::inc(x_700);
lean::dec(x_697);
if (lean::obj_tag(x_698) == 0)
{
obj* x_703; obj* x_706; obj* x_707; 
x_703 = lean::cnstr_get(x_698, 0);
lean::inc(x_703);
lean::dec(x_698);
if (lean::is_scalar(x_679)) {
 x_706 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_706 = x_679;
}
lean::cnstr_set(x_706, 0, x_703);
if (lean::is_scalar(x_688)) {
 x_707 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_707 = x_688;
}
lean::cnstr_set(x_707, 0, x_706);
lean::cnstr_set(x_707, 1, x_700);
x_3 = x_707;
goto lbl_4;
}
else
{
obj* x_708; obj* x_711; obj* x_714; obj* x_715; obj* x_717; 
x_708 = lean::cnstr_get(x_698, 0);
lean::inc(x_708);
lean::dec(x_698);
x_711 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_1);
lean::inc(x_711);
x_714 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_711, x_1, x_700);
x_715 = lean::cnstr_get(x_714, 0);
lean::inc(x_715);
x_717 = lean::cnstr_get(x_714, 1);
lean::inc(x_717);
lean::dec(x_714);
if (lean::obj_tag(x_715) == 0)
{
obj* x_721; obj* x_724; obj* x_725; 
lean::dec(x_708);
x_721 = lean::cnstr_get(x_715, 0);
lean::inc(x_721);
lean::dec(x_715);
if (lean::is_scalar(x_679)) {
 x_724 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_724 = x_679;
}
lean::cnstr_set(x_724, 0, x_721);
if (lean::is_scalar(x_688)) {
 x_725 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_725 = x_688;
}
lean::cnstr_set(x_725, 0, x_724);
lean::cnstr_set(x_725, 1, x_717);
x_3 = x_725;
goto lbl_4;
}
else
{
obj* x_727; obj* x_728; 
lean::dec(x_715);
if (lean::is_scalar(x_679)) {
 x_727 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_727 = x_679;
}
lean::cnstr_set(x_727, 0, x_708);
if (lean::is_scalar(x_688)) {
 x_728 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_728 = x_688;
}
lean::cnstr_set(x_728, 0, x_727);
lean::cnstr_set(x_728, 1, x_717);
x_3 = x_728;
goto lbl_4;
}
}
}
}
}
}
case 10:
{
obj* x_729; unsigned char x_731; obj* x_732; size_t x_734; obj* x_735; obj* x_736; obj* x_739; obj* x_740; obj* x_742; 
x_729 = lean::cnstr_get(x_0, 0);
lean::inc(x_729);
x_731 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*3);
x_732 = lean::cnstr_get(x_0, 1);
lean::inc(x_732);
x_734 = lean::cnstr_get_scalar<size_t>(x_0, sizeof(void*)*2);
lean::inc(x_1);
x_739 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_729, x_1, x_2);
x_740 = lean::cnstr_get(x_739, 0);
lean::inc(x_740);
x_742 = lean::cnstr_get(x_739, 1);
lean::inc(x_742);
lean::dec(x_739);
if (lean::obj_tag(x_740) == 0)
{
obj* x_745; obj* x_747; obj* x_748; 
x_745 = lean::cnstr_get(x_740, 0);
lean::inc(x_745);
if (lean::is_shared(x_740)) {
 lean::dec(x_740);
 x_747 = lean::box(0);
} else {
 lean::cnstr_release(x_740, 0);
 x_747 = x_740;
}
if (lean::is_scalar(x_747)) {
 x_748 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_748 = x_747;
}
lean::cnstr_set(x_748, 0, x_745);
x_735 = x_748;
x_736 = x_742;
goto lbl_737;
}
else
{
obj* x_749; obj* x_750; obj* x_753; obj* x_754; obj* x_756; 
if (lean::is_shared(x_740)) {
 lean::dec(x_740);
 x_749 = lean::box(0);
} else {
 lean::cnstr_release(x_740, 0);
 x_749 = x_740;
}
x_750 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__5;
lean::inc(x_1);
lean::inc(x_750);
x_753 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_750, x_1, x_742);
x_754 = lean::cnstr_get(x_753, 0);
lean::inc(x_754);
x_756 = lean::cnstr_get(x_753, 1);
lean::inc(x_756);
lean::dec(x_753);
if (lean::obj_tag(x_754) == 0)
{
obj* x_759; obj* x_762; 
x_759 = lean::cnstr_get(x_754, 0);
lean::inc(x_759);
lean::dec(x_754);
if (lean::is_scalar(x_749)) {
 x_762 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_762 = x_749;
}
lean::cnstr_set(x_762, 0, x_759);
x_735 = x_762;
x_736 = x_756;
goto lbl_737;
}
else
{
obj* x_766; obj* x_767; obj* x_769; 
lean::dec(x_754);
lean::dec(x_749);
lean::inc(x_1);
x_766 = _l_s4_lean_s2_ir_s3_cpp_s21_emit__template__param(x_731, x_1, x_756);
x_767 = lean::cnstr_get(x_766, 0);
lean::inc(x_767);
x_769 = lean::cnstr_get(x_766, 1);
lean::inc(x_769);
lean::dec(x_766);
x_735 = x_767;
x_736 = x_769;
goto lbl_737;
}
}
lbl_737:
{

if (lean::obj_tag(x_735) == 0)
{
obj* x_773; obj* x_775; obj* x_776; obj* x_777; 
lean::dec(x_732);
x_773 = lean::cnstr_get(x_735, 0);
lean::inc(x_773);
if (lean::is_shared(x_735)) {
 lean::dec(x_735);
 x_775 = lean::box(0);
} else {
 lean::cnstr_release(x_735, 0);
 x_775 = x_735;
}
if (lean::is_scalar(x_775)) {
 x_776 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_776 = x_775;
}
lean::cnstr_set(x_776, 0, x_773);
x_777 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_777, 0, x_776);
lean::cnstr_set(x_777, 1, x_736);
x_3 = x_777;
goto lbl_4;
}
else
{
obj* x_778; obj* x_779; obj* x_782; obj* x_783; obj* x_785; obj* x_787; 
if (lean::is_shared(x_735)) {
 lean::dec(x_735);
 x_778 = lean::box(0);
} else {
 lean::cnstr_release(x_735, 0);
 x_778 = x_735;
}
x_779 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_779);
x_782 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_779, x_1, x_736);
x_783 = lean::cnstr_get(x_782, 0);
lean::inc(x_783);
x_785 = lean::cnstr_get(x_782, 1);
lean::inc(x_785);
if (lean::is_shared(x_782)) {
 lean::dec(x_782);
 x_787 = lean::box(0);
} else {
 lean::cnstr_release(x_782, 0);
 lean::cnstr_release(x_782, 1);
 x_787 = x_782;
}
if (lean::obj_tag(x_783) == 0)
{
obj* x_789; obj* x_792; obj* x_793; 
lean::dec(x_732);
x_789 = lean::cnstr_get(x_783, 0);
lean::inc(x_789);
lean::dec(x_783);
if (lean::is_scalar(x_778)) {
 x_792 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_792 = x_778;
}
lean::cnstr_set(x_792, 0, x_789);
if (lean::is_scalar(x_787)) {
 x_793 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_793 = x_787;
}
lean::cnstr_set(x_793, 0, x_792);
lean::cnstr_set(x_793, 1, x_785);
x_3 = x_793;
goto lbl_4;
}
else
{
obj* x_796; obj* x_797; obj* x_799; 
lean::dec(x_783);
lean::inc(x_1);
x_796 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_732, x_1, x_785);
x_797 = lean::cnstr_get(x_796, 0);
lean::inc(x_797);
x_799 = lean::cnstr_get(x_796, 1);
lean::inc(x_799);
lean::dec(x_796);
if (lean::obj_tag(x_797) == 0)
{
obj* x_802; obj* x_805; obj* x_806; 
x_802 = lean::cnstr_get(x_797, 0);
lean::inc(x_802);
lean::dec(x_797);
if (lean::is_scalar(x_778)) {
 x_805 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_805 = x_778;
}
lean::cnstr_set(x_805, 0, x_802);
if (lean::is_scalar(x_787)) {
 x_806 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_806 = x_787;
}
lean::cnstr_set(x_806, 0, x_805);
lean::cnstr_set(x_806, 1, x_799);
x_3 = x_806;
goto lbl_4;
}
else
{
obj* x_808; obj* x_811; obj* x_812; obj* x_814; 
lean::dec(x_797);
x_808 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_808);
x_811 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_808, x_1, x_799);
x_812 = lean::cnstr_get(x_811, 0);
lean::inc(x_812);
x_814 = lean::cnstr_get(x_811, 1);
lean::inc(x_814);
lean::dec(x_811);
if (lean::obj_tag(x_812) == 0)
{
obj* x_817; obj* x_820; obj* x_821; 
x_817 = lean::cnstr_get(x_812, 0);
lean::inc(x_817);
lean::dec(x_812);
if (lean::is_scalar(x_778)) {
 x_820 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_820 = x_778;
}
lean::cnstr_set(x_820, 0, x_817);
if (lean::is_scalar(x_787)) {
 x_821 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_821 = x_787;
}
lean::cnstr_set(x_821, 0, x_820);
lean::cnstr_set(x_821, 1, x_814);
x_3 = x_821;
goto lbl_4;
}
else
{
obj* x_824; obj* x_825; obj* x_827; 
lean::dec(x_812);
lean::inc(x_1);
x_824 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__1(x_734, x_1, x_814);
x_825 = lean::cnstr_get(x_824, 0);
lean::inc(x_825);
x_827 = lean::cnstr_get(x_824, 1);
lean::inc(x_827);
lean::dec(x_824);
if (lean::obj_tag(x_825) == 0)
{
obj* x_830; obj* x_833; obj* x_834; 
x_830 = lean::cnstr_get(x_825, 0);
lean::inc(x_830);
lean::dec(x_825);
if (lean::is_scalar(x_778)) {
 x_833 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_833 = x_778;
}
lean::cnstr_set(x_833, 0, x_830);
if (lean::is_scalar(x_787)) {
 x_834 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_834 = x_787;
}
lean::cnstr_set(x_834, 0, x_833);
lean::cnstr_set(x_834, 1, x_827);
x_3 = x_834;
goto lbl_4;
}
else
{
obj* x_835; obj* x_838; obj* x_841; obj* x_842; obj* x_844; 
x_835 = lean::cnstr_get(x_825, 0);
lean::inc(x_835);
lean::dec(x_825);
x_838 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_1);
lean::inc(x_838);
x_841 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_838, x_1, x_827);
x_842 = lean::cnstr_get(x_841, 0);
lean::inc(x_842);
x_844 = lean::cnstr_get(x_841, 1);
lean::inc(x_844);
lean::dec(x_841);
if (lean::obj_tag(x_842) == 0)
{
obj* x_848; obj* x_851; obj* x_852; 
lean::dec(x_835);
x_848 = lean::cnstr_get(x_842, 0);
lean::inc(x_848);
lean::dec(x_842);
if (lean::is_scalar(x_778)) {
 x_851 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_851 = x_778;
}
lean::cnstr_set(x_851, 0, x_848);
if (lean::is_scalar(x_787)) {
 x_852 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_852 = x_787;
}
lean::cnstr_set(x_852, 0, x_851);
lean::cnstr_set(x_852, 1, x_844);
x_3 = x_852;
goto lbl_4;
}
else
{
obj* x_854; obj* x_855; 
lean::dec(x_842);
if (lean::is_scalar(x_778)) {
 x_854 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_854 = x_778;
}
lean::cnstr_set(x_854, 0, x_835);
if (lean::is_scalar(x_787)) {
 x_855 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_855 = x_787;
}
lean::cnstr_set(x_855, 0, x_854);
lean::cnstr_set(x_855, 1, x_844);
x_3 = x_855;
goto lbl_4;
}
}
}
}
}
}
}
}
case 11:
{
obj* x_856; obj* x_858; obj* x_860; obj* x_863; 
x_856 = lean::cnstr_get(x_0, 0);
lean::inc(x_856);
x_858 = lean::cnstr_get(x_0, 1);
lean::inc(x_858);
x_860 = lean::cnstr_get(x_0, 2);
lean::inc(x_860);
lean::inc(x_1);
x_863 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure(x_856, x_858, x_860, x_1, x_2);
x_3 = x_863;
goto lbl_4;
}
case 12:
{
obj* x_864; obj* x_866; obj* x_869; 
x_864 = lean::cnstr_get(x_0, 0);
lean::inc(x_864);
x_866 = lean::cnstr_get(x_0, 1);
lean::inc(x_866);
lean::inc(x_1);
x_869 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply(x_864, x_866, x_1, x_2);
x_3 = x_869;
goto lbl_4;
}
case 13:
{
obj* x_870; obj* x_872; obj* x_874; obj* x_876; obj* x_877; obj* x_880; obj* x_881; obj* x_883; 
x_870 = lean::cnstr_get(x_0, 0);
lean::inc(x_870);
x_872 = lean::cnstr_get(x_0, 1);
lean::inc(x_872);
x_874 = lean::cnstr_get(x_0, 2);
lean::inc(x_874);
lean::inc(x_1);
x_880 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_870, x_1, x_2);
x_881 = lean::cnstr_get(x_880, 0);
lean::inc(x_881);
x_883 = lean::cnstr_get(x_880, 1);
lean::inc(x_883);
lean::dec(x_880);
if (lean::obj_tag(x_881) == 0)
{
obj* x_886; obj* x_888; obj* x_889; 
x_886 = lean::cnstr_get(x_881, 0);
lean::inc(x_886);
if (lean::is_shared(x_881)) {
 lean::dec(x_881);
 x_888 = lean::box(0);
} else {
 lean::cnstr_release(x_881, 0);
 x_888 = x_881;
}
if (lean::is_scalar(x_888)) {
 x_889 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_889 = x_888;
}
lean::cnstr_set(x_889, 0, x_886);
x_876 = x_889;
x_877 = x_883;
goto lbl_878;
}
else
{
obj* x_891; obj* x_894; obj* x_895; obj* x_897; 
lean::dec(x_881);
x_891 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__6;
lean::inc(x_1);
lean::inc(x_891);
x_894 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_891, x_1, x_883);
x_895 = lean::cnstr_get(x_894, 0);
lean::inc(x_895);
x_897 = lean::cnstr_get(x_894, 1);
lean::inc(x_897);
lean::dec(x_894);
x_876 = x_895;
x_877 = x_897;
goto lbl_878;
}
lbl_878:
{

if (lean::obj_tag(x_876) == 0)
{
obj* x_902; obj* x_904; obj* x_905; obj* x_906; 
lean::dec(x_872);
lean::dec(x_874);
x_902 = lean::cnstr_get(x_876, 0);
lean::inc(x_902);
if (lean::is_shared(x_876)) {
 lean::dec(x_876);
 x_904 = lean::box(0);
} else {
 lean::cnstr_release(x_876, 0);
 x_904 = x_876;
}
if (lean::is_scalar(x_904)) {
 x_905 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_905 = x_904;
}
lean::cnstr_set(x_905, 0, x_902);
x_906 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_906, 0, x_905);
lean::cnstr_set(x_906, 1, x_877);
x_3 = x_906;
goto lbl_4;
}
else
{
obj* x_907; obj* x_908; obj* x_911; obj* x_912; obj* x_914; obj* x_916; 
if (lean::is_shared(x_876)) {
 lean::dec(x_876);
 x_907 = lean::box(0);
} else {
 lean::cnstr_release(x_876, 0);
 x_907 = x_876;
}
x_908 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_908);
x_911 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_908, x_1, x_877);
x_912 = lean::cnstr_get(x_911, 0);
lean::inc(x_912);
x_914 = lean::cnstr_get(x_911, 1);
lean::inc(x_914);
if (lean::is_shared(x_911)) {
 lean::dec(x_911);
 x_916 = lean::box(0);
} else {
 lean::cnstr_release(x_911, 0);
 lean::cnstr_release(x_911, 1);
 x_916 = x_911;
}
if (lean::obj_tag(x_912) == 0)
{
obj* x_919; obj* x_922; obj* x_923; 
lean::dec(x_872);
lean::dec(x_874);
x_919 = lean::cnstr_get(x_912, 0);
lean::inc(x_919);
lean::dec(x_912);
if (lean::is_scalar(x_907)) {
 x_922 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_922 = x_907;
}
lean::cnstr_set(x_922, 0, x_919);
if (lean::is_scalar(x_916)) {
 x_923 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_923 = x_916;
}
lean::cnstr_set(x_923, 0, x_922);
lean::cnstr_set(x_923, 1, x_914);
x_3 = x_923;
goto lbl_4;
}
else
{
obj* x_926; obj* x_927; obj* x_929; 
lean::dec(x_912);
lean::inc(x_1);
x_926 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_872, x_1, x_914);
x_927 = lean::cnstr_get(x_926, 0);
lean::inc(x_927);
x_929 = lean::cnstr_get(x_926, 1);
lean::inc(x_929);
lean::dec(x_926);
if (lean::obj_tag(x_927) == 0)
{
obj* x_933; obj* x_936; obj* x_937; 
lean::dec(x_874);
x_933 = lean::cnstr_get(x_927, 0);
lean::inc(x_933);
lean::dec(x_927);
if (lean::is_scalar(x_907)) {
 x_936 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_936 = x_907;
}
lean::cnstr_set(x_936, 0, x_933);
if (lean::is_scalar(x_916)) {
 x_937 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_937 = x_916;
}
lean::cnstr_set(x_937, 0, x_936);
lean::cnstr_set(x_937, 1, x_929);
x_3 = x_937;
goto lbl_4;
}
else
{
obj* x_939; obj* x_942; obj* x_943; obj* x_945; 
lean::dec(x_927);
x_939 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_939);
x_942 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_939, x_1, x_929);
x_943 = lean::cnstr_get(x_942, 0);
lean::inc(x_943);
x_945 = lean::cnstr_get(x_942, 1);
lean::inc(x_945);
lean::dec(x_942);
if (lean::obj_tag(x_943) == 0)
{
obj* x_949; obj* x_952; obj* x_953; 
lean::dec(x_874);
x_949 = lean::cnstr_get(x_943, 0);
lean::inc(x_949);
lean::dec(x_943);
if (lean::is_scalar(x_907)) {
 x_952 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_952 = x_907;
}
lean::cnstr_set(x_952, 0, x_949);
if (lean::is_scalar(x_916)) {
 x_953 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_953 = x_916;
}
lean::cnstr_set(x_953, 0, x_952);
lean::cnstr_set(x_953, 1, x_945);
x_3 = x_953;
goto lbl_4;
}
else
{
obj* x_956; obj* x_957; obj* x_959; 
lean::dec(x_943);
lean::inc(x_1);
x_956 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_874, x_1, x_945);
x_957 = lean::cnstr_get(x_956, 0);
lean::inc(x_957);
x_959 = lean::cnstr_get(x_956, 1);
lean::inc(x_959);
lean::dec(x_956);
if (lean::obj_tag(x_957) == 0)
{
obj* x_962; obj* x_965; obj* x_966; 
x_962 = lean::cnstr_get(x_957, 0);
lean::inc(x_962);
lean::dec(x_957);
if (lean::is_scalar(x_907)) {
 x_965 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_965 = x_907;
}
lean::cnstr_set(x_965, 0, x_962);
if (lean::is_scalar(x_916)) {
 x_966 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_966 = x_916;
}
lean::cnstr_set(x_966, 0, x_965);
lean::cnstr_set(x_966, 1, x_959);
x_3 = x_966;
goto lbl_4;
}
else
{
obj* x_967; obj* x_970; obj* x_973; obj* x_974; obj* x_976; 
x_967 = lean::cnstr_get(x_957, 0);
lean::inc(x_967);
lean::dec(x_957);
x_970 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_1);
lean::inc(x_970);
x_973 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_970, x_1, x_959);
x_974 = lean::cnstr_get(x_973, 0);
lean::inc(x_974);
x_976 = lean::cnstr_get(x_973, 1);
lean::inc(x_976);
lean::dec(x_973);
if (lean::obj_tag(x_974) == 0)
{
obj* x_980; obj* x_983; obj* x_984; 
lean::dec(x_967);
x_980 = lean::cnstr_get(x_974, 0);
lean::inc(x_980);
lean::dec(x_974);
if (lean::is_scalar(x_907)) {
 x_983 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_983 = x_907;
}
lean::cnstr_set(x_983, 0, x_980);
if (lean::is_scalar(x_916)) {
 x_984 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_984 = x_916;
}
lean::cnstr_set(x_984, 0, x_983);
lean::cnstr_set(x_984, 1, x_976);
x_3 = x_984;
goto lbl_4;
}
else
{
obj* x_986; obj* x_987; 
lean::dec(x_974);
if (lean::is_scalar(x_907)) {
 x_986 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_986 = x_907;
}
lean::cnstr_set(x_986, 0, x_967);
if (lean::is_scalar(x_916)) {
 x_987 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_987 = x_916;
}
lean::cnstr_set(x_987, 0, x_986);
lean::cnstr_set(x_987, 1, x_976);
x_3 = x_987;
goto lbl_4;
}
}
}
}
}
}
}
}
case 14:
{
obj* x_988; unsigned char x_990; obj* x_991; obj* x_993; obj* x_995; obj* x_996; obj* x_998; obj* x_999; obj* x_1002; obj* x_1003; obj* x_1005; 
x_988 = lean::cnstr_get(x_0, 0);
lean::inc(x_988);
x_990 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*3);
x_991 = lean::cnstr_get(x_0, 1);
lean::inc(x_991);
x_993 = lean::cnstr_get(x_0, 2);
lean::inc(x_993);
lean::inc(x_1);
x_1002 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_988, x_1, x_2);
x_1003 = lean::cnstr_get(x_1002, 0);
lean::inc(x_1003);
x_1005 = lean::cnstr_get(x_1002, 1);
lean::inc(x_1005);
lean::dec(x_1002);
if (lean::obj_tag(x_1003) == 0)
{
obj* x_1008; obj* x_1010; obj* x_1011; 
x_1008 = lean::cnstr_get(x_1003, 0);
lean::inc(x_1008);
if (lean::is_shared(x_1003)) {
 lean::dec(x_1003);
 x_1010 = lean::box(0);
} else {
 lean::cnstr_release(x_1003, 0);
 x_1010 = x_1003;
}
if (lean::is_scalar(x_1010)) {
 x_1011 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1011 = x_1010;
}
lean::cnstr_set(x_1011, 0, x_1008);
x_998 = x_1011;
x_999 = x_1005;
goto lbl_1000;
}
else
{
obj* x_1013; obj* x_1016; obj* x_1017; obj* x_1019; 
lean::dec(x_1003);
x_1013 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__7;
lean::inc(x_1);
lean::inc(x_1013);
x_1016 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1013, x_1, x_1005);
x_1017 = lean::cnstr_get(x_1016, 0);
lean::inc(x_1017);
x_1019 = lean::cnstr_get(x_1016, 1);
lean::inc(x_1019);
lean::dec(x_1016);
x_998 = x_1017;
x_999 = x_1019;
goto lbl_1000;
}
lbl_997:
{

if (lean::obj_tag(x_995) == 0)
{
obj* x_1023; obj* x_1025; obj* x_1026; obj* x_1027; 
lean::dec(x_993);
x_1023 = lean::cnstr_get(x_995, 0);
lean::inc(x_1023);
if (lean::is_shared(x_995)) {
 lean::dec(x_995);
 x_1025 = lean::box(0);
} else {
 lean::cnstr_release(x_995, 0);
 x_1025 = x_995;
}
if (lean::is_scalar(x_1025)) {
 x_1026 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1026 = x_1025;
}
lean::cnstr_set(x_1026, 0, x_1023);
x_1027 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1027, 0, x_1026);
lean::cnstr_set(x_1027, 1, x_996);
x_3 = x_1027;
goto lbl_4;
}
else
{
obj* x_1028; obj* x_1029; obj* x_1032; obj* x_1033; obj* x_1035; obj* x_1037; 
if (lean::is_shared(x_995)) {
 lean::dec(x_995);
 x_1028 = lean::box(0);
} else {
 lean::cnstr_release(x_995, 0);
 x_1028 = x_995;
}
x_1029 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_1029);
x_1032 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1029, x_1, x_996);
x_1033 = lean::cnstr_get(x_1032, 0);
lean::inc(x_1033);
x_1035 = lean::cnstr_get(x_1032, 1);
lean::inc(x_1035);
if (lean::is_shared(x_1032)) {
 lean::dec(x_1032);
 x_1037 = lean::box(0);
} else {
 lean::cnstr_release(x_1032, 0);
 lean::cnstr_release(x_1032, 1);
 x_1037 = x_1032;
}
if (lean::obj_tag(x_1033) == 0)
{
obj* x_1039; obj* x_1042; obj* x_1043; 
lean::dec(x_993);
x_1039 = lean::cnstr_get(x_1033, 0);
lean::inc(x_1039);
lean::dec(x_1033);
if (lean::is_scalar(x_1028)) {
 x_1042 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1042 = x_1028;
}
lean::cnstr_set(x_1042, 0, x_1039);
if (lean::is_scalar(x_1037)) {
 x_1043 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1043 = x_1037;
}
lean::cnstr_set(x_1043, 0, x_1042);
lean::cnstr_set(x_1043, 1, x_1035);
x_3 = x_1043;
goto lbl_4;
}
else
{
obj* x_1046; obj* x_1047; obj* x_1049; 
lean::dec(x_1033);
lean::inc(x_1);
x_1046 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_993, x_1, x_1035);
x_1047 = lean::cnstr_get(x_1046, 0);
lean::inc(x_1047);
x_1049 = lean::cnstr_get(x_1046, 1);
lean::inc(x_1049);
lean::dec(x_1046);
if (lean::obj_tag(x_1047) == 0)
{
obj* x_1052; obj* x_1055; obj* x_1056; 
x_1052 = lean::cnstr_get(x_1047, 0);
lean::inc(x_1052);
lean::dec(x_1047);
if (lean::is_scalar(x_1028)) {
 x_1055 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1055 = x_1028;
}
lean::cnstr_set(x_1055, 0, x_1052);
if (lean::is_scalar(x_1037)) {
 x_1056 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1056 = x_1037;
}
lean::cnstr_set(x_1056, 0, x_1055);
lean::cnstr_set(x_1056, 1, x_1049);
x_3 = x_1056;
goto lbl_4;
}
else
{
obj* x_1057; obj* x_1060; obj* x_1063; obj* x_1064; obj* x_1066; 
x_1057 = lean::cnstr_get(x_1047, 0);
lean::inc(x_1057);
lean::dec(x_1047);
x_1060 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_1);
lean::inc(x_1060);
x_1063 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1060, x_1, x_1049);
x_1064 = lean::cnstr_get(x_1063, 0);
lean::inc(x_1064);
x_1066 = lean::cnstr_get(x_1063, 1);
lean::inc(x_1066);
lean::dec(x_1063);
if (lean::obj_tag(x_1064) == 0)
{
obj* x_1070; obj* x_1073; obj* x_1074; 
lean::dec(x_1057);
x_1070 = lean::cnstr_get(x_1064, 0);
lean::inc(x_1070);
lean::dec(x_1064);
if (lean::is_scalar(x_1028)) {
 x_1073 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1073 = x_1028;
}
lean::cnstr_set(x_1073, 0, x_1070);
if (lean::is_scalar(x_1037)) {
 x_1074 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1074 = x_1037;
}
lean::cnstr_set(x_1074, 0, x_1073);
lean::cnstr_set(x_1074, 1, x_1066);
x_3 = x_1074;
goto lbl_4;
}
else
{
obj* x_1076; obj* x_1077; 
lean::dec(x_1064);
if (lean::is_scalar(x_1028)) {
 x_1076 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1076 = x_1028;
}
lean::cnstr_set(x_1076, 0, x_1057);
if (lean::is_scalar(x_1037)) {
 x_1077 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1077 = x_1037;
}
lean::cnstr_set(x_1077, 0, x_1076);
lean::cnstr_set(x_1077, 1, x_1066);
x_3 = x_1077;
goto lbl_4;
}
}
}
}
}
lbl_1000:
{

if (lean::obj_tag(x_998) == 0)
{
obj* x_1080; obj* x_1082; obj* x_1083; obj* x_1084; 
lean::dec(x_993);
lean::dec(x_991);
x_1080 = lean::cnstr_get(x_998, 0);
lean::inc(x_1080);
if (lean::is_shared(x_998)) {
 lean::dec(x_998);
 x_1082 = lean::box(0);
} else {
 lean::cnstr_release(x_998, 0);
 x_1082 = x_998;
}
if (lean::is_scalar(x_1082)) {
 x_1083 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1083 = x_1082;
}
lean::cnstr_set(x_1083, 0, x_1080);
x_1084 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1084, 0, x_1083);
lean::cnstr_set(x_1084, 1, x_999);
x_3 = x_1084;
goto lbl_4;
}
else
{
obj* x_1085; obj* x_1086; obj* x_1089; obj* x_1090; obj* x_1092; obj* x_1094; 
if (lean::is_shared(x_998)) {
 lean::dec(x_998);
 x_1085 = lean::box(0);
} else {
 lean::cnstr_release(x_998, 0);
 x_1085 = x_998;
}
x_1086 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_1086);
x_1089 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1086, x_1, x_999);
x_1090 = lean::cnstr_get(x_1089, 0);
lean::inc(x_1090);
x_1092 = lean::cnstr_get(x_1089, 1);
lean::inc(x_1092);
if (lean::is_shared(x_1089)) {
 lean::dec(x_1089);
 x_1094 = lean::box(0);
} else {
 lean::cnstr_release(x_1089, 0);
 lean::cnstr_release(x_1089, 1);
 x_1094 = x_1089;
}
if (lean::obj_tag(x_1090) == 0)
{
obj* x_1097; obj* x_1100; obj* x_1101; 
lean::dec(x_993);
lean::dec(x_991);
x_1097 = lean::cnstr_get(x_1090, 0);
lean::inc(x_1097);
lean::dec(x_1090);
if (lean::is_scalar(x_1085)) {
 x_1100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1100 = x_1085;
}
lean::cnstr_set(x_1100, 0, x_1097);
if (lean::is_scalar(x_1094)) {
 x_1101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1101 = x_1094;
}
lean::cnstr_set(x_1101, 0, x_1100);
lean::cnstr_set(x_1101, 1, x_1092);
x_3 = x_1101;
goto lbl_4;
}
else
{
obj* x_1105; obj* x_1106; obj* x_1108; 
lean::dec(x_1094);
lean::dec(x_1090);
lean::inc(x_1);
x_1105 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__type__size(x_990, x_1, x_1092);
x_1106 = lean::cnstr_get(x_1105, 0);
lean::inc(x_1106);
x_1108 = lean::cnstr_get(x_1105, 1);
lean::inc(x_1108);
lean::dec(x_1105);
if (lean::obj_tag(x_1106) == 0)
{
obj* x_1112; obj* x_1115; 
lean::dec(x_991);
x_1112 = lean::cnstr_get(x_1106, 0);
lean::inc(x_1112);
lean::dec(x_1106);
if (lean::is_scalar(x_1085)) {
 x_1115 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1115 = x_1085;
}
lean::cnstr_set(x_1115, 0, x_1112);
x_995 = x_1115;
x_996 = x_1108;
goto lbl_997;
}
else
{
obj* x_1117; obj* x_1120; obj* x_1121; obj* x_1123; 
lean::dec(x_1106);
x_1117 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_1117);
x_1120 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1117, x_1, x_1108);
x_1121 = lean::cnstr_get(x_1120, 0);
lean::inc(x_1121);
x_1123 = lean::cnstr_get(x_1120, 1);
lean::inc(x_1123);
lean::dec(x_1120);
if (lean::obj_tag(x_1121) == 0)
{
obj* x_1127; obj* x_1130; 
lean::dec(x_991);
x_1127 = lean::cnstr_get(x_1121, 0);
lean::inc(x_1127);
lean::dec(x_1121);
if (lean::is_scalar(x_1085)) {
 x_1130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1130 = x_1085;
}
lean::cnstr_set(x_1130, 0, x_1127);
x_995 = x_1130;
x_996 = x_1123;
goto lbl_997;
}
else
{
obj* x_1134; obj* x_1135; obj* x_1137; 
lean::dec(x_1085);
lean::dec(x_1121);
lean::inc(x_1);
x_1134 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_991, x_1, x_1123);
x_1135 = lean::cnstr_get(x_1134, 0);
lean::inc(x_1135);
x_1137 = lean::cnstr_get(x_1134, 1);
lean::inc(x_1137);
lean::dec(x_1134);
x_995 = x_1135;
x_996 = x_1137;
goto lbl_997;
}
}
}
}
}
}
default:
{
obj* x_1140; obj* x_1142; obj* x_1144; obj* x_1146; obj* x_1147; unsigned char x_1149; unsigned char x_1151; obj* x_1153; obj* x_1156; 
x_1140 = lean::cnstr_get(x_0, 0);
lean::inc(x_1140);
x_1142 = lean::cnstr_get(x_0, 1);
lean::inc(x_1142);
x_1144 = lean::cnstr_get(x_0, 2);
lean::inc(x_1144);
x_1153 = lean::cnstr_get(x_1, 1);
lean::inc(x_1153);
lean::inc(x_1144);
x_1156 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s2_ir_s9_get__type_s9___spec__2_s6___rarg(x_1153, x_1144);
if (lean::obj_tag(x_1156) == 0)
{
unsigned char x_1158; 
lean::dec(x_1156);
x_1158 = 0;
x_1149 = x_1158;
goto lbl_1150;
}
else
{
obj* x_1159; unsigned char x_1162; obj* x_1164; obj* x_1165; obj* x_1166; 
x_1159 = lean::cnstr_get(x_1156, 0);
lean::inc(x_1159);
lean::dec(x_1156);
x_1162 = lean::unbox(x_1159);
lean::dec(x_1159);
x_1164 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_1162);
x_1165 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_1166 = lean::nat_dec_eq(x_1164, x_1165);
lean::dec(x_1164);
if (lean::obj_tag(x_1166) == 0)
{
unsigned char x_1169; 
lean::dec(x_1166);
x_1169 = 0;
x_1149 = x_1169;
goto lbl_1150;
}
else
{
unsigned char x_1171; 
lean::dec(x_1166);
x_1171 = 0;
x_1151 = x_1171;
goto lbl_1152;
}
}
lbl_1148:
{

if (lean::obj_tag(x_1146) == 0)
{
obj* x_1173; obj* x_1175; obj* x_1176; obj* x_1177; 
lean::dec(x_1144);
x_1173 = lean::cnstr_get(x_1146, 0);
lean::inc(x_1173);
if (lean::is_shared(x_1146)) {
 lean::dec(x_1146);
 x_1175 = lean::box(0);
} else {
 lean::cnstr_release(x_1146, 0);
 x_1175 = x_1146;
}
if (lean::is_scalar(x_1175)) {
 x_1176 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1176 = x_1175;
}
lean::cnstr_set(x_1176, 0, x_1173);
x_1177 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1177, 0, x_1176);
lean::cnstr_set(x_1177, 1, x_1147);
x_3 = x_1177;
goto lbl_4;
}
else
{
obj* x_1178; obj* x_1179; obj* x_1182; obj* x_1183; obj* x_1185; obj* x_1187; 
if (lean::is_shared(x_1146)) {
 lean::dec(x_1146);
 x_1178 = lean::box(0);
} else {
 lean::cnstr_release(x_1146, 0);
 x_1178 = x_1146;
}
x_1179 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_1179);
x_1182 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1179, x_1, x_1147);
x_1183 = lean::cnstr_get(x_1182, 0);
lean::inc(x_1183);
x_1185 = lean::cnstr_get(x_1182, 1);
lean::inc(x_1185);
if (lean::is_shared(x_1182)) {
 lean::dec(x_1182);
 x_1187 = lean::box(0);
} else {
 lean::cnstr_release(x_1182, 0);
 lean::cnstr_release(x_1182, 1);
 x_1187 = x_1182;
}
if (lean::obj_tag(x_1183) == 0)
{
obj* x_1189; obj* x_1192; obj* x_1193; 
lean::dec(x_1144);
x_1189 = lean::cnstr_get(x_1183, 0);
lean::inc(x_1189);
lean::dec(x_1183);
if (lean::is_scalar(x_1178)) {
 x_1192 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1192 = x_1178;
}
lean::cnstr_set(x_1192, 0, x_1189);
if (lean::is_scalar(x_1187)) {
 x_1193 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1193 = x_1187;
}
lean::cnstr_set(x_1193, 0, x_1192);
lean::cnstr_set(x_1193, 1, x_1185);
x_3 = x_1193;
goto lbl_4;
}
else
{
obj* x_1196; obj* x_1197; obj* x_1199; 
lean::dec(x_1183);
lean::inc(x_1);
x_1196 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_1144, x_1, x_1185);
x_1197 = lean::cnstr_get(x_1196, 0);
lean::inc(x_1197);
x_1199 = lean::cnstr_get(x_1196, 1);
lean::inc(x_1199);
lean::dec(x_1196);
if (lean::obj_tag(x_1197) == 0)
{
obj* x_1202; obj* x_1205; obj* x_1206; 
x_1202 = lean::cnstr_get(x_1197, 0);
lean::inc(x_1202);
lean::dec(x_1197);
if (lean::is_scalar(x_1178)) {
 x_1205 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1205 = x_1178;
}
lean::cnstr_set(x_1205, 0, x_1202);
if (lean::is_scalar(x_1187)) {
 x_1206 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1206 = x_1187;
}
lean::cnstr_set(x_1206, 0, x_1205);
lean::cnstr_set(x_1206, 1, x_1199);
x_3 = x_1206;
goto lbl_4;
}
else
{
obj* x_1207; obj* x_1210; obj* x_1213; obj* x_1214; obj* x_1216; 
x_1207 = lean::cnstr_get(x_1197, 0);
lean::inc(x_1207);
lean::dec(x_1197);
x_1210 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_1);
lean::inc(x_1210);
x_1213 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1210, x_1, x_1199);
x_1214 = lean::cnstr_get(x_1213, 0);
lean::inc(x_1214);
x_1216 = lean::cnstr_get(x_1213, 1);
lean::inc(x_1216);
lean::dec(x_1213);
if (lean::obj_tag(x_1214) == 0)
{
obj* x_1220; obj* x_1223; obj* x_1224; 
lean::dec(x_1207);
x_1220 = lean::cnstr_get(x_1214, 0);
lean::inc(x_1220);
lean::dec(x_1214);
if (lean::is_scalar(x_1178)) {
 x_1223 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1223 = x_1178;
}
lean::cnstr_set(x_1223, 0, x_1220);
if (lean::is_scalar(x_1187)) {
 x_1224 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1224 = x_1187;
}
lean::cnstr_set(x_1224, 0, x_1223);
lean::cnstr_set(x_1224, 1, x_1216);
x_3 = x_1224;
goto lbl_4;
}
else
{
obj* x_1226; obj* x_1227; 
lean::dec(x_1214);
if (lean::is_scalar(x_1178)) {
 x_1226 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1226 = x_1178;
}
lean::cnstr_set(x_1226, 0, x_1207);
if (lean::is_scalar(x_1187)) {
 x_1227 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1227 = x_1187;
}
lean::cnstr_set(x_1227, 0, x_1226);
lean::cnstr_set(x_1227, 1, x_1216);
x_3 = x_1227;
goto lbl_4;
}
}
}
}
}
lbl_1150:
{
obj* x_1228; obj* x_1231; obj* x_1232; obj* x_1234; obj* x_1236; 
x_1228 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__8;
lean::inc(x_1);
lean::inc(x_1228);
x_1231 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1228, x_1, x_2);
x_1232 = lean::cnstr_get(x_1231, 0);
lean::inc(x_1232);
x_1234 = lean::cnstr_get(x_1231, 1);
lean::inc(x_1234);
if (lean::is_shared(x_1231)) {
 lean::dec(x_1231);
 x_1236 = lean::box(0);
} else {
 lean::cnstr_release(x_1231, 0);
 lean::cnstr_release(x_1231, 1);
 x_1236 = x_1231;
}
if (lean::obj_tag(x_1232) == 0)
{
obj* x_1240; obj* x_1242; obj* x_1243; obj* x_1244; 
lean::dec(x_1140);
lean::dec(x_1142);
lean::dec(x_1144);
x_1240 = lean::cnstr_get(x_1232, 0);
lean::inc(x_1240);
if (lean::is_shared(x_1232)) {
 lean::dec(x_1232);
 x_1242 = lean::box(0);
} else {
 lean::cnstr_release(x_1232, 0);
 x_1242 = x_1232;
}
if (lean::is_scalar(x_1242)) {
 x_1243 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1243 = x_1242;
}
lean::cnstr_set(x_1243, 0, x_1240);
if (lean::is_scalar(x_1236)) {
 x_1244 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1244 = x_1236;
}
lean::cnstr_set(x_1244, 0, x_1243);
lean::cnstr_set(x_1244, 1, x_1234);
x_3 = x_1244;
goto lbl_4;
}
else
{
obj* x_1245; obj* x_1246; obj* x_1249; obj* x_1250; obj* x_1252; 
if (lean::is_shared(x_1232)) {
 lean::dec(x_1232);
 x_1245 = lean::box(0);
} else {
 lean::cnstr_release(x_1232, 0);
 x_1245 = x_1232;
}
x_1246 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_1246);
x_1249 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1246, x_1, x_1234);
x_1250 = lean::cnstr_get(x_1249, 0);
lean::inc(x_1250);
x_1252 = lean::cnstr_get(x_1249, 1);
lean::inc(x_1252);
lean::dec(x_1249);
if (lean::obj_tag(x_1250) == 0)
{
obj* x_1258; obj* x_1261; obj* x_1262; 
lean::dec(x_1140);
lean::dec(x_1142);
lean::dec(x_1144);
x_1258 = lean::cnstr_get(x_1250, 0);
lean::inc(x_1258);
lean::dec(x_1250);
if (lean::is_scalar(x_1245)) {
 x_1261 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1261 = x_1245;
}
lean::cnstr_set(x_1261, 0, x_1258);
if (lean::is_scalar(x_1236)) {
 x_1262 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1262 = x_1236;
}
lean::cnstr_set(x_1262, 0, x_1261);
lean::cnstr_set(x_1262, 1, x_1252);
x_3 = x_1262;
goto lbl_4;
}
else
{
obj* x_1266; obj* x_1267; obj* x_1269; 
lean::dec(x_1250);
lean::dec(x_1236);
lean::inc(x_1);
x_1266 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_1140, x_1, x_1252);
x_1267 = lean::cnstr_get(x_1266, 0);
lean::inc(x_1267);
x_1269 = lean::cnstr_get(x_1266, 1);
lean::inc(x_1269);
lean::dec(x_1266);
if (lean::obj_tag(x_1267) == 0)
{
obj* x_1273; obj* x_1276; 
lean::dec(x_1142);
x_1273 = lean::cnstr_get(x_1267, 0);
lean::inc(x_1273);
lean::dec(x_1267);
if (lean::is_scalar(x_1245)) {
 x_1276 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1276 = x_1245;
}
lean::cnstr_set(x_1276, 0, x_1273);
x_1146 = x_1276;
x_1147 = x_1269;
goto lbl_1148;
}
else
{
obj* x_1278; obj* x_1281; obj* x_1282; obj* x_1284; 
lean::dec(x_1267);
x_1278 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_1278);
x_1281 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1278, x_1, x_1269);
x_1282 = lean::cnstr_get(x_1281, 0);
lean::inc(x_1282);
x_1284 = lean::cnstr_get(x_1281, 1);
lean::inc(x_1284);
lean::dec(x_1281);
if (lean::obj_tag(x_1282) == 0)
{
obj* x_1288; obj* x_1291; 
lean::dec(x_1142);
x_1288 = lean::cnstr_get(x_1282, 0);
lean::inc(x_1288);
lean::dec(x_1282);
if (lean::is_scalar(x_1245)) {
 x_1291 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1291 = x_1245;
}
lean::cnstr_set(x_1291, 0, x_1288);
x_1146 = x_1291;
x_1147 = x_1284;
goto lbl_1148;
}
else
{
obj* x_1295; obj* x_1296; obj* x_1298; 
lean::dec(x_1282);
lean::dec(x_1245);
lean::inc(x_1);
x_1295 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_1142, x_1, x_1284);
x_1296 = lean::cnstr_get(x_1295, 0);
lean::inc(x_1296);
x_1298 = lean::cnstr_get(x_1295, 1);
lean::inc(x_1298);
lean::dec(x_1295);
x_1146 = x_1296;
x_1147 = x_1298;
goto lbl_1148;
}
}
}
}
}
lbl_1152:
{
obj* x_1301; obj* x_1304; obj* x_1305; obj* x_1307; obj* x_1309; 
x_1301 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__9;
lean::inc(x_1);
lean::inc(x_1301);
x_1304 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1301, x_1, x_2);
x_1305 = lean::cnstr_get(x_1304, 0);
lean::inc(x_1305);
x_1307 = lean::cnstr_get(x_1304, 1);
lean::inc(x_1307);
if (lean::is_shared(x_1304)) {
 lean::dec(x_1304);
 x_1309 = lean::box(0);
} else {
 lean::cnstr_release(x_1304, 0);
 lean::cnstr_release(x_1304, 1);
 x_1309 = x_1304;
}
if (lean::obj_tag(x_1305) == 0)
{
obj* x_1313; obj* x_1315; obj* x_1316; obj* x_1317; 
lean::dec(x_1140);
lean::dec(x_1142);
lean::dec(x_1144);
x_1313 = lean::cnstr_get(x_1305, 0);
lean::inc(x_1313);
if (lean::is_shared(x_1305)) {
 lean::dec(x_1305);
 x_1315 = lean::box(0);
} else {
 lean::cnstr_release(x_1305, 0);
 x_1315 = x_1305;
}
if (lean::is_scalar(x_1315)) {
 x_1316 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1316 = x_1315;
}
lean::cnstr_set(x_1316, 0, x_1313);
if (lean::is_scalar(x_1309)) {
 x_1317 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1317 = x_1309;
}
lean::cnstr_set(x_1317, 0, x_1316);
lean::cnstr_set(x_1317, 1, x_1307);
x_3 = x_1317;
goto lbl_4;
}
else
{
obj* x_1318; obj* x_1319; obj* x_1322; obj* x_1323; obj* x_1325; 
if (lean::is_shared(x_1305)) {
 lean::dec(x_1305);
 x_1318 = lean::box(0);
} else {
 lean::cnstr_release(x_1305, 0);
 x_1318 = x_1305;
}
x_1319 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_1319);
x_1322 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1319, x_1, x_1307);
x_1323 = lean::cnstr_get(x_1322, 0);
lean::inc(x_1323);
x_1325 = lean::cnstr_get(x_1322, 1);
lean::inc(x_1325);
lean::dec(x_1322);
if (lean::obj_tag(x_1323) == 0)
{
obj* x_1331; obj* x_1334; obj* x_1335; 
lean::dec(x_1140);
lean::dec(x_1142);
lean::dec(x_1144);
x_1331 = lean::cnstr_get(x_1323, 0);
lean::inc(x_1331);
lean::dec(x_1323);
if (lean::is_scalar(x_1318)) {
 x_1334 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1334 = x_1318;
}
lean::cnstr_set(x_1334, 0, x_1331);
if (lean::is_scalar(x_1309)) {
 x_1335 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1335 = x_1309;
}
lean::cnstr_set(x_1335, 0, x_1334);
lean::cnstr_set(x_1335, 1, x_1325);
x_3 = x_1335;
goto lbl_4;
}
else
{
obj* x_1339; obj* x_1340; obj* x_1342; 
lean::dec(x_1309);
lean::dec(x_1323);
lean::inc(x_1);
x_1339 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_1140, x_1, x_1325);
x_1340 = lean::cnstr_get(x_1339, 0);
lean::inc(x_1340);
x_1342 = lean::cnstr_get(x_1339, 1);
lean::inc(x_1342);
lean::dec(x_1339);
if (lean::obj_tag(x_1340) == 0)
{
obj* x_1346; obj* x_1349; 
lean::dec(x_1142);
x_1346 = lean::cnstr_get(x_1340, 0);
lean::inc(x_1346);
lean::dec(x_1340);
if (lean::is_scalar(x_1318)) {
 x_1349 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1349 = x_1318;
}
lean::cnstr_set(x_1349, 0, x_1346);
x_1146 = x_1349;
x_1147 = x_1342;
goto lbl_1148;
}
else
{
obj* x_1351; obj* x_1354; obj* x_1355; obj* x_1357; 
lean::dec(x_1340);
x_1351 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_1351);
x_1354 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_1351, x_1, x_1342);
x_1355 = lean::cnstr_get(x_1354, 0);
lean::inc(x_1355);
x_1357 = lean::cnstr_get(x_1354, 1);
lean::inc(x_1357);
lean::dec(x_1354);
if (lean::obj_tag(x_1355) == 0)
{
obj* x_1361; obj* x_1364; 
lean::dec(x_1142);
x_1361 = lean::cnstr_get(x_1355, 0);
lean::inc(x_1361);
lean::dec(x_1355);
if (lean::is_scalar(x_1318)) {
 x_1364 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1364 = x_1318;
}
lean::cnstr_set(x_1364, 0, x_1361);
x_1146 = x_1364;
x_1147 = x_1357;
goto lbl_1148;
}
else
{
obj* x_1368; obj* x_1369; obj* x_1371; 
lean::dec(x_1355);
lean::dec(x_1318);
lean::inc(x_1);
x_1368 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_1142, x_1, x_1357);
x_1369 = lean::cnstr_get(x_1368, 0);
lean::inc(x_1369);
x_1371 = lean::cnstr_get(x_1368, 1);
lean::inc(x_1371);
lean::dec(x_1368);
x_1146 = x_1369;
x_1147 = x_1371;
goto lbl_1148;
}
}
}
}
}
}
}
lbl_4:
{
obj* x_1374; obj* x_1376; obj* x_1378; 
x_1374 = lean::cnstr_get(x_3, 0);
lean::inc(x_1374);
x_1376 = lean::cnstr_get(x_3, 1);
lean::inc(x_1376);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_1378 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_1378 = x_3;
}
if (lean::obj_tag(x_1374) == 0)
{
obj* x_1380; obj* x_1382; obj* x_1383; unsigned char x_1384; obj* x_1385; obj* x_1387; obj* x_1388; obj* x_1389; obj* x_1391; obj* x_1392; obj* x_1393; obj* x_1394; obj* x_1395; obj* x_1396; obj* x_1397; obj* x_1398; obj* x_1399; 
lean::dec(x_1);
x_1380 = lean::cnstr_get(x_1374, 0);
lean::inc(x_1380);
if (lean::is_shared(x_1374)) {
 lean::dec(x_1374);
 x_1382 = lean::box(0);
} else {
 lean::cnstr_release(x_1374, 0);
 x_1382 = x_1374;
}
x_1383 = _l_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main(x_0);
x_1384 = 0;
x_1385 = _l_s4_lean_s2_ir_s5_instr_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_1385);
x_1387 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1387, 0, x_1385);
lean::cnstr_set(x_1387, 1, x_1383);
lean::cnstr_set_scalar(x_1387, sizeof(void*)*2, x_1384);
x_1388 = x_1387;
x_1389 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_1389);
x_1391 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1391, 0, x_1388);
lean::cnstr_set(x_1391, 1, x_1389);
lean::cnstr_set_scalar(x_1391, sizeof(void*)*2, x_1384);
x_1392 = x_1391;
x_1393 = lean::alloc_cnstr(1, 0, 0);
;
x_1394 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1394, 0, x_1392);
lean::cnstr_set(x_1394, 1, x_1393);
lean::cnstr_set_scalar(x_1394, sizeof(void*)*2, x_1384);
x_1395 = x_1394;
x_1396 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1396, 0, x_1395);
lean::cnstr_set(x_1396, 1, x_1380);
lean::cnstr_set_scalar(x_1396, sizeof(void*)*2, x_1384);
x_1397 = x_1396;
if (lean::is_scalar(x_1382)) {
 x_1398 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1398 = x_1382;
}
lean::cnstr_set(x_1398, 0, x_1397);
if (lean::is_scalar(x_1378)) {
 x_1399 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1399 = x_1378;
}
lean::cnstr_set(x_1399, 0, x_1398);
lean::cnstr_set(x_1399, 1, x_1376);
return x_1399;
}
else
{
obj* x_1400; obj* x_1401; obj* x_1402; obj* x_1404; 
if (lean::is_shared(x_1374)) {
 lean::dec(x_1374);
 x_1400 = lean::box(0);
} else {
 lean::cnstr_release(x_1374, 0);
 x_1400 = x_1374;
}
x_1401 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos(x_1, x_1376);
x_1402 = lean::cnstr_get(x_1401, 0);
lean::inc(x_1402);
x_1404 = lean::cnstr_get(x_1401, 1);
lean::inc(x_1404);
lean::dec(x_1401);
if (lean::obj_tag(x_1402) == 0)
{
obj* x_1407; obj* x_1410; unsigned char x_1411; obj* x_1412; obj* x_1414; obj* x_1415; obj* x_1416; obj* x_1418; obj* x_1419; obj* x_1420; obj* x_1421; obj* x_1422; obj* x_1423; obj* x_1424; obj* x_1425; obj* x_1426; 
x_1407 = lean::cnstr_get(x_1402, 0);
lean::inc(x_1407);
lean::dec(x_1402);
x_1410 = _l_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main(x_0);
x_1411 = 0;
x_1412 = _l_s4_lean_s2_ir_s5_instr_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_1412);
x_1414 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1414, 0, x_1412);
lean::cnstr_set(x_1414, 1, x_1410);
lean::cnstr_set_scalar(x_1414, sizeof(void*)*2, x_1411);
x_1415 = x_1414;
x_1416 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_1416);
x_1418 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1418, 0, x_1415);
lean::cnstr_set(x_1418, 1, x_1416);
lean::cnstr_set_scalar(x_1418, sizeof(void*)*2, x_1411);
x_1419 = x_1418;
x_1420 = lean::alloc_cnstr(1, 0, 0);
;
x_1421 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1421, 0, x_1419);
lean::cnstr_set(x_1421, 1, x_1420);
lean::cnstr_set_scalar(x_1421, sizeof(void*)*2, x_1411);
x_1422 = x_1421;
x_1423 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1423, 0, x_1422);
lean::cnstr_set(x_1423, 1, x_1407);
lean::cnstr_set_scalar(x_1423, sizeof(void*)*2, x_1411);
x_1424 = x_1423;
if (lean::is_scalar(x_1400)) {
 x_1425 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1425 = x_1400;
}
lean::cnstr_set(x_1425, 0, x_1424);
if (lean::is_scalar(x_1378)) {
 x_1426 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1426 = x_1378;
}
lean::cnstr_set(x_1426, 0, x_1425);
lean::cnstr_set(x_1426, 1, x_1404);
return x_1426;
}
else
{
obj* x_1429; 
lean::dec(x_0);
lean::dec(x_1400);
if (lean::is_scalar(x_1378)) {
 x_1429 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1429 = x_1378;
}
lean::cnstr_set(x_1429, 0, x_1402);
lean::cnstr_set(x_1429, 1, x_1404);
return x_1429;
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::alloc_cnstr");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::cnstr_set_obj");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::cnstr_obj");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::cnstr_set_scalar");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__5() {
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::cnstr_scalar");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__6() {
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::alloc_array");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__7() {
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::alloc_sarray");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__8() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::sarray_set_data");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__9() {
{
obj* x_0; 
x_0 = lean::mk_string("lean::array_set_obj");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__1(size_t x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::dec(x_1);
x_4 = _l_s5_usize_s7_to__nat_s6___main(x_0);
x_5 = _l_s3_nat_s4_repr(x_4);
x_6 = lean::string_append(x_2, x_5);
lean::dec(x_5);
x_8 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__2(unsigned short x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::dec(x_1);
x_4 = _l_s6_uint16_s7_to__nat_s6___main(x_0);
x_5 = _l_s3_nat_s4_repr(x_4);
x_6 = lean::string_append(x_2, x_5);
lean::dec(x_5);
x_8 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__3(unsigned short x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::dec(x_1);
x_4 = _l_s6_uint16_s7_to__nat_s6___main(x_0);
x_5 = _l_s3_nat_s4_repr(x_4);
x_6 = lean::string_append(x_2, x_5);
lean::dec(x_5);
x_8 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
size_t x_3; obj* x_4; 
x_3 = lean::unbox_size_t(x_0);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__1(x_3, x_1, x_2);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__2_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned short x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__2(x_3, x_1, x_2);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__3_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned short x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s9___spec__3(x_3, x_1, x_2);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s11_emit__block(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; unsigned char x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = _l_s4_list_s5_empty_s6___main_s6___rarg(x_3);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
lean::dec(x_0);
if (x_5 == 0)
{
obj* x_16; 
x_16 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__block_s11___closed__2;
lean::inc(x_16);
x_13 = x_16;
x_14 = x_2;
goto lbl_15;
}
else
{
obj* x_18; 
x_18 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_18);
x_13 = x_18;
x_14 = x_2;
goto lbl_15;
}
lbl_15:
{

if (lean::obj_tag(x_13) == 0)
{
obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_6);
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_1);
x_24 = lean::cnstr_get(x_13, 0);
lean::inc(x_24);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_26 = x_13;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_14);
return x_28;
}
else
{
obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_36; 
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_29 = x_13;
}
lean::inc(x_1);
x_31 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid(x_6, x_1, x_14);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_36 = x_31;
}
if (lean::obj_tag(x_32) == 0)
{
obj* x_40; obj* x_43; obj* x_44; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_1);
x_40 = lean::cnstr_get(x_32, 0);
lean::inc(x_40);
lean::dec(x_32);
if (lean::is_scalar(x_29)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_29;
}
lean::cnstr_set(x_43, 0, x_40);
if (lean::is_scalar(x_36)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_36;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_34);
return x_44;
}
else
{
obj* x_46; obj* x_49; obj* x_50; obj* x_52; 
lean::dec(x_32);
x_46 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__block_s11___closed__1;
lean::inc(x_1);
lean::inc(x_46);
x_49 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_46, x_1, x_34);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_58; obj* x_61; obj* x_62; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_1);
x_58 = lean::cnstr_get(x_50, 0);
lean::inc(x_58);
lean::dec(x_50);
if (lean::is_scalar(x_29)) {
 x_61 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_61 = x_29;
}
lean::cnstr_set(x_61, 0, x_58);
if (lean::is_scalar(x_36)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_36;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_52);
return x_62;
}
else
{
obj* x_64; obj* x_67; obj* x_68; obj* x_70; 
lean::dec(x_50);
x_64 = _l_s4_lean_s6_format_s2_be_s6___main_s11___closed__1;
lean::inc(x_1);
lean::inc(x_64);
x_67 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_64, x_1, x_52);
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
if (lean::obj_tag(x_68) == 0)
{
obj* x_76; obj* x_79; obj* x_80; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_1);
x_76 = lean::cnstr_get(x_68, 0);
lean::inc(x_76);
lean::dec(x_68);
if (lean::is_scalar(x_29)) {
 x_79 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_79 = x_29;
}
lean::cnstr_set(x_79, 0, x_76);
if (lean::is_scalar(x_36)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_36;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_70);
return x_80;
}
else
{
obj* x_83; obj* x_84; obj* x_86; 
lean::dec(x_68);
lean::inc(x_1);
x_83 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__block_s9___spec__1(x_8, x_1, x_70);
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
lean::dec(x_83);
if (lean::obj_tag(x_84) == 0)
{
obj* x_91; obj* x_94; obj* x_95; 
lean::dec(x_10);
lean::dec(x_1);
x_91 = lean::cnstr_get(x_84, 0);
lean::inc(x_91);
lean::dec(x_84);
if (lean::is_scalar(x_29)) {
 x_94 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_94 = x_29;
}
lean::cnstr_set(x_94, 0, x_91);
if (lean::is_scalar(x_36)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_36;
}
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_86);
return x_95;
}
else
{
obj* x_99; 
lean::dec(x_84);
lean::dec(x_36);
lean::dec(x_29);
x_99 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__terminator(x_10, x_1, x_86);
return x_99;
}
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__block_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string(":");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__block_s11___closed__2() {
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("failed to extract C++ code, definition contains phi nodes");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__block_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
obj* x_29; 
lean::dec(x_15);
lean::dec(x_19);
x_29 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__block_s9___spec__1(x_10, x_1, x_17);
return x_29;
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s12_emit__header(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; unsigned char x_13; obj* x_16; obj* x_17; obj* x_19; 
x_3 = lean::cnstr_get(x_0, 2);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_13 = lean::unbox(x_3);
lean::dec(x_3);
lean::inc(x_1);
x_16 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__type(x_13, x_1, x_2);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
if (lean::obj_tag(x_17) == 0)
{
obj* x_22; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_17, 0);
lean::inc(x_22);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_24 = x_17;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
x_10 = x_25;
x_11 = x_19;
goto lbl_12;
}
else
{
obj* x_27; obj* x_30; obj* x_31; obj* x_33; 
lean::dec(x_17);
x_27 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_27);
x_30 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_27, x_1, x_19);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
x_10 = x_31;
x_11 = x_33;
goto lbl_12;
}
lbl_12:
{

if (lean::obj_tag(x_10) == 0)
{
obj* x_39; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_5);
lean::dec(x_7);
lean::dec(x_1);
x_39 = lean::cnstr_get(x_10, 0);
lean::inc(x_39);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_41 = x_10;
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_39);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_11);
return x_43;
}
else
{
obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_51; 
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_44 = x_10;
}
lean::inc(x_1);
x_46 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__fnid(x_5, x_1, x_11);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
if (lean::is_shared(x_46)) {
 lean::dec(x_46);
 x_51 = lean::box(0);
} else {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_51 = x_46;
}
if (lean::obj_tag(x_47) == 0)
{
obj* x_54; obj* x_57; obj* x_58; 
lean::dec(x_7);
lean::dec(x_1);
x_54 = lean::cnstr_get(x_47, 0);
lean::inc(x_54);
lean::dec(x_47);
if (lean::is_scalar(x_44)) {
 x_57 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_57 = x_44;
}
lean::cnstr_set(x_57, 0, x_54);
if (lean::is_scalar(x_51)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_51;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_49);
return x_58;
}
else
{
obj* x_60; obj* x_63; obj* x_64; obj* x_66; 
lean::dec(x_47);
x_60 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_60);
x_63 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_60, x_1, x_49);
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_63, 1);
lean::inc(x_66);
lean::dec(x_63);
if (lean::obj_tag(x_64) == 0)
{
obj* x_71; obj* x_74; obj* x_75; 
lean::dec(x_7);
lean::dec(x_1);
x_71 = lean::cnstr_get(x_64, 0);
lean::inc(x_71);
lean::dec(x_64);
if (lean::is_scalar(x_44)) {
 x_74 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_74 = x_44;
}
lean::cnstr_set(x_74, 0, x_71);
if (lean::is_scalar(x_51)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_51;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_66);
return x_75;
}
else
{
obj* x_77; obj* x_78; obj* x_82; obj* x_83; obj* x_85; 
lean::dec(x_64);
x_77 = _l_s4_lean_s2_ir_s3_cpp_s12_emit__header_s11___closed__1;
x_78 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__3;
lean::inc(x_1);
lean::inc(x_78);
lean::inc(x_77);
x_82 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg(x_77, x_78, x_7, x_1, x_66);
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
if (lean::obj_tag(x_83) == 0)
{
obj* x_89; obj* x_92; obj* x_93; 
lean::dec(x_1);
x_89 = lean::cnstr_get(x_83, 0);
lean::inc(x_89);
lean::dec(x_83);
if (lean::is_scalar(x_44)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_44;
}
lean::cnstr_set(x_92, 0, x_89);
if (lean::is_scalar(x_51)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_51;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_85);
return x_93;
}
else
{
obj* x_94; obj* x_97; obj* x_99; obj* x_100; obj* x_102; 
x_94 = lean::cnstr_get(x_83, 0);
lean::inc(x_94);
lean::dec(x_83);
x_97 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_97);
x_99 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_97, x_1, x_85);
x_100 = lean::cnstr_get(x_99, 0);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_99, 1);
lean::inc(x_102);
lean::dec(x_99);
if (lean::obj_tag(x_100) == 0)
{
obj* x_106; obj* x_109; obj* x_110; 
lean::dec(x_94);
x_106 = lean::cnstr_get(x_100, 0);
lean::inc(x_106);
lean::dec(x_100);
if (lean::is_scalar(x_44)) {
 x_109 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_109 = x_44;
}
lean::cnstr_set(x_109, 0, x_106);
if (lean::is_scalar(x_51)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_51;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_102);
return x_110;
}
else
{
obj* x_112; obj* x_113; 
lean::dec(x_100);
if (lean::is_scalar(x_44)) {
 x_112 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_112 = x_44;
}
lean::cnstr_set(x_112, 0, x_94);
if (lean::is_scalar(x_51)) {
 x_113 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_113 = x_51;
}
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_102);
return x_113;
}
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s12_emit__header_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s2_ir_s3_cpp_s15_emit__arg__list_s11___lambda__1), 3, 0);
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s11_decl__local(obj* x_0, unsigned char x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::inc(x_2);
x_5 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__type(x_1, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_0);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
if (lean::is_scalar(x_10)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_10;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_25; 
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
}
x_19 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_2);
lean::inc(x_19);
x_22 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_19, x_2, x_8);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_33; obj* x_34; 
lean::dec(x_0);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
if (lean::is_scalar(x_18)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_18;
}
lean::cnstr_set(x_33, 0, x_30);
if (lean::is_scalar(x_10)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_10;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_25);
return x_34;
}
else
{
obj* x_37; obj* x_38; obj* x_40; 
lean::dec(x_23);
lean::inc(x_2);
x_37 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__var(x_0, x_2, x_25);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_44; obj* x_47; obj* x_48; 
lean::dec(x_2);
x_44 = lean::cnstr_get(x_38, 0);
lean::inc(x_44);
lean::dec(x_38);
if (lean::is_scalar(x_18)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_18;
}
lean::cnstr_set(x_47, 0, x_44);
if (lean::is_scalar(x_10)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_10;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_40);
return x_48;
}
else
{
obj* x_52; 
lean::dec(x_38);
lean::dec(x_10);
lean::dec(x_18);
x_52 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos(x_2, x_40);
return x_52;
}
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s11_decl__local_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = _l_s4_lean_s2_ir_s3_cpp_s11_decl__local(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s12_decl__locals(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; unsigned char x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_5 = 0;
x_6 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__2(x_0, x_3, x_5, x_1, x_2);
return x_6;
}
}
obj* _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__1(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_1) == 0)
{
unsigned char x_4; obj* x_5; 
lean::dec(x_0);
lean::dec(x_1);
x_4 = 0;
x_5 = lean::box(x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; obj* x_15; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
lean::inc(x_0);
x_15 = _l_s4_lean_s4_name_s12_has__dec__eq_s6___main(x_11, x_0);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; 
lean::dec(x_15);
x_17 = _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__1(x_0, x_8);
return x_17;
}
else
{
unsigned char x_21; obj* x_22; 
lean::dec(x_8);
lean::dec(x_15);
lean::dec(x_0);
x_21 = 1;
x_22 = lean::box(x_21);
return x_22;
}
}
}
}
obj* _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__2(obj* x_0, obj* x_1, unsigned char x_2, obj* x_3, obj* x_4) {
{

switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
x_8 = lean::box(x_2);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_4);
return x_10;
}
case 1:
{
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_22; obj* x_23; obj* x_25; obj* x_27; 
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_1, 2);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_1, 3);
lean::inc(x_17);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_0);
x_22 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__2(x_0, x_11, x_2, x_3, x_4);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 x_27 = x_22;
}
if (lean::obj_tag(x_23) == 0)
{
obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_13);
lean::dec(x_15);
lean::dec(x_17);
lean::dec(x_0);
lean::dec(x_3);
x_33 = lean::cnstr_get(x_23, 0);
lean::inc(x_33);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_35 = x_23;
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
if (lean::is_scalar(x_27)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_27;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_25);
return x_37;
}
else
{
obj* x_38; obj* x_41; unsigned char x_42; 
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_38 = x_23;
}
lean::inc(x_0);
lean::inc(x_13);
x_41 = _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__1(x_13, x_0);
x_42 = lean::unbox(x_41);
lean::dec(x_41);
if (x_42 == 0)
{
unsigned char x_44; obj* x_47; obj* x_48; obj* x_50; 
x_44 = lean::unbox(x_15);
lean::dec(x_15);
lean::inc(x_3);
x_47 = _l_s4_lean_s2_ir_s3_cpp_s11_decl__local(x_13, x_44, x_3, x_25);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
lean::dec(x_47);
if (lean::obj_tag(x_48) == 0)
{
obj* x_56; obj* x_59; obj* x_60; 
lean::dec(x_17);
lean::dec(x_0);
lean::dec(x_3);
x_56 = lean::cnstr_get(x_48, 0);
lean::inc(x_56);
lean::dec(x_48);
if (lean::is_scalar(x_38)) {
 x_59 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_59 = x_38;
}
lean::cnstr_set(x_59, 0, x_56);
if (lean::is_scalar(x_27)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_27;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_50);
return x_60;
}
else
{
unsigned char x_64; obj* x_65; 
lean::dec(x_27);
lean::dec(x_48);
lean::dec(x_38);
x_64 = 0;
x_65 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__2(x_0, x_17, x_64, x_3, x_50);
return x_65;
}
}
else
{
unsigned char x_70; obj* x_71; 
lean::dec(x_27);
lean::dec(x_13);
lean::dec(x_15);
lean::dec(x_38);
x_70 = 0;
x_71 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__2(x_0, x_17, x_70, x_3, x_25);
return x_71;
}
}
}
default:
{
obj* x_72; obj* x_74; obj* x_76; obj* x_78; obj* x_83; obj* x_84; obj* x_86; obj* x_88; 
x_72 = lean::cnstr_get(x_1, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_1, 1);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_1, 2);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_1, 3);
lean::inc(x_78);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_0);
x_83 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__2(x_0, x_72, x_2, x_3, x_4);
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
if (lean::is_shared(x_83)) {
 lean::dec(x_83);
 x_88 = lean::box(0);
} else {
 lean::cnstr_release(x_83, 0);
 lean::cnstr_release(x_83, 1);
 x_88 = x_83;
}
if (lean::obj_tag(x_84) == 0)
{
obj* x_94; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_76);
lean::dec(x_78);
lean::dec(x_74);
lean::dec(x_0);
lean::dec(x_3);
x_94 = lean::cnstr_get(x_84, 0);
lean::inc(x_94);
if (lean::is_shared(x_84)) {
 lean::dec(x_84);
 x_96 = lean::box(0);
} else {
 lean::cnstr_release(x_84, 0);
 x_96 = x_84;
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_94);
if (lean::is_scalar(x_88)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_88;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_86);
return x_98;
}
else
{
obj* x_99; obj* x_102; unsigned char x_103; 
if (lean::is_shared(x_84)) {
 lean::dec(x_84);
 x_99 = lean::box(0);
} else {
 lean::cnstr_release(x_84, 0);
 x_99 = x_84;
}
lean::inc(x_0);
lean::inc(x_74);
x_102 = _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__1(x_74, x_0);
x_103 = lean::unbox(x_102);
lean::dec(x_102);
if (x_103 == 0)
{
unsigned char x_105; obj* x_108; obj* x_109; obj* x_111; 
x_105 = lean::unbox(x_76);
lean::dec(x_76);
lean::inc(x_3);
x_108 = _l_s4_lean_s2_ir_s3_cpp_s11_decl__local(x_74, x_105, x_3, x_86);
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_108, 1);
lean::inc(x_111);
lean::dec(x_108);
if (lean::obj_tag(x_109) == 0)
{
obj* x_117; obj* x_120; obj* x_121; 
lean::dec(x_78);
lean::dec(x_0);
lean::dec(x_3);
x_117 = lean::cnstr_get(x_109, 0);
lean::inc(x_117);
lean::dec(x_109);
if (lean::is_scalar(x_99)) {
 x_120 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_120 = x_99;
}
lean::cnstr_set(x_120, 0, x_117);
if (lean::is_scalar(x_88)) {
 x_121 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_121 = x_88;
}
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_111);
return x_121;
}
else
{
unsigned char x_125; obj* x_126; 
lean::dec(x_109);
lean::dec(x_99);
lean::dec(x_88);
x_125 = 0;
x_126 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__2(x_0, x_78, x_125, x_3, x_111);
return x_126;
}
}
else
{
unsigned char x_131; obj* x_132; 
lean::dec(x_99);
lean::dec(x_76);
lean::dec(x_74);
lean::dec(x_88);
x_131 = 0;
x_132 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__2(x_0, x_78, x_131, x_3, x_86);
return x_132;
}
}
}
}
}
}
obj* _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__2_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
unsigned char x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s12_decl__locals_s9___spec__2(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s13_need__uncurry(obj* x_0) {
{
obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_7; 
x_1 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_0);
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
lean::inc(x_2);
x_5 = _l_s4_list_s6_length_s6___main_s6___rarg(x_2);
x_6 = _l_s4_lean_s18_closure__max__args;
x_7 = lean::nat_dec_lt(x_6, x_5);
lean::dec(x_5);
if (lean::obj_tag(x_7) == 0)
{
unsigned char x_12; obj* x_13; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_2);
x_12 = 0;
x_13 = lean::box(x_12);
return x_13;
}
else
{
obj* x_15; unsigned char x_18; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_7);
x_15 = lean::cnstr_get(x_1, 2);
lean::inc(x_15);
lean::dec(x_1);
x_18 = lean::unbox(x_15);
lean::dec(x_15);
x_20 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_18);
x_21 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_22 = lean::nat_dec_eq(x_20, x_21);
lean::dec(x_20);
if (lean::obj_tag(x_22) == 0)
{
unsigned char x_26; obj* x_27; 
lean::dec(x_2);
lean::dec(x_22);
x_26 = 0;
x_27 = lean::box(x_26);
return x_27;
}
else
{
obj* x_29; 
lean::dec(x_22);
x_29 = _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_need__uncurry_s9___spec__1(x_2);
return x_29;
}
}
}
}
obj* _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_need__uncurry_s9___spec__1(obj* x_0) {
{

if (lean::obj_tag(x_0) == 0)
{
unsigned char x_2; obj* x_3; 
lean::dec(x_0);
x_2 = 1;
x_3 = lean::box(x_2);
return x_3;
}
else
{
obj* x_4; obj* x_6; unsigned char x_9; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get_scalar<unsigned char>(x_4, sizeof(void*)*1);
lean::dec(x_4);
x_11 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_9);
x_12 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_13 = lean::nat_dec_eq(x_11, x_12);
lean::dec(x_11);
if (lean::obj_tag(x_13) == 0)
{
unsigned char x_17; obj* x_18; 
lean::dec(x_13);
lean::dec(x_6);
x_17 = 0;
x_18 = lean::box(x_17);
return x_18;
}
else
{
obj* x_20; 
lean::dec(x_13);
x_20 = _l_s4_list_s5_foldr_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_need__uncurry_s9___spec__1(x_6);
return x_20;
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = _l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header_s11___closed__1;
lean::inc(x_1);
lean::inc(x_3);
x_6 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_3, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_0);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_16 = x_7;
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
if (lean::is_scalar(x_11)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_11;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_9);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_25; obj* x_26; obj* x_28; 
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_19 = x_7;
}
x_20 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_0);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
lean::dec(x_20);
lean::inc(x_1);
x_25 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__fnid(x_21, x_1, x_9);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_32; obj* x_35; obj* x_36; 
lean::dec(x_1);
x_32 = lean::cnstr_get(x_26, 0);
lean::inc(x_32);
lean::dec(x_26);
if (lean::is_scalar(x_19)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_19;
}
lean::cnstr_set(x_35, 0, x_32);
if (lean::is_scalar(x_11)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_11;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_28);
return x_36;
}
else
{
obj* x_40; obj* x_42; 
lean::dec(x_11);
lean::dec(x_19);
lean::dec(x_26);
x_40 = _l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header_s11___closed__2;
lean::inc(x_40);
x_42 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_40, x_1, x_28);
return x_42;
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("obj* uncurry");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("(obj** as)");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_1);
lean::inc(x_0);
x_11 = _l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header(x_0, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_12, 0);
lean::inc(x_17);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
x_6 = x_20;
x_7 = x_14;
goto lbl_8;
}
else
{
obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_28; obj* x_32; 
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_21 = x_12;
}
x_22 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__3;
lean::inc(x_1);
lean::inc(x_22);
x_25 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_22, x_1, x_14);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
lean::inc(x_0);
x_32 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_0);
if (lean::obj_tag(x_26) == 0)
{
obj* x_34; obj* x_37; 
lean::dec(x_32);
x_34 = lean::cnstr_get(x_26, 0);
lean::inc(x_34);
lean::dec(x_26);
if (lean::is_scalar(x_21)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_21;
}
lean::cnstr_set(x_37, 0, x_34);
x_6 = x_37;
x_7 = x_28;
goto lbl_8;
}
else
{
obj* x_39; obj* x_42; obj* x_45; obj* x_46; obj* x_48; 
lean::dec(x_26);
x_39 = lean::cnstr_get(x_32, 0);
lean::inc(x_39);
lean::dec(x_32);
x_42 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__terminator_s11___closed__1;
lean::inc(x_1);
lean::inc(x_42);
x_45 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_42, x_1, x_28);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
if (lean::obj_tag(x_46) == 0)
{
obj* x_52; obj* x_55; 
lean::dec(x_39);
x_52 = lean::cnstr_get(x_46, 0);
lean::inc(x_52);
lean::dec(x_46);
if (lean::is_scalar(x_21)) {
 x_55 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_55 = x_21;
}
lean::cnstr_set(x_55, 0, x_52);
x_6 = x_55;
x_7 = x_48;
goto lbl_8;
}
else
{
obj* x_59; obj* x_60; obj* x_62; 
lean::dec(x_46);
lean::dec(x_21);
lean::inc(x_1);
x_59 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__fnid(x_39, x_1, x_48);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
x_6 = x_60;
x_7 = x_62;
goto lbl_8;
}
}
}
lbl_5:
{

if (lean::obj_tag(x_3) == 0)
{
obj* x_66; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_1);
x_66 = lean::cnstr_get(x_3, 0);
lean::inc(x_66);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_68 = x_3;
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_66);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_4);
return x_70;
}
else
{
obj* x_71; obj* x_73; obj* x_74; obj* x_76; obj* x_78; 
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_71 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_71 = x_3;
}
lean::inc(x_1);
x_73 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos(x_1, x_4);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_78 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 lean::cnstr_release(x_73, 1);
 x_78 = x_73;
}
if (lean::obj_tag(x_74) == 0)
{
obj* x_80; obj* x_83; obj* x_84; 
lean::dec(x_1);
x_80 = lean::cnstr_get(x_74, 0);
lean::inc(x_80);
lean::dec(x_74);
if (lean::is_scalar(x_71)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_71;
}
lean::cnstr_set(x_83, 0, x_80);
if (lean::is_scalar(x_78)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_78;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_76);
return x_84;
}
else
{
obj* x_88; obj* x_90; 
lean::dec(x_78);
lean::dec(x_71);
lean::dec(x_74);
x_88 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__1;
lean::inc(x_88);
x_90 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_88, x_1, x_76);
return x_90;
}
}
}
lbl_8:
{

if (lean::obj_tag(x_6) == 0)
{
obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_0);
x_92 = lean::cnstr_get(x_6, 0);
lean::inc(x_92);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_94 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_94 = x_6;
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_92);
x_3 = x_95;
x_4 = x_7;
goto lbl_5;
}
else
{
obj* x_96; obj* x_97; obj* x_100; obj* x_101; obj* x_103; 
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_96 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_96 = x_6;
}
x_97 = _l_s4_prod_s9_has__repr_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_97);
x_100 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_97, x_1, x_7);
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
lean::dec(x_100);
if (lean::obj_tag(x_101) == 0)
{
obj* x_107; obj* x_110; 
lean::dec(x_0);
x_107 = lean::cnstr_get(x_101, 0);
lean::inc(x_107);
lean::dec(x_101);
if (lean::is_scalar(x_96)) {
 x_110 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_110 = x_96;
}
lean::cnstr_set(x_110, 0, x_107);
x_3 = x_110;
x_4 = x_103;
goto lbl_5;
}
else
{
obj* x_112; obj* x_115; obj* x_116; obj* x_118; 
lean::dec(x_101);
x_112 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__2;
lean::inc(x_1);
lean::inc(x_112);
x_115 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_112, x_1, x_103);
x_116 = lean::cnstr_get(x_115, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_115, 1);
lean::inc(x_118);
lean::dec(x_115);
if (lean::obj_tag(x_116) == 0)
{
obj* x_122; obj* x_125; 
lean::dec(x_0);
x_122 = lean::cnstr_get(x_116, 0);
lean::inc(x_122);
lean::dec(x_116);
if (lean::is_scalar(x_96)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_96;
}
lean::cnstr_set(x_125, 0, x_122);
x_3 = x_125;
x_4 = x_118;
goto lbl_5;
}
else
{
obj* x_128; obj* x_129; obj* x_131; 
lean::dec(x_116);
lean::inc(x_1);
x_128 = _l_s3_nat_s7_mrepeat_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__1(x_0, x_1, x_118);
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_128, 1);
lean::inc(x_131);
lean::dec(x_128);
if (lean::obj_tag(x_129) == 0)
{
obj* x_134; obj* x_137; 
x_134 = lean::cnstr_get(x_129, 0);
lean::inc(x_134);
lean::dec(x_129);
if (lean::is_scalar(x_96)) {
 x_137 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_137 = x_96;
}
lean::cnstr_set(x_137, 0, x_134);
x_3 = x_137;
x_4 = x_131;
goto lbl_5;
}
else
{
obj* x_138; obj* x_141; obj* x_144; obj* x_145; obj* x_147; 
x_138 = lean::cnstr_get(x_129, 0);
lean::inc(x_138);
lean::dec(x_129);
x_141 = _l_s6_option_s9_has__repr_s6___rarg_s11___closed__3;
lean::inc(x_1);
lean::inc(x_141);
x_144 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_141, x_1, x_131);
x_145 = lean::cnstr_get(x_144, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_144, 1);
lean::inc(x_147);
lean::dec(x_144);
if (lean::obj_tag(x_145) == 0)
{
obj* x_151; obj* x_154; 
lean::dec(x_138);
x_151 = lean::cnstr_get(x_145, 0);
lean::inc(x_151);
lean::dec(x_145);
if (lean::is_scalar(x_96)) {
 x_154 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_154 = x_96;
}
lean::cnstr_set(x_154, 0, x_151);
x_3 = x_154;
x_4 = x_147;
goto lbl_5;
}
else
{
obj* x_156; 
lean::dec(x_145);
if (lean::is_scalar(x_96)) {
 x_156 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_156 = x_96;
}
lean::cnstr_set(x_156, 0, x_138);
x_3 = x_156;
x_4 = x_147;
goto lbl_5;
}
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("}\n");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("as[0]");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string(" {\n");
return x_0;
}
}
obj* _l_s9_reader__t_s4_pure_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* _l_s9_reader__t_s4_pure_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__2(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_pure_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__2_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s3_nat_s6_repeat_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__3(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
lean::dec(x_4);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_0, x_7);
lean::dec(x_0);
lean::inc(x_1);
lean::inc(x_8);
x_12 = _l_s3_nat_s6_repeat_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__3(x_8, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 x_17 = x_12;
}
if (lean::obj_tag(x_13) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_7);
lean::dec(x_8);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_13, 0);
lean::inc(x_21);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_23 = x_13;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_17)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_17;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_15);
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_33; 
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_26 = x_13;
}
x_27 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_27);
x_30 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_27, x_1, x_15);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
if (lean::obj_tag(x_31) == 0)
{
obj* x_39; obj* x_42; obj* x_43; 
lean::dec(x_7);
lean::dec(x_8);
lean::dec(x_1);
x_39 = lean::cnstr_get(x_31, 0);
lean::inc(x_39);
lean::dec(x_31);
if (lean::is_scalar(x_26)) {
 x_42 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_42 = x_26;
}
lean::cnstr_set(x_42, 0, x_39);
if (lean::is_scalar(x_17)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_17;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_33);
return x_43;
}
else
{
obj* x_45; obj* x_48; obj* x_49; obj* x_51; 
lean::dec(x_31);
x_45 = _l_s3_nat_s6_repeat_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__3_s11___closed__1;
lean::inc(x_1);
lean::inc(x_45);
x_48 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_45, x_1, x_33);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_57; obj* x_60; obj* x_61; 
lean::dec(x_7);
lean::dec(x_8);
lean::dec(x_1);
x_57 = lean::cnstr_get(x_49, 0);
lean::inc(x_57);
lean::dec(x_49);
if (lean::is_scalar(x_26)) {
 x_60 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_60 = x_26;
}
lean::cnstr_set(x_60, 0, x_57);
if (lean::is_scalar(x_17)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_17;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_51);
return x_61;
}
else
{
obj* x_63; obj* x_67; obj* x_68; obj* x_70; 
lean::dec(x_49);
x_63 = lean::nat_add(x_8, x_7);
lean::dec(x_7);
lean::dec(x_8);
lean::inc(x_1);
x_67 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s9___spec__1(x_63, x_1, x_51);
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
if (lean::obj_tag(x_68) == 0)
{
obj* x_74; obj* x_77; obj* x_78; 
lean::dec(x_1);
x_74 = lean::cnstr_get(x_68, 0);
lean::inc(x_74);
lean::dec(x_68);
if (lean::is_scalar(x_26)) {
 x_77 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_77 = x_26;
}
lean::cnstr_set(x_77, 0, x_74);
if (lean::is_scalar(x_17)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_17;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_70);
return x_78;
}
else
{
obj* x_82; obj* x_84; 
lean::dec(x_17);
lean::dec(x_68);
lean::dec(x_26);
x_82 = _l_s4_list_s4_repr_s6___main_s6___rarg_s11___closed__3;
lean::inc(x_82);
x_84 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_82, x_1, x_70);
return x_84;
}
}
}
}
}
else
{
unsigned char x_87; obj* x_88; obj* x_89; 
lean::dec(x_4);
lean::dec(x_0);
x_87 = 0;
x_88 = lean::box(x_87);
x_89 = _l_s9_reader__t_s4_pure_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__2_s6___rarg(x_88, x_1, x_2);
return x_89;
}
}
}
obj* _init__l_s3_nat_s6_repeat_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__3_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("as[");
return x_0;
}
}
obj* _l_s3_nat_s7_mrepeat_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_12; 
x_3 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_0);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = _l_s4_list_s6_length_s6___main_s6___rarg(x_4);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_7, x_8);
lean::dec(x_8);
lean::dec(x_7);
x_12 = _l_s3_nat_s6_repeat_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__3(x_9, x_1, x_2);
return x_12;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s15_emit__def__core(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_10; 
lean::dec(x_0);
lean::dec(x_1);
x_10 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_10);
x_5 = x_10;
x_6 = x_2;
goto lbl_7;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_19; unsigned char x_20; obj* x_22; 
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_12, 1);
lean::inc(x_16);
lean::inc(x_0);
x_19 = _l_s4_lean_s2_ir_s3_cpp_s13_need__uncurry(x_0);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_24; 
x_24 = lean::alloc_cnstr(0, 0, 0);
;
x_22 = x_24;
goto lbl_23;
}
else
{
obj* x_25; 
x_25 = lean::alloc_cnstr(1, 0, 0);
;
x_22 = x_25;
goto lbl_23;
}
lbl_23:
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_33; 
lean::inc(x_1);
x_30 = _l_s4_lean_s2_ir_s3_cpp_s12_emit__header(x_12, x_1, x_2);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
if (lean::obj_tag(x_31) == 0)
{
obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_16);
x_37 = lean::cnstr_get(x_31, 0);
lean::inc(x_37);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 x_39 = x_31;
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_37);
x_26 = x_40;
x_27 = x_33;
goto lbl_28;
}
else
{
obj* x_41; obj* x_42; obj* x_45; obj* x_46; obj* x_48; 
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 x_41 = x_31;
}
x_42 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__1;
lean::inc(x_1);
lean::inc(x_42);
x_45 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_42, x_1, x_33);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
if (lean::obj_tag(x_46) == 0)
{
obj* x_52; obj* x_55; 
lean::dec(x_16);
x_52 = lean::cnstr_get(x_46, 0);
lean::inc(x_52);
lean::dec(x_46);
if (lean::is_scalar(x_41)) {
 x_55 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_55 = x_41;
}
lean::cnstr_set(x_55, 0, x_52);
x_26 = x_55;
x_27 = x_48;
goto lbl_28;
}
else
{
obj* x_57; obj* x_60; obj* x_61; obj* x_63; 
lean::dec(x_46);
x_57 = _l_s4_lean_s6_format_s2_be_s6___main_s11___closed__1;
lean::inc(x_1);
lean::inc(x_57);
x_60 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_57, x_1, x_48);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_67; obj* x_70; 
lean::dec(x_16);
x_67 = lean::cnstr_get(x_61, 0);
lean::inc(x_67);
lean::dec(x_61);
if (lean::is_scalar(x_41)) {
 x_70 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_70 = x_41;
}
lean::cnstr_set(x_70, 0, x_67);
x_26 = x_70;
x_27 = x_63;
goto lbl_28;
}
else
{
obj* x_74; obj* x_75; obj* x_77; 
lean::dec(x_61);
lean::dec(x_41);
lean::inc(x_1);
x_74 = _l_s4_lean_s2_ir_s3_cpp_s12_decl__locals(x_16, x_1, x_63);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
lean::dec(x_74);
x_26 = x_75;
x_27 = x_77;
goto lbl_28;
}
}
}
lbl_28:
{

if (lean::obj_tag(x_26) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_22);
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_1);
x_84 = lean::cnstr_get(x_26, 0);
lean::inc(x_84);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_86 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_86 = x_26;
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_84);
x_5 = x_87;
x_6 = x_27;
goto lbl_7;
}
else
{
obj* x_88; obj* x_90; obj* x_91; obj* x_93; 
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_88 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_88 = x_26;
}
lean::inc(x_1);
x_90 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s15_emit__def__core_s9___spec__1(x_14, x_1, x_27);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
if (lean::obj_tag(x_91) == 0)
{
obj* x_99; obj* x_102; 
lean::dec(x_22);
lean::dec(x_0);
lean::dec(x_1);
x_99 = lean::cnstr_get(x_91, 0);
lean::inc(x_99);
lean::dec(x_91);
if (lean::is_scalar(x_88)) {
 x_102 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_102 = x_88;
}
lean::cnstr_set(x_102, 0, x_99);
x_5 = x_102;
x_6 = x_93;
goto lbl_7;
}
else
{
obj* x_104; obj* x_107; obj* x_108; obj* x_110; 
lean::dec(x_91);
x_104 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__2;
lean::inc(x_1);
lean::inc(x_104);
x_107 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_104, x_1, x_93);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_107, 1);
lean::inc(x_110);
lean::dec(x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_116; obj* x_119; 
lean::dec(x_22);
lean::dec(x_0);
lean::dec(x_1);
x_116 = lean::cnstr_get(x_108, 0);
lean::inc(x_116);
lean::dec(x_108);
if (lean::is_scalar(x_88)) {
 x_119 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_119 = x_88;
}
lean::cnstr_set(x_119, 0, x_116);
x_5 = x_119;
x_6 = x_110;
goto lbl_7;
}
else
{
obj* x_121; obj* x_124; obj* x_125; obj* x_127; 
lean::dec(x_108);
x_121 = _l_s4_lean_s6_format_s2_be_s6___main_s11___closed__1;
lean::inc(x_1);
lean::inc(x_121);
x_124 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_121, x_1, x_110);
x_125 = lean::cnstr_get(x_124, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_124, 1);
lean::inc(x_127);
lean::dec(x_124);
if (lean::obj_tag(x_125) == 0)
{
obj* x_133; obj* x_136; 
lean::dec(x_22);
lean::dec(x_0);
lean::dec(x_1);
x_133 = lean::cnstr_get(x_125, 0);
lean::inc(x_133);
lean::dec(x_125);
if (lean::is_scalar(x_88)) {
 x_136 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_136 = x_88;
}
lean::cnstr_set(x_136, 0, x_133);
x_5 = x_136;
x_6 = x_127;
goto lbl_7;
}
else
{

lean::dec(x_125);
lean::dec(x_88);
if (lean::obj_tag(x_22) == 0)
{
obj* x_142; 
lean::dec(x_22);
lean::dec(x_0);
lean::dec(x_1);
x_142 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_142);
x_5 = x_142;
x_6 = x_127;
goto lbl_7;
}
else
{
obj* x_145; obj* x_146; obj* x_148; 
lean::dec(x_22);
x_145 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry(x_0, x_1, x_127);
x_146 = lean::cnstr_get(x_145, 0);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_145, 1);
lean::inc(x_148);
lean::dec(x_145);
x_5 = x_146;
x_6 = x_148;
goto lbl_7;
}
}
}
}
}
}
}
}
lbl_7:
{

if (lean::obj_tag(x_5) == 0)
{
obj* x_151; obj* x_153; obj* x_154; obj* x_157; unsigned char x_158; obj* x_159; obj* x_161; obj* x_162; obj* x_163; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
x_151 = lean::cnstr_get(x_5, 0);
lean::inc(x_151);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_153 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_153 = x_5;
}
x_154 = lean::cnstr_get(x_4, 0);
lean::inc(x_154);
lean::dec(x_4);
x_157 = _l_s4_lean_s7_to__fmt_s4___at_s4_lean_s2_ir_s5_instr_s10_to__format_s6___main_s9___spec__2(x_154);
x_158 = 0;
x_159 = _l_s4_lean_s2_ir_s6_header_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_159);
x_161 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_161, 0, x_159);
lean::cnstr_set(x_161, 1, x_157);
lean::cnstr_set_scalar(x_161, sizeof(void*)*2, x_158);
x_162 = x_161;
x_163 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_163);
x_165 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_165, 0, x_162);
lean::cnstr_set(x_165, 1, x_163);
lean::cnstr_set_scalar(x_165, sizeof(void*)*2, x_158);
x_166 = x_165;
x_167 = lean::alloc_cnstr(1, 0, 0);
;
x_168 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_168, 0, x_166);
lean::cnstr_set(x_168, 1, x_167);
lean::cnstr_set_scalar(x_168, sizeof(void*)*2, x_158);
x_169 = x_168;
x_170 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_170, 0, x_169);
lean::cnstr_set(x_170, 1, x_151);
lean::cnstr_set_scalar(x_170, sizeof(void*)*2, x_158);
x_171 = x_170;
if (lean::is_scalar(x_153)) {
 x_172 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_172 = x_153;
}
lean::cnstr_set(x_172, 0, x_171);
x_173 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_173, 0, x_172);
lean::cnstr_set(x_173, 1, x_6);
return x_173;
}
else
{
obj* x_175; 
lean::dec(x_4);
x_175 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_175, 0, x_5);
lean::cnstr_set(x_175, 1, x_6);
return x_175;
}
}
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s15_emit__def__core_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__block(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
obj* x_29; 
lean::dec(x_15);
lean::dec(x_19);
x_29 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s15_emit__def__core_s9___spec__1(x_10, x_1, x_17);
return x_29;
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s9_emit__def(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 3);
lean::inc(x_6);
lean::inc(x_0);
x_9 = _l_s4_lean_s2_ir_s12_infer__types(x_0, x_6);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_0);
lean::dec(x_3);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_14 = x_9;
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_2);
return x_16;
}
else
{
obj* x_17; obj* x_20; obj* x_21; 
x_17 = lean::cnstr_get(x_9, 0);
lean::inc(x_17);
lean::dec(x_9);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_3);
lean::cnstr_set(x_20, 1, x_17);
x_21 = _l_s4_lean_s2_ir_s3_cpp_s15_emit__def__core(x_0, x_20, x_2);
return x_21;
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s13_collect__used(obj* x_0) {
{
obj* x_1; obj* x_3; 
x_1 = _l_s4_lean_s2_ir_s13_mk__fnid__set;
lean::inc(x_1);
x_3 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__6(x_1, x_0);
return x_3;
}
}
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__3(obj* x_0, obj* x_1, unsigned char x_2) {
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; obj* x_5; 
x_3 = lean::box(x_2);
lean::inc(x_0);
x_5 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_3);
lean::cnstr_set(x_5, 3, x_0);
return x_5;
}
case 1:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_17; unsigned char x_18; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 2);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 3);
lean::inc(x_12);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_14 = x_0;
}
lean::inc(x_8);
lean::inc(x_1);
x_17 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_8);
x_18 = lean::unbox(x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_22; unsigned char x_23; 
lean::inc(x_1);
lean::inc(x_8);
x_22 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_8, x_1);
x_23 = lean::unbox(x_22);
lean::dec(x_22);
if (x_23 == 0)
{
obj* x_27; obj* x_28; 
lean::dec(x_10);
lean::dec(x_8);
x_27 = lean::box(x_2);
if (lean::is_scalar(x_14)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_14;
}
lean::cnstr_set(x_28, 0, x_6);
lean::cnstr_set(x_28, 1, x_1);
lean::cnstr_set(x_28, 2, x_27);
lean::cnstr_set(x_28, 3, x_12);
return x_28;
}
else
{
obj* x_29; obj* x_30; 
x_29 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__3(x_12, x_1, x_2);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_8);
lean::cnstr_set(x_30, 2, x_10);
lean::cnstr_set(x_30, 3, x_29);
return x_30;
}
}
else
{
obj* x_31; obj* x_32; 
x_31 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__3(x_6, x_1, x_2);
if (lean::is_scalar(x_14)) {
 x_32 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_32 = x_14;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_8);
lean::cnstr_set(x_32, 2, x_10);
lean::cnstr_set(x_32, 3, x_12);
return x_32;
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_44; unsigned char x_45; 
x_33 = lean::cnstr_get(x_0, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 2);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_0, 3);
lean::inc(x_39);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_41 = x_0;
}
lean::inc(x_35);
lean::inc(x_1);
x_44 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_35);
x_45 = lean::unbox(x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_49; unsigned char x_50; 
lean::inc(x_1);
lean::inc(x_35);
x_49 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_35, x_1);
x_50 = lean::unbox(x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_54; obj* x_55; 
lean::dec(x_35);
lean::dec(x_37);
x_54 = lean::box(x_2);
if (lean::is_scalar(x_41)) {
 x_55 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_55 = x_41;
}
lean::cnstr_set(x_55, 0, x_33);
lean::cnstr_set(x_55, 1, x_1);
lean::cnstr_set(x_55, 2, x_54);
lean::cnstr_set(x_55, 3, x_39);
return x_55;
}
else
{
unsigned char x_57; 
lean::inc(x_39);
x_57 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_39);
if (x_57 == 0)
{
obj* x_59; obj* x_60; 
lean::dec(x_41);
x_59 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__3(x_39, x_1, x_2);
x_60 = _l_s6_rbnode_s14_balance2__node_s6___main_s6___rarg(x_59, x_35, x_37, x_33);
return x_60;
}
else
{
obj* x_61; obj* x_62; 
x_61 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__3(x_39, x_1, x_2);
if (lean::is_scalar(x_41)) {
 x_62 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_62 = x_41;
}
lean::cnstr_set(x_62, 0, x_33);
lean::cnstr_set(x_62, 1, x_35);
lean::cnstr_set(x_62, 2, x_37);
lean::cnstr_set(x_62, 3, x_61);
return x_62;
}
}
}
else
{
unsigned char x_64; 
lean::inc(x_33);
x_64 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_33);
if (x_64 == 0)
{
obj* x_66; obj* x_67; 
lean::dec(x_41);
x_66 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__3(x_33, x_1, x_2);
x_67 = _l_s6_rbnode_s14_balance1__node_s6___main_s6___rarg(x_66, x_35, x_37, x_39);
return x_67;
}
else
{
obj* x_68; obj* x_69; 
x_68 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__3(x_33, x_1, x_2);
if (lean::is_scalar(x_41)) {
 x_69 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_69 = x_41;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_35);
lean::cnstr_set(x_69, 2, x_37);
lean::cnstr_set(x_69, 3, x_39);
return x_69;
}
}
}
}
}
}
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__2(obj* x_0, obj* x_1, unsigned char x_2) {
{
unsigned char x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_0);
x_5 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__3(x_0, x_1, x_2);
x_6 = _l_s6_rbnode_s18_mk__insert__result_s6___main_s6___rarg(x_4, x_5);
return x_6;
}
}
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__1(obj* x_0, obj* x_1, unsigned char x_2) {
{
obj* x_3; 
x_3 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_1) == 0)
{

lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
switch (lean::obj_tag(x_3)) {
case 0:
{
obj* x_9; 
lean::dec(x_3);
x_9 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_9;
}
case 1:
{
obj* x_11; 
lean::dec(x_3);
x_11 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_11;
}
case 2:
{
obj* x_13; 
lean::dec(x_3);
x_13 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_13;
}
case 3:
{
obj* x_15; 
lean::dec(x_3);
x_15 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_15;
}
case 4:
{
obj* x_17; 
lean::dec(x_3);
x_17 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_17;
}
case 5:
{
obj* x_18; unsigned char x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_3, 1);
lean::inc(x_18);
lean::dec(x_3);
x_21 = 0;
x_22 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__2(x_0, x_18, x_21);
x_23 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_22, x_5);
return x_23;
}
case 6:
{
obj* x_25; 
lean::dec(x_3);
x_25 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_25;
}
case 7:
{
obj* x_27; 
lean::dec(x_3);
x_27 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_27;
}
case 8:
{
obj* x_29; 
lean::dec(x_3);
x_29 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_29;
}
case 9:
{
obj* x_31; 
lean::dec(x_3);
x_31 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_31;
}
case 10:
{
obj* x_33; 
lean::dec(x_3);
x_33 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_33;
}
case 11:
{
obj* x_34; unsigned char x_37; obj* x_38; obj* x_39; 
x_34 = lean::cnstr_get(x_3, 1);
lean::inc(x_34);
lean::dec(x_3);
x_37 = 0;
x_38 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__2(x_0, x_34, x_37);
x_39 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_38, x_5);
return x_39;
}
case 12:
{
obj* x_41; 
lean::dec(x_3);
x_41 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_41;
}
case 13:
{
obj* x_43; 
lean::dec(x_3);
x_43 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_43;
}
case 14:
{
obj* x_45; 
lean::dec(x_3);
x_45 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_45;
}
default:
{
obj* x_47; 
lean::dec(x_3);
x_47 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_5);
return x_47;
}
}
}
}
}
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__5(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_1) == 0)
{

lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
lean::dec(x_3);
x_11 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__4(x_0, x_8);
x_12 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__5(x_11, x_5);
return x_12;
}
}
}
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__6(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_1) == 0)
{

lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_9; 
lean::dec(x_3);
x_9 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__6(x_0, x_5);
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__5(x_0, x_10);
x_14 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__6(x_13, x_5);
return x_14;
}
}
}
}
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__3_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__3(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__2_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__2(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__1(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; unsigned char x_6; obj* x_8; 
x_3 = _l_s4_lean_s2_ir_s13_mk__fnid__set;
lean::inc(x_3);
x_5 = _l_s4_list_s5_foldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_collect__used_s9___spec__6(x_3, x_0);
x_6 = 0;
lean::inc(x_1);
x_8 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1(x_1, x_5, x_6, x_1, x_2);
return x_8;
}
}
obj* _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1(obj* x_0, obj* x_1, unsigned char x_2, obj* x_3, obj* x_4) {
{

switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
x_8 = lean::box(x_2);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_4);
return x_10;
}
case 1:
{
obj* x_11; obj* x_13; obj* x_15; obj* x_20; obj* x_21; obj* x_23; obj* x_25; 
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_1, 3);
lean::inc(x_15);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_0);
x_20 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1(x_0, x_11, x_2, x_3, x_4);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_release(x_20, 1);
 x_25 = x_20;
}
if (lean::obj_tag(x_21) == 0)
{
obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_13);
lean::dec(x_15);
lean::dec(x_0);
lean::dec(x_3);
x_30 = lean::cnstr_get(x_21, 0);
lean::inc(x_30);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_32 = x_21;
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
if (lean::is_scalar(x_25)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_25;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_23);
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_44; 
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_35 = x_21;
}
x_39 = lean::cnstr_get(x_0, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_39, 3);
lean::inc(x_41);
lean::inc(x_13);
x_44 = lean::apply_1(x_41, x_13);
if (lean::obj_tag(x_44) == 0)
{
obj* x_48; 
lean::dec(x_13);
lean::dec(x_44);
lean::dec(x_39);
x_48 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_48);
x_36 = x_48;
x_37 = x_23;
goto lbl_38;
}
else
{
obj* x_50; obj* x_53; obj* x_56; 
x_50 = lean::cnstr_get(x_44, 0);
lean::inc(x_50);
lean::dec(x_44);
x_53 = lean::cnstr_get(x_39, 4);
lean::inc(x_53);
lean::dec(x_39);
x_56 = lean::apply_1(x_53, x_13);
if (lean::obj_tag(x_56) == 0)
{
obj* x_59; obj* x_61; unsigned char x_62; obj* x_65; 
lean::dec(x_56);
lean::inc(x_50);
x_59 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_50);
lean::inc(x_50);
x_61 = _l_s4_lean_s2_ir_s3_cpp_s13_need__uncurry(x_50);
x_62 = lean::unbox(x_61);
lean::dec(x_61);
lean::inc(x_3);
x_65 = _l_s4_lean_s2_ir_s3_cpp_s12_emit__header(x_59, x_3, x_23);
if (x_62 == 0)
{
obj* x_67; obj* x_69; 
lean::dec(x_50);
x_67 = lean::cnstr_get(x_65, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_65, 1);
lean::inc(x_69);
lean::dec(x_65);
if (lean::obj_tag(x_67) == 0)
{
obj* x_72; obj* x_74; obj* x_75; 
x_72 = lean::cnstr_get(x_67, 0);
lean::inc(x_72);
if (lean::is_shared(x_67)) {
 lean::dec(x_67);
 x_74 = lean::box(0);
} else {
 lean::cnstr_release(x_67, 0);
 x_74 = x_67;
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_72);
x_36 = x_75;
x_37 = x_69;
goto lbl_38;
}
else
{
obj* x_76; obj* x_77; obj* x_80; obj* x_81; obj* x_83; 
if (lean::is_shared(x_67)) {
 lean::dec(x_67);
 x_76 = lean::box(0);
} else {
 lean::cnstr_release(x_67, 0);
 x_76 = x_67;
}
x_77 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__1;
lean::inc(x_3);
lean::inc(x_77);
x_80 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_77, x_3, x_69);
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_80, 1);
lean::inc(x_83);
lean::dec(x_80);
if (lean::obj_tag(x_81) == 0)
{
obj* x_86; obj* x_89; 
x_86 = lean::cnstr_get(x_81, 0);
lean::inc(x_86);
lean::dec(x_81);
if (lean::is_scalar(x_76)) {
 x_89 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_89 = x_76;
}
lean::cnstr_set(x_89, 0, x_86);
x_36 = x_89;
x_37 = x_83;
goto lbl_38;
}
else
{
obj* x_92; 
lean::dec(x_76);
lean::dec(x_81);
x_92 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_92);
x_36 = x_92;
x_37 = x_83;
goto lbl_38;
}
}
}
else
{
obj* x_94; obj* x_96; 
x_94 = lean::cnstr_get(x_65, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_65, 1);
lean::inc(x_96);
lean::dec(x_65);
if (lean::obj_tag(x_94) == 0)
{
obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_50);
x_100 = lean::cnstr_get(x_94, 0);
lean::inc(x_100);
if (lean::is_shared(x_94)) {
 lean::dec(x_94);
 x_102 = lean::box(0);
} else {
 lean::cnstr_release(x_94, 0);
 x_102 = x_94;
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_100);
x_36 = x_103;
x_37 = x_96;
goto lbl_38;
}
else
{
obj* x_104; obj* x_105; obj* x_108; obj* x_109; obj* x_111; 
if (lean::is_shared(x_94)) {
 lean::dec(x_94);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_94, 0);
 x_104 = x_94;
}
x_105 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__1;
lean::inc(x_3);
lean::inc(x_105);
x_108 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_105, x_3, x_96);
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_108, 1);
lean::inc(x_111);
lean::dec(x_108);
if (lean::obj_tag(x_109) == 0)
{
obj* x_116; obj* x_119; 
lean::dec(x_105);
lean::dec(x_50);
x_116 = lean::cnstr_get(x_109, 0);
lean::inc(x_116);
lean::dec(x_109);
if (lean::is_scalar(x_104)) {
 x_119 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_119 = x_104;
}
lean::cnstr_set(x_119, 0, x_116);
x_36 = x_119;
x_37 = x_111;
goto lbl_38;
}
else
{
obj* x_122; obj* x_123; obj* x_125; 
lean::dec(x_109);
lean::inc(x_3);
x_122 = _l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header(x_50, x_3, x_111);
x_123 = lean::cnstr_get(x_122, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get(x_122, 1);
lean::inc(x_125);
lean::dec(x_122);
if (lean::obj_tag(x_123) == 0)
{
obj* x_129; obj* x_132; 
lean::dec(x_105);
x_129 = lean::cnstr_get(x_123, 0);
lean::inc(x_129);
lean::dec(x_123);
if (lean::is_scalar(x_104)) {
 x_132 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_132 = x_104;
}
lean::cnstr_set(x_132, 0, x_129);
x_36 = x_132;
x_37 = x_125;
goto lbl_38;
}
else
{
obj* x_137; obj* x_138; obj* x_140; 
lean::dec(x_123);
lean::dec(x_104);
lean::inc(x_3);
lean::inc(x_105);
x_137 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_105, x_3, x_125);
x_138 = lean::cnstr_get(x_137, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_137, 1);
lean::inc(x_140);
lean::dec(x_137);
x_36 = x_138;
x_37 = x_140;
goto lbl_38;
}
}
}
}
}
else
{
obj* x_144; obj* x_147; obj* x_148; obj* x_150; 
lean::dec(x_56);
x_144 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__2;
lean::inc(x_3);
lean::inc(x_144);
x_147 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_144, x_3, x_23);
x_148 = lean::cnstr_get(x_147, 0);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_147, 1);
lean::inc(x_150);
lean::dec(x_147);
if (lean::obj_tag(x_148) == 0)
{
obj* x_154; obj* x_156; obj* x_157; 
lean::dec(x_50);
x_154 = lean::cnstr_get(x_148, 0);
lean::inc(x_154);
if (lean::is_shared(x_148)) {
 lean::dec(x_148);
 x_156 = lean::box(0);
} else {
 lean::cnstr_release(x_148, 0);
 x_156 = x_148;
}
if (lean::is_scalar(x_156)) {
 x_157 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_157 = x_156;
}
lean::cnstr_set(x_157, 0, x_154);
x_36 = x_157;
x_37 = x_150;
goto lbl_38;
}
else
{
obj* x_158; obj* x_160; obj* x_162; unsigned char x_163; obj* x_166; 
if (lean::is_shared(x_148)) {
 lean::dec(x_148);
 x_158 = lean::box(0);
} else {
 lean::cnstr_release(x_148, 0);
 x_158 = x_148;
}
lean::inc(x_50);
x_160 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_50);
lean::inc(x_50);
x_162 = _l_s4_lean_s2_ir_s3_cpp_s13_need__uncurry(x_50);
x_163 = lean::unbox(x_162);
lean::dec(x_162);
lean::inc(x_3);
x_166 = _l_s4_lean_s2_ir_s3_cpp_s12_emit__header(x_160, x_3, x_150);
if (x_163 == 0)
{
obj* x_168; obj* x_170; 
lean::dec(x_50);
x_168 = lean::cnstr_get(x_166, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_166, 1);
lean::inc(x_170);
lean::dec(x_166);
if (lean::obj_tag(x_168) == 0)
{
obj* x_173; obj* x_176; 
x_173 = lean::cnstr_get(x_168, 0);
lean::inc(x_173);
lean::dec(x_168);
if (lean::is_scalar(x_158)) {
 x_176 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_176 = x_158;
}
lean::cnstr_set(x_176, 0, x_173);
x_36 = x_176;
x_37 = x_170;
goto lbl_38;
}
else
{
obj* x_178; obj* x_181; obj* x_182; obj* x_184; 
lean::dec(x_168);
x_178 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__1;
lean::inc(x_3);
lean::inc(x_178);
x_181 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_178, x_3, x_170);
x_182 = lean::cnstr_get(x_181, 0);
lean::inc(x_182);
x_184 = lean::cnstr_get(x_181, 1);
lean::inc(x_184);
lean::dec(x_181);
if (lean::obj_tag(x_182) == 0)
{
obj* x_187; obj* x_190; 
x_187 = lean::cnstr_get(x_182, 0);
lean::inc(x_187);
lean::dec(x_182);
if (lean::is_scalar(x_158)) {
 x_190 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_190 = x_158;
}
lean::cnstr_set(x_190, 0, x_187);
x_36 = x_190;
x_37 = x_184;
goto lbl_38;
}
else
{
obj* x_193; 
lean::dec(x_182);
lean::dec(x_158);
x_193 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_193);
x_36 = x_193;
x_37 = x_184;
goto lbl_38;
}
}
}
else
{
obj* x_195; obj* x_197; 
x_195 = lean::cnstr_get(x_166, 0);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_166, 1);
lean::inc(x_197);
lean::dec(x_166);
if (lean::obj_tag(x_195) == 0)
{
obj* x_201; obj* x_204; 
lean::dec(x_50);
x_201 = lean::cnstr_get(x_195, 0);
lean::inc(x_201);
lean::dec(x_195);
if (lean::is_scalar(x_158)) {
 x_204 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_204 = x_158;
}
lean::cnstr_set(x_204, 0, x_201);
x_36 = x_204;
x_37 = x_197;
goto lbl_38;
}
else
{
obj* x_206; obj* x_209; obj* x_210; obj* x_212; 
lean::dec(x_195);
x_206 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__1;
lean::inc(x_3);
lean::inc(x_206);
x_209 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_206, x_3, x_197);
x_210 = lean::cnstr_get(x_209, 0);
lean::inc(x_210);
x_212 = lean::cnstr_get(x_209, 1);
lean::inc(x_212);
lean::dec(x_209);
if (lean::obj_tag(x_210) == 0)
{
obj* x_217; obj* x_220; 
lean::dec(x_206);
lean::dec(x_50);
x_217 = lean::cnstr_get(x_210, 0);
lean::inc(x_217);
lean::dec(x_210);
if (lean::is_scalar(x_158)) {
 x_220 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_220 = x_158;
}
lean::cnstr_set(x_220, 0, x_217);
x_36 = x_220;
x_37 = x_212;
goto lbl_38;
}
else
{
obj* x_223; obj* x_224; obj* x_226; 
lean::dec(x_210);
lean::inc(x_3);
x_223 = _l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header(x_50, x_3, x_212);
x_224 = lean::cnstr_get(x_223, 0);
lean::inc(x_224);
x_226 = lean::cnstr_get(x_223, 1);
lean::inc(x_226);
lean::dec(x_223);
if (lean::obj_tag(x_224) == 0)
{
obj* x_230; obj* x_233; 
lean::dec(x_206);
x_230 = lean::cnstr_get(x_224, 0);
lean::inc(x_230);
lean::dec(x_224);
if (lean::is_scalar(x_158)) {
 x_233 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_233 = x_158;
}
lean::cnstr_set(x_233, 0, x_230);
x_36 = x_233;
x_37 = x_226;
goto lbl_38;
}
else
{
obj* x_238; obj* x_239; obj* x_241; 
lean::dec(x_224);
lean::dec(x_158);
lean::inc(x_3);
lean::inc(x_206);
x_238 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_206, x_3, x_226);
x_239 = lean::cnstr_get(x_238, 0);
lean::inc(x_239);
x_241 = lean::cnstr_get(x_238, 1);
lean::inc(x_241);
lean::dec(x_238);
x_36 = x_239;
x_37 = x_241;
goto lbl_38;
}
}
}
}
}
}
}
lbl_38:
{

if (lean::obj_tag(x_36) == 0)
{
obj* x_247; obj* x_250; obj* x_251; 
lean::dec(x_15);
lean::dec(x_0);
lean::dec(x_3);
x_247 = lean::cnstr_get(x_36, 0);
lean::inc(x_247);
lean::dec(x_36);
if (lean::is_scalar(x_35)) {
 x_250 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_250 = x_35;
}
lean::cnstr_set(x_250, 0, x_247);
if (lean::is_scalar(x_25)) {
 x_251 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_251 = x_25;
}
lean::cnstr_set(x_251, 0, x_250);
lean::cnstr_set(x_251, 1, x_37);
return x_251;
}
else
{
unsigned char x_255; obj* x_256; 
lean::dec(x_25);
lean::dec(x_35);
lean::dec(x_36);
x_255 = 0;
x_256 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1(x_0, x_15, x_255, x_3, x_37);
return x_256;
}
}
}
}
default:
{
obj* x_257; obj* x_259; obj* x_261; obj* x_266; obj* x_267; obj* x_269; obj* x_271; 
x_257 = lean::cnstr_get(x_1, 0);
lean::inc(x_257);
x_259 = lean::cnstr_get(x_1, 1);
lean::inc(x_259);
x_261 = lean::cnstr_get(x_1, 3);
lean::inc(x_261);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_0);
x_266 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1(x_0, x_257, x_2, x_3, x_4);
x_267 = lean::cnstr_get(x_266, 0);
lean::inc(x_267);
x_269 = lean::cnstr_get(x_266, 1);
lean::inc(x_269);
if (lean::is_shared(x_266)) {
 lean::dec(x_266);
 x_271 = lean::box(0);
} else {
 lean::cnstr_release(x_266, 0);
 lean::cnstr_release(x_266, 1);
 x_271 = x_266;
}
if (lean::obj_tag(x_267) == 0)
{
obj* x_276; obj* x_278; obj* x_279; obj* x_280; 
lean::dec(x_0);
lean::dec(x_3);
lean::dec(x_261);
lean::dec(x_259);
x_276 = lean::cnstr_get(x_267, 0);
lean::inc(x_276);
if (lean::is_shared(x_267)) {
 lean::dec(x_267);
 x_278 = lean::box(0);
} else {
 lean::cnstr_release(x_267, 0);
 x_278 = x_267;
}
if (lean::is_scalar(x_278)) {
 x_279 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_279 = x_278;
}
lean::cnstr_set(x_279, 0, x_276);
if (lean::is_scalar(x_271)) {
 x_280 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_280 = x_271;
}
lean::cnstr_set(x_280, 0, x_279);
lean::cnstr_set(x_280, 1, x_269);
return x_280;
}
else
{
obj* x_281; obj* x_282; obj* x_283; obj* x_285; obj* x_287; obj* x_290; 
if (lean::is_shared(x_267)) {
 lean::dec(x_267);
 x_281 = lean::box(0);
} else {
 lean::cnstr_release(x_267, 0);
 x_281 = x_267;
}
x_285 = lean::cnstr_get(x_0, 0);
lean::inc(x_285);
x_287 = lean::cnstr_get(x_285, 3);
lean::inc(x_287);
lean::inc(x_259);
x_290 = lean::apply_1(x_287, x_259);
if (lean::obj_tag(x_290) == 0)
{
obj* x_294; 
lean::dec(x_285);
lean::dec(x_290);
lean::dec(x_259);
x_294 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_294);
x_282 = x_294;
x_283 = x_269;
goto lbl_284;
}
else
{
obj* x_296; obj* x_299; obj* x_302; 
x_296 = lean::cnstr_get(x_290, 0);
lean::inc(x_296);
lean::dec(x_290);
x_299 = lean::cnstr_get(x_285, 4);
lean::inc(x_299);
lean::dec(x_285);
x_302 = lean::apply_1(x_299, x_259);
if (lean::obj_tag(x_302) == 0)
{
obj* x_305; obj* x_307; unsigned char x_308; obj* x_311; 
lean::dec(x_302);
lean::inc(x_296);
x_305 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_296);
lean::inc(x_296);
x_307 = _l_s4_lean_s2_ir_s3_cpp_s13_need__uncurry(x_296);
x_308 = lean::unbox(x_307);
lean::dec(x_307);
lean::inc(x_3);
x_311 = _l_s4_lean_s2_ir_s3_cpp_s12_emit__header(x_305, x_3, x_269);
if (x_308 == 0)
{
obj* x_313; obj* x_315; 
lean::dec(x_296);
x_313 = lean::cnstr_get(x_311, 0);
lean::inc(x_313);
x_315 = lean::cnstr_get(x_311, 1);
lean::inc(x_315);
lean::dec(x_311);
if (lean::obj_tag(x_313) == 0)
{
obj* x_318; obj* x_320; obj* x_321; 
x_318 = lean::cnstr_get(x_313, 0);
lean::inc(x_318);
if (lean::is_shared(x_313)) {
 lean::dec(x_313);
 x_320 = lean::box(0);
} else {
 lean::cnstr_release(x_313, 0);
 x_320 = x_313;
}
if (lean::is_scalar(x_320)) {
 x_321 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_321 = x_320;
}
lean::cnstr_set(x_321, 0, x_318);
x_282 = x_321;
x_283 = x_315;
goto lbl_284;
}
else
{
obj* x_322; obj* x_323; obj* x_326; obj* x_327; obj* x_329; 
if (lean::is_shared(x_313)) {
 lean::dec(x_313);
 x_322 = lean::box(0);
} else {
 lean::cnstr_release(x_313, 0);
 x_322 = x_313;
}
x_323 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__1;
lean::inc(x_3);
lean::inc(x_323);
x_326 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_323, x_3, x_315);
x_327 = lean::cnstr_get(x_326, 0);
lean::inc(x_327);
x_329 = lean::cnstr_get(x_326, 1);
lean::inc(x_329);
lean::dec(x_326);
if (lean::obj_tag(x_327) == 0)
{
obj* x_332; obj* x_335; 
x_332 = lean::cnstr_get(x_327, 0);
lean::inc(x_332);
lean::dec(x_327);
if (lean::is_scalar(x_322)) {
 x_335 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_335 = x_322;
}
lean::cnstr_set(x_335, 0, x_332);
x_282 = x_335;
x_283 = x_329;
goto lbl_284;
}
else
{
obj* x_338; 
lean::dec(x_327);
lean::dec(x_322);
x_338 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_338);
x_282 = x_338;
x_283 = x_329;
goto lbl_284;
}
}
}
else
{
obj* x_340; obj* x_342; 
x_340 = lean::cnstr_get(x_311, 0);
lean::inc(x_340);
x_342 = lean::cnstr_get(x_311, 1);
lean::inc(x_342);
lean::dec(x_311);
if (lean::obj_tag(x_340) == 0)
{
obj* x_346; obj* x_348; obj* x_349; 
lean::dec(x_296);
x_346 = lean::cnstr_get(x_340, 0);
lean::inc(x_346);
if (lean::is_shared(x_340)) {
 lean::dec(x_340);
 x_348 = lean::box(0);
} else {
 lean::cnstr_release(x_340, 0);
 x_348 = x_340;
}
if (lean::is_scalar(x_348)) {
 x_349 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_349 = x_348;
}
lean::cnstr_set(x_349, 0, x_346);
x_282 = x_349;
x_283 = x_342;
goto lbl_284;
}
else
{
obj* x_350; obj* x_351; obj* x_354; obj* x_355; obj* x_357; 
if (lean::is_shared(x_340)) {
 lean::dec(x_340);
 x_350 = lean::box(0);
} else {
 lean::cnstr_release(x_340, 0);
 x_350 = x_340;
}
x_351 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__1;
lean::inc(x_3);
lean::inc(x_351);
x_354 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_351, x_3, x_342);
x_355 = lean::cnstr_get(x_354, 0);
lean::inc(x_355);
x_357 = lean::cnstr_get(x_354, 1);
lean::inc(x_357);
lean::dec(x_354);
if (lean::obj_tag(x_355) == 0)
{
obj* x_362; obj* x_365; 
lean::dec(x_351);
lean::dec(x_296);
x_362 = lean::cnstr_get(x_355, 0);
lean::inc(x_362);
lean::dec(x_355);
if (lean::is_scalar(x_350)) {
 x_365 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_365 = x_350;
}
lean::cnstr_set(x_365, 0, x_362);
x_282 = x_365;
x_283 = x_357;
goto lbl_284;
}
else
{
obj* x_368; obj* x_369; obj* x_371; 
lean::dec(x_355);
lean::inc(x_3);
x_368 = _l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header(x_296, x_3, x_357);
x_369 = lean::cnstr_get(x_368, 0);
lean::inc(x_369);
x_371 = lean::cnstr_get(x_368, 1);
lean::inc(x_371);
lean::dec(x_368);
if (lean::obj_tag(x_369) == 0)
{
obj* x_375; obj* x_378; 
lean::dec(x_351);
x_375 = lean::cnstr_get(x_369, 0);
lean::inc(x_375);
lean::dec(x_369);
if (lean::is_scalar(x_350)) {
 x_378 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_378 = x_350;
}
lean::cnstr_set(x_378, 0, x_375);
x_282 = x_378;
x_283 = x_371;
goto lbl_284;
}
else
{
obj* x_383; obj* x_384; obj* x_386; 
lean::dec(x_369);
lean::dec(x_350);
lean::inc(x_3);
lean::inc(x_351);
x_383 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_351, x_3, x_371);
x_384 = lean::cnstr_get(x_383, 0);
lean::inc(x_384);
x_386 = lean::cnstr_get(x_383, 1);
lean::inc(x_386);
lean::dec(x_383);
x_282 = x_384;
x_283 = x_386;
goto lbl_284;
}
}
}
}
}
else
{
obj* x_390; obj* x_393; obj* x_394; obj* x_396; 
lean::dec(x_302);
x_390 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__2;
lean::inc(x_3);
lean::inc(x_390);
x_393 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_390, x_3, x_269);
x_394 = lean::cnstr_get(x_393, 0);
lean::inc(x_394);
x_396 = lean::cnstr_get(x_393, 1);
lean::inc(x_396);
lean::dec(x_393);
if (lean::obj_tag(x_394) == 0)
{
obj* x_400; obj* x_402; obj* x_403; 
lean::dec(x_296);
x_400 = lean::cnstr_get(x_394, 0);
lean::inc(x_400);
if (lean::is_shared(x_394)) {
 lean::dec(x_394);
 x_402 = lean::box(0);
} else {
 lean::cnstr_release(x_394, 0);
 x_402 = x_394;
}
if (lean::is_scalar(x_402)) {
 x_403 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_403 = x_402;
}
lean::cnstr_set(x_403, 0, x_400);
x_282 = x_403;
x_283 = x_396;
goto lbl_284;
}
else
{
obj* x_404; obj* x_406; obj* x_408; unsigned char x_409; obj* x_412; 
if (lean::is_shared(x_394)) {
 lean::dec(x_394);
 x_404 = lean::box(0);
} else {
 lean::cnstr_release(x_394, 0);
 x_404 = x_394;
}
lean::inc(x_296);
x_406 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_296);
lean::inc(x_296);
x_408 = _l_s4_lean_s2_ir_s3_cpp_s13_need__uncurry(x_296);
x_409 = lean::unbox(x_408);
lean::dec(x_408);
lean::inc(x_3);
x_412 = _l_s4_lean_s2_ir_s3_cpp_s12_emit__header(x_406, x_3, x_396);
if (x_409 == 0)
{
obj* x_414; obj* x_416; 
lean::dec(x_296);
x_414 = lean::cnstr_get(x_412, 0);
lean::inc(x_414);
x_416 = lean::cnstr_get(x_412, 1);
lean::inc(x_416);
lean::dec(x_412);
if (lean::obj_tag(x_414) == 0)
{
obj* x_419; obj* x_422; 
x_419 = lean::cnstr_get(x_414, 0);
lean::inc(x_419);
lean::dec(x_414);
if (lean::is_scalar(x_404)) {
 x_422 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_422 = x_404;
}
lean::cnstr_set(x_422, 0, x_419);
x_282 = x_422;
x_283 = x_416;
goto lbl_284;
}
else
{
obj* x_424; obj* x_427; obj* x_428; obj* x_430; 
lean::dec(x_414);
x_424 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__1;
lean::inc(x_3);
lean::inc(x_424);
x_427 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_424, x_3, x_416);
x_428 = lean::cnstr_get(x_427, 0);
lean::inc(x_428);
x_430 = lean::cnstr_get(x_427, 1);
lean::inc(x_430);
lean::dec(x_427);
if (lean::obj_tag(x_428) == 0)
{
obj* x_433; obj* x_436; 
x_433 = lean::cnstr_get(x_428, 0);
lean::inc(x_433);
lean::dec(x_428);
if (lean::is_scalar(x_404)) {
 x_436 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_436 = x_404;
}
lean::cnstr_set(x_436, 0, x_433);
x_282 = x_436;
x_283 = x_430;
goto lbl_284;
}
else
{
obj* x_439; 
lean::dec(x_428);
lean::dec(x_404);
x_439 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_439);
x_282 = x_439;
x_283 = x_430;
goto lbl_284;
}
}
}
else
{
obj* x_441; obj* x_443; 
x_441 = lean::cnstr_get(x_412, 0);
lean::inc(x_441);
x_443 = lean::cnstr_get(x_412, 1);
lean::inc(x_443);
lean::dec(x_412);
if (lean::obj_tag(x_441) == 0)
{
obj* x_447; obj* x_450; 
lean::dec(x_296);
x_447 = lean::cnstr_get(x_441, 0);
lean::inc(x_447);
lean::dec(x_441);
if (lean::is_scalar(x_404)) {
 x_450 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_450 = x_404;
}
lean::cnstr_set(x_450, 0, x_447);
x_282 = x_450;
x_283 = x_443;
goto lbl_284;
}
else
{
obj* x_452; obj* x_455; obj* x_456; obj* x_458; 
lean::dec(x_441);
x_452 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__1;
lean::inc(x_3);
lean::inc(x_452);
x_455 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_452, x_3, x_443);
x_456 = lean::cnstr_get(x_455, 0);
lean::inc(x_456);
x_458 = lean::cnstr_get(x_455, 1);
lean::inc(x_458);
lean::dec(x_455);
if (lean::obj_tag(x_456) == 0)
{
obj* x_463; obj* x_466; 
lean::dec(x_452);
lean::dec(x_296);
x_463 = lean::cnstr_get(x_456, 0);
lean::inc(x_463);
lean::dec(x_456);
if (lean::is_scalar(x_404)) {
 x_466 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_466 = x_404;
}
lean::cnstr_set(x_466, 0, x_463);
x_282 = x_466;
x_283 = x_458;
goto lbl_284;
}
else
{
obj* x_469; obj* x_470; obj* x_472; 
lean::dec(x_456);
lean::inc(x_3);
x_469 = _l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header(x_296, x_3, x_458);
x_470 = lean::cnstr_get(x_469, 0);
lean::inc(x_470);
x_472 = lean::cnstr_get(x_469, 1);
lean::inc(x_472);
lean::dec(x_469);
if (lean::obj_tag(x_470) == 0)
{
obj* x_476; obj* x_479; 
lean::dec(x_452);
x_476 = lean::cnstr_get(x_470, 0);
lean::inc(x_476);
lean::dec(x_470);
if (lean::is_scalar(x_404)) {
 x_479 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_479 = x_404;
}
lean::cnstr_set(x_479, 0, x_476);
x_282 = x_479;
x_283 = x_472;
goto lbl_284;
}
else
{
obj* x_484; obj* x_485; obj* x_487; 
lean::dec(x_404);
lean::dec(x_470);
lean::inc(x_3);
lean::inc(x_452);
x_484 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_452, x_3, x_472);
x_485 = lean::cnstr_get(x_484, 0);
lean::inc(x_485);
x_487 = lean::cnstr_get(x_484, 1);
lean::inc(x_487);
lean::dec(x_484);
x_282 = x_485;
x_283 = x_487;
goto lbl_284;
}
}
}
}
}
}
}
lbl_284:
{

if (lean::obj_tag(x_282) == 0)
{
obj* x_493; obj* x_496; obj* x_497; 
lean::dec(x_0);
lean::dec(x_3);
lean::dec(x_261);
x_493 = lean::cnstr_get(x_282, 0);
lean::inc(x_493);
lean::dec(x_282);
if (lean::is_scalar(x_281)) {
 x_496 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_496 = x_281;
}
lean::cnstr_set(x_496, 0, x_493);
if (lean::is_scalar(x_271)) {
 x_497 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_497 = x_271;
}
lean::cnstr_set(x_497, 0, x_496);
lean::cnstr_set(x_497, 1, x_283);
return x_497;
}
else
{
unsigned char x_501; obj* x_502; 
lean::dec(x_282);
lean::dec(x_281);
lean::dec(x_271);
x_501 = 0;
x_502 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1(x_0, x_261, x_501, x_3, x_283);
return x_502;
}
}
}
}
}
}
}
obj* _init__l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string(";\n");
return x_0;
}
}
obj* _init__l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("extern \"C\" ");
return x_0;
}
}
obj* _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
unsigned char x_5; obj* x_6; 
x_5 = lean::unbox(x_2);
x_6 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s24_emit__global__var__decls(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s24_emit__global__var__decls_s9___spec__1(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s24_emit__global__var__decls_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; unsigned char x_14; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_8);
x_14 = lean::cnstr_get_scalar<unsigned char>(x_13, sizeof(void*)*3);
if (x_14 == 0)
{
obj* x_16; 
lean::dec(x_13);
x_16 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s24_emit__global__var__decls_s9___spec__1(x_10, x_1, x_2);
return x_16;
}
else
{
obj* x_17; unsigned char x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_27; 
x_17 = lean::cnstr_get(x_13, 2);
lean::inc(x_17);
x_19 = lean::unbox(x_17);
lean::dec(x_17);
lean::inc(x_1);
x_22 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__type(x_19, x_1, x_2);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 x_27 = x_22;
}
if (lean::obj_tag(x_23) == 0)
{
obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_13);
lean::dec(x_10);
lean::dec(x_1);
x_31 = lean::cnstr_get(x_23, 0);
lean::inc(x_31);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_33 = x_23;
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_31);
if (lean::is_scalar(x_27)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_27;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_25);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_40; obj* x_41; obj* x_43; 
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_36 = x_23;
}
x_37 = _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_37);
x_40 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_37, x_1, x_25);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_49; obj* x_52; obj* x_53; 
lean::dec(x_13);
lean::dec(x_10);
lean::dec(x_1);
x_49 = lean::cnstr_get(x_41, 0);
lean::inc(x_49);
lean::dec(x_41);
if (lean::is_scalar(x_36)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_36;
}
lean::cnstr_set(x_52, 0, x_49);
if (lean::is_scalar(x_27)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_27;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_43);
return x_53;
}
else
{
obj* x_55; obj* x_59; obj* x_60; obj* x_62; 
lean::dec(x_41);
x_55 = lean::cnstr_get(x_13, 0);
lean::inc(x_55);
lean::dec(x_13);
lean::inc(x_1);
x_59 = _l_s4_lean_s2_ir_s3_cpp_s12_emit__global(x_55, x_1, x_43);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_60) == 0)
{
obj* x_67; obj* x_70; obj* x_71; 
lean::dec(x_10);
lean::dec(x_1);
x_67 = lean::cnstr_get(x_60, 0);
lean::inc(x_67);
lean::dec(x_60);
if (lean::is_scalar(x_36)) {
 x_70 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_70 = x_36;
}
lean::cnstr_set(x_70, 0, x_67);
if (lean::is_scalar(x_27)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_27;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_62);
return x_71;
}
else
{
obj* x_73; obj* x_76; obj* x_77; obj* x_79; 
lean::dec(x_60);
x_73 = _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__1;
lean::inc(x_1);
lean::inc(x_73);
x_76 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_73, x_1, x_62);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
if (lean::obj_tag(x_77) == 0)
{
obj* x_84; obj* x_87; obj* x_88; 
lean::dec(x_10);
lean::dec(x_1);
x_84 = lean::cnstr_get(x_77, 0);
lean::inc(x_84);
lean::dec(x_77);
if (lean::is_scalar(x_36)) {
 x_87 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_87 = x_36;
}
lean::cnstr_set(x_87, 0, x_84);
if (lean::is_scalar(x_27)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_27;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_79);
return x_88;
}
else
{
obj* x_92; 
lean::dec(x_77);
lean::dec(x_36);
lean::dec(x_27);
x_92 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s24_emit__global__var__decls_s9___spec__1(x_10, x_1, x_79);
return x_92;
}
}
}
}
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__1;
lean::inc(x_1);
lean::inc(x_3);
x_6 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_3, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_0);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_16 = x_7;
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
if (lean::is_scalar(x_11)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_11;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_9);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_26; 
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_19 = x_7;
}
x_20 = _l_s4_lean_s2_ir_s3_cpp_s18_initialize__prefix;
lean::inc(x_1);
lean::inc(x_20);
x_23 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_20, x_1, x_9);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_31; obj* x_34; obj* x_35; 
lean::dec(x_0);
lean::dec(x_1);
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
lean::dec(x_24);
if (lean::is_scalar(x_19)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_19;
}
lean::cnstr_set(x_34, 0, x_31);
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_26);
return x_35;
}
else
{
obj* x_37; obj* x_39; obj* x_42; obj* x_43; obj* x_45; 
lean::dec(x_24);
x_37 = lean::cnstr_get(x_1, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
lean::inc(x_1);
x_42 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_39, x_1, x_26);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_51; obj* x_54; obj* x_55; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_37);
x_51 = lean::cnstr_get(x_43, 0);
lean::inc(x_51);
lean::dec(x_43);
if (lean::is_scalar(x_19)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_19;
}
lean::cnstr_set(x_54, 0, x_51);
if (lean::is_scalar(x_11)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_11;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_45);
return x_55;
}
else
{
obj* x_57; obj* x_60; obj* x_61; obj* x_63; 
lean::dec(x_43);
x_57 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__2;
lean::inc(x_1);
lean::inc(x_57);
x_60 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_57, x_1, x_45);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_69; obj* x_72; obj* x_73; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_37);
x_69 = lean::cnstr_get(x_61, 0);
lean::inc(x_69);
lean::dec(x_61);
if (lean::is_scalar(x_19)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_19;
}
lean::cnstr_set(x_72, 0, x_69);
if (lean::is_scalar(x_11)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_11;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_63);
return x_73;
}
else
{
obj* x_75; obj* x_78; obj* x_79; obj* x_81; 
lean::dec(x_61);
x_75 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__3;
lean::inc(x_1);
lean::inc(x_75);
x_78 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_75, x_1, x_63);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
lean::dec(x_78);
if (lean::obj_tag(x_79) == 0)
{
obj* x_87; obj* x_90; obj* x_91; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_37);
x_87 = lean::cnstr_get(x_79, 0);
lean::inc(x_87);
lean::dec(x_79);
if (lean::is_scalar(x_19)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_19;
}
lean::cnstr_set(x_90, 0, x_87);
if (lean::is_scalar(x_11)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_11;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_81);
return x_91;
}
else
{
obj* x_93; obj* x_96; obj* x_97; obj* x_99; 
lean::dec(x_79);
x_93 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__4;
lean::inc(x_1);
lean::inc(x_93);
x_96 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_93, x_1, x_81);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
lean::dec(x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_105; obj* x_108; obj* x_109; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_37);
x_105 = lean::cnstr_get(x_97, 0);
lean::inc(x_105);
lean::dec(x_97);
if (lean::is_scalar(x_19)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_19;
}
lean::cnstr_set(x_108, 0, x_105);
if (lean::is_scalar(x_11)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_11;
}
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_99);
return x_109;
}
else
{
obj* x_111; obj* x_115; obj* x_116; obj* x_118; 
lean::dec(x_97);
x_111 = lean::cnstr_get(x_37, 1);
lean::inc(x_111);
lean::dec(x_37);
lean::inc(x_1);
x_115 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__1(x_111, x_1, x_99);
x_116 = lean::cnstr_get(x_115, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_115, 1);
lean::inc(x_118);
lean::dec(x_115);
if (lean::obj_tag(x_116) == 0)
{
obj* x_123; obj* x_126; obj* x_127; 
lean::dec(x_0);
lean::dec(x_1);
x_123 = lean::cnstr_get(x_116, 0);
lean::inc(x_123);
lean::dec(x_116);
if (lean::is_scalar(x_19)) {
 x_126 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_126 = x_19;
}
lean::cnstr_set(x_126, 0, x_123);
if (lean::is_scalar(x_11)) {
 x_127 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_127 = x_11;
}
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_118);
return x_127;
}
else
{
obj* x_130; obj* x_131; obj* x_133; 
lean::dec(x_116);
lean::inc(x_1);
x_130 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__2(x_0, x_1, x_118);
x_131 = lean::cnstr_get(x_130, 0);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_130, 1);
lean::inc(x_133);
lean::dec(x_130);
if (lean::obj_tag(x_131) == 0)
{
obj* x_137; obj* x_140; obj* x_141; 
lean::dec(x_1);
x_137 = lean::cnstr_get(x_131, 0);
lean::inc(x_137);
lean::dec(x_131);
if (lean::is_scalar(x_19)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_19;
}
lean::cnstr_set(x_140, 0, x_137);
if (lean::is_scalar(x_11)) {
 x_141 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_141 = x_11;
}
lean::cnstr_set(x_141, 0, x_140);
lean::cnstr_set(x_141, 1, x_133);
return x_141;
}
else
{
obj* x_145; obj* x_147; 
lean::dec(x_131);
lean::dec(x_11);
lean::dec(x_19);
x_145 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__1;
lean::inc(x_145);
x_147 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_145, x_1, x_133);
return x_147;
}
}
}
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("void ");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("() {\n");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string("if (_G_initialized) return;\n");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string("_G_initialized = true;\n");
return x_0;
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_21; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = _l_s4_lean_s2_ir_s3_cpp_s18_initialize__prefix;
lean::inc(x_1);
lean::inc(x_13);
x_16 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_13, x_1, x_2);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_21 = x_16;
}
if (lean::obj_tag(x_17) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_1);
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_27 = x_17;
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
if (lean::is_scalar(x_21)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_21;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_19);
return x_29;
}
else
{
obj* x_30; obj* x_32; obj* x_33; obj* x_35; 
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_30 = x_17;
}
lean::inc(x_1);
x_32 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_8, x_1, x_19);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
lean::dec(x_32);
if (lean::obj_tag(x_33) == 0)
{
obj* x_40; obj* x_43; obj* x_44; 
lean::dec(x_10);
lean::dec(x_1);
x_40 = lean::cnstr_get(x_33, 0);
lean::inc(x_40);
lean::dec(x_33);
if (lean::is_scalar(x_30)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_30;
}
lean::cnstr_set(x_43, 0, x_40);
if (lean::is_scalar(x_21)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_21;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_35);
return x_44;
}
else
{
obj* x_46; obj* x_49; obj* x_50; obj* x_52; 
lean::dec(x_33);
x_46 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__1_s11___closed__1;
lean::inc(x_1);
lean::inc(x_46);
x_49 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_46, x_1, x_35);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_57; obj* x_60; obj* x_61; 
lean::dec(x_10);
lean::dec(x_1);
x_57 = lean::cnstr_get(x_50, 0);
lean::inc(x_57);
lean::dec(x_50);
if (lean::is_scalar(x_30)) {
 x_60 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_60 = x_30;
}
lean::cnstr_set(x_60, 0, x_57);
if (lean::is_scalar(x_21)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_21;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_52);
return x_61;
}
else
{
obj* x_65; 
lean::dec(x_21);
lean::dec(x_30);
lean::dec(x_50);
x_65 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__1(x_10, x_1, x_52);
return x_65;
}
}
}
}
}
}
obj* _init__l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__1_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("();\n");
return x_0;
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; unsigned char x_14; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_8);
x_14 = lean::cnstr_get_scalar<unsigned char>(x_13, sizeof(void*)*3);
if (x_14 == 0)
{
obj* x_16; 
lean::dec(x_13);
x_16 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__2(x_10, x_1, x_2);
return x_16;
}
else
{
obj* x_17; obj* x_22; obj* x_23; obj* x_25; obj* x_27; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
lean::dec(x_13);
lean::inc(x_1);
lean::inc(x_17);
x_22 = _l_s4_lean_s2_ir_s3_cpp_s12_emit__global(x_17, x_1, x_2);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 x_27 = x_22;
}
if (lean::obj_tag(x_23) == 0)
{
obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_17);
lean::dec(x_10);
lean::dec(x_1);
x_31 = lean::cnstr_get(x_23, 0);
lean::inc(x_31);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_33 = x_23;
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_31);
if (lean::is_scalar(x_27)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_27;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_25);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_40; obj* x_41; obj* x_43; 
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_36 = x_23;
}
x_37 = _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1;
lean::inc(x_1);
lean::inc(x_37);
x_40 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_37, x_1, x_25);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_49; obj* x_52; obj* x_53; 
lean::dec(x_17);
lean::dec(x_10);
lean::dec(x_1);
x_49 = lean::cnstr_get(x_41, 0);
lean::inc(x_49);
lean::dec(x_41);
if (lean::is_scalar(x_36)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_36;
}
lean::cnstr_set(x_52, 0, x_49);
if (lean::is_scalar(x_27)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_27;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_43);
return x_53;
}
else
{
obj* x_56; obj* x_57; obj* x_59; 
lean::dec(x_41);
lean::inc(x_1);
x_56 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__fnid(x_17, x_1, x_43);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
if (lean::obj_tag(x_57) == 0)
{
obj* x_64; obj* x_67; obj* x_68; 
lean::dec(x_10);
lean::dec(x_1);
x_64 = lean::cnstr_get(x_57, 0);
lean::inc(x_64);
lean::dec(x_57);
if (lean::is_scalar(x_36)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_36;
}
lean::cnstr_set(x_67, 0, x_64);
if (lean::is_scalar(x_27)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_27;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_59);
return x_68;
}
else
{
obj* x_70; obj* x_73; obj* x_74; obj* x_76; 
lean::dec(x_57);
x_70 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__1_s11___closed__1;
lean::inc(x_1);
lean::inc(x_70);
x_73 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_70, x_1, x_59);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_81; obj* x_84; obj* x_85; 
lean::dec(x_10);
lean::dec(x_1);
x_81 = lean::cnstr_get(x_74, 0);
lean::inc(x_81);
lean::dec(x_74);
if (lean::is_scalar(x_36)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_36;
}
lean::cnstr_set(x_84, 0, x_81);
if (lean::is_scalar(x_27)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_27;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_76);
return x_85;
}
else
{
obj* x_89; 
lean::dec(x_27);
lean::dec(x_74);
lean::dec(x_36);
x_89 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__2(x_10, x_1, x_76);
return x_89;
}
}
}
}
}
}
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__1;
lean::inc(x_1);
lean::inc(x_3);
x_6 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_3, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_0);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_16 = x_7;
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
if (lean::is_scalar(x_11)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_11;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_9);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_26; 
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_19 = x_7;
}
x_20 = _l_s4_lean_s2_ir_s3_cpp_s16_finalize__prefix;
lean::inc(x_1);
lean::inc(x_20);
x_23 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_20, x_1, x_9);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_31; obj* x_34; obj* x_35; 
lean::dec(x_0);
lean::dec(x_1);
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
lean::dec(x_24);
if (lean::is_scalar(x_19)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_19;
}
lean::cnstr_set(x_34, 0, x_31);
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_26);
return x_35;
}
else
{
obj* x_37; obj* x_39; obj* x_42; obj* x_43; obj* x_45; 
lean::dec(x_24);
x_37 = lean::cnstr_get(x_1, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
lean::inc(x_1);
x_42 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_39, x_1, x_26);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_51; obj* x_54; obj* x_55; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_37);
x_51 = lean::cnstr_get(x_43, 0);
lean::inc(x_51);
lean::dec(x_43);
if (lean::is_scalar(x_19)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_19;
}
lean::cnstr_set(x_54, 0, x_51);
if (lean::is_scalar(x_11)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_11;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_45);
return x_55;
}
else
{
obj* x_57; obj* x_60; obj* x_61; obj* x_63; 
lean::dec(x_43);
x_57 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__2;
lean::inc(x_1);
lean::inc(x_57);
x_60 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_57, x_1, x_45);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_69; obj* x_72; obj* x_73; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_37);
x_69 = lean::cnstr_get(x_61, 0);
lean::inc(x_69);
lean::dec(x_61);
if (lean::is_scalar(x_19)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_19;
}
lean::cnstr_set(x_72, 0, x_69);
if (lean::is_scalar(x_11)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_11;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_63);
return x_73;
}
else
{
obj* x_75; obj* x_78; obj* x_79; obj* x_81; 
lean::dec(x_61);
x_75 = _l_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s11___closed__1;
lean::inc(x_1);
lean::inc(x_75);
x_78 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_75, x_1, x_63);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
lean::dec(x_78);
if (lean::obj_tag(x_79) == 0)
{
obj* x_87; obj* x_90; obj* x_91; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_37);
x_87 = lean::cnstr_get(x_79, 0);
lean::inc(x_87);
lean::dec(x_79);
if (lean::is_scalar(x_19)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_19;
}
lean::cnstr_set(x_90, 0, x_87);
if (lean::is_scalar(x_11)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_11;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_81);
return x_91;
}
else
{
obj* x_93; obj* x_96; obj* x_97; obj* x_99; 
lean::dec(x_79);
x_93 = _l_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s11___closed__2;
lean::inc(x_1);
lean::inc(x_93);
x_96 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_93, x_1, x_81);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
lean::dec(x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_105; obj* x_108; obj* x_109; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_37);
x_105 = lean::cnstr_get(x_97, 0);
lean::inc(x_105);
lean::dec(x_97);
if (lean::is_scalar(x_19)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_19;
}
lean::cnstr_set(x_108, 0, x_105);
if (lean::is_scalar(x_11)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_11;
}
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_99);
return x_109;
}
else
{
obj* x_111; obj* x_115; obj* x_116; obj* x_118; 
lean::dec(x_97);
x_111 = lean::cnstr_get(x_37, 1);
lean::inc(x_111);
lean::dec(x_37);
lean::inc(x_1);
x_115 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__1(x_111, x_1, x_99);
x_116 = lean::cnstr_get(x_115, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_115, 1);
lean::inc(x_118);
lean::dec(x_115);
if (lean::obj_tag(x_116) == 0)
{
obj* x_123; obj* x_126; obj* x_127; 
lean::dec(x_0);
lean::dec(x_1);
x_123 = lean::cnstr_get(x_116, 0);
lean::inc(x_123);
lean::dec(x_116);
if (lean::is_scalar(x_19)) {
 x_126 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_126 = x_19;
}
lean::cnstr_set(x_126, 0, x_123);
if (lean::is_scalar(x_11)) {
 x_127 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_127 = x_11;
}
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_118);
return x_127;
}
else
{
obj* x_130; obj* x_131; obj* x_133; 
lean::dec(x_116);
lean::inc(x_1);
x_130 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2(x_0, x_1, x_118);
x_131 = lean::cnstr_get(x_130, 0);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_130, 1);
lean::inc(x_133);
lean::dec(x_130);
if (lean::obj_tag(x_131) == 0)
{
obj* x_137; obj* x_140; obj* x_141; 
lean::dec(x_1);
x_137 = lean::cnstr_get(x_131, 0);
lean::inc(x_137);
lean::dec(x_131);
if (lean::is_scalar(x_19)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_19;
}
lean::cnstr_set(x_140, 0, x_137);
if (lean::is_scalar(x_11)) {
 x_141 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_141 = x_11;
}
lean::cnstr_set(x_141, 0, x_140);
lean::cnstr_set(x_141, 1, x_133);
return x_141;
}
else
{
obj* x_145; obj* x_147; 
lean::dec(x_131);
lean::dec(x_11);
lean::dec(x_19);
x_145 = _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__1;
lean::inc(x_145);
x_147 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_145, x_1, x_133);
return x_147;
}
}
}
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("if (_G_finalized) return;\n");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("_G_finalized = true;\n");
return x_0;
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_21; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = _l_s4_lean_s2_ir_s3_cpp_s16_finalize__prefix;
lean::inc(x_1);
lean::inc(x_13);
x_16 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_13, x_1, x_2);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_21 = x_16;
}
if (lean::obj_tag(x_17) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_8);
lean::dec(x_10);
lean::dec(x_1);
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_27 = x_17;
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
if (lean::is_scalar(x_21)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_21;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_19);
return x_29;
}
else
{
obj* x_30; obj* x_32; obj* x_33; obj* x_35; 
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 x_30 = x_17;
}
lean::inc(x_1);
x_32 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_8, x_1, x_19);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
lean::dec(x_32);
if (lean::obj_tag(x_33) == 0)
{
obj* x_40; obj* x_43; obj* x_44; 
lean::dec(x_10);
lean::dec(x_1);
x_40 = lean::cnstr_get(x_33, 0);
lean::inc(x_40);
lean::dec(x_33);
if (lean::is_scalar(x_30)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_30;
}
lean::cnstr_set(x_43, 0, x_40);
if (lean::is_scalar(x_21)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_21;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_35);
return x_44;
}
else
{
obj* x_46; obj* x_49; obj* x_50; obj* x_52; 
lean::dec(x_33);
x_46 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__1_s11___closed__1;
lean::inc(x_1);
lean::inc(x_46);
x_49 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_46, x_1, x_35);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_57; obj* x_60; obj* x_61; 
lean::dec(x_10);
lean::dec(x_1);
x_57 = lean::cnstr_get(x_50, 0);
lean::inc(x_57);
lean::dec(x_50);
if (lean::is_scalar(x_30)) {
 x_60 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_60 = x_30;
}
lean::cnstr_set(x_60, 0, x_57);
if (lean::is_scalar(x_21)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_21;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_52);
return x_61;
}
else
{
obj* x_65; 
lean::dec(x_21);
lean::dec(x_30);
lean::dec(x_50);
x_65 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__1(x_10, x_1, x_52);
return x_65;
}
}
}
}
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_16; unsigned char x_17; unsigned char x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_16 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_8);
x_19 = lean::cnstr_get_scalar<unsigned char>(x_16, sizeof(void*)*3);
if (x_19 == 0)
{

if (x_19 == 0)
{
obj* x_21; 
lean::dec(x_16);
x_21 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_21);
x_13 = x_21;
x_14 = x_2;
goto lbl_15;
}
else
{
unsigned char x_23; 
x_23 = 0;
x_17 = x_23;
goto lbl_18;
}
}
else
{
obj* x_24; unsigned char x_26; obj* x_28; obj* x_29; obj* x_30; 
x_24 = lean::cnstr_get(x_16, 2);
lean::inc(x_24);
x_26 = lean::unbox(x_24);
lean::dec(x_24);
x_28 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_26);
x_29 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__1;
x_30 = lean::nat_dec_eq(x_28, x_29);
lean::dec(x_28);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; 
lean::dec(x_16);
lean::dec(x_30);
x_34 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_34);
x_13 = x_34;
x_14 = x_2;
goto lbl_15;
}
else
{

lean::dec(x_30);
if (x_19 == 0)
{
obj* x_38; 
lean::dec(x_16);
x_38 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_38);
x_13 = x_38;
x_14 = x_2;
goto lbl_15;
}
else
{
unsigned char x_40; 
x_40 = 0;
x_17 = x_40;
goto lbl_18;
}
}
}
lbl_15:
{

if (lean::obj_tag(x_13) == 0)
{
obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_10);
lean::dec(x_1);
x_43 = lean::cnstr_get(x_13, 0);
lean::inc(x_43);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_45 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_45 = x_13;
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_43);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_14);
return x_47;
}
else
{
obj* x_49; 
lean::dec(x_13);
x_49 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2(x_10, x_1, x_14);
return x_49;
}
}
lbl_18:
{
obj* x_50; obj* x_53; obj* x_54; obj* x_56; 
x_50 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__1;
lean::inc(x_1);
lean::inc(x_50);
x_53 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_50, x_1, x_2);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
lean::dec(x_53);
if (lean::obj_tag(x_54) == 0)
{
obj* x_60; obj* x_62; obj* x_63; 
lean::dec(x_16);
x_60 = lean::cnstr_get(x_54, 0);
lean::inc(x_60);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_62 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_62 = x_54;
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_60);
x_13 = x_63;
x_14 = x_56;
goto lbl_15;
}
else
{
obj* x_64; obj* x_65; obj* x_70; obj* x_71; obj* x_73; 
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_64 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_64 = x_54;
}
x_65 = lean::cnstr_get(x_16, 0);
lean::inc(x_65);
lean::dec(x_16);
lean::inc(x_1);
lean::inc(x_65);
x_70 = _l_s4_lean_s2_ir_s3_cpp_s12_emit__global(x_65, x_1, x_56);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
lean::dec(x_70);
if (lean::obj_tag(x_71) == 0)
{
obj* x_77; obj* x_80; 
lean::dec(x_65);
x_77 = lean::cnstr_get(x_71, 0);
lean::inc(x_77);
lean::dec(x_71);
if (lean::is_scalar(x_64)) {
 x_80 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_80 = x_64;
}
lean::cnstr_set(x_80, 0, x_77);
x_13 = x_80;
x_14 = x_73;
goto lbl_15;
}
else
{
obj* x_82; obj* x_85; obj* x_86; obj* x_88; 
lean::dec(x_71);
x_82 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__2;
lean::inc(x_1);
lean::inc(x_82);
x_85 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_82, x_1, x_73);
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_85, 1);
lean::inc(x_88);
lean::dec(x_85);
if (lean::obj_tag(x_86) == 0)
{
obj* x_92; obj* x_95; 
lean::dec(x_65);
x_92 = lean::cnstr_get(x_86, 0);
lean::inc(x_92);
lean::dec(x_86);
if (lean::is_scalar(x_64)) {
 x_95 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_95 = x_64;
}
lean::cnstr_set(x_95, 0, x_92);
x_13 = x_95;
x_14 = x_88;
goto lbl_15;
}
else
{
obj* x_98; obj* x_99; obj* x_101; 
lean::dec(x_86);
lean::inc(x_1);
x_98 = _l_s4_lean_s2_ir_s3_cpp_s12_emit__global(x_65, x_1, x_88);
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_98, 1);
lean::inc(x_101);
lean::dec(x_98);
if (lean::obj_tag(x_99) == 0)
{
obj* x_104; obj* x_107; 
x_104 = lean::cnstr_get(x_99, 0);
lean::inc(x_104);
lean::dec(x_99);
if (lean::is_scalar(x_64)) {
 x_107 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_107 = x_64;
}
lean::cnstr_set(x_107, 0, x_104);
x_13 = x_107;
x_14 = x_101;
goto lbl_15;
}
else
{
obj* x_110; obj* x_113; obj* x_114; obj* x_116; 
lean::dec(x_64);
lean::dec(x_99);
x_110 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__3;
lean::inc(x_1);
lean::inc(x_110);
x_113 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_110, x_1, x_101);
x_114 = lean::cnstr_get(x_113, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_113, 1);
lean::inc(x_116);
lean::dec(x_113);
x_13 = x_114;
x_14 = x_116;
goto lbl_15;
}
}
}
}
}
}
}
}
obj* _init__l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("if (!is_scalar(");
return x_0;
}
}
obj* _init__l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string(")) lean::dec_ref(");
return x_0;
}
}
obj* _init__l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string(");\n");
return x_0;
}
}
obj* _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_2, 5);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_11; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_4);
x_9 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_1);
return x_11;
}
else
{
obj* x_12; obj* x_15; obj* x_18; 
x_12 = lean::cnstr_get(x_4, 0);
lean::inc(x_12);
lean::dec(x_4);
x_15 = lean::cnstr_get(x_2, 3);
lean::inc(x_15);
lean::inc(x_12);
x_18 = lean::apply_1(x_15, x_12);
if (lean::obj_tag(x_18) == 0)
{
obj* x_22; obj* x_23; unsigned char x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_18);
lean::dec(x_0);
lean::dec(x_2);
x_22 = _l_s4_lean_s2_ir_s2_id_s10_to__string_s6___main(x_12);
x_23 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = 0;
x_25 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__1;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_24);
x_28 = x_27;
x_29 = _l_s4_lean_s2_ir_s3_phi_s15_decorate__error_s6___rarg_s11___lambda__1_s11___closed__2;
lean::inc(x_29);
x_31 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_29);
lean::cnstr_set_scalar(x_31, sizeof(void*)*2, x_24);
x_32 = x_31;
x_33 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_1);
return x_34;
}
else
{
obj* x_35; obj* x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_46; unsigned char x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_58; 
x_35 = lean::cnstr_get(x_18, 0);
lean::inc(x_35);
lean::dec(x_18);
x_38 = _l_s4_lean_s2_ir_s4_decl_s6_header_s6___main(x_35);
x_39 = lean::cnstr_get(x_38, 1);
lean::inc(x_39);
x_41 = _l_s4_list_s6_length_s6___main_s6___rarg(x_39);
x_42 = lean::mk_nat_obj(0u);
x_43 = lean::nat_dec_eq(x_41, x_42);
lean::dec(x_42);
lean::dec(x_41);
x_46 = lean::cnstr_get(x_38, 2);
lean::inc(x_46);
lean::dec(x_38);
x_49 = lean::unbox(x_46);
lean::dec(x_46);
x_51 = _l_s4_lean_s2_ir_s7_type2id_s6___main(x_49);
x_52 = _l_s4_lean_s2_ir_s26_valid__assign__unop__types_s11___closed__4;
x_53 = lean::nat_dec_eq(x_51, x_52);
lean::dec(x_51);
x_55 = lean::cnstr_get(x_2, 0);
lean::inc(x_55);
lean::dec(x_2);
if (lean::obj_tag(x_53) == 0)
{
obj* x_61; 
lean::dec(x_53);
x_61 = lean::alloc_cnstr(0, 0, 0);
;
x_58 = x_61;
goto lbl_59;
}
else
{
obj* x_63; 
lean::dec(x_53);
x_63 = lean::alloc_cnstr(1, 0, 0);
;
x_58 = x_63;
goto lbl_59;
}
lbl_59:
{
obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_71; 
if (lean::obj_tag(x_43) == 0)
{
obj* x_76; obj* x_77; unsigned char x_78; obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_85; obj* x_86; obj* x_87; 
lean::dec(x_58);
lean::dec(x_43);
lean::inc(x_12);
x_76 = _l_s4_lean_s2_ir_s2_id_s10_to__string_s6___main(x_12);
x_77 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_77, 0, x_76);
x_78 = 0;
x_79 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__5;
lean::inc(x_79);
x_81 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set(x_81, 1, x_77);
lean::cnstr_set_scalar(x_81, sizeof(void*)*2, x_78);
x_82 = x_81;
x_83 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__6;
lean::inc(x_83);
x_85 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_85, 0, x_82);
lean::cnstr_set(x_85, 1, x_83);
lean::cnstr_set_scalar(x_85, sizeof(void*)*2, x_78);
x_86 = x_85;
x_87 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
x_70 = x_87;
x_71 = x_1;
goto lbl_72;
}
else
{

lean::dec(x_43);
if (lean::obj_tag(x_58) == 0)
{
obj* x_91; obj* x_92; unsigned char x_93; obj* x_94; obj* x_96; obj* x_97; obj* x_98; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_58);
lean::inc(x_12);
x_91 = _l_s4_lean_s2_ir_s2_id_s10_to__string_s6___main(x_12);
x_92 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_92, 0, x_91);
x_93 = 0;
x_94 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__5;
lean::inc(x_94);
x_96 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_96, 0, x_94);
lean::cnstr_set(x_96, 1, x_92);
lean::cnstr_set_scalar(x_96, sizeof(void*)*2, x_93);
x_97 = x_96;
x_98 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__7;
lean::inc(x_98);
x_100 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_100, 0, x_97);
lean::cnstr_set(x_100, 1, x_98);
lean::cnstr_set_scalar(x_100, sizeof(void*)*2, x_93);
x_101 = x_100;
x_102 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_102, 0, x_101);
x_70 = x_102;
x_71 = x_1;
goto lbl_72;
}
else
{
obj* x_104; 
lean::dec(x_58);
x_104 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_104);
x_70 = x_104;
x_71 = x_1;
goto lbl_72;
}
}
lbl_66:
{

if (lean::obj_tag(x_64) == 0)
{
obj* x_108; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_55);
lean::dec(x_0);
x_108 = lean::cnstr_get(x_64, 0);
lean::inc(x_108);
if (lean::is_shared(x_64)) {
 lean::dec(x_64);
 x_110 = lean::box(0);
} else {
 lean::cnstr_release(x_64, 0);
 x_110 = x_64;
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_108);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_65);
return x_112;
}
else
{
obj* x_113; obj* x_114; obj* x_117; obj* x_118; obj* x_120; obj* x_122; 
if (lean::is_shared(x_64)) {
 lean::dec(x_64);
 x_113 = lean::box(0);
} else {
 lean::cnstr_release(x_64, 0);
 x_113 = x_64;
}
x_114 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__1_s11___closed__1;
lean::inc(x_0);
lean::inc(x_114);
x_117 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_114, x_0, x_65);
x_118 = lean::cnstr_get(x_117, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_117, 1);
lean::inc(x_120);
if (lean::is_shared(x_117)) {
 lean::dec(x_117);
 x_122 = lean::box(0);
} else {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_122 = x_117;
}
if (lean::obj_tag(x_118) == 0)
{
obj* x_126; obj* x_129; obj* x_130; 
lean::dec(x_114);
lean::dec(x_55);
lean::dec(x_0);
x_126 = lean::cnstr_get(x_118, 0);
lean::inc(x_126);
lean::dec(x_118);
if (lean::is_scalar(x_113)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_113;
}
lean::cnstr_set(x_129, 0, x_126);
if (lean::is_scalar(x_122)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_122;
}
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_120);
return x_130;
}
else
{
obj* x_132; obj* x_135; obj* x_136; obj* x_138; 
lean::dec(x_118);
x_132 = _l_s4_lean_s2_ir_s3_cpp_s16_finalize__prefix;
lean::inc(x_0);
lean::inc(x_132);
x_135 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_132, x_0, x_120);
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_135, 1);
lean::inc(x_138);
lean::dec(x_135);
if (lean::obj_tag(x_136) == 0)
{
obj* x_144; obj* x_147; obj* x_148; 
lean::dec(x_114);
lean::dec(x_55);
lean::dec(x_0);
x_144 = lean::cnstr_get(x_136, 0);
lean::inc(x_144);
lean::dec(x_136);
if (lean::is_scalar(x_113)) {
 x_147 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_147 = x_113;
}
lean::cnstr_set(x_147, 0, x_144);
if (lean::is_scalar(x_122)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_122;
}
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_138);
return x_148;
}
else
{
obj* x_151; obj* x_152; obj* x_154; 
lean::dec(x_136);
lean::inc(x_0);
x_151 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_55, x_0, x_138);
x_152 = lean::cnstr_get(x_151, 0);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_151, 1);
lean::inc(x_154);
lean::dec(x_151);
if (lean::obj_tag(x_152) == 0)
{
obj* x_159; obj* x_162; obj* x_163; 
lean::dec(x_114);
lean::dec(x_0);
x_159 = lean::cnstr_get(x_152, 0);
lean::inc(x_159);
lean::dec(x_152);
if (lean::is_scalar(x_113)) {
 x_162 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_162 = x_113;
}
lean::cnstr_set(x_162, 0, x_159);
if (lean::is_scalar(x_122)) {
 x_163 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_163 = x_122;
}
lean::cnstr_set(x_163, 0, x_162);
lean::cnstr_set(x_163, 1, x_154);
return x_163;
}
else
{
obj* x_167; obj* x_168; obj* x_170; 
lean::dec(x_152);
lean::inc(x_0);
lean::inc(x_114);
x_167 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_114, x_0, x_154);
x_168 = lean::cnstr_get(x_167, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_167, 1);
lean::inc(x_170);
lean::dec(x_167);
if (lean::obj_tag(x_168) == 0)
{
obj* x_174; obj* x_177; obj* x_178; 
lean::dec(x_0);
x_174 = lean::cnstr_get(x_168, 0);
lean::inc(x_174);
lean::dec(x_168);
if (lean::is_scalar(x_113)) {
 x_177 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_177 = x_113;
}
lean::cnstr_set(x_177, 0, x_174);
if (lean::is_scalar(x_122)) {
 x_178 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_178 = x_122;
}
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set(x_178, 1, x_170);
return x_178;
}
else
{
obj* x_182; obj* x_184; 
lean::dec(x_168);
lean::dec(x_122);
lean::dec(x_113);
x_182 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__2;
lean::inc(x_182);
x_184 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_182, x_0, x_170);
return x_184;
}
}
}
}
}
}
lbl_69:
{

if (lean::obj_tag(x_67) == 0)
{
obj* x_186; obj* x_188; obj* x_189; 
lean::dec(x_12);
x_186 = lean::cnstr_get(x_67, 0);
lean::inc(x_186);
if (lean::is_shared(x_67)) {
 lean::dec(x_67);
 x_188 = lean::box(0);
} else {
 lean::cnstr_release(x_67, 0);
 x_188 = x_67;
}
if (lean::is_scalar(x_188)) {
 x_189 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_189 = x_188;
}
lean::cnstr_set(x_189, 0, x_186);
x_64 = x_189;
x_65 = x_68;
goto lbl_66;
}
else
{
obj* x_190; obj* x_193; obj* x_194; obj* x_196; 
if (lean::is_shared(x_67)) {
 lean::dec(x_67);
 x_190 = lean::box(0);
} else {
 lean::cnstr_release(x_67, 0);
 x_190 = x_67;
}
lean::inc(x_0);
lean::inc(x_55);
x_193 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_55, x_0, x_68);
x_194 = lean::cnstr_get(x_193, 0);
lean::inc(x_194);
x_196 = lean::cnstr_get(x_193, 1);
lean::inc(x_196);
lean::dec(x_193);
if (lean::obj_tag(x_194) == 0)
{
obj* x_200; obj* x_203; 
lean::dec(x_12);
x_200 = lean::cnstr_get(x_194, 0);
lean::inc(x_200);
lean::dec(x_194);
if (lean::is_scalar(x_190)) {
 x_203 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_203 = x_190;
}
lean::cnstr_set(x_203, 0, x_200);
x_64 = x_203;
x_65 = x_196;
goto lbl_66;
}
else
{
obj* x_205; obj* x_208; obj* x_209; obj* x_211; 
lean::dec(x_194);
x_205 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__1_s11___closed__1;
lean::inc(x_0);
lean::inc(x_205);
x_208 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_205, x_0, x_196);
x_209 = lean::cnstr_get(x_208, 0);
lean::inc(x_209);
x_211 = lean::cnstr_get(x_208, 1);
lean::inc(x_211);
lean::dec(x_208);
if (lean::obj_tag(x_209) == 0)
{
obj* x_215; obj* x_218; 
lean::dec(x_12);
x_215 = lean::cnstr_get(x_209, 0);
lean::inc(x_215);
lean::dec(x_209);
if (lean::is_scalar(x_190)) {
 x_218 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_218 = x_190;
}
lean::cnstr_set(x_218, 0, x_215);
x_64 = x_218;
x_65 = x_211;
goto lbl_66;
}
else
{
obj* x_220; obj* x_223; obj* x_224; obj* x_226; 
lean::dec(x_209);
x_220 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__3;
lean::inc(x_0);
lean::inc(x_220);
x_223 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_220, x_0, x_211);
x_224 = lean::cnstr_get(x_223, 0);
lean::inc(x_224);
x_226 = lean::cnstr_get(x_223, 1);
lean::inc(x_226);
lean::dec(x_223);
if (lean::obj_tag(x_224) == 0)
{
obj* x_230; obj* x_233; 
lean::dec(x_12);
x_230 = lean::cnstr_get(x_224, 0);
lean::inc(x_230);
lean::dec(x_224);
if (lean::is_scalar(x_190)) {
 x_233 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_233 = x_190;
}
lean::cnstr_set(x_233, 0, x_230);
x_64 = x_233;
x_65 = x_226;
goto lbl_66;
}
else
{
obj* x_237; obj* x_238; obj* x_240; 
lean::dec(x_224);
lean::dec(x_190);
lean::inc(x_0);
x_237 = _l_s4_lean_s2_ir_s3_cpp_s10_emit__fnid(x_12, x_0, x_226);
x_238 = lean::cnstr_get(x_237, 0);
lean::inc(x_238);
x_240 = lean::cnstr_get(x_237, 1);
lean::inc(x_240);
lean::dec(x_237);
x_64 = x_238;
x_65 = x_240;
goto lbl_66;
}
}
}
}
}
lbl_72:
{

if (lean::obj_tag(x_70) == 0)
{
obj* x_243; obj* x_245; obj* x_246; 
x_243 = lean::cnstr_get(x_70, 0);
lean::inc(x_243);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_245 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_245 = x_70;
}
if (lean::is_scalar(x_245)) {
 x_246 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_246 = x_245;
}
lean::cnstr_set(x_246, 0, x_243);
x_67 = x_246;
x_68 = x_71;
goto lbl_69;
}
else
{
obj* x_247; obj* x_248; obj* x_251; obj* x_252; obj* x_254; 
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_247 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_247 = x_70;
}
x_248 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__4;
lean::inc(x_0);
lean::inc(x_248);
x_251 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_248, x_0, x_71);
x_252 = lean::cnstr_get(x_251, 0);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_251, 1);
lean::inc(x_254);
lean::dec(x_251);
if (lean::obj_tag(x_252) == 0)
{
obj* x_257; obj* x_260; 
x_257 = lean::cnstr_get(x_252, 0);
lean::inc(x_257);
lean::dec(x_252);
if (lean::is_scalar(x_247)) {
 x_260 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_260 = x_247;
}
lean::cnstr_set(x_260, 0, x_257);
x_67 = x_260;
x_68 = x_254;
goto lbl_69;
}
else
{
obj* x_263; obj* x_266; obj* x_267; obj* x_269; 
lean::dec(x_252);
lean::dec(x_247);
x_263 = _l_s4_lean_s2_ir_s3_cpp_s18_initialize__prefix;
lean::inc(x_0);
lean::inc(x_263);
x_266 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_263, x_0, x_254);
x_267 = lean::cnstr_get(x_266, 0);
lean::inc(x_267);
x_269 = lean::cnstr_get(x_266, 1);
lean::inc(x_269);
lean::dec(x_266);
x_67 = x_267;
x_68 = x_269;
goto lbl_69;
}
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__1() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("unknown main function '");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("return r;\n}\n");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string("int r = ");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__4() {
{
obj* x_0; 
x_0 = lean::mk_string("int main() {\n");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__5() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("invalid main function '");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__6() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("', it must not take any arguments");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__7() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("', return type must be int32");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s4_lean_s2_ir_s12_extract__cpp(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_15; obj* x_16; obj* x_18; 
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
x_4 = _l_s4_lean_s2_ir_s3_cpp_s12_file__header(x_2);
x_5 = _l_s4_lean_s6_format_s2_be_s6___main_s11___closed__1;
x_6 = lean::string_append(x_4, x_5);
x_7 = _l_s4_lean_s2_ir_s11_mk__context;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_7);
lean::inc(x_9);
lean::inc(x_0);
x_15 = _l_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers(x_0, x_9, x_6);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
if (lean::obj_tag(x_16) == 0)
{
obj* x_21; obj* x_23; obj* x_24; 
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_23 = x_16;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
x_10 = x_24;
x_11 = x_18;
goto lbl_12;
}
else
{
obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_32; 
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_25 = x_16;
}
x_26 = _l_s4_lean_s2_ir_s12_extract__cpp_s11___closed__1;
lean::inc(x_9);
lean::inc(x_26);
x_29 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_26, x_9, x_18);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_35; obj* x_38; 
x_35 = lean::cnstr_get(x_30, 0);
lean::inc(x_35);
lean::dec(x_30);
if (lean::is_scalar(x_25)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_25;
}
lean::cnstr_set(x_38, 0, x_35);
x_10 = x_38;
x_11 = x_32;
goto lbl_12;
}
else
{
obj* x_41; obj* x_44; obj* x_45; obj* x_47; 
lean::dec(x_25);
lean::dec(x_30);
x_41 = _l_s4_lean_s2_ir_s12_extract__cpp_s11___closed__2;
lean::inc(x_9);
lean::inc(x_41);
x_44 = _l_s4_lean_s2_ir_s3_cpp_s4_emit_s4___at_s4_lean_s2_ir_s3_cpp_s10_emit__line_s9___spec__1(x_41, x_9, x_32);
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_44, 1);
lean::inc(x_47);
lean::dec(x_44);
x_10 = x_45;
x_11 = x_47;
goto lbl_12;
}
}
lbl_12:
{

if (lean::obj_tag(x_10) == 0)
{
obj* x_53; obj* x_55; obj* x_56; 
lean::dec(x_11);
lean::dec(x_9);
lean::dec(x_0);
x_53 = lean::cnstr_get(x_10, 0);
lean::inc(x_53);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_55 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_55 = x_10;
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
return x_56;
}
else
{
obj* x_57; obj* x_60; obj* x_61; obj* x_63; 
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_57 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_57 = x_10;
}
lean::inc(x_9);
lean::inc(x_0);
x_60 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s24_emit__global__var__decls_s9___spec__1(x_0, x_9, x_11);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_69; obj* x_72; 
lean::dec(x_63);
lean::dec(x_9);
lean::dec(x_0);
x_69 = lean::cnstr_get(x_61, 0);
lean::inc(x_69);
lean::dec(x_61);
if (lean::is_scalar(x_57)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_57;
}
lean::cnstr_set(x_72, 0, x_69);
return x_72;
}
else
{
obj* x_76; obj* x_77; obj* x_79; 
lean::dec(x_61);
lean::inc(x_9);
lean::inc(x_0);
x_76 = _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc(x_0, x_9, x_63);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
if (lean::obj_tag(x_77) == 0)
{
obj* x_85; obj* x_88; 
lean::dec(x_79);
lean::dec(x_9);
lean::dec(x_0);
x_85 = lean::cnstr_get(x_77, 0);
lean::inc(x_85);
lean::dec(x_77);
if (lean::is_scalar(x_57)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_57;
}
lean::cnstr_set(x_88, 0, x_85);
return x_88;
}
else
{
obj* x_92; obj* x_93; obj* x_95; 
lean::dec(x_77);
lean::inc(x_9);
lean::inc(x_0);
x_92 = _l_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc(x_0, x_9, x_79);
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_92, 1);
lean::inc(x_95);
lean::dec(x_92);
if (lean::obj_tag(x_93) == 0)
{
obj* x_101; obj* x_104; 
lean::dec(x_95);
lean::dec(x_9);
lean::dec(x_0);
x_101 = lean::cnstr_get(x_93, 0);
lean::inc(x_101);
lean::dec(x_93);
if (lean::is_scalar(x_57)) {
 x_104 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_104 = x_57;
}
lean::cnstr_set(x_104, 0, x_101);
return x_104;
}
else
{
obj* x_107; obj* x_108; obj* x_110; 
lean::dec(x_93);
lean::inc(x_9);
x_107 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s12_extract__cpp_s9___spec__1(x_0, x_9, x_95);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_107, 1);
lean::inc(x_110);
lean::dec(x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_115; obj* x_118; 
lean::dec(x_110);
lean::dec(x_9);
x_115 = lean::cnstr_get(x_108, 0);
lean::inc(x_115);
lean::dec(x_108);
if (lean::is_scalar(x_57)) {
 x_118 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_118 = x_57;
}
lean::cnstr_set(x_118, 0, x_115);
return x_118;
}
else
{
obj* x_120; obj* x_121; obj* x_123; 
lean::dec(x_108);
x_120 = _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc(x_9, x_110);
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_120, 1);
lean::inc(x_123);
lean::dec(x_120);
if (lean::obj_tag(x_121) == 0)
{
obj* x_127; obj* x_130; 
lean::dec(x_123);
x_127 = lean::cnstr_get(x_121, 0);
lean::inc(x_127);
lean::dec(x_121);
if (lean::is_scalar(x_57)) {
 x_130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_130 = x_57;
}
lean::cnstr_set(x_130, 0, x_127);
return x_130;
}
else
{
obj* x_132; 
lean::dec(x_121);
if (lean::is_scalar(x_57)) {
 x_132 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_132 = x_57;
}
lean::cnstr_set(x_132, 0, x_123);
return x_132;
}
}
}
}
}
}
}
}
}
obj* _init__l_s4_lean_s2_ir_s12_extract__cpp_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("static bool _G_initialized = false;\n");
return x_0;
}
}
obj* _init__l_s4_lean_s2_ir_s12_extract__cpp_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("static bool _G_finalized = false;\n");
return x_0;
}
}
obj* _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s12_extract__cpp_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_0);
lean::dec(x_1);
x_5 = _l_s4_lean_s2_ir_s11_match__type_s11___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
lean::inc(x_1);
x_14 = _l_s4_lean_s2_ir_s3_cpp_s9_emit__def(x_8, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 x_19 = x_14;
}
if (lean::obj_tag(x_15) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_10);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_15, 0);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_17);
return x_26;
}
else
{
obj* x_29; 
lean::dec(x_15);
lean::dec(x_19);
x_29 = _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s12_extract__cpp_s9___spec__1(x_10, x_1, x_17);
return x_29;
}
}
}
}
void _l_initialize__l_s4_init_s4_lean_s14_name__mangling();
void _l_initialize__l_s4_init_s4_lean_s6_config();
void _l_initialize__l_s4_init_s4_lean_s2_ir_s11_type__check();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s2_ir_s12_extract__cpp() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_lean_s14_name__mangling();
 _l_initialize__l_s4_init_s4_lean_s6_config();
 _l_initialize__l_s4_init_s4_lean_s2_ir_s11_type__check();
 _l_s4_lean_s2_ir_s3_cpp_s18_initialize__prefix = _init__l_s4_lean_s2_ir_s3_cpp_s18_initialize__prefix();
 _l_s4_lean_s2_ir_s3_cpp_s16_finalize__prefix = _init__l_s4_lean_s2_ir_s3_cpp_s16_finalize__prefix();
 _l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s12_file__header_s11___closed__4();
 _l_s4_lean_s2_ir_s3_cpp_s10_extract__m = _init__l_s4_lean_s2_ir_s3_cpp_s10_extract__m();
 _l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s10_monad__run = _init__l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s10_monad__run();
 _l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s13_monad__reader = _init__l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s13_monad__reader();
 _l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s12_monad__state = _init__l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s12_monad__state();
 _l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s13_monad__except = _init__l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s13_monad__except();
 _l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s5_monad = _init__l_s4_lean_s2_ir_s3_cpp_s10_extract__m_s5_monad();
 _l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__blockid_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s7_fid2cpp_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s7_fid2cpp_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s9_is__const_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s9_is__const_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s10_global2cpp_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s10_global2cpp_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__4();
 _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__5 = _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__5();
 _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__6 = _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__6();
 _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__7 = _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__7();
 _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__8 = _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__8();
 _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__9 = _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s11___closed__9();
 _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s12___closed__10 = _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s12___closed__10();
 _l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s12___closed__11 = _init__l_s4_lean_s2_ir_s3_cpp_s8_type2cpp_s6___main_s12___closed__11();
 _l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s14_emit__sep__aux_s6___main_s6___rarg_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__template__params_s11___closed__4();
 _l_s4_lean_s2_ir_s3_cpp_s9_emit__eos_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s9_emit__eos_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__cases_s6___main_s11___closed__4();
 _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__4();
 _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5 = _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__5();
 _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__6 = _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__6();
 _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__7 = _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__7();
 _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__8 = _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__8();
 _l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__9 = _init__l_s4_lean_s2_ir_s3_cpp_s10_emit__case_s6___main_s11___closed__9();
 _l_s4_lean_s2_ir_s3_cpp_s16_emit__terminator_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__terminator_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s16_emit__type__size_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__type__size_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__infix_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__4();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__5 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__5();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__6 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__6();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__7 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__7();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__8 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__8();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__9 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s11___closed__9();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__10 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__10();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__11 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__11();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__12 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__12();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__13 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__13();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__14 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__14();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__15 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__15();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__16 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__16();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__17 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__17();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__18 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__18();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__19 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__19();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__20 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__20();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__21 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__21();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__22 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__22();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__23 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__23();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__24 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__24();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__25 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__25();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__26 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__26();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__27 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__27();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__28 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__28();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__29 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__29();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__30 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__30();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__31 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__31();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__32 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__32();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__33 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__33();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__34 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__34();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__35 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__35();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__36 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__36();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__37 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__37();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__38 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__38();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__39 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__39();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__40 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__40();
 _l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__41 = _init__l_s4_lean_s2_ir_s3_cpp_s19_emit__assign__binop_s12___closed__41();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__4();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__5 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__5();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__6 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__6();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__7 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__7();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__8 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__8();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__9 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s11___closed__9();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__10 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__10();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__11 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__11();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__12 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__12();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__13 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__13();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__14 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__14();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__15 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__15();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__16 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__16();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__17 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__17();
 _l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__18 = _init__l_s4_lean_s2_ir_s3_cpp_s16_assign__unop2cpp_s6___main_s12___closed__18();
 _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__num__suffix_s6___main_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__4();
 _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__5 = _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__5();
 _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__6 = _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__6();
 _l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__7 = _init__l_s4_lean_s2_ir_s3_cpp_s17_emit__assign__lit_s11___closed__7();
 _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__4();
 _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__5 = _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__5();
 _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__6 = _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__6();
 _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__7 = _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__7();
 _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__8 = _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__8();
 _l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__9 = _init__l_s4_lean_s2_ir_s3_cpp_s8_unop2cpp_s6___main_s11___closed__9();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__4();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__5 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__5();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__6 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__6();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__7 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__7();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__8 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__8();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__9 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__apply_s11___closed__9();
 _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s11___closed__4();
 _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s9___spec__1_s11___closed__1 = _init__l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__closure_s9___spec__1_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__4();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__5 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__5();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__6 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__6();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__7 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__7();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__8 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__8();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__9 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__instr_s11___closed__9();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__block_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__block_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s11_emit__block_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s11_emit__block_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s12_emit__header_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s12_emit__header_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s21_emit__uncurry__header_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s11___closed__3();
 _l_s3_nat_s6_repeat_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__3_s11___closed__1 = _init__l_s3_nat_s6_repeat_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s13_emit__uncurry_s9___spec__3_s11___closed__1();
 _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__1 = _init__l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__1();
 _l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__2 = _init__l_s6_rbnode_s5_mfold_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s19_emit__used__headers_s9___spec__1_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s11___closed__4();
 _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__1_s11___closed__1 = _init__l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s22_emit__initialize__proc_s9___spec__1_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s11___closed__2();
 _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__1 = _init__l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__1();
 _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__2 = _init__l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__2();
 _l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__3 = _init__l_s4_list_s8_mmap_x27_s6___main_s4___at_s4_lean_s2_ir_s3_cpp_s20_emit__finalize__proc_s9___spec__2_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__1 = _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__1();
 _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__2 = _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__2();
 _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__3 = _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__3();
 _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__4 = _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__4();
 _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__5 = _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__5();
 _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__6 = _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__6();
 _l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__7 = _init__l_s4_lean_s2_ir_s3_cpp_s16_emit__main__proc_s11___closed__7();
 _l_s4_lean_s2_ir_s12_extract__cpp_s11___closed__1 = _init__l_s4_lean_s2_ir_s12_extract__cpp_s11___closed__1();
 _l_s4_lean_s2_ir_s12_extract__cpp_s11___closed__2 = _init__l_s4_lean_s2_ir_s12_extract__cpp_s11___closed__2();
}
