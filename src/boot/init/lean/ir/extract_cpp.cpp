// Lean compiler output
// Module: init.lean.ir.extract_cpp
// Imports: init.lean.name_mangling init.lean.config init.lean.ir.type_check
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_lean_ir_cpp_emit__assign__binop___closed__15;
obj* l_lean_ir_cpp_emit__apply(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__sep__aux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__unop(uint8, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__apply___closed__8;
obj* l_lean_ir_cpp_emit__assign__unop___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__5;
obj* l_lean_ir_cpp_emit__uncurry__header___closed__2;
obj* l_lean_ir_cpp_emit__main__proc___closed__1;
obj* l_except__t_monad__run___rarg(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1(obj*, obj*);
obj* l_lean_ir_cpp_emit(obj*);
obj* l_lean_ir_cpp_emit__uncurry__header(obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___boxed(obj*, obj*);
obj* l_lean_ir_cpp_emit__cases___main(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(uint16, obj*, obj*);
obj* l_lean_ir_cpp_emit__arg__list___lambda__1(obj*, obj*, obj*);
extern obj* l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
obj* l_lean_ir_cpp_emit__num__suffix___main___closed__1;
obj* l_lean_ir_cpp_emit__block(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__7;
obj* l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___closed__1;
extern obj* l_lean_ir_valid__assign__unop__types___closed__4;
obj* l_lean_ir_cpp_emit__infix(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__case___main___closed__6;
obj* l_lean_ir_cpp_emit__sep___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__case___main___closed__9;
obj* l_lean_ir_terminator_to__format___main(obj*);
obj* l_lean_ir_cpp_extract__m_monad;
obj* l_lean_ir_cpp_emit__template__param(uint8, obj*, obj*);
obj* l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
obj* l_lean_ir_cpp_file__header___closed__4;
obj* l_lean_ir_cpp_emit__main__proc___closed__4;
obj* l_rbnode_balance2__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__4(obj*, obj*);
obj* l_lean_ir_cpp_emit__infix___closed__1;
obj* l_rbnode_insert___at_lean_ir_cpp_collect__used___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__14;
obj* l_lean_ir_cpp_emit__assign__binop___closed__4;
obj* l_id_run(obj*);
obj* l_lean_ir_cpp_emit__finalize__proc___closed__2;
obj* l_lean_ir_cpp_emit__template__params___closed__2;
obj* l_lean_ir_cpp_emit__assign__binop___closed__38;
obj* l_lean_ir_instr_to__format___main(obj*);
obj* l_lean_ir_cpp_emit__instr___closed__1;
obj* l_lean_ir_cpp_unop2cpp___main___closed__9;
extern obj* l_lean_ir_match__type___closed__5;
obj* l_lean_ir_cpp_emit__case___main___closed__7;
obj* l_lean_ir_cpp_emit__eos___closed__1;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__8;
obj* l_lean_ir_cpp_initialize__prefix;
obj* l_lean_ir_cpp_emit__assign__binop___closed__37;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__17;
obj* l_lean_ir_cpp_emit__assign__binop___closed__3;
obj* l_lean_ir_cpp_emit__def__core(obj*, obj*, obj*);
obj* l_state__t_monad__run___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__6;
obj* l_lean_ir_extract__cpp___closed__1;
obj* l_lean_ir_cpp_emit__apply___closed__1;
obj* l_lean_ir_cpp_assign__unop2cpp___main(uint8, uint8);
obj* l_id_monad___lambda__1(obj*, obj*, obj*, obj*);
uint8 l_list_empty___main___rarg(obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__20;
obj* l_lean_ir_cpp_emit__arith___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__lit___closed__4;
obj* l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___closed__1;
obj* l_lean_ir_cpp_emit__case___main(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__main__proc___closed__6;
obj* l_lean_ir_cpp_unop2cpp___boxed(obj*);
obj* l_lean_ir_cpp_type2cpp___boxed(obj*);
obj* l_lean_ir_cpp_assign__unop2cpp(uint8, uint8);
obj* l_lean_ir_cpp_emit__assign__binop___closed__18;
obj* l_lean_ir_cpp_is__const(obj*, obj*, obj*);
obj* l_lean_ir_cpp_type2cpp___main___closed__10;
obj* l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__33;
obj* l_lean_ir_cpp_emit__unop___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__cases___main___closed__2;
obj* l_lean_ir_cpp_emit__num__suffix(uint8, obj*, obj*);
obj* l_lean_ir_cpp_unop2cpp___main(uint8);
obj* l_lean_ir_cpp_extract__m;
obj* l_lean_ir_cpp_emit__finalize__proc___closed__1;
obj* l_string_quote(obj*);
obj* l_int_repr___main(obj*);
obj* l_lean_ir_cpp_fid2cpp___closed__1;
obj* l_lean_ir_cpp_fid2cpp(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__instr___closed__9;
obj* l_lean_ir_cpp_emit__num__suffix___main(uint8, obj*, obj*);
obj* l_lean_ir_type2id___main(uint8);
obj* l_lean_ir_cpp_emit__type__size___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__lit___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__uncurry___closed__2;
obj* l_lean_ir_cpp_unop2cpp___main___boxed(obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__24;
obj* l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__5(obj*, obj*);
obj* l_lean_ir_cpp_emit__case___main___closed__3;
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
obj* l_lean_ir_cpp_emit__sep__aux___main(obj*);
obj* l_lean_ir_cpp_emit__assign__binop___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__initialize__proc___closed__1;
obj* l_lean_ir_cpp_emit__terminator(obj*, obj*, obj*);
obj* l_state__t_monad__state___rarg(obj*);
obj* l_lean_ir_cpp_emit__instr___closed__5;
obj* l_lean_ir_cpp_emit__num__suffix___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__instr___closed__3;
extern obj* l_lean_ir_mk__fnid__set;
obj* l_lean_ir_cpp_emit__template__params(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__template__param___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__type__size___closed__1;
obj* l_lean_ir_cpp_emit__main__proc___closed__2;
obj* l_except__t_monad__except___rarg(obj*);
obj* l_lean_ir_cpp_emit__uncurry___closed__1;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__18;
obj* l_rbnode_mk__insert__result___main___rarg(uint8, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__27;
obj* l_lean_ir_cpp_emit__assign__binop___closed__1;
obj* l_lean_ir_cpp_type2cpp___main___closed__3;
obj* l_lean_ir_cpp_decl__locals(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__case(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__closure___closed__2;
obj* l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(obj*);
obj* l_lean_ir_cpp_type2cpp___main___closed__7;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__9;
extern obj* l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
obj* l_id_bind(obj*, obj*);
obj* l_lean_ir_decl_header___main(obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__header___closed__1;
obj* l_lean_ir_cpp_emit__instr___closed__7;
obj* l_lean_ir_cpp_emit__assign__binop___closed__29;
obj* l_list_foldr___main___at_lean_ir_cpp_need__uncurry___spec__1(obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__13;
obj* l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_ir_id_to__string___main(obj*);
extern obj* l_uint32__sz;
obj* l_lean_ir_cpp_emit__finalize__proc(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(usize, obj*, obj*);
obj* l_lean_ir_cpp_emit__cases___main___closed__1;
obj* l_lean_ir_cpp_unop2cpp___main___closed__6;
obj* l_lean_ir_extract__cpp(obj*, obj*);
obj* l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2(obj*);
obj* l_lean_ir_cpp_emit__assign__lit___closed__2;
obj* l_lean_ir_cpp_emit__global__var__decls(obj*, obj*, obj*);
obj* l_lean_ir_cpp_unop2cpp___main___closed__8;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__2;
obj* l___private_694751983__name_mangle__aux___main(obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__9;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__15;
extern obj* l_list_repr__aux___main___rarg___closed__1;
obj* l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__cases(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__13;
obj* l_lean_ir_cpp_emit__main__proc___closed__7;
obj* l_lean_ir_cpp_emit__cases___main___closed__4;
obj* l_except__t_lift___rarg(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__used__headers(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__initialize__proc___closed__4;
obj* l_lean_ir_cpp_emit__blockid___closed__1;
obj* l_lean_ir_cpp_type2cpp___main(uint8);
obj* l_lean_ir_cpp_emit__arg__list(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__41;
obj* l_lean_ir_cpp_emit__assign__binop___closed__12;
obj* l_lean_ir_cpp_emit__main__proc(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_cpp_collect__used___spec__1(obj*, obj*, obj*);
extern obj* l_list_repr___main___rarg___closed__3;
extern obj* l_lean_format_be___main___closed__1;
obj* l_lean_ir_cpp_emit__uncurry__header___closed__1;
obj* l_lean_ir_cpp_emit__assign__binop___closed__23;
obj* l_lean_ir_cpp_extract__m_monad__except;
obj* l_id(obj*);
obj* l_lean_ir_cpp_emit__apply___closed__6;
obj* l_lean_ir_cpp_emit__sep(obj*);
obj* l_lean_ir_infer__types(obj*, obj*);
extern obj* l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_cpp_emit__closure___closed__3;
obj* l_lean_ir_cpp_emit__closure___closed__4;
obj* l_lean_ir_cpp_unop2cpp___main___closed__4;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__10;
obj* l_lean_ir_cpp_emit__sep__aux(obj*);
obj* l_lean_ir_cpp_emit__case___main___closed__8;
obj* l_lean_ir_cpp_type2cpp___main___closed__2;
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__block___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__fnid(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__cases___main___closed__3;
obj* l_lean_ir_cpp_comma(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__4;
obj* l_lean_ir_cpp_emit__apply___closed__7;
obj* l_lean_ir_cpp_emit__assign__binop(obj*, uint8, uint8, obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__3;
obj* l_lean_ir_cpp_emit__block___closed__2;
obj* l_lean_ir_cpp_finalize__prefix;
obj* l_lean_ir_extract__cpp___closed__2;
obj* l_lean_ir_cpp_emit__uncurry(obj*, obj*, obj*);
obj* l_lean_ir_cpp_type2cpp(uint8);
obj* l_lean_ir_cpp_emit__case___main___closed__4;
obj* l_lean_ir_cpp_emit__assign__binop___closed__21;
obj* l_lean_ir_cpp_file__header___closed__1;
obj* l_reader__t_read___rarg(obj*, obj*);
obj* l_lean_ir_cpp_emit__type___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__initialize__proc___closed__2;
obj* l_lean_ir_cpp_emit__case___main___closed__2;
obj* l_monad__state__trans___rarg(obj*, obj*);
obj* l_lean_ir_cpp_emit__var(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__31;
obj* l_lean_ir_cpp_emit__assign__unop(obj*, uint8, uint8, obj*, obj*, obj*);
obj* l_lean_ir_cpp_paren(obj*);
obj* l_lean_ir_cpp_type2cpp___main___closed__9;
obj* l_except__t_monad___rarg(obj*);
obj* l_lean_ir_cpp_emit__uncurry___closed__3;
obj* l_lean_ir_cpp_emit__logical__arith(uint8, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__11;
obj* l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(obj*, obj*);
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__2___boxed(obj*, obj*, obj*);
obj* l_id_monad___lambda__3(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__12;
obj* l_lean_ir_cpp_emit__case___main___closed__1;
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_lean_ir_cpp_extract__m_monad__reader;
obj* l_lean_ir_cpp_emit__assign__binop___closed__28;
obj* l_lean_ir_cpp_emit__assign__binop___closed__10;
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3___boxed(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__initialize__proc___closed__3;
obj* l_lean_ir_cpp_emit__case___main___closed__5;
obj* l_lean_ir_cpp_paren___rarg(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__header(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__34;
obj* l_lean_ir_cpp_emit__assign__binop___closed__26;
obj* l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1___closed__1;
obj* l_lean_ir_cpp_emit__num__suffix___main___closed__2;
obj* l_state__t_monad___rarg(obj*);
obj* l_lean_ir_cpp_emit__blockid(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__template__params___closed__4;
obj* l_lean_ir_cpp_emit__main__proc___closed__3;
obj* l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__initialize__proc(obj*, obj*, obj*);
obj* l_lean_ir_cpp_type2cpp___main___closed__5;
extern obj* l_int_repr___main___closed__1;
obj* l_lean_ir_cpp_type2cpp___main___closed__8;
obj* l_lean_ir_cpp_emit__terminator___closed__1;
obj* l_lean_ir_cpp_file__header___closed__3;
obj* l_lean_ir_cpp_emit__logical__arith___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_extract__m_monad__state;
obj* l_lean_ir_cpp_emit__assign__binop___closed__17;
obj* l_lean_ir_cpp_type2cpp___main___closed__4;
obj* l_lean_ir_cpp_emit__instr___closed__6;
obj* l_lean_ir_cpp_emit__block___closed__1;
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__template__params___closed__1;
obj* l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__6(obj*, obj*);
obj* l_lean_ir_cpp_unop2cpp___main___closed__2;
obj* l_lean_ir_cpp_unop2cpp___main___closed__5;
extern obj* l_prod_has__repr___rarg___closed__1;
obj* l_lean_ir_cpp_emit__sep__aux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_decl__local___boxed(obj*, obj*, obj*, obj*);
obj* l_reader__t_lift(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__eos(obj*, obj*);
obj* l_lean_ir_cpp_emit__instr___closed__8;
extern obj* l___private_2909413099__string_mangle__aux___main___closed__2;
obj* l_lean_ir_cpp_emit__apply___closed__4;
obj* l_lean_ir_cpp_emit__global(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__lit___closed__3;
obj* l_lean_ir_cpp_need__uncurry(obj*);
obj* l_lean_ir_cpp_extract__m_monad__run;
obj* l_lean_ir_cpp_is__const___closed__1;
obj* l_lean_ir_cpp_emit__line(obj*, obj*);
obj* l_lean_ir_cpp_unop2cpp___main___closed__1;
obj* l_lean_ir_cpp_emit__assign__binop___closed__40;
obj* l_lean_ir_cpp_emit__var__list(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__2(uint16, obj*, obj*);
obj* l_lean_ir_cpp_emit__instr___closed__2;
obj* l_lean_ir_cpp_emit__closure(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_type2cpp___main___closed__6;
obj* l_lean_ir_cpp_emit__arith(uint8, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__7;
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__2;
obj* l_lean_ir_cpp_emit__type__size(uint8, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__35;
obj* l_list_length__aux___main___rarg(obj*, obj*);
obj* l_lean_ir_cpp_emit__type(uint8, obj*, obj*);
obj* l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2___rarg(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__16;
uint8 l_rbnode_get__color___main___rarg(obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__1;
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__def__core___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__8;
obj* l_lean_ir_cpp_emit__instr(obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_lean_ir_cpp_decl__locals___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__lit___closed__5;
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__16;
obj* l_lean_ir_cpp_emit__apply___closed__9;
obj* l_lean_ir_cpp_emit__apply___closed__5;
obj* l_lean_ir_cpp_global2cpp___closed__1;
obj* l_lean_ir_cpp_emit__assign__binop___closed__25;
obj* l_lean_ir_cpp_type2cpp___main___closed__11;
obj* l_lean_ir_cpp_emit__template__params___closed__3;
obj* l_lean_ir_cpp_emit__assign__binop___closed__5;
obj* l_lean_ir_cpp_decl__local(obj*, uint8, obj*, obj*);
obj* l_lean_ir_cpp_emit__apply___closed__2;
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_ir_cpp_type2cpp___main___boxed(obj*);
obj* l_lean_ir_cpp_collect__used(obj*);
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__11;
obj* l_list_mmap_x_27___main___at_lean_ir_extract__cpp___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__lit___closed__6;
extern obj* l_lean_ir_valid__assign__unop__types___closed__1;
obj* l_nat_repr(obj*);
obj* l_lean_ir_cpp_emit__main__proc___closed__5;
obj* l_lean_ir_cpp_global2cpp(obj*, obj*, obj*);
obj* l_lean_ir_cpp_unop2cpp___main___closed__3;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__14;
obj* l_lean_ir_cpp_emit__assign__lit___closed__7;
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__global__var__decls___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__lit(obj*, uint8, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__op__x(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_file__header___closed__2;
obj* l_lean_ir_cpp_emit__closure___closed__1;
obj* l_lean_ir_cpp_assign__unop2cpp___main___boxed(obj*, obj*);
obj* l_rbnode_balance1__node___main___rarg(obj*, obj*, obj*, obj*);
obj* l_id_monad___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__num__suffix___main___boxed(obj*, obj*, obj*);
extern obj* l_lean_ir_mk__context;
extern obj* l_option_has__repr___rarg___closed__3;
obj* l_lean_ir_cpp_emit__assign__binop___closed__39;
obj* l_lean_ir_cpp_emit__big__binop(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_monad__run___rarg(obj*, obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2;
obj* l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__x__op__y(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__19;
obj* l_lean_ir_cpp_emit__assign__binop___closed__30;
obj* l_lean_ir_cpp_type2cpp___main___closed__1;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__3;
obj* l_lean_ir_cpp_emit__assign__binop___closed__36;
obj* l_lean_ir_cpp_unop2cpp(uint8);
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__num__suffix___main___closed__3;
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__lit___closed__1;
obj* l_lean_ir_cpp_file__header(obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__2;
obj* l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
obj* l_lean_ir_cpp_emit__instr___closed__4;
obj* l_lean_ir_cpp_emit__apply___closed__3;
obj* l_lean_ir_cpp_emit__assign__binop___closed__32;
obj* l_lean_ir_cpp_emit__assign__binop___closed__22;
extern obj* l_lean_closure__max__args;
obj* l_lean_ir_cpp_emit__assign__binop___closed__6;
extern obj* l_lean_ir_is__arith__ty___closed__1;
obj* l_lean_ir_cpp_unop2cpp___main___closed__7;
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__1;
obj* l_lean_ir_cpp_emit__def(obj*, obj*, obj*);
extern obj* l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
obj* _init_l_lean_ir_cpp_initialize__prefix() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_lean_initialize_");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_finalize__prefix() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_lean_finalize_");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_file__header___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("#include <");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_file__header___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("/object.h>\n");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_file__header___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("/apply.h>\n");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_file__header___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("typedef lean::object obj;");
return x_0;
}
}
obj* l_lean_ir_cpp_file__header(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_1 = l_lean_ir_cpp_file__header___closed__1;
lean::inc(x_1);
x_3 = lean::string_append(x_1, x_0);
x_4 = l_lean_ir_cpp_file__header___closed__2;
x_5 = lean::string_append(x_3, x_4);
x_6 = lean::string_append(x_5, x_1);
x_7 = lean::string_append(x_6, x_0);
lean::dec(x_0);
x_9 = l_lean_ir_cpp_file__header___closed__3;
x_10 = lean::string_append(x_7, x_9);
x_11 = l_lean_ir_cpp_file__header___closed__4;
x_12 = lean::string_append(x_10, x_11);
return x_12;
}
}
obj* _init_l_lean_ir_cpp_extract__m_monad__run() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_id_run), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__run___rarg), 5, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad__run___rarg), 3, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad__run___rarg), 4, 1);
lean::closure_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init_l_lean_ir_cpp_extract__m_monad__reader() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_state__t_monad___rarg(x_9);
x_11 = l_except__t_monad___rarg(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_read___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
return x_12;
}
}
obj* _init_l_lean_ir_cpp_extract__m_monad__state() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
x_11 = l_state__t_monad___rarg(x_9);
lean::inc(x_11);
x_13 = l_except__t_monad___rarg(x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift), 4, 3);
lean::closure_set(x_14, 0, lean::box(0));
lean::closure_set(x_14, 1, lean::box(0));
lean::closure_set(x_14, 2, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_lift___rarg), 3, 1);
lean::closure_set(x_15, 0, x_11);
x_16 = l_state__t_monad__state___rarg(x_9);
x_17 = l_monad__state__trans___rarg(x_15, x_16);
x_18 = l_monad__state__trans___rarg(x_14, x_17);
return x_18;
}
}
obj* _init_l_lean_ir_cpp_extract__m_monad__except() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_state__t_monad___rarg(x_9);
x_11 = l_except__t_monad__except___rarg(x_10);
x_12 = l_reader__t_monad__except___rarg(x_11);
return x_12;
}
}
obj* _init_l_lean_ir_cpp_extract__m_monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_state__t_monad___rarg(x_9);
x_11 = l_except__t_monad___rarg(x_10);
x_12 = l_reader__t_monad___rarg(x_11);
return x_12;
}
}
obj* _init_l_lean_ir_cpp_extract__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_ir_cpp_emit___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::dec(x_2);
x_5 = lean::apply_1(x_0, x_1);
x_6 = lean::string_append(x_3, x_5);
lean::dec(x_5);
x_8 = l_lean_ir_match__type___closed__5;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
}
obj* l_lean_ir_cpp_emit(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; 
lean::dec(x_1);
x_4 = lean::string_append(x_2, x_0);
lean::dec(x_0);
x_6 = l_lean_ir_match__type___closed__5;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
}
obj* l_lean_ir_cpp_emit__line(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = l_lean_format_be___main___closed__1;
lean::inc(x_2);
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_2, x_0, x_1);
return x_4;
}
}
obj* l_lean_ir_cpp_paren___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_3);
x_6 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
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
lean::dec(x_0);
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
 lean::cnstr_set_tag(x_19, 0);
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
x_36 = l_option_has__repr___rarg___closed__3;
lean::inc(x_36);
x_38 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_36, x_1, x_24);
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
 lean::cnstr_set_tag(x_19, 0);
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
obj* l_lean_ir_cpp_paren(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_paren___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_ir_cpp_comma(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
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
x_19 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_19);
x_22 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_2, x_8);
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
 lean::cnstr_set_tag(x_18, 0);
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
obj* l_lean_ir_cpp_emit__var(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = l___private_2909413099__string_mangle__aux___main___closed__2;
lean::inc(x_3);
x_5 = l___private_694751983__name_mangle__aux___main(x_3, x_0);
x_6 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_5, x_1, x_2);
return x_6;
}
}
obj* _init_l_lean_ir_cpp_emit__blockid___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_lbl");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__blockid(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = l_lean_ir_cpp_emit__blockid___closed__1;
lean::inc(x_3);
x_5 = l___private_694751983__name_mangle__aux___main(x_3, x_0);
x_6 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_5, x_1, x_2);
return x_6;
}
}
obj* _init_l_lean_ir_cpp_fid2cpp___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_l");
return x_0;
}
}
obj* l_lean_ir_cpp_fid2cpp(obj* x_0, obj* x_1, obj* x_2) {
_start:
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
x_12 = l_lean_ir_cpp_fid2cpp___closed__1;
lean::inc(x_12);
x_14 = l___private_694751983__name_mangle__aux___main(x_12, x_0);
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
obj* l_lean_ir_cpp_emit__fnid(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
lean::inc(x_1);
x_4 = l_lean_ir_cpp_fid2cpp(x_0, x_1, x_2);
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
x_20 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_17, x_1, x_7);
return x_20;
}
}
}
obj* _init_l_lean_ir_cpp_is__const___closed__1() {
_start:
{
uint8 x_0; obj* x_1; obj* x_2; 
x_0 = 0;
x_1 = lean::box(x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_ir_cpp_is__const(obj* x_0, obj* x_1, obj* x_2) {
_start:
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
x_11 = l_lean_ir_cpp_is__const___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set(x_13, 1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_17; uint8 x_18; obj* x_20; obj* x_21; obj* x_22; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
x_17 = l_lean_ir_decl_header___main(x_14);
x_18 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*3);
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
obj* _init_l_lean_ir_cpp_global2cpp___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_g");
return x_0;
}
}
obj* l_lean_ir_cpp_global2cpp(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; 
x_3 = l_lean_ir_cpp_fid2cpp(x_0, x_1, x_2);
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
x_17 = l_lean_ir_cpp_global2cpp___closed__1;
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
obj* l_lean_ir_cpp_emit__global(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
lean::inc(x_1);
x_4 = l_lean_ir_cpp_global2cpp(x_0, x_1, x_2);
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
x_20 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_17, x_1, x_7);
return x_20;
}
}
}
obj* _init_l_lean_ir_cpp_type2cpp___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unsigned char");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_type2cpp___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unsigned short");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_type2cpp___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unsigned");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_type2cpp___main___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("unsigned long long");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_type2cpp___main___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("size_t");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_type2cpp___main___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("short");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_type2cpp___main___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("int");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_type2cpp___main___closed__8() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("long long");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_type2cpp___main___closed__9() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("float");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_type2cpp___main___closed__10() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("double");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_type2cpp___main___closed__11() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("obj*");
return x_0;
}
}
obj* l_lean_ir_cpp_type2cpp___main(uint8 x_0) {
_start:
{
switch (x_0) {
case 0:
{
obj* x_1; 
x_1 = l_lean_ir_cpp_type2cpp___main___closed__1;
lean::inc(x_1);
return x_1;
}
case 1:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_type2cpp___main___closed__1;
lean::inc(x_3);
return x_3;
}
case 2:
{
obj* x_5; 
x_5 = l_lean_ir_cpp_type2cpp___main___closed__2;
lean::inc(x_5);
return x_5;
}
case 3:
{
obj* x_7; 
x_7 = l_lean_ir_cpp_type2cpp___main___closed__3;
lean::inc(x_7);
return x_7;
}
case 4:
{
obj* x_9; 
x_9 = l_lean_ir_cpp_type2cpp___main___closed__4;
lean::inc(x_9);
return x_9;
}
case 5:
{
obj* x_11; 
x_11 = l_lean_ir_cpp_type2cpp___main___closed__5;
lean::inc(x_11);
return x_11;
}
case 6:
{
obj* x_13; 
x_13 = l_lean_ir_cpp_type2cpp___main___closed__6;
lean::inc(x_13);
return x_13;
}
case 7:
{
obj* x_15; 
x_15 = l_lean_ir_cpp_type2cpp___main___closed__7;
lean::inc(x_15);
return x_15;
}
case 8:
{
obj* x_17; 
x_17 = l_lean_ir_cpp_type2cpp___main___closed__8;
lean::inc(x_17);
return x_17;
}
case 9:
{
obj* x_19; 
x_19 = l_lean_ir_cpp_type2cpp___main___closed__9;
lean::inc(x_19);
return x_19;
}
case 10:
{
obj* x_21; 
x_21 = l_lean_ir_cpp_type2cpp___main___closed__10;
lean::inc(x_21);
return x_21;
}
default:
{
obj* x_23; 
x_23 = l_lean_ir_cpp_type2cpp___main___closed__11;
lean::inc(x_23);
return x_23;
}
}
}
}
obj* l_lean_ir_cpp_type2cpp___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_cpp_type2cpp___main(x_1);
return x_2;
}
}
obj* l_lean_ir_cpp_type2cpp(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_cpp_type2cpp___main(x_0);
return x_1;
}
}
obj* l_lean_ir_cpp_type2cpp___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_cpp_type2cpp(x_1);
return x_2;
}
}
obj* l_lean_ir_cpp_emit__type(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_cpp_type2cpp___main(x_0);
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_ir_cpp_emit__type___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_ir_cpp_emit__type(x_3, x_1, x_2);
return x_4;
}
}
obj* _init_l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" ");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__sep__aux___main___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_9; obj* x_11; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_9 = l_lean_ir_match__type___closed__5;
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
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
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
x_40 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1, x_3, x_25);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_50; obj* x_53; obj* x_54; 
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_50 = lean::cnstr_get(x_41, 0);
lean::inc(x_50);
lean::dec(x_41);
if (lean::is_scalar(x_37)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_37;
 lean::cnstr_set_tag(x_37, 0);
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
x_56 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_56);
x_59 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_56, x_3, x_43);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_60) == 0)
{
obj* x_69; obj* x_72; obj* x_73; 
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_69 = lean::cnstr_get(x_60, 0);
lean::inc(x_69);
lean::dec(x_60);
if (lean::is_scalar(x_37)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_37;
 lean::cnstr_set_tag(x_37, 0);
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
lean::dec(x_27);
lean::dec(x_37);
lean::dec(x_60);
x_2 = x_14;
x_4 = x_62;
goto _start;
}
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__sep__aux___main(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__sep__aux___main___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_ir_cpp_emit__sep__aux___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_lean_ir_cpp_emit__sep__aux(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__sep__aux___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_ir_cpp_emit__sep___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_1, x_2, x_0, x_3, x_4);
return x_5;
}
}
obj* l_lean_ir_cpp_emit__sep(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__sep___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_ir_cpp_emit__var__list(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__var), 3, 0);
x_4 = lean::mk_string(",");
x_5 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* _init_l_lean_ir_cpp_emit__template__params___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("<");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__template__params___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__type___boxed), 3, 0);
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__template__params___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(",");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__template__params___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(">");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__template__params(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = l_lean_ir_cpp_emit__template__params___closed__1;
lean::inc(x_1);
lean::inc(x_3);
x_6 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
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
lean::dec(x_0);
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
x_20 = l_lean_ir_cpp_emit__template__params___closed__2;
x_21 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_1);
lean::inc(x_21);
lean::inc(x_20);
x_25 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_20, x_21, x_0, x_1, x_9);
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
 lean::cnstr_set_tag(x_19, 0);
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
x_40 = l_lean_ir_cpp_emit__template__params___closed__4;
lean::inc(x_40);
x_42 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_40, x_1, x_28);
return x_42;
}
}
}
}
obj* l_lean_ir_cpp_emit__template__param(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::box(0);
x_4 = lean::box(x_0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = l_lean_ir_cpp_emit__template__params(x_5, x_1, x_2);
return x_6;
}
}
obj* l_lean_ir_cpp_emit__template__param___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_ir_cpp_emit__template__param(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_ir_cpp_emit__arg__list(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__arg__list___lambda__1), 3, 0);
x_4 = lean::mk_string(",");
x_5 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_ir_cpp_emit__arg__list___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_3 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit__type(x_3, x_1, x_2);
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
lean::dec(x_0);
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
x_19 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_19);
x_22 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_1, x_8);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_33; obj* x_34; 
lean::dec(x_1);
lean::dec(x_0);
x_30 = lean::cnstr_get(x_23, 0);
lean::inc(x_30);
lean::dec(x_23);
if (lean::is_scalar(x_18)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_18;
 lean::cnstr_set_tag(x_18, 0);
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
x_41 = l_lean_ir_cpp_emit__var(x_38, x_1, x_25);
return x_41;
}
}
}
}
obj* _init_l_lean_ir_cpp_emit__eos___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(";");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__eos(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_2 = l_lean_ir_cpp_emit__eos___closed__1;
lean::inc(x_0);
lean::inc(x_2);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_2, x_0, x_1);
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
x_19 = l_lean_format_be___main___closed__1;
lean::inc(x_19);
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_0, x_8);
return x_21;
}
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
lean::dec(x_1);
x_4 = l_nat_repr(x_0);
x_5 = lean::string_append(x_2, x_4);
lean::dec(x_4);
x_7 = l_lean_ir_match__type___closed__5;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_5);
return x_9;
}
}
obj* _init_l_lean_ir_cpp_emit__cases___main___closed__1() {
_start:
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
obj* _init_l_lean_ir_cpp_emit__cases___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("default: goto ");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__cases___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("case ");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__cases___main___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(": goto ");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__cases___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_7; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = l_lean_ir_cpp_emit__cases___main___closed__1;
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
x_17 = l_lean_ir_cpp_emit__cases___main___closed__2;
lean::inc(x_2);
lean::inc(x_17);
x_20 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_17, x_2, x_3);
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
x_35 = l_lean_ir_cpp_emit__blockid(x_10, x_2, x_23);
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
 lean::cnstr_set_tag(x_33, 0);
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
lean::dec(x_36);
lean::dec(x_25);
lean::dec(x_33);
x_50 = l_lean_ir_cpp_emit__eos(x_2, x_38);
return x_50;
}
}
}
else
{
obj* x_51; obj* x_54; obj* x_55; obj* x_57; obj* x_59; 
x_51 = l_lean_ir_cpp_emit__cases___main___closed__3;
lean::inc(x_2);
lean::inc(x_51);
x_54 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_51, x_2, x_3);
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
x_72 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_1, x_2, x_57);
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
 lean::cnstr_set_tag(x_69, 0);
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
x_92 = l_lean_ir_cpp_emit__cases___main___closed__4;
lean::inc(x_2);
lean::inc(x_92);
x_95 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_92, x_2, x_75);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_95, 1);
lean::inc(x_98);
lean::dec(x_95);
if (lean::obj_tag(x_96) == 0)
{
obj* x_105; obj* x_108; obj* x_109; 
lean::dec(x_12);
lean::dec(x_10);
lean::dec(x_2);
lean::dec(x_89);
x_105 = lean::cnstr_get(x_96, 0);
lean::inc(x_105);
lean::dec(x_96);
if (lean::is_scalar(x_69)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_69;
 lean::cnstr_set_tag(x_69, 0);
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
x_112 = l_lean_ir_cpp_emit__blockid(x_10, x_2, x_98);
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_112, 1);
lean::inc(x_115);
lean::dec(x_112);
if (lean::obj_tag(x_113) == 0)
{
obj* x_121; obj* x_124; obj* x_125; 
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_89);
x_121 = lean::cnstr_get(x_113, 0);
lean::inc(x_121);
lean::dec(x_113);
if (lean::is_scalar(x_69)) {
 x_124 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_124 = x_69;
 lean::cnstr_set_tag(x_69, 0);
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
x_128 = l_lean_ir_cpp_emit__eos(x_2, x_115);
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_128, 1);
lean::inc(x_131);
lean::dec(x_128);
if (lean::obj_tag(x_129) == 0)
{
obj* x_137; obj* x_140; obj* x_141; 
lean::dec(x_12);
lean::dec(x_2);
lean::dec(x_89);
x_137 = lean::cnstr_get(x_129, 0);
lean::inc(x_137);
lean::dec(x_129);
if (lean::is_scalar(x_69)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_69;
 lean::cnstr_set_tag(x_69, 0);
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
lean::dec(x_129);
lean::dec(x_69);
lean::dec(x_59);
x_0 = x_12;
x_1 = x_89;
x_3 = x_131;
goto _start;
}
}
}
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__cases(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_cpp_emit__cases___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l_lean_ir_cpp_emit__case___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" {");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__case___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("}");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__case___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("switch ");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__case___main___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("goto ");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__case___main___closed__5() {
_start:
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
obj* _init_l_lean_ir_cpp_emit__case___main___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("if (");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__case___main___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(") goto ");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__case___main___closed__8() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("; else goto ");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__case___main___closed__9() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" == 0) goto ");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__case___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_9; 
x_9 = lean::box(0);
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
lean::dec(x_1);
lean::dec(x_0);
x_17 = l_lean_ir_cpp_emit__case___main___closed__4;
lean::inc(x_2);
lean::inc(x_17);
x_20 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_17, x_2, x_3);
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
x_35 = l_lean_ir_cpp_emit__blockid(x_10, x_2, x_23);
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
 lean::cnstr_set_tag(x_33, 0);
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
lean::dec(x_36);
lean::dec(x_25);
lean::dec(x_33);
x_50 = l_lean_ir_cpp_emit__eos(x_2, x_38);
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
lean::dec(x_1);
lean::dec(x_53);
x_61 = lean::cnstr_get(x_2, 1);
lean::inc(x_61);
lean::inc(x_0);
x_64 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_61, x_0);
if (lean::obj_tag(x_64) == 0)
{
obj* x_69; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_51);
lean::dec(x_64);
x_69 = l_lean_ir_cpp_emit__case___main___closed__5;
lean::inc(x_69);
x_58 = x_69;
x_59 = x_3;
goto lbl_60;
}
else
{
obj* x_71; uint8 x_74; 
x_71 = lean::cnstr_get(x_64, 0);
lean::inc(x_71);
lean::dec(x_64);
x_74 = lean::unbox(x_71);
lean::dec(x_71);
switch (x_74) {
case 0:
{
obj* x_76; obj* x_79; obj* x_80; obj* x_82; 
x_76 = l_lean_ir_cpp_emit__case___main___closed__6;
lean::inc(x_2);
lean::inc(x_76);
x_79 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_76, x_2, x_3);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
if (lean::obj_tag(x_80) == 0)
{
obj* x_88; obj* x_90; obj* x_91; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_51);
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
x_94 = l_lean_ir_cpp_emit__var(x_0, x_2, x_82);
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_94, 1);
lean::inc(x_97);
lean::dec(x_94);
if (lean::obj_tag(x_95) == 0)
{
obj* x_102; obj* x_105; 
lean::dec(x_10);
lean::dec(x_51);
x_102 = lean::cnstr_get(x_95, 0);
lean::inc(x_102);
lean::dec(x_95);
if (lean::is_scalar(x_92)) {
 x_105 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_105 = x_92;
 lean::cnstr_set_tag(x_92, 0);
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
x_107 = l_lean_ir_cpp_emit__case___main___closed__7;
lean::inc(x_2);
lean::inc(x_107);
x_110 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_107, x_2, x_97);
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_110, 1);
lean::inc(x_113);
lean::dec(x_110);
if (lean::obj_tag(x_111) == 0)
{
obj* x_118; obj* x_121; 
lean::dec(x_10);
lean::dec(x_51);
x_118 = lean::cnstr_get(x_111, 0);
lean::inc(x_118);
lean::dec(x_111);
if (lean::is_scalar(x_92)) {
 x_121 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_121 = x_92;
 lean::cnstr_set_tag(x_92, 0);
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
x_124 = l_lean_ir_cpp_emit__blockid(x_51, x_2, x_113);
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
 lean::cnstr_set_tag(x_92, 0);
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
x_136 = l_lean_ir_cpp_emit__case___main___closed__8;
lean::inc(x_2);
lean::inc(x_136);
x_139 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_136, x_2, x_127);
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
 lean::cnstr_set_tag(x_92, 0);
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
x_153 = l_lean_ir_cpp_emit__blockid(x_10, x_2, x_142);
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
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_51);
x_162 = l_lean_ir_cpp_emit__case___main___closed__5;
lean::inc(x_162);
x_58 = x_162;
x_59 = x_3;
goto lbl_60;
}
case 2:
{
obj* x_167; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_51);
x_167 = l_lean_ir_cpp_emit__case___main___closed__5;
lean::inc(x_167);
x_58 = x_167;
x_59 = x_3;
goto lbl_60;
}
case 3:
{
obj* x_169; obj* x_172; obj* x_173; obj* x_175; 
x_169 = l_lean_ir_cpp_emit__case___main___closed__6;
lean::inc(x_2);
lean::inc(x_169);
x_172 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_169, x_2, x_3);
x_173 = lean::cnstr_get(x_172, 0);
lean::inc(x_173);
x_175 = lean::cnstr_get(x_172, 1);
lean::inc(x_175);
lean::dec(x_172);
if (lean::obj_tag(x_173) == 0)
{
obj* x_181; obj* x_183; obj* x_184; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_51);
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
x_187 = l_lean_ir_cpp_emit__var(x_0, x_2, x_175);
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
x_190 = lean::cnstr_get(x_187, 1);
lean::inc(x_190);
lean::dec(x_187);
if (lean::obj_tag(x_188) == 0)
{
obj* x_195; obj* x_198; 
lean::dec(x_10);
lean::dec(x_51);
x_195 = lean::cnstr_get(x_188, 0);
lean::inc(x_195);
lean::dec(x_188);
if (lean::is_scalar(x_185)) {
 x_198 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_198 = x_185;
 lean::cnstr_set_tag(x_185, 0);
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
x_200 = l_lean_ir_cpp_emit__case___main___closed__9;
lean::inc(x_2);
lean::inc(x_200);
x_203 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_200, x_2, x_190);
x_204 = lean::cnstr_get(x_203, 0);
lean::inc(x_204);
x_206 = lean::cnstr_get(x_203, 1);
lean::inc(x_206);
lean::dec(x_203);
if (lean::obj_tag(x_204) == 0)
{
obj* x_211; obj* x_214; 
lean::dec(x_10);
lean::dec(x_51);
x_211 = lean::cnstr_get(x_204, 0);
lean::inc(x_211);
lean::dec(x_204);
if (lean::is_scalar(x_185)) {
 x_214 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_214 = x_185;
 lean::cnstr_set_tag(x_185, 0);
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
x_217 = l_lean_ir_cpp_emit__blockid(x_10, x_2, x_206);
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
 lean::cnstr_set_tag(x_185, 0);
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
x_229 = l_lean_ir_cpp_emit__case___main___closed__8;
lean::inc(x_2);
lean::inc(x_229);
x_232 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_229, x_2, x_220);
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
 lean::cnstr_set_tag(x_185, 0);
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
x_246 = l_lean_ir_cpp_emit__blockid(x_51, x_2, x_235);
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
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_51);
x_255 = l_lean_ir_cpp_emit__case___main___closed__5;
lean::inc(x_255);
x_58 = x_255;
x_59 = x_3;
goto lbl_60;
}
case 5:
{
obj* x_260; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_51);
x_260 = l_lean_ir_cpp_emit__case___main___closed__5;
lean::inc(x_260);
x_58 = x_260;
x_59 = x_3;
goto lbl_60;
}
case 6:
{
obj* x_265; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_51);
x_265 = l_lean_ir_cpp_emit__case___main___closed__5;
lean::inc(x_265);
x_58 = x_265;
x_59 = x_3;
goto lbl_60;
}
case 7:
{
obj* x_270; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_51);
x_270 = l_lean_ir_cpp_emit__case___main___closed__5;
lean::inc(x_270);
x_58 = x_270;
x_59 = x_3;
goto lbl_60;
}
case 8:
{
obj* x_275; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_51);
x_275 = l_lean_ir_cpp_emit__case___main___closed__5;
lean::inc(x_275);
x_58 = x_275;
x_59 = x_3;
goto lbl_60;
}
case 9:
{
obj* x_280; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_51);
x_280 = l_lean_ir_cpp_emit__case___main___closed__5;
lean::inc(x_280);
x_58 = x_280;
x_59 = x_3;
goto lbl_60;
}
case 10:
{
obj* x_285; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_51);
x_285 = l_lean_ir_cpp_emit__case___main___closed__5;
lean::inc(x_285);
x_58 = x_285;
x_59 = x_3;
goto lbl_60;
}
default:
{
obj* x_290; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_51);
x_290 = l_lean_ir_cpp_emit__case___main___closed__5;
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
x_299 = l_lean_ir_cpp_emit__eos(x_2, x_59);
return x_299;
}
}
}
else
{
obj* x_303; 
lean::dec(x_10);
lean::dec(x_51);
lean::dec(x_53);
x_303 = lean::box(0);
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
x_312 = l_lean_ir_cpp_emit__case___main___closed__1;
lean::inc(x_2);
lean::inc(x_312);
x_315 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_312, x_2, x_5);
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
 lean::cnstr_set_tag(x_311, 0);
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
x_329 = l_lean_format_be___main___closed__1;
lean::inc(x_2);
lean::inc(x_329);
x_332 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_329, x_2, x_318);
x_333 = lean::cnstr_get(x_332, 0);
lean::inc(x_333);
x_335 = lean::cnstr_get(x_332, 1);
lean::inc(x_335);
lean::dec(x_332);
if (lean::obj_tag(x_333) == 0)
{
obj* x_340; obj* x_343; obj* x_344; 
lean::dec(x_1);
lean::dec(x_2);
x_340 = lean::cnstr_get(x_333, 0);
lean::inc(x_340);
lean::dec(x_333);
if (lean::is_scalar(x_311)) {
 x_343 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_343 = x_311;
 lean::cnstr_set_tag(x_311, 0);
}
lean::cnstr_set(x_343, 0, x_340);
if (lean::is_scalar(x_320)) {
 x_344 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_344 = x_320;
}
lean::cnstr_set(x_344, 0, x_343);
lean::cnstr_set(x_344, 1, x_335);
return x_344;
}
else
{
obj* x_346; obj* x_348; obj* x_349; obj* x_351; 
lean::dec(x_333);
x_346 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_348 = l_lean_ir_cpp_emit__cases___main(x_1, x_346, x_2, x_335);
x_349 = lean::cnstr_get(x_348, 0);
lean::inc(x_349);
x_351 = lean::cnstr_get(x_348, 1);
lean::inc(x_351);
lean::dec(x_348);
if (lean::obj_tag(x_349) == 0)
{
obj* x_355; obj* x_358; obj* x_359; 
lean::dec(x_2);
x_355 = lean::cnstr_get(x_349, 0);
lean::inc(x_355);
lean::dec(x_349);
if (lean::is_scalar(x_311)) {
 x_358 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_358 = x_311;
 lean::cnstr_set_tag(x_311, 0);
}
lean::cnstr_set(x_358, 0, x_355);
if (lean::is_scalar(x_320)) {
 x_359 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_359 = x_320;
}
lean::cnstr_set(x_359, 0, x_358);
lean::cnstr_set(x_359, 1, x_351);
return x_359;
}
else
{
obj* x_361; obj* x_364; obj* x_365; obj* x_367; 
lean::dec(x_349);
x_361 = l_lean_ir_cpp_emit__case___main___closed__2;
lean::inc(x_2);
lean::inc(x_361);
x_364 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_361, x_2, x_351);
x_365 = lean::cnstr_get(x_364, 0);
lean::inc(x_365);
x_367 = lean::cnstr_get(x_364, 1);
lean::inc(x_367);
lean::dec(x_364);
if (lean::obj_tag(x_365) == 0)
{
obj* x_371; obj* x_374; obj* x_375; 
lean::dec(x_2);
x_371 = lean::cnstr_get(x_365, 0);
lean::inc(x_371);
lean::dec(x_365);
if (lean::is_scalar(x_311)) {
 x_374 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_374 = x_311;
 lean::cnstr_set_tag(x_311, 0);
}
lean::cnstr_set(x_374, 0, x_371);
if (lean::is_scalar(x_320)) {
 x_375 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_375 = x_320;
}
lean::cnstr_set(x_375, 0, x_374);
lean::cnstr_set(x_375, 1, x_367);
return x_375;
}
else
{
obj* x_380; 
lean::dec(x_365);
lean::dec(x_311);
lean::dec(x_320);
lean::inc(x_329);
x_380 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_329, x_2, x_367);
return x_380;
}
}
}
}
}
}
lbl_8:
{
obj* x_382; obj* x_385; obj* x_386; obj* x_388; obj* x_390; 
lean::dec(x_7);
x_382 = l_lean_ir_cpp_emit__case___main___closed__3;
lean::inc(x_2);
lean::inc(x_382);
x_385 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_382, x_2, x_3);
x_386 = lean::cnstr_get(x_385, 0);
lean::inc(x_386);
x_388 = lean::cnstr_get(x_385, 1);
lean::inc(x_388);
if (lean::is_shared(x_385)) {
 lean::dec(x_385);
 x_390 = lean::box(0);
} else {
 lean::cnstr_release(x_385, 0);
 lean::cnstr_release(x_385, 1);
 x_390 = x_385;
}
if (lean::obj_tag(x_386) == 0)
{
obj* x_394; obj* x_396; obj* x_397; obj* x_398; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_394 = lean::cnstr_get(x_386, 0);
lean::inc(x_394);
if (lean::is_shared(x_386)) {
 lean::dec(x_386);
 x_396 = lean::box(0);
} else {
 lean::cnstr_release(x_386, 0);
 x_396 = x_386;
}
if (lean::is_scalar(x_396)) {
 x_397 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_397 = x_396;
}
lean::cnstr_set(x_397, 0, x_394);
if (lean::is_scalar(x_390)) {
 x_398 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_398 = x_390;
}
lean::cnstr_set(x_398, 0, x_397);
lean::cnstr_set(x_398, 1, x_388);
return x_398;
}
else
{
obj* x_400; obj* x_401; obj* x_404; obj* x_405; obj* x_407; 
lean::dec(x_390);
if (lean::is_shared(x_386)) {
 lean::dec(x_386);
 x_400 = lean::box(0);
} else {
 lean::cnstr_release(x_386, 0);
 x_400 = x_386;
}
x_401 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_401);
x_404 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_401, x_2, x_388);
x_405 = lean::cnstr_get(x_404, 0);
lean::inc(x_405);
x_407 = lean::cnstr_get(x_404, 1);
lean::inc(x_407);
lean::dec(x_404);
if (lean::obj_tag(x_405) == 0)
{
obj* x_411; obj* x_414; 
lean::dec(x_0);
x_411 = lean::cnstr_get(x_405, 0);
lean::inc(x_411);
lean::dec(x_405);
if (lean::is_scalar(x_400)) {
 x_414 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_414 = x_400;
 lean::cnstr_set_tag(x_400, 0);
}
lean::cnstr_set(x_414, 0, x_411);
x_4 = x_414;
x_5 = x_407;
goto lbl_6;
}
else
{
obj* x_417; obj* x_418; obj* x_420; 
lean::dec(x_405);
lean::inc(x_2);
x_417 = l_lean_ir_cpp_emit__var(x_0, x_2, x_407);
x_418 = lean::cnstr_get(x_417, 0);
lean::inc(x_418);
x_420 = lean::cnstr_get(x_417, 1);
lean::inc(x_420);
lean::dec(x_417);
if (lean::obj_tag(x_418) == 0)
{
obj* x_423; obj* x_426; 
x_423 = lean::cnstr_get(x_418, 0);
lean::inc(x_423);
lean::dec(x_418);
if (lean::is_scalar(x_400)) {
 x_426 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_426 = x_400;
 lean::cnstr_set_tag(x_400, 0);
}
lean::cnstr_set(x_426, 0, x_423);
x_4 = x_426;
x_5 = x_420;
goto lbl_6;
}
else
{
obj* x_427; obj* x_430; obj* x_433; obj* x_434; obj* x_436; 
x_427 = lean::cnstr_get(x_418, 0);
lean::inc(x_427);
lean::dec(x_418);
x_430 = l_option_has__repr___rarg___closed__3;
lean::inc(x_2);
lean::inc(x_430);
x_433 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_430, x_2, x_420);
x_434 = lean::cnstr_get(x_433, 0);
lean::inc(x_434);
x_436 = lean::cnstr_get(x_433, 1);
lean::inc(x_436);
lean::dec(x_433);
if (lean::obj_tag(x_434) == 0)
{
obj* x_440; obj* x_443; 
lean::dec(x_427);
x_440 = lean::cnstr_get(x_434, 0);
lean::inc(x_440);
lean::dec(x_434);
if (lean::is_scalar(x_400)) {
 x_443 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_443 = x_400;
 lean::cnstr_set_tag(x_400, 0);
}
lean::cnstr_set(x_443, 0, x_440);
x_4 = x_443;
x_5 = x_436;
goto lbl_6;
}
else
{
obj* x_445; 
lean::dec(x_434);
if (lean::is_scalar(x_400)) {
 x_445 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_445 = x_400;
}
lean::cnstr_set(x_445, 0, x_427);
x_4 = x_445;
x_5 = x_436;
goto lbl_6;
}
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__case(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_cpp_emit__case___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l_lean_ir_cpp_emit__terminator___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("return ");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__terminator(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_14; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = l_lean_ir_cpp_emit__terminator___closed__1;
lean::inc(x_1);
lean::inc(x_8);
x_11 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_8, x_1, x_2);
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
x_25 = l_lean_ir_cpp_emit__var(x_6, x_1, x_14);
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
 lean::cnstr_set_tag(x_23, 0);
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
x_38 = l_lean_ir_cpp_emit__eos(x_1, x_28);
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
x_48 = l_lean_ir_cpp_emit__case___main(x_44, x_46, x_1, x_2);
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
x_56 = l_lean_ir_cpp_emit__case___main___closed__4;
lean::inc(x_1);
lean::inc(x_56);
x_59 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_56, x_1, x_2);
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
x_73 = l_lean_ir_cpp_emit__blockid(x_54, x_1, x_62);
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
 lean::cnstr_set_tag(x_71, 0);
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
x_86 = l_lean_ir_cpp_emit__eos(x_1, x_76);
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
obj* x_92; obj* x_94; obj* x_95; uint8 x_96; obj* x_97; obj* x_99; obj* x_100; obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_92 = lean::cnstr_get(x_3, 0);
lean::inc(x_92);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_94 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_94 = x_3;
}
x_95 = l_lean_ir_terminator_to__format___main(x_0);
x_96 = 0;
x_97 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_97);
x_99 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_99, 0, x_97);
lean::cnstr_set(x_99, 1, x_95);
lean::cnstr_set_scalar(x_99, sizeof(void*)*2, x_96);
x_100 = x_99;
x_101 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_101);
x_103 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_103, 0, x_100);
lean::cnstr_set(x_103, 1, x_101);
lean::cnstr_set_scalar(x_103, sizeof(void*)*2, x_96);
x_104 = x_103;
x_105 = lean::box(1);
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
obj* _init_l_lean_ir_cpp_emit__type__size___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("sizeof");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__type__size(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = l_lean_ir_cpp_emit__type__size___closed__1;
lean::inc(x_1);
lean::inc(x_3);
x_6 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
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
x_19 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_19);
x_22 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_1, x_9);
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
 lean::cnstr_set_tag(x_18, 0);
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
x_36 = l_lean_ir_cpp_emit__type(x_0, x_1, x_25);
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
 lean::cnstr_set_tag(x_18, 0);
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
x_51 = l_option_has__repr___rarg___closed__3;
lean::inc(x_51);
x_53 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_51, x_1, x_39);
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
 lean::cnstr_set_tag(x_18, 0);
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
obj* l_lean_ir_cpp_emit__type__size___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_ir_cpp_emit__type__size(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_ir_cpp_emit__op__x(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::inc(x_2);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_0, x_2, x_3);
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
x_19 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_19);
x_22 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_2, x_8);
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
 lean::cnstr_set_tag(x_18, 0);
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
x_37 = l_lean_ir_cpp_emit__var(x_1, x_2, x_25);
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
 lean::cnstr_set_tag(x_18, 0);
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
x_52 = l_option_has__repr___rarg___closed__3;
lean::inc(x_52);
x_54 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_52, x_2, x_40);
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
 lean::cnstr_set_tag(x_18, 0);
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
obj* _init_l_lean_ir_cpp_emit__infix___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = ");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__infix(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_13; 
lean::inc(x_4);
x_10 = l_lean_ir_cpp_emit__var(x_0, x_4, x_5);
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
x_21 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_4);
lean::inc(x_21);
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_21, x_4, x_13);
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
lean::dec(x_3);
lean::dec(x_2);
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
x_41 = l_lean_ir_cpp_emit__var(x_1, x_4, x_7);
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
lean::dec(x_3);
lean::dec(x_2);
x_50 = lean::cnstr_get(x_42, 0);
lean::inc(x_50);
lean::dec(x_42);
if (lean::is_scalar(x_39)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_39;
 lean::cnstr_set_tag(x_39, 0);
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
x_56 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_56);
x_59 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_56, x_4, x_44);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_60) == 0)
{
obj* x_68; obj* x_71; obj* x_72; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_68 = lean::cnstr_get(x_60, 0);
lean::inc(x_68);
lean::dec(x_60);
if (lean::is_scalar(x_39)) {
 x_71 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_71 = x_39;
 lean::cnstr_set_tag(x_39, 0);
}
lean::cnstr_set(x_71, 0, x_68);
if (lean::is_scalar(x_46)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_46;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_62);
return x_72;
}
else
{
obj* x_75; obj* x_76; obj* x_78; 
lean::dec(x_60);
lean::inc(x_4);
x_75 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_4, x_62);
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
lean::dec(x_75);
if (lean::obj_tag(x_76) == 0)
{
obj* x_83; obj* x_86; obj* x_87; 
lean::dec(x_4);
lean::dec(x_2);
x_83 = lean::cnstr_get(x_76, 0);
lean::inc(x_83);
lean::dec(x_76);
if (lean::is_scalar(x_39)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_39;
 lean::cnstr_set_tag(x_39, 0);
}
lean::cnstr_set(x_86, 0, x_83);
if (lean::is_scalar(x_46)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_46;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_78);
return x_87;
}
else
{
obj* x_91; obj* x_92; obj* x_94; 
lean::dec(x_76);
lean::inc(x_4);
lean::inc(x_56);
x_91 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_56, x_4, x_78);
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_91, 1);
lean::inc(x_94);
lean::dec(x_91);
if (lean::obj_tag(x_92) == 0)
{
obj* x_99; obj* x_102; obj* x_103; 
lean::dec(x_4);
lean::dec(x_2);
x_99 = lean::cnstr_get(x_92, 0);
lean::inc(x_99);
lean::dec(x_92);
if (lean::is_scalar(x_39)) {
 x_102 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_102 = x_39;
 lean::cnstr_set_tag(x_39, 0);
}
lean::cnstr_set(x_102, 0, x_99);
if (lean::is_scalar(x_46)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_46;
}
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_94);
return x_103;
}
else
{
obj* x_107; 
lean::dec(x_92);
lean::dec(x_46);
lean::dec(x_39);
x_107 = l_lean_ir_cpp_emit__var(x_2, x_4, x_94);
return x_107;
}
}
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__big__binop(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_13; 
lean::inc(x_4);
x_10 = l_lean_ir_cpp_emit__var(x_0, x_4, x_5);
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
x_22 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_4);
lean::inc(x_22);
x_25 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_4, x_13);
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
 lean::cnstr_set_tag(x_21, 0);
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
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_4, x_28);
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
x_54 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_54);
x_57 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_54, x_4, x_7);
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
 lean::cnstr_set_tag(x_53, 0);
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
x_73 = l_lean_ir_cpp_emit__var(x_1, x_4, x_60);
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
 lean::cnstr_set_tag(x_53, 0);
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
x_87 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_87);
x_90 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_87, x_4, x_76);
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
 lean::cnstr_set_tag(x_53, 0);
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
x_105 = l_lean_ir_cpp_emit__var(x_2, x_4, x_93);
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
 lean::cnstr_set_tag(x_53, 0);
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
x_120 = l_option_has__repr___rarg___closed__3;
lean::inc(x_120);
x_122 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_120, x_4, x_108);
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
 lean::cnstr_set_tag(x_53, 0);
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
obj* l_lean_ir_cpp_emit__arith(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
switch (x_0) {
case 0:
{
obj* x_9; 
lean::dec(x_5);
x_9 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_9;
}
case 1:
{
obj* x_11; 
lean::dec(x_5);
x_11 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_11;
}
case 2:
{
obj* x_13; 
lean::dec(x_5);
x_13 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_13;
}
case 3:
{
obj* x_15; 
lean::dec(x_5);
x_15 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_15;
}
case 4:
{
obj* x_17; 
lean::dec(x_5);
x_17 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_17;
}
case 5:
{
obj* x_19; 
lean::dec(x_5);
x_19 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_19;
}
case 6:
{
obj* x_21; 
lean::dec(x_5);
x_21 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_21;
}
case 7:
{
obj* x_23; 
lean::dec(x_5);
x_23 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_23;
}
case 8:
{
obj* x_25; 
lean::dec(x_5);
x_25 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_25;
}
case 9:
{
obj* x_27; 
lean::dec(x_5);
x_27 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_27;
}
case 10:
{
obj* x_29; 
lean::dec(x_5);
x_29 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_29;
}
default:
{
obj* x_31; 
lean::dec(x_4);
x_31 = l_lean_ir_cpp_emit__big__binop(x_1, x_2, x_3, x_5, x_6, x_7);
return x_31;
}
}
}
}
obj* l_lean_ir_cpp_emit__arith___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_0);
x_9 = l_lean_ir_cpp_emit__arith(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* l_lean_ir_cpp_emit__logical__arith(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
switch (x_0) {
case 0:
{
obj* x_11; 
lean::dec(x_5);
lean::dec(x_6);
x_11 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_7, x_8);
return x_11;
}
case 1:
{
obj* x_14; 
lean::dec(x_4);
lean::dec(x_6);
x_14 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_14;
}
case 2:
{
obj* x_17; 
lean::dec(x_4);
lean::dec(x_6);
x_17 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_17;
}
case 3:
{
obj* x_20; 
lean::dec(x_4);
lean::dec(x_6);
x_20 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_20;
}
case 4:
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_6);
x_23 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_23;
}
case 5:
{
obj* x_26; 
lean::dec(x_4);
lean::dec(x_6);
x_26 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_26;
}
case 6:
{
obj* x_29; 
lean::dec(x_4);
lean::dec(x_6);
x_29 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_29;
}
case 7:
{
obj* x_32; 
lean::dec(x_4);
lean::dec(x_6);
x_32 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_32;
}
case 8:
{
obj* x_35; 
lean::dec(x_4);
lean::dec(x_6);
x_35 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_35;
}
case 9:
{
obj* x_38; 
lean::dec(x_4);
lean::dec(x_6);
x_38 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_38;
}
case 10:
{
obj* x_41; 
lean::dec(x_4);
lean::dec(x_6);
x_41 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_41;
}
default:
{
obj* x_44; 
lean::dec(x_5);
lean::dec(x_4);
x_44 = l_lean_ir_cpp_emit__big__binop(x_1, x_2, x_3, x_6, x_7, x_8);
return x_44;
}
}
}
}
obj* l_lean_ir_cpp_emit__logical__arith___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; obj* x_10; 
x_9 = lean::unbox(x_0);
x_10 = l_lean_ir_cpp_emit__logical__arith(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::sarray_data");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("+");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_add");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_sub");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("*");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_mul");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("/");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__8() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_div");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__9() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("%");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__10() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_mod");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__11() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_add");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__12() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_sub");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__13() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_mul");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__14() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_div");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__15() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_mod");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__16() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("<<");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__17() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(">>");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__18() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("&&");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__19() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("&");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__20() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_land");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__21() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("||");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__22() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("|");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__23() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_lor");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__24() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("!=");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__25() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("^");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__26() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_lxor");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__27() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("<=");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__28() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_le");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__29() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_lt");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__30() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("==");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__31() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_eq");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__32() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_ne");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__33() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_le");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__34() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_lt");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__35() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_eq");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__36() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_ne");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__37() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::array_obj");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__38() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::sarray_push");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__39() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::array_push");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__40() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::string_push");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__binop___closed__41() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::string_append");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__assign__binop(obj* x_0, uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; 
switch (x_2) {
case 0:
{
obj* x_12; obj* x_13; obj* x_16; 
x_12 = l_lean_ir_cpp_emit__assign__binop___closed__2;
x_13 = l_lean_ir_cpp_emit__assign__binop___closed__3;
lean::inc(x_13);
lean::inc(x_12);
x_16 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_12, x_13, x_5, x_6);
return x_16;
}
case 1:
{
obj* x_17; obj* x_18; obj* x_21; 
x_17 = l_int_repr___main___closed__1;
x_18 = l_lean_ir_cpp_emit__assign__binop___closed__4;
lean::inc(x_18);
lean::inc(x_17);
x_21 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_17, x_18, x_5, x_6);
return x_21;
}
case 2:
{
obj* x_22; obj* x_23; obj* x_26; 
x_22 = l_lean_ir_cpp_emit__assign__binop___closed__5;
x_23 = l_lean_ir_cpp_emit__assign__binop___closed__6;
lean::inc(x_23);
lean::inc(x_22);
x_26 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_22, x_23, x_5, x_6);
return x_26;
}
case 3:
{
obj* x_27; obj* x_28; obj* x_31; 
x_27 = l_lean_ir_cpp_emit__assign__binop___closed__7;
x_28 = l_lean_ir_cpp_emit__assign__binop___closed__8;
lean::inc(x_28);
lean::inc(x_27);
x_31 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_27, x_28, x_5, x_6);
return x_31;
}
case 4:
{
obj* x_32; obj* x_33; obj* x_36; 
x_32 = l_lean_ir_cpp_emit__assign__binop___closed__9;
x_33 = l_lean_ir_cpp_emit__assign__binop___closed__10;
lean::inc(x_33);
lean::inc(x_32);
x_36 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_32, x_33, x_5, x_6);
return x_36;
}
case 5:
{
obj* x_37; obj* x_39; 
x_37 = l_lean_ir_cpp_emit__assign__binop___closed__11;
lean::inc(x_37);
x_39 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_37, x_5, x_6);
return x_39;
}
case 6:
{
obj* x_40; obj* x_42; 
x_40 = l_lean_ir_cpp_emit__assign__binop___closed__12;
lean::inc(x_40);
x_42 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_40, x_5, x_6);
return x_42;
}
case 7:
{
obj* x_43; obj* x_45; 
x_43 = l_lean_ir_cpp_emit__assign__binop___closed__13;
lean::inc(x_43);
x_45 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_43, x_5, x_6);
return x_45;
}
case 8:
{
obj* x_46; obj* x_48; 
x_46 = l_lean_ir_cpp_emit__assign__binop___closed__14;
lean::inc(x_46);
x_48 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_46, x_5, x_6);
return x_48;
}
case 9:
{
obj* x_49; obj* x_51; 
x_49 = l_lean_ir_cpp_emit__assign__binop___closed__15;
lean::inc(x_49);
x_51 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_49, x_5, x_6);
return x_51;
}
case 10:
{
obj* x_52; obj* x_54; 
x_52 = l_lean_ir_cpp_emit__assign__binop___closed__16;
lean::inc(x_52);
x_54 = l_lean_ir_cpp_emit__infix(x_0, x_3, x_4, x_52, x_5, x_6);
return x_54;
}
case 11:
{
obj* x_55; obj* x_57; 
x_55 = l_lean_ir_cpp_emit__assign__binop___closed__17;
lean::inc(x_55);
x_57 = l_lean_ir_cpp_emit__infix(x_0, x_3, x_4, x_55, x_5, x_6);
return x_57;
}
case 12:
{
obj* x_58; obj* x_59; obj* x_60; obj* x_64; 
x_58 = l_lean_ir_cpp_emit__assign__binop___closed__18;
x_59 = l_lean_ir_cpp_emit__assign__binop___closed__19;
x_60 = l_lean_ir_cpp_emit__assign__binop___closed__20;
lean::inc(x_60);
lean::inc(x_59);
lean::inc(x_58);
x_64 = l_lean_ir_cpp_emit__logical__arith(x_1, x_0, x_3, x_4, x_58, x_59, x_60, x_5, x_6);
return x_64;
}
case 13:
{
obj* x_65; obj* x_66; obj* x_67; obj* x_71; 
x_65 = l_lean_ir_cpp_emit__assign__binop___closed__21;
x_66 = l_lean_ir_cpp_emit__assign__binop___closed__22;
x_67 = l_lean_ir_cpp_emit__assign__binop___closed__23;
lean::inc(x_67);
lean::inc(x_66);
lean::inc(x_65);
x_71 = l_lean_ir_cpp_emit__logical__arith(x_1, x_0, x_3, x_4, x_65, x_66, x_67, x_5, x_6);
return x_71;
}
case 14:
{
obj* x_72; obj* x_73; obj* x_74; obj* x_78; 
x_72 = l_lean_ir_cpp_emit__assign__binop___closed__24;
x_73 = l_lean_ir_cpp_emit__assign__binop___closed__25;
x_74 = l_lean_ir_cpp_emit__assign__binop___closed__26;
lean::inc(x_74);
lean::inc(x_73);
lean::inc(x_72);
x_78 = l_lean_ir_cpp_emit__logical__arith(x_1, x_0, x_3, x_4, x_72, x_73, x_74, x_5, x_6);
return x_78;
}
case 15:
{
obj* x_79; obj* x_80; obj* x_83; 
x_79 = l_lean_ir_cpp_emit__assign__binop___closed__27;
x_80 = l_lean_ir_cpp_emit__assign__binop___closed__28;
lean::inc(x_80);
lean::inc(x_79);
x_83 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_79, x_80, x_5, x_6);
return x_83;
}
case 16:
{
obj* x_84; obj* x_85; obj* x_88; 
x_84 = l_lean_ir_cpp_emit__template__params___closed__1;
x_85 = l_lean_ir_cpp_emit__assign__binop___closed__29;
lean::inc(x_85);
lean::inc(x_84);
x_88 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_84, x_85, x_5, x_6);
return x_88;
}
case 17:
{
obj* x_89; obj* x_90; obj* x_93; 
x_89 = l_lean_ir_cpp_emit__assign__binop___closed__30;
x_90 = l_lean_ir_cpp_emit__assign__binop___closed__31;
lean::inc(x_90);
lean::inc(x_89);
x_93 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_89, x_90, x_5, x_6);
return x_93;
}
case 18:
{
obj* x_94; obj* x_95; obj* x_98; 
x_94 = l_lean_ir_cpp_emit__assign__binop___closed__24;
x_95 = l_lean_ir_cpp_emit__assign__binop___closed__32;
lean::inc(x_95);
lean::inc(x_94);
x_98 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_94, x_95, x_5, x_6);
return x_98;
}
case 19:
{
obj* x_99; obj* x_101; 
x_99 = l_lean_ir_cpp_emit__assign__binop___closed__33;
lean::inc(x_99);
x_101 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_99, x_5, x_6);
return x_101;
}
case 20:
{
obj* x_102; obj* x_104; 
x_102 = l_lean_ir_cpp_emit__assign__binop___closed__34;
lean::inc(x_102);
x_104 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_102, x_5, x_6);
return x_104;
}
case 21:
{
obj* x_105; obj* x_107; 
x_105 = l_lean_ir_cpp_emit__assign__binop___closed__35;
lean::inc(x_105);
x_107 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_105, x_5, x_6);
return x_107;
}
case 22:
{
obj* x_108; obj* x_110; 
x_108 = l_lean_ir_cpp_emit__assign__binop___closed__36;
lean::inc(x_108);
x_110 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_108, x_5, x_6);
return x_110;
}
case 23:
{
switch (x_1) {
case 0:
{
obj* x_111; 
x_111 = lean::box(0);
x_7 = x_111;
goto lbl_8;
}
case 1:
{
obj* x_112; 
x_112 = lean::box(0);
x_7 = x_112;
goto lbl_8;
}
case 2:
{
obj* x_113; 
x_113 = lean::box(0);
x_7 = x_113;
goto lbl_8;
}
case 3:
{
obj* x_114; 
x_114 = lean::box(0);
x_7 = x_114;
goto lbl_8;
}
case 4:
{
obj* x_115; 
x_115 = lean::box(0);
x_7 = x_115;
goto lbl_8;
}
case 5:
{
obj* x_116; 
x_116 = lean::box(0);
x_7 = x_116;
goto lbl_8;
}
case 6:
{
obj* x_117; 
x_117 = lean::box(0);
x_7 = x_117;
goto lbl_8;
}
case 7:
{
obj* x_118; 
x_118 = lean::box(0);
x_7 = x_118;
goto lbl_8;
}
case 8:
{
obj* x_119; 
x_119 = lean::box(0);
x_7 = x_119;
goto lbl_8;
}
case 9:
{
obj* x_120; 
x_120 = lean::box(0);
x_7 = x_120;
goto lbl_8;
}
case 10:
{
obj* x_121; 
x_121 = lean::box(0);
x_7 = x_121;
goto lbl_8;
}
default:
{
obj* x_123; obj* x_124; obj* x_126; 
lean::inc(x_5);
x_123 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
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
x_134 = l_lean_ir_cpp_emit__assign__binop___closed__37;
lean::inc(x_5);
lean::inc(x_134);
x_137 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_134, x_5, x_126);
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
x_144 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
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
lean::dec(x_5);
lean::dec(x_4);
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
x_159 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_5);
lean::inc(x_159);
x_162 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_159, x_5, x_147);
x_163 = lean::cnstr_get(x_162, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_162, 1);
lean::inc(x_165);
lean::dec(x_162);
if (lean::obj_tag(x_163) == 0)
{
obj* x_171; obj* x_174; obj* x_175; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_171 = lean::cnstr_get(x_163, 0);
lean::inc(x_171);
lean::dec(x_163);
if (lean::is_scalar(x_158)) {
 x_174 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_174 = x_158;
 lean::cnstr_set_tag(x_158, 0);
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
x_182 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_179, x_4);
if (lean::obj_tag(x_182) == 0)
{
obj* x_184; obj* x_187; obj* x_188; obj* x_190; 
lean::dec(x_182);
x_184 = l_lean_ir_cpp_emit__assign__binop___closed__38;
lean::inc(x_5);
lean::inc(x_184);
x_187 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_184, x_5, x_165);
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
obj* x_193; uint8 x_196; obj* x_198; obj* x_199; uint8 x_200; 
x_193 = lean::cnstr_get(x_182, 0);
lean::inc(x_193);
lean::dec(x_182);
x_196 = lean::unbox(x_193);
lean::dec(x_193);
x_198 = l_lean_ir_type2id___main(x_196);
x_199 = l_lean_ir_valid__assign__unop__types___closed__1;
x_200 = lean::nat_dec_eq(x_198, x_199);
lean::dec(x_198);
if (x_200 == 0)
{
obj* x_202; obj* x_205; obj* x_206; obj* x_208; 
x_202 = l_lean_ir_cpp_emit__assign__binop___closed__38;
lean::inc(x_5);
lean::inc(x_202);
x_205 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_202, x_5, x_165);
x_206 = lean::cnstr_get(x_205, 0);
lean::inc(x_206);
x_208 = lean::cnstr_get(x_205, 1);
lean::inc(x_208);
lean::dec(x_205);
x_9 = x_206;
x_10 = x_208;
goto lbl_11;
}
else
{
obj* x_211; obj* x_214; obj* x_215; obj* x_217; 
x_211 = l_lean_ir_cpp_emit__assign__binop___closed__39;
lean::inc(x_5);
lean::inc(x_211);
x_214 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_211, x_5, x_165);
x_215 = lean::cnstr_get(x_214, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_214, 1);
lean::inc(x_217);
lean::dec(x_214);
x_9 = x_215;
x_10 = x_217;
goto lbl_11;
}
}
}
}
}
case 25:
{
obj* x_221; obj* x_222; obj* x_224; 
lean::inc(x_5);
x_221 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_222 = lean::cnstr_get(x_221, 0);
lean::inc(x_222);
x_224 = lean::cnstr_get(x_221, 1);
lean::inc(x_224);
lean::dec(x_221);
if (lean::obj_tag(x_222) == 0)
{
obj* x_227; obj* x_229; obj* x_230; 
x_227 = lean::cnstr_get(x_222, 0);
lean::inc(x_227);
if (lean::is_shared(x_222)) {
 lean::dec(x_222);
 x_229 = lean::box(0);
} else {
 lean::cnstr_release(x_222, 0);
 x_229 = x_222;
}
if (lean::is_scalar(x_229)) {
 x_230 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_230 = x_229;
}
lean::cnstr_set(x_230, 0, x_227);
x_9 = x_230;
x_10 = x_224;
goto lbl_11;
}
else
{
obj* x_232; obj* x_235; obj* x_236; obj* x_238; 
lean::dec(x_222);
x_232 = l_lean_ir_cpp_emit__assign__binop___closed__40;
lean::inc(x_5);
lean::inc(x_232);
x_235 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_232, x_5, x_224);
x_236 = lean::cnstr_get(x_235, 0);
lean::inc(x_236);
x_238 = lean::cnstr_get(x_235, 1);
lean::inc(x_238);
lean::dec(x_235);
x_9 = x_236;
x_10 = x_238;
goto lbl_11;
}
}
default:
{
obj* x_242; obj* x_243; obj* x_245; 
lean::inc(x_5);
x_242 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_243 = lean::cnstr_get(x_242, 0);
lean::inc(x_243);
x_245 = lean::cnstr_get(x_242, 1);
lean::inc(x_245);
lean::dec(x_242);
if (lean::obj_tag(x_243) == 0)
{
obj* x_248; obj* x_250; obj* x_251; 
x_248 = lean::cnstr_get(x_243, 0);
lean::inc(x_248);
if (lean::is_shared(x_243)) {
 lean::dec(x_243);
 x_250 = lean::box(0);
} else {
 lean::cnstr_release(x_243, 0);
 x_250 = x_243;
}
if (lean::is_scalar(x_250)) {
 x_251 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_251 = x_250;
}
lean::cnstr_set(x_251, 0, x_248);
x_9 = x_251;
x_10 = x_245;
goto lbl_11;
}
else
{
obj* x_253; obj* x_256; obj* x_257; obj* x_259; 
lean::dec(x_243);
x_253 = l_lean_ir_cpp_emit__assign__binop___closed__41;
lean::inc(x_5);
lean::inc(x_253);
x_256 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_253, x_5, x_245);
x_257 = lean::cnstr_get(x_256, 0);
lean::inc(x_257);
x_259 = lean::cnstr_get(x_256, 1);
lean::inc(x_259);
lean::dec(x_256);
x_9 = x_257;
x_10 = x_259;
goto lbl_11;
}
}
}
lbl_8:
{
obj* x_263; obj* x_264; obj* x_267; obj* x_268; obj* x_270; 
lean::dec(x_7);
lean::inc(x_5);
x_267 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_268 = lean::cnstr_get(x_267, 0);
lean::inc(x_268);
x_270 = lean::cnstr_get(x_267, 1);
lean::inc(x_270);
lean::dec(x_267);
if (lean::obj_tag(x_268) == 0)
{
obj* x_273; obj* x_275; obj* x_276; 
x_273 = lean::cnstr_get(x_268, 0);
lean::inc(x_273);
if (lean::is_shared(x_268)) {
 lean::dec(x_268);
 x_275 = lean::box(0);
} else {
 lean::cnstr_release(x_268, 0);
 x_275 = x_268;
}
if (lean::is_scalar(x_275)) {
 x_276 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_276 = x_275;
}
lean::cnstr_set(x_276, 0, x_273);
x_263 = x_276;
x_264 = x_270;
goto lbl_265;
}
else
{
obj* x_277; obj* x_278; obj* x_281; obj* x_282; obj* x_284; 
if (lean::is_shared(x_268)) {
 lean::dec(x_268);
 x_277 = lean::box(0);
} else {
 lean::cnstr_release(x_268, 0);
 x_277 = x_268;
}
x_278 = l_lean_ir_cpp_emit__assign__binop___closed__1;
lean::inc(x_5);
lean::inc(x_278);
x_281 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_278, x_5, x_270);
x_282 = lean::cnstr_get(x_281, 0);
lean::inc(x_282);
x_284 = lean::cnstr_get(x_281, 1);
lean::inc(x_284);
lean::dec(x_281);
if (lean::obj_tag(x_282) == 0)
{
obj* x_287; obj* x_290; 
x_287 = lean::cnstr_get(x_282, 0);
lean::inc(x_287);
lean::dec(x_282);
if (lean::is_scalar(x_277)) {
 x_290 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_290 = x_277;
 lean::cnstr_set_tag(x_277, 0);
}
lean::cnstr_set(x_290, 0, x_287);
x_263 = x_290;
x_264 = x_284;
goto lbl_265;
}
else
{
obj* x_294; obj* x_295; obj* x_297; 
lean::dec(x_282);
lean::dec(x_277);
lean::inc(x_5);
x_294 = l_lean_ir_cpp_emit__template__param(x_1, x_5, x_284);
x_295 = lean::cnstr_get(x_294, 0);
lean::inc(x_295);
x_297 = lean::cnstr_get(x_294, 1);
lean::inc(x_297);
lean::dec(x_294);
x_263 = x_295;
x_264 = x_297;
goto lbl_265;
}
}
lbl_265:
{
if (lean::obj_tag(x_263) == 0)
{
obj* x_303; obj* x_305; obj* x_306; obj* x_307; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_303 = lean::cnstr_get(x_263, 0);
lean::inc(x_303);
if (lean::is_shared(x_263)) {
 lean::dec(x_263);
 x_305 = lean::box(0);
} else {
 lean::cnstr_release(x_263, 0);
 x_305 = x_263;
}
if (lean::is_scalar(x_305)) {
 x_306 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_306 = x_305;
}
lean::cnstr_set(x_306, 0, x_303);
x_307 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_307, 0, x_306);
lean::cnstr_set(x_307, 1, x_264);
return x_307;
}
else
{
obj* x_308; obj* x_309; obj* x_312; obj* x_313; obj* x_315; obj* x_317; 
if (lean::is_shared(x_263)) {
 lean::dec(x_263);
 x_308 = lean::box(0);
} else {
 lean::cnstr_release(x_263, 0);
 x_308 = x_263;
}
x_309 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_309);
x_312 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_309, x_5, x_264);
x_313 = lean::cnstr_get(x_312, 0);
lean::inc(x_313);
x_315 = lean::cnstr_get(x_312, 1);
lean::inc(x_315);
if (lean::is_shared(x_312)) {
 lean::dec(x_312);
 x_317 = lean::box(0);
} else {
 lean::cnstr_release(x_312, 0);
 lean::cnstr_release(x_312, 1);
 x_317 = x_312;
}
if (lean::obj_tag(x_313) == 0)
{
obj* x_321; obj* x_324; obj* x_325; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_321 = lean::cnstr_get(x_313, 0);
lean::inc(x_321);
lean::dec(x_313);
if (lean::is_scalar(x_308)) {
 x_324 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_324 = x_308;
 lean::cnstr_set_tag(x_308, 0);
}
lean::cnstr_set(x_324, 0, x_321);
if (lean::is_scalar(x_317)) {
 x_325 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_325 = x_317;
}
lean::cnstr_set(x_325, 0, x_324);
lean::cnstr_set(x_325, 1, x_315);
return x_325;
}
else
{
obj* x_328; obj* x_329; obj* x_331; 
lean::dec(x_313);
lean::inc(x_5);
x_328 = l_lean_ir_cpp_emit__var(x_3, x_5, x_315);
x_329 = lean::cnstr_get(x_328, 0);
lean::inc(x_329);
x_331 = lean::cnstr_get(x_328, 1);
lean::inc(x_331);
lean::dec(x_328);
if (lean::obj_tag(x_329) == 0)
{
obj* x_336; obj* x_339; obj* x_340; 
lean::dec(x_5);
lean::dec(x_4);
x_336 = lean::cnstr_get(x_329, 0);
lean::inc(x_336);
lean::dec(x_329);
if (lean::is_scalar(x_308)) {
 x_339 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_339 = x_308;
 lean::cnstr_set_tag(x_308, 0);
}
lean::cnstr_set(x_339, 0, x_336);
if (lean::is_scalar(x_317)) {
 x_340 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_340 = x_317;
}
lean::cnstr_set(x_340, 0, x_339);
lean::cnstr_set(x_340, 1, x_331);
return x_340;
}
else
{
obj* x_342; obj* x_345; obj* x_346; obj* x_348; 
lean::dec(x_329);
x_342 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_342);
x_345 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_342, x_5, x_331);
x_346 = lean::cnstr_get(x_345, 0);
lean::inc(x_346);
x_348 = lean::cnstr_get(x_345, 1);
lean::inc(x_348);
lean::dec(x_345);
if (lean::obj_tag(x_346) == 0)
{
obj* x_353; obj* x_356; obj* x_357; 
lean::dec(x_5);
lean::dec(x_4);
x_353 = lean::cnstr_get(x_346, 0);
lean::inc(x_353);
lean::dec(x_346);
if (lean::is_scalar(x_308)) {
 x_356 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_356 = x_308;
 lean::cnstr_set_tag(x_308, 0);
}
lean::cnstr_set(x_356, 0, x_353);
if (lean::is_scalar(x_317)) {
 x_357 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_357 = x_317;
}
lean::cnstr_set(x_357, 0, x_356);
lean::cnstr_set(x_357, 1, x_348);
return x_357;
}
else
{
obj* x_360; obj* x_361; obj* x_363; 
lean::dec(x_346);
lean::inc(x_5);
x_360 = l_lean_ir_cpp_emit__var(x_4, x_5, x_348);
x_361 = lean::cnstr_get(x_360, 0);
lean::inc(x_361);
x_363 = lean::cnstr_get(x_360, 1);
lean::inc(x_363);
lean::dec(x_360);
if (lean::obj_tag(x_361) == 0)
{
obj* x_367; obj* x_370; obj* x_371; 
lean::dec(x_5);
x_367 = lean::cnstr_get(x_361, 0);
lean::inc(x_367);
lean::dec(x_361);
if (lean::is_scalar(x_308)) {
 x_370 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_370 = x_308;
 lean::cnstr_set_tag(x_308, 0);
}
lean::cnstr_set(x_370, 0, x_367);
if (lean::is_scalar(x_317)) {
 x_371 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_371 = x_317;
}
lean::cnstr_set(x_371, 0, x_370);
lean::cnstr_set(x_371, 1, x_363);
return x_371;
}
else
{
obj* x_372; obj* x_375; obj* x_377; obj* x_378; obj* x_380; 
x_372 = lean::cnstr_get(x_361, 0);
lean::inc(x_372);
lean::dec(x_361);
x_375 = l_option_has__repr___rarg___closed__3;
lean::inc(x_375);
x_377 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_375, x_5, x_363);
x_378 = lean::cnstr_get(x_377, 0);
lean::inc(x_378);
x_380 = lean::cnstr_get(x_377, 1);
lean::inc(x_380);
lean::dec(x_377);
if (lean::obj_tag(x_378) == 0)
{
obj* x_384; obj* x_387; obj* x_388; 
lean::dec(x_372);
x_384 = lean::cnstr_get(x_378, 0);
lean::inc(x_384);
lean::dec(x_378);
if (lean::is_scalar(x_308)) {
 x_387 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_387 = x_308;
 lean::cnstr_set_tag(x_308, 0);
}
lean::cnstr_set(x_387, 0, x_384);
if (lean::is_scalar(x_317)) {
 x_388 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_388 = x_317;
}
lean::cnstr_set(x_388, 0, x_387);
lean::cnstr_set(x_388, 1, x_380);
return x_388;
}
else
{
obj* x_390; obj* x_391; 
lean::dec(x_378);
if (lean::is_scalar(x_308)) {
 x_390 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_390 = x_308;
}
lean::cnstr_set(x_390, 0, x_372);
if (lean::is_scalar(x_317)) {
 x_391 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_391 = x_317;
}
lean::cnstr_set(x_391, 0, x_390);
lean::cnstr_set(x_391, 1, x_380);
return x_391;
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
obj* x_395; obj* x_397; obj* x_398; obj* x_399; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_395 = lean::cnstr_get(x_9, 0);
lean::inc(x_395);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_397 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_397 = x_9;
}
if (lean::is_scalar(x_397)) {
 x_398 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_398 = x_397;
}
lean::cnstr_set(x_398, 0, x_395);
x_399 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_399, 0, x_398);
lean::cnstr_set(x_399, 1, x_10);
return x_399;
}
else
{
obj* x_400; obj* x_401; obj* x_404; obj* x_405; obj* x_407; obj* x_409; 
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_400 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_400 = x_9;
}
x_401 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_401);
x_404 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_401, x_5, x_10);
x_405 = lean::cnstr_get(x_404, 0);
lean::inc(x_405);
x_407 = lean::cnstr_get(x_404, 1);
lean::inc(x_407);
if (lean::is_shared(x_404)) {
 lean::dec(x_404);
 x_409 = lean::box(0);
} else {
 lean::cnstr_release(x_404, 0);
 lean::cnstr_release(x_404, 1);
 x_409 = x_404;
}
if (lean::obj_tag(x_405) == 0)
{
obj* x_413; obj* x_416; obj* x_417; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_413 = lean::cnstr_get(x_405, 0);
lean::inc(x_413);
lean::dec(x_405);
if (lean::is_scalar(x_400)) {
 x_416 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_416 = x_400;
 lean::cnstr_set_tag(x_400, 0);
}
lean::cnstr_set(x_416, 0, x_413);
if (lean::is_scalar(x_409)) {
 x_417 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_417 = x_409;
}
lean::cnstr_set(x_417, 0, x_416);
lean::cnstr_set(x_417, 1, x_407);
return x_417;
}
else
{
obj* x_420; obj* x_421; obj* x_423; 
lean::dec(x_405);
lean::inc(x_5);
x_420 = l_lean_ir_cpp_emit__var(x_3, x_5, x_407);
x_421 = lean::cnstr_get(x_420, 0);
lean::inc(x_421);
x_423 = lean::cnstr_get(x_420, 1);
lean::inc(x_423);
lean::dec(x_420);
if (lean::obj_tag(x_421) == 0)
{
obj* x_428; obj* x_431; obj* x_432; 
lean::dec(x_5);
lean::dec(x_4);
x_428 = lean::cnstr_get(x_421, 0);
lean::inc(x_428);
lean::dec(x_421);
if (lean::is_scalar(x_400)) {
 x_431 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_431 = x_400;
 lean::cnstr_set_tag(x_400, 0);
}
lean::cnstr_set(x_431, 0, x_428);
if (lean::is_scalar(x_409)) {
 x_432 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_432 = x_409;
}
lean::cnstr_set(x_432, 0, x_431);
lean::cnstr_set(x_432, 1, x_423);
return x_432;
}
else
{
obj* x_434; obj* x_437; obj* x_438; obj* x_440; 
lean::dec(x_421);
x_434 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_434);
x_437 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_434, x_5, x_423);
x_438 = lean::cnstr_get(x_437, 0);
lean::inc(x_438);
x_440 = lean::cnstr_get(x_437, 1);
lean::inc(x_440);
lean::dec(x_437);
if (lean::obj_tag(x_438) == 0)
{
obj* x_445; obj* x_448; obj* x_449; 
lean::dec(x_5);
lean::dec(x_4);
x_445 = lean::cnstr_get(x_438, 0);
lean::inc(x_445);
lean::dec(x_438);
if (lean::is_scalar(x_400)) {
 x_448 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_448 = x_400;
 lean::cnstr_set_tag(x_400, 0);
}
lean::cnstr_set(x_448, 0, x_445);
if (lean::is_scalar(x_409)) {
 x_449 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_449 = x_409;
}
lean::cnstr_set(x_449, 0, x_448);
lean::cnstr_set(x_449, 1, x_440);
return x_449;
}
else
{
obj* x_452; obj* x_453; obj* x_455; 
lean::dec(x_438);
lean::inc(x_5);
x_452 = l_lean_ir_cpp_emit__var(x_4, x_5, x_440);
x_453 = lean::cnstr_get(x_452, 0);
lean::inc(x_453);
x_455 = lean::cnstr_get(x_452, 1);
lean::inc(x_455);
lean::dec(x_452);
if (lean::obj_tag(x_453) == 0)
{
obj* x_459; obj* x_462; obj* x_463; 
lean::dec(x_5);
x_459 = lean::cnstr_get(x_453, 0);
lean::inc(x_459);
lean::dec(x_453);
if (lean::is_scalar(x_400)) {
 x_462 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_462 = x_400;
 lean::cnstr_set_tag(x_400, 0);
}
lean::cnstr_set(x_462, 0, x_459);
if (lean::is_scalar(x_409)) {
 x_463 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_463 = x_409;
}
lean::cnstr_set(x_463, 0, x_462);
lean::cnstr_set(x_463, 1, x_455);
return x_463;
}
else
{
obj* x_464; obj* x_467; obj* x_469; obj* x_470; obj* x_472; 
x_464 = lean::cnstr_get(x_453, 0);
lean::inc(x_464);
lean::dec(x_453);
x_467 = l_option_has__repr___rarg___closed__3;
lean::inc(x_467);
x_469 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_467, x_5, x_455);
x_470 = lean::cnstr_get(x_469, 0);
lean::inc(x_470);
x_472 = lean::cnstr_get(x_469, 1);
lean::inc(x_472);
lean::dec(x_469);
if (lean::obj_tag(x_470) == 0)
{
obj* x_476; obj* x_479; obj* x_480; 
lean::dec(x_464);
x_476 = lean::cnstr_get(x_470, 0);
lean::inc(x_476);
lean::dec(x_470);
if (lean::is_scalar(x_400)) {
 x_479 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_479 = x_400;
 lean::cnstr_set_tag(x_400, 0);
}
lean::cnstr_set(x_479, 0, x_476);
if (lean::is_scalar(x_409)) {
 x_480 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_480 = x_409;
}
lean::cnstr_set(x_480, 0, x_479);
lean::cnstr_set(x_480, 1, x_472);
return x_480;
}
else
{
obj* x_482; obj* x_483; 
lean::dec(x_470);
if (lean::is_scalar(x_400)) {
 x_482 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_482 = x_400;
}
lean::cnstr_set(x_482, 0, x_464);
if (lean::is_scalar(x_409)) {
 x_483 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_483 = x_409;
}
lean::cnstr_set(x_483, 0, x_482);
lean::cnstr_set(x_483, 1, x_472);
return x_483;
}
}
}
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__assign__binop___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; uint8 x_8; obj* x_9; 
x_7 = lean::unbox(x_1);
x_8 = lean::unbox(x_2);
x_9 = l_lean_ir_cpp_emit__assign__binop(x_0, x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
obj* l_lean_ir_cpp_emit__x__op__y(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_12; 
lean::inc(x_3);
x_9 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
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
x_20 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
lean::inc(x_20);
x_23 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_20, x_3, x_12);
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
lean::dec(x_3);
lean::dec(x_2);
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
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1, x_3, x_6);
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
lean::dec(x_3);
lean::dec(x_2);
x_47 = lean::cnstr_get(x_40, 0);
lean::inc(x_47);
lean::dec(x_40);
if (lean::is_scalar(x_37)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_37;
 lean::cnstr_set_tag(x_37, 0);
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
x_53 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_53);
x_56 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_53, x_3, x_42);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
if (lean::obj_tag(x_57) == 0)
{
obj* x_64; obj* x_67; obj* x_68; 
lean::dec(x_3);
lean::dec(x_2);
x_64 = lean::cnstr_get(x_57, 0);
lean::inc(x_64);
lean::dec(x_57);
if (lean::is_scalar(x_37)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_37;
 lean::cnstr_set_tag(x_37, 0);
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
x_71 = l_lean_ir_cpp_emit__var(x_2, x_3, x_59);
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
 lean::cnstr_set_tag(x_37, 0);
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
x_86 = l_option_has__repr___rarg___closed__3;
lean::inc(x_86);
x_88 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_86, x_3, x_74);
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
 lean::cnstr_set_tag(x_37, 0);
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
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("~");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("!");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::int_neg");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat2int");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::is_scalar");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::is_shared");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::is_null");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__8() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("static_cast<");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__9() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::box");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__10() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::unbox");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__11() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::array_copy");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__12() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::sarray_copy");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__13() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::array_size");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__14() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::sarray_size");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__15() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::string_len");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__16() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::nat_succ");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__17() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::obj_tag");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__18() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::cnstr_tag");
return x_0;
}
}
obj* l_lean_ir_cpp_assign__unop2cpp___main(uint8 x_0, uint8 x_1) {
_start:
{
switch (x_1) {
case 0:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = l_lean_ir_type2id___main(x_0);
x_3 = l_lean_ir_is__arith__ty___closed__1;
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_2);
if (x_4 == 0)
{
obj* x_6; 
x_6 = l_lean_ir_cpp_assign__unop2cpp___main___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; 
x_8 = l_lean_ir_cpp_assign__unop2cpp___main___closed__2;
lean::inc(x_8);
return x_8;
}
}
case 1:
{
obj* x_10; 
x_10 = l_int_repr___main___closed__1;
lean::inc(x_10);
return x_10;
}
case 2:
{
obj* x_12; 
x_12 = l_lean_ir_cpp_assign__unop2cpp___main___closed__3;
lean::inc(x_12);
return x_12;
}
case 3:
{
obj* x_14; 
x_14 = l_lean_ir_cpp_assign__unop2cpp___main___closed__4;
lean::inc(x_14);
return x_14;
}
case 4:
{
obj* x_16; 
x_16 = l_lean_ir_cpp_assign__unop2cpp___main___closed__5;
lean::inc(x_16);
return x_16;
}
case 5:
{
obj* x_18; 
x_18 = l_lean_ir_cpp_assign__unop2cpp___main___closed__6;
lean::inc(x_18);
return x_18;
}
case 6:
{
obj* x_20; 
x_20 = l_lean_ir_cpp_assign__unop2cpp___main___closed__7;
lean::inc(x_20);
return x_20;
}
case 7:
{
obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; 
x_22 = l_lean_ir_cpp_type2cpp___main(x_0);
x_23 = l_lean_ir_cpp_assign__unop2cpp___main___closed__8;
lean::inc(x_23);
x_25 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_27 = l_lean_ir_cpp_emit__template__params___closed__4;
x_28 = lean::string_append(x_25, x_27);
return x_28;
}
case 8:
{
obj* x_29; 
x_29 = l_lean_ir_cpp_assign__unop2cpp___main___closed__9;
lean::inc(x_29);
return x_29;
}
case 9:
{
obj* x_31; 
x_31 = l_lean_ir_cpp_assign__unop2cpp___main___closed__10;
lean::inc(x_31);
return x_31;
}
case 10:
{
obj* x_33; 
x_33 = l_lean_ir_cpp_assign__unop2cpp___main___closed__11;
lean::inc(x_33);
return x_33;
}
case 11:
{
obj* x_35; 
x_35 = l_lean_ir_cpp_assign__unop2cpp___main___closed__12;
lean::inc(x_35);
return x_35;
}
case 12:
{
obj* x_37; 
x_37 = l_lean_ir_cpp_assign__unop2cpp___main___closed__13;
lean::inc(x_37);
return x_37;
}
case 13:
{
obj* x_39; 
x_39 = l_lean_ir_cpp_assign__unop2cpp___main___closed__14;
lean::inc(x_39);
return x_39;
}
case 14:
{
obj* x_41; 
x_41 = l_lean_ir_cpp_assign__unop2cpp___main___closed__15;
lean::inc(x_41);
return x_41;
}
case 15:
{
obj* x_43; 
x_43 = l_lean_ir_cpp_assign__unop2cpp___main___closed__16;
lean::inc(x_43);
return x_43;
}
case 16:
{
obj* x_45; 
x_45 = l_lean_ir_cpp_assign__unop2cpp___main___closed__17;
lean::inc(x_45);
return x_45;
}
default:
{
obj* x_47; 
x_47 = l_lean_ir_cpp_assign__unop2cpp___main___closed__18;
lean::inc(x_47);
return x_47;
}
}
}
}
obj* l_lean_ir_cpp_assign__unop2cpp___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_lean_ir_cpp_assign__unop2cpp___main(x_2, x_3);
return x_4;
}
}
obj* l_lean_ir_cpp_assign__unop2cpp(uint8 x_0, uint8 x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_cpp_assign__unop2cpp___main(x_0, x_1);
return x_2;
}
}
obj* l_lean_ir_cpp_assign__unop2cpp___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; uint8 x_3; obj* x_4; 
x_2 = lean::unbox(x_0);
x_3 = lean::unbox(x_1);
x_4 = l_lean_ir_cpp_assign__unop2cpp(x_2, x_3);
return x_4;
}
}
obj* l_lean_ir_cpp_emit__assign__unop(obj* x_0, uint8 x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_14; 
x_6 = l_lean_ir_cpp_assign__unop2cpp___main(x_1, x_2);
lean::inc(x_4);
x_11 = l_lean_ir_cpp_emit__var(x_0, x_4, x_5);
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
x_22 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_4);
lean::inc(x_22);
x_25 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_4, x_14);
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
x_41 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_6, x_4, x_8);
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
 lean::cnstr_set_tag(x_39, 0);
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
x_55 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_55);
x_58 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_55, x_4, x_44);
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
 lean::cnstr_set_tag(x_39, 0);
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
x_73 = l_lean_ir_cpp_emit__var(x_3, x_4, x_61);
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
 lean::cnstr_set_tag(x_39, 0);
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
x_88 = l_option_has__repr___rarg___closed__3;
lean::inc(x_88);
x_90 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_88, x_4, x_76);
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
 lean::cnstr_set_tag(x_39, 0);
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
obj* l_lean_ir_cpp_emit__assign__unop___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; uint8 x_7; obj* x_8; 
x_6 = lean::unbox(x_1);
x_7 = lean::unbox(x_2);
x_8 = l_lean_ir_cpp_emit__assign__unop(x_0, x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
obj* _init_l_lean_ir_cpp_emit__num__suffix___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("u");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__num__suffix___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ull");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__num__suffix___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("ll");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__num__suffix___main(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
switch (x_0) {
case 0:
{
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
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
x_8 = l_lean_ir_match__type___closed__5;
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
x_12 = l_lean_ir_match__type___closed__5;
lean::inc(x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_2);
return x_14;
}
case 3:
{
obj* x_15; obj* x_17; 
x_15 = l_lean_ir_cpp_emit__num__suffix___main___closed__1;
lean::inc(x_15);
x_17 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_15, x_1, x_2);
return x_17;
}
case 4:
{
obj* x_18; obj* x_20; 
x_18 = l_lean_ir_cpp_emit__num__suffix___main___closed__2;
lean::inc(x_18);
x_20 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_18, x_1, x_2);
return x_20;
}
case 5:
{
obj* x_22; obj* x_24; 
lean::dec(x_1);
x_22 = l_lean_ir_match__type___closed__5;
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
x_26 = l_lean_ir_match__type___closed__5;
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
x_30 = l_lean_ir_match__type___closed__5;
lean::inc(x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_2);
return x_32;
}
case 8:
{
obj* x_33; obj* x_35; 
x_33 = l_lean_ir_cpp_emit__num__suffix___main___closed__3;
lean::inc(x_33);
x_35 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_33, x_1, x_2);
return x_35;
}
case 9:
{
obj* x_37; obj* x_39; 
lean::dec(x_1);
x_37 = l_lean_ir_match__type___closed__5;
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
x_41 = l_lean_ir_match__type___closed__5;
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
x_45 = l_lean_ir_match__type___closed__5;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_2);
return x_47;
}
}
}
}
obj* l_lean_ir_cpp_emit__num__suffix___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_ir_cpp_emit__num__suffix___main(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_ir_cpp_emit__num__suffix(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_emit__num__suffix___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_ir_cpp_emit__num__suffix___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_ir_cpp_emit__num__suffix(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
lean::dec(x_1);
x_4 = l_int_repr___main(x_0);
x_5 = lean::string_append(x_2, x_4);
lean::dec(x_4);
x_7 = l_lean_ir_match__type___closed__5;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_5);
return x_9;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__lit___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = false");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__lit___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = true");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__lit___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::mk_string");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__lit___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_uint32__sz;
x_1 = lean::nat2int(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__lit___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::mk_mpz_core(lean::mpz(\"");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__lit___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("\"))");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__assign__lit___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::mk_nat_obj");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__assign__lit(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
uint8 x_5; 
x_5 = lean::cnstr_get_scalar<uint8>(x_2, 0);
lean::dec(x_2);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
lean::inc(x_3);
x_8 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
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
x_22 = l_lean_ir_cpp_emit__assign__lit___closed__1;
lean::inc(x_22);
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_3, x_11);
return x_24;
}
}
else
{
obj* x_26; obj* x_27; obj* x_29; obj* x_31; 
lean::inc(x_3);
x_26 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
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
x_40 = l_lean_ir_cpp_emit__assign__lit___closed__2;
lean::inc(x_40);
x_42 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_40, x_3, x_29);
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
x_47 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
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
lean::dec(x_3);
lean::dec(x_43);
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
x_61 = l_lean_ir_cpp_emit__assign__lit___closed__3;
lean::inc(x_3);
lean::inc(x_61);
x_64 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_61, x_3, x_50);
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_64, 1);
lean::inc(x_67);
lean::dec(x_64);
if (lean::obj_tag(x_65) == 0)
{
obj* x_72; obj* x_75; obj* x_76; 
lean::dec(x_3);
lean::dec(x_43);
x_72 = lean::cnstr_get(x_65, 0);
lean::inc(x_72);
lean::dec(x_65);
if (lean::is_scalar(x_60)) {
 x_75 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_75 = x_60;
 lean::cnstr_set_tag(x_60, 0);
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
x_78 = l_string_quote(x_43);
x_79 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_79);
x_82 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_79, x_3, x_67);
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
if (lean::obj_tag(x_83) == 0)
{
obj* x_90; obj* x_93; obj* x_94; 
lean::dec(x_3);
lean::dec(x_78);
x_90 = lean::cnstr_get(x_83, 0);
lean::inc(x_90);
lean::dec(x_83);
if (lean::is_scalar(x_60)) {
 x_93 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_93 = x_60;
 lean::cnstr_set_tag(x_60, 0);
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
x_97 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_78, x_3, x_85);
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
 lean::cnstr_set_tag(x_60, 0);
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
x_112 = l_option_has__repr___rarg___closed__3;
lean::inc(x_112);
x_114 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_112, x_3, x_100);
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
 lean::cnstr_set_tag(x_60, 0);
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
obj* x_129; obj* x_132; 
x_129 = lean::cnstr_get(x_2, 0);
lean::inc(x_129);
lean::dec(x_2);
switch (x_1) {
case 0:
{
obj* x_134; 
x_134 = lean::box(0);
x_132 = x_134;
goto lbl_133;
}
case 1:
{
obj* x_135; 
x_135 = lean::box(0);
x_132 = x_135;
goto lbl_133;
}
case 2:
{
obj* x_136; 
x_136 = lean::box(0);
x_132 = x_136;
goto lbl_133;
}
case 3:
{
obj* x_137; 
x_137 = lean::box(0);
x_132 = x_137;
goto lbl_133;
}
case 4:
{
obj* x_138; 
x_138 = lean::box(0);
x_132 = x_138;
goto lbl_133;
}
case 5:
{
obj* x_139; 
x_139 = lean::box(0);
x_132 = x_139;
goto lbl_133;
}
case 6:
{
obj* x_140; 
x_140 = lean::box(0);
x_132 = x_140;
goto lbl_133;
}
case 7:
{
obj* x_141; 
x_141 = lean::box(0);
x_132 = x_141;
goto lbl_133;
}
case 8:
{
obj* x_142; 
x_142 = lean::box(0);
x_132 = x_142;
goto lbl_133;
}
case 9:
{
obj* x_143; 
x_143 = lean::box(0);
x_132 = x_143;
goto lbl_133;
}
case 10:
{
obj* x_144; 
x_144 = lean::box(0);
x_132 = x_144;
goto lbl_133;
}
default:
{
obj* x_145; uint8 x_146; obj* x_147; obj* x_148; obj* x_151; obj* x_152; obj* x_154; 
x_145 = l_lean_ir_cpp_emit__assign__lit___closed__4;
x_146 = lean::int_dec_lt(x_129, x_145);
lean::inc(x_3);
x_151 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
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
x_162 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
lean::inc(x_162);
x_165 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_162, x_3, x_154);
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
obj* x_173; obj* x_175; obj* x_176; obj* x_177; 
lean::dec(x_3);
lean::dec(x_129);
x_173 = lean::cnstr_get(x_147, 0);
lean::inc(x_173);
if (lean::is_shared(x_147)) {
 lean::dec(x_147);
 x_175 = lean::box(0);
} else {
 lean::cnstr_release(x_147, 0);
 x_175 = x_147;
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_173);
x_177 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_177, 0, x_176);
lean::cnstr_set(x_177, 1, x_148);
return x_177;
}
else
{
obj* x_178; 
if (lean::is_shared(x_147)) {
 lean::dec(x_147);
 x_178 = lean::box(0);
} else {
 lean::cnstr_release(x_147, 0);
 x_178 = x_147;
}
if (x_146 == 0)
{
obj* x_179; obj* x_182; obj* x_183; obj* x_185; obj* x_187; 
x_179 = l_lean_ir_cpp_emit__assign__lit___closed__5;
lean::inc(x_3);
lean::inc(x_179);
x_182 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_179, x_3, x_148);
x_183 = lean::cnstr_get(x_182, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_182, 1);
lean::inc(x_185);
if (lean::is_shared(x_182)) {
 lean::dec(x_182);
 x_187 = lean::box(0);
} else {
 lean::cnstr_release(x_182, 0);
 lean::cnstr_release(x_182, 1);
 x_187 = x_182;
}
if (lean::obj_tag(x_183) == 0)
{
obj* x_190; obj* x_193; obj* x_194; 
lean::dec(x_3);
lean::dec(x_129);
x_190 = lean::cnstr_get(x_183, 0);
lean::inc(x_190);
lean::dec(x_183);
if (lean::is_scalar(x_178)) {
 x_193 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_193 = x_178;
 lean::cnstr_set_tag(x_178, 0);
}
lean::cnstr_set(x_193, 0, x_190);
if (lean::is_scalar(x_187)) {
 x_194 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_194 = x_187;
}
lean::cnstr_set(x_194, 0, x_193);
lean::cnstr_set(x_194, 1, x_185);
return x_194;
}
else
{
obj* x_197; obj* x_198; obj* x_200; 
lean::dec(x_183);
lean::inc(x_3);
x_197 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_129, x_3, x_185);
x_198 = lean::cnstr_get(x_197, 0);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_197, 1);
lean::inc(x_200);
lean::dec(x_197);
if (lean::obj_tag(x_198) == 0)
{
obj* x_204; obj* x_207; obj* x_208; 
lean::dec(x_3);
x_204 = lean::cnstr_get(x_198, 0);
lean::inc(x_204);
lean::dec(x_198);
if (lean::is_scalar(x_178)) {
 x_207 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_207 = x_178;
 lean::cnstr_set_tag(x_178, 0);
}
lean::cnstr_set(x_207, 0, x_204);
if (lean::is_scalar(x_187)) {
 x_208 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_208 = x_187;
}
lean::cnstr_set(x_208, 0, x_207);
lean::cnstr_set(x_208, 1, x_200);
return x_208;
}
else
{
obj* x_212; obj* x_214; 
lean::dec(x_178);
lean::dec(x_187);
lean::dec(x_198);
x_212 = l_lean_ir_cpp_emit__assign__lit___closed__6;
lean::inc(x_212);
x_214 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_212, x_3, x_200);
return x_214;
}
}
}
else
{
obj* x_215; obj* x_218; obj* x_219; obj* x_221; obj* x_223; 
x_215 = l_lean_ir_cpp_emit__assign__lit___closed__7;
lean::inc(x_3);
lean::inc(x_215);
x_218 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_215, x_3, x_148);
x_219 = lean::cnstr_get(x_218, 0);
lean::inc(x_219);
x_221 = lean::cnstr_get(x_218, 1);
lean::inc(x_221);
if (lean::is_shared(x_218)) {
 lean::dec(x_218);
 x_223 = lean::box(0);
} else {
 lean::cnstr_release(x_218, 0);
 lean::cnstr_release(x_218, 1);
 x_223 = x_218;
}
if (lean::obj_tag(x_219) == 0)
{
obj* x_226; obj* x_229; obj* x_230; 
lean::dec(x_3);
lean::dec(x_129);
x_226 = lean::cnstr_get(x_219, 0);
lean::inc(x_226);
lean::dec(x_219);
if (lean::is_scalar(x_178)) {
 x_229 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_229 = x_178;
 lean::cnstr_set_tag(x_178, 0);
}
lean::cnstr_set(x_229, 0, x_226);
if (lean::is_scalar(x_223)) {
 x_230 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_230 = x_223;
}
lean::cnstr_set(x_230, 0, x_229);
lean::cnstr_set(x_230, 1, x_221);
return x_230;
}
else
{
obj* x_232; obj* x_235; obj* x_236; obj* x_238; 
lean::dec(x_219);
x_232 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_232);
x_235 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_232, x_3, x_221);
x_236 = lean::cnstr_get(x_235, 0);
lean::inc(x_236);
x_238 = lean::cnstr_get(x_235, 1);
lean::inc(x_238);
lean::dec(x_235);
if (lean::obj_tag(x_236) == 0)
{
obj* x_243; obj* x_246; obj* x_247; 
lean::dec(x_3);
lean::dec(x_129);
x_243 = lean::cnstr_get(x_236, 0);
lean::inc(x_243);
lean::dec(x_236);
if (lean::is_scalar(x_178)) {
 x_246 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_246 = x_178;
 lean::cnstr_set_tag(x_178, 0);
}
lean::cnstr_set(x_246, 0, x_243);
if (lean::is_scalar(x_223)) {
 x_247 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_247 = x_223;
}
lean::cnstr_set(x_247, 0, x_246);
lean::cnstr_set(x_247, 1, x_238);
return x_247;
}
else
{
obj* x_250; obj* x_251; obj* x_253; 
lean::dec(x_236);
lean::inc(x_3);
x_250 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_129, x_3, x_238);
x_251 = lean::cnstr_get(x_250, 0);
lean::inc(x_251);
x_253 = lean::cnstr_get(x_250, 1);
lean::inc(x_253);
lean::dec(x_250);
if (lean::obj_tag(x_251) == 0)
{
obj* x_257; obj* x_260; obj* x_261; 
lean::dec(x_3);
x_257 = lean::cnstr_get(x_251, 0);
lean::inc(x_257);
lean::dec(x_251);
if (lean::is_scalar(x_178)) {
 x_260 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_260 = x_178;
 lean::cnstr_set_tag(x_178, 0);
}
lean::cnstr_set(x_260, 0, x_257);
if (lean::is_scalar(x_223)) {
 x_261 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_261 = x_223;
}
lean::cnstr_set(x_261, 0, x_260);
lean::cnstr_set(x_261, 1, x_253);
return x_261;
}
else
{
obj* x_263; obj* x_266; obj* x_267; obj* x_269; 
lean::dec(x_251);
x_263 = l_lean_ir_cpp_emit__num__suffix___main___closed__1;
lean::inc(x_3);
lean::inc(x_263);
x_266 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_263, x_3, x_253);
x_267 = lean::cnstr_get(x_266, 0);
lean::inc(x_267);
x_269 = lean::cnstr_get(x_266, 1);
lean::inc(x_269);
lean::dec(x_266);
if (lean::obj_tag(x_267) == 0)
{
obj* x_273; obj* x_276; obj* x_277; 
lean::dec(x_3);
x_273 = lean::cnstr_get(x_267, 0);
lean::inc(x_273);
lean::dec(x_267);
if (lean::is_scalar(x_178)) {
 x_276 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_276 = x_178;
 lean::cnstr_set_tag(x_178, 0);
}
lean::cnstr_set(x_276, 0, x_273);
if (lean::is_scalar(x_223)) {
 x_277 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_277 = x_223;
}
lean::cnstr_set(x_277, 0, x_276);
lean::cnstr_set(x_277, 1, x_269);
return x_277;
}
else
{
obj* x_278; obj* x_281; obj* x_283; obj* x_284; obj* x_286; 
x_278 = lean::cnstr_get(x_267, 0);
lean::inc(x_278);
lean::dec(x_267);
x_281 = l_option_has__repr___rarg___closed__3;
lean::inc(x_281);
x_283 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_281, x_3, x_269);
x_284 = lean::cnstr_get(x_283, 0);
lean::inc(x_284);
x_286 = lean::cnstr_get(x_283, 1);
lean::inc(x_286);
lean::dec(x_283);
if (lean::obj_tag(x_284) == 0)
{
obj* x_290; obj* x_293; obj* x_294; 
lean::dec(x_278);
x_290 = lean::cnstr_get(x_284, 0);
lean::inc(x_290);
lean::dec(x_284);
if (lean::is_scalar(x_178)) {
 x_293 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_293 = x_178;
 lean::cnstr_set_tag(x_178, 0);
}
lean::cnstr_set(x_293, 0, x_290);
if (lean::is_scalar(x_223)) {
 x_294 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_294 = x_223;
}
lean::cnstr_set(x_294, 0, x_293);
lean::cnstr_set(x_294, 1, x_286);
return x_294;
}
else
{
obj* x_296; obj* x_297; 
lean::dec(x_284);
if (lean::is_scalar(x_178)) {
 x_296 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_296 = x_178;
}
lean::cnstr_set(x_296, 0, x_278);
if (lean::is_scalar(x_223)) {
 x_297 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_297 = x_223;
}
lean::cnstr_set(x_297, 0, x_296);
lean::cnstr_set(x_297, 1, x_286);
return x_297;
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
obj* x_300; obj* x_301; obj* x_303; obj* x_305; 
lean::dec(x_132);
lean::inc(x_3);
x_300 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_301 = lean::cnstr_get(x_300, 0);
lean::inc(x_301);
x_303 = lean::cnstr_get(x_300, 1);
lean::inc(x_303);
if (lean::is_shared(x_300)) {
 lean::dec(x_300);
 x_305 = lean::box(0);
} else {
 lean::cnstr_release(x_300, 0);
 lean::cnstr_release(x_300, 1);
 x_305 = x_300;
}
if (lean::obj_tag(x_301) == 0)
{
obj* x_308; obj* x_310; obj* x_311; obj* x_312; 
lean::dec(x_3);
lean::dec(x_129);
x_308 = lean::cnstr_get(x_301, 0);
lean::inc(x_308);
if (lean::is_shared(x_301)) {
 lean::dec(x_301);
 x_310 = lean::box(0);
} else {
 lean::cnstr_release(x_301, 0);
 x_310 = x_301;
}
if (lean::is_scalar(x_310)) {
 x_311 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_311 = x_310;
}
lean::cnstr_set(x_311, 0, x_308);
if (lean::is_scalar(x_305)) {
 x_312 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_312 = x_305;
}
lean::cnstr_set(x_312, 0, x_311);
lean::cnstr_set(x_312, 1, x_303);
return x_312;
}
else
{
obj* x_313; obj* x_314; obj* x_317; obj* x_318; obj* x_320; 
if (lean::is_shared(x_301)) {
 lean::dec(x_301);
 x_313 = lean::box(0);
} else {
 lean::cnstr_release(x_301, 0);
 x_313 = x_301;
}
x_314 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
lean::inc(x_314);
x_317 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_314, x_3, x_303);
x_318 = lean::cnstr_get(x_317, 0);
lean::inc(x_318);
x_320 = lean::cnstr_get(x_317, 1);
lean::inc(x_320);
lean::dec(x_317);
if (lean::obj_tag(x_318) == 0)
{
obj* x_325; obj* x_328; obj* x_329; 
lean::dec(x_3);
lean::dec(x_129);
x_325 = lean::cnstr_get(x_318, 0);
lean::inc(x_325);
lean::dec(x_318);
if (lean::is_scalar(x_313)) {
 x_328 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_328 = x_313;
 lean::cnstr_set_tag(x_313, 0);
}
lean::cnstr_set(x_328, 0, x_325);
if (lean::is_scalar(x_305)) {
 x_329 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_329 = x_305;
}
lean::cnstr_set(x_329, 0, x_328);
lean::cnstr_set(x_329, 1, x_320);
return x_329;
}
else
{
obj* x_332; obj* x_333; obj* x_335; 
lean::dec(x_318);
lean::inc(x_3);
x_332 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_129, x_3, x_320);
x_333 = lean::cnstr_get(x_332, 0);
lean::inc(x_333);
x_335 = lean::cnstr_get(x_332, 1);
lean::inc(x_335);
lean::dec(x_332);
if (lean::obj_tag(x_333) == 0)
{
obj* x_339; obj* x_342; obj* x_343; 
lean::dec(x_3);
x_339 = lean::cnstr_get(x_333, 0);
lean::inc(x_339);
lean::dec(x_333);
if (lean::is_scalar(x_313)) {
 x_342 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_342 = x_313;
 lean::cnstr_set_tag(x_313, 0);
}
lean::cnstr_set(x_342, 0, x_339);
if (lean::is_scalar(x_305)) {
 x_343 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_343 = x_305;
}
lean::cnstr_set(x_343, 0, x_342);
lean::cnstr_set(x_343, 1, x_335);
return x_343;
}
else
{
obj* x_347; 
lean::dec(x_313);
lean::dec(x_305);
lean::dec(x_333);
x_347 = l_lean_ir_cpp_emit__num__suffix___main(x_1, x_3, x_335);
return x_347;
}
}
}
}
}
default:
{
obj* x_348; obj* x_352; obj* x_353; obj* x_355; obj* x_357; 
x_348 = lean::cnstr_get(x_2, 0);
lean::inc(x_348);
lean::dec(x_2);
lean::inc(x_3);
x_352 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_353 = lean::cnstr_get(x_352, 0);
lean::inc(x_353);
x_355 = lean::cnstr_get(x_352, 1);
lean::inc(x_355);
if (lean::is_shared(x_352)) {
 lean::dec(x_352);
 x_357 = lean::box(0);
} else {
 lean::cnstr_release(x_352, 0);
 lean::cnstr_release(x_352, 1);
 x_357 = x_352;
}
if (lean::obj_tag(x_353) == 0)
{
obj* x_360; obj* x_362; obj* x_363; obj* x_364; 
lean::dec(x_3);
lean::dec(x_348);
x_360 = lean::cnstr_get(x_353, 0);
lean::inc(x_360);
if (lean::is_shared(x_353)) {
 lean::dec(x_353);
 x_362 = lean::box(0);
} else {
 lean::cnstr_release(x_353, 0);
 x_362 = x_353;
}
if (lean::is_scalar(x_362)) {
 x_363 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_363 = x_362;
}
lean::cnstr_set(x_363, 0, x_360);
if (lean::is_scalar(x_357)) {
 x_364 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_364 = x_357;
}
lean::cnstr_set(x_364, 0, x_363);
lean::cnstr_set(x_364, 1, x_355);
return x_364;
}
else
{
obj* x_365; obj* x_366; obj* x_369; obj* x_370; obj* x_372; 
if (lean::is_shared(x_353)) {
 lean::dec(x_353);
 x_365 = lean::box(0);
} else {
 lean::cnstr_release(x_353, 0);
 x_365 = x_353;
}
x_366 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
lean::inc(x_366);
x_369 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_366, x_3, x_355);
x_370 = lean::cnstr_get(x_369, 0);
lean::inc(x_370);
x_372 = lean::cnstr_get(x_369, 1);
lean::inc(x_372);
lean::dec(x_369);
if (lean::obj_tag(x_370) == 0)
{
obj* x_377; obj* x_380; obj* x_381; 
lean::dec(x_3);
lean::dec(x_348);
x_377 = lean::cnstr_get(x_370, 0);
lean::inc(x_377);
lean::dec(x_370);
if (lean::is_scalar(x_365)) {
 x_380 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_380 = x_365;
 lean::cnstr_set_tag(x_365, 0);
}
lean::cnstr_set(x_380, 0, x_377);
if (lean::is_scalar(x_357)) {
 x_381 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_381 = x_357;
}
lean::cnstr_set(x_381, 0, x_380);
lean::cnstr_set(x_381, 1, x_372);
return x_381;
}
else
{
obj* x_385; 
lean::dec(x_370);
lean::dec(x_365);
lean::dec(x_357);
x_385 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_348, x_3, x_372);
return x_385;
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__assign__lit___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
x_6 = l_lean_ir_cpp_emit__assign__lit(x_0, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* _init_l_lean_ir_cpp_unop2cpp___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::inc_ref");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_unop2cpp___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::dec_ref");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_unop2cpp___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::dec_shared_ref");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_unop2cpp___main___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::inc");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_unop2cpp___main___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::dec");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_unop2cpp___main___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("free");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_unop2cpp___main___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::dealloc");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_unop2cpp___main___closed__8() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::array_pop");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_unop2cpp___main___closed__9() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::sarray_pop");
return x_0;
}
}
obj* l_lean_ir_cpp_unop2cpp___main(uint8 x_0) {
_start:
{
switch (x_0) {
case 0:
{
obj* x_1; 
x_1 = l_lean_ir_cpp_unop2cpp___main___closed__1;
lean::inc(x_1);
return x_1;
}
case 1:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_unop2cpp___main___closed__2;
lean::inc(x_3);
return x_3;
}
case 2:
{
obj* x_5; 
x_5 = l_lean_ir_cpp_unop2cpp___main___closed__3;
lean::inc(x_5);
return x_5;
}
case 3:
{
obj* x_7; 
x_7 = l_lean_ir_cpp_unop2cpp___main___closed__4;
lean::inc(x_7);
return x_7;
}
case 4:
{
obj* x_9; 
x_9 = l_lean_ir_cpp_unop2cpp___main___closed__5;
lean::inc(x_9);
return x_9;
}
case 5:
{
obj* x_11; 
x_11 = l_lean_ir_cpp_unop2cpp___main___closed__6;
lean::inc(x_11);
return x_11;
}
case 6:
{
obj* x_13; 
x_13 = l_lean_ir_cpp_unop2cpp___main___closed__7;
lean::inc(x_13);
return x_13;
}
case 7:
{
obj* x_15; 
x_15 = l_lean_ir_cpp_unop2cpp___main___closed__8;
lean::inc(x_15);
return x_15;
}
default:
{
obj* x_17; 
x_17 = l_lean_ir_cpp_unop2cpp___main___closed__9;
lean::inc(x_17);
return x_17;
}
}
}
}
obj* l_lean_ir_cpp_unop2cpp___main___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_cpp_unop2cpp___main(x_1);
return x_2;
}
}
obj* l_lean_ir_cpp_unop2cpp(uint8 x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_cpp_unop2cpp___main(x_0);
return x_1;
}
}
obj* l_lean_ir_cpp_unop2cpp___boxed(obj* x_0) {
_start:
{
uint8 x_1; obj* x_2; 
x_1 = lean::unbox(x_0);
x_2 = l_lean_ir_cpp_unop2cpp(x_1);
return x_2;
}
}
obj* l_lean_ir_cpp_emit__unop(uint8 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_4 = l_lean_ir_cpp_unop2cpp___main(x_0);
lean::inc(x_2);
x_6 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_4, x_2, x_3);
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
x_20 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_20);
x_23 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_20, x_2, x_9);
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
 lean::cnstr_set_tag(x_19, 0);
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
x_38 = l_lean_ir_cpp_emit__var(x_1, x_2, x_26);
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
 lean::cnstr_set_tag(x_19, 0);
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
x_53 = l_option_has__repr___rarg___closed__3;
lean::inc(x_53);
x_55 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_53, x_2, x_41);
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
 lean::cnstr_set_tag(x_19, 0);
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
obj* l_lean_ir_cpp_emit__unop___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_0);
x_5 = l_lean_ir_cpp_emit__unop(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_ir_cpp_emit__apply___closed__1() {
_start:
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
obj* _init_l_lean_ir_cpp_emit__apply___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__var), 3, 0);
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__apply___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = apply_");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__apply___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("; }");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__apply___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("as");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__apply___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("}; ");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__apply___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = apply_m");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__apply___closed__8() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("{ obj * as[");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__apply___closed__9() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("] = {");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__apply(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_7 = l_lean_ir_cpp_emit__apply___closed__1;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; uint8 x_18; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_14 = lean::mk_nat_obj(0u);
lean::inc(x_12);
x_16 = l_list_length__aux___main___rarg(x_12, x_14);
x_17 = l_lean_closure__max__args;
x_18 = lean::nat_dec_lt(x_17, x_16);
if (x_18 == 0)
{
obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_28; 
lean::dec(x_12);
lean::dec(x_10);
lean::inc(x_2);
x_25 = l_lean_ir_cpp_emit__var(x_0, x_2, x_3);
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
x_36 = l_lean_ir_cpp_emit__apply___closed__3;
lean::inc(x_2);
lean::inc(x_36);
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_36, x_2, x_28);
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
lean::dec(x_16);
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
x_55 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_16, x_2, x_22);
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
 lean::cnstr_set_tag(x_53, 0);
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
x_69 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_69);
x_72 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_69, x_2, x_58);
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
 lean::cnstr_set_tag(x_53, 0);
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
x_86 = l_lean_ir_cpp_emit__apply___closed__2;
x_87 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_2);
lean::inc(x_87);
lean::inc(x_86);
x_91 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_86, x_87, x_1, x_2, x_75);
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
 lean::cnstr_set_tag(x_53, 0);
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
x_106 = l_option_has__repr___rarg___closed__3;
lean::inc(x_106);
x_108 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_106, x_2, x_94);
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
 lean::cnstr_set_tag(x_53, 0);
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
obj* x_124; obj* x_125; obj* x_127; obj* x_128; obj* x_130; obj* x_131; obj* x_133; obj* x_134; obj* x_136; obj* x_139; obj* x_140; obj* x_142; 
lean::dec(x_1);
x_136 = l_lean_ir_cpp_emit__apply___closed__8;
lean::inc(x_2);
lean::inc(x_136);
x_139 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_136, x_2, x_3);
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_139, 1);
lean::inc(x_142);
lean::dec(x_139);
if (lean::obj_tag(x_140) == 0)
{
obj* x_145; obj* x_147; obj* x_148; 
x_145 = lean::cnstr_get(x_140, 0);
lean::inc(x_145);
if (lean::is_shared(x_140)) {
 lean::dec(x_140);
 x_147 = lean::box(0);
} else {
 lean::cnstr_release(x_140, 0);
 x_147 = x_140;
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_145);
x_133 = x_148;
x_134 = x_142;
goto lbl_135;
}
else
{
obj* x_149; obj* x_152; obj* x_153; obj* x_155; 
if (lean::is_shared(x_140)) {
 lean::dec(x_140);
 x_149 = lean::box(0);
} else {
 lean::cnstr_release(x_140, 0);
 x_149 = x_140;
}
lean::inc(x_2);
lean::inc(x_16);
x_152 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_16, x_2, x_142);
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_152, 1);
lean::inc(x_155);
lean::dec(x_152);
if (lean::obj_tag(x_153) == 0)
{
obj* x_158; obj* x_161; 
x_158 = lean::cnstr_get(x_153, 0);
lean::inc(x_158);
lean::dec(x_153);
if (lean::is_scalar(x_149)) {
 x_161 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_161 = x_149;
 lean::cnstr_set_tag(x_149, 0);
}
lean::cnstr_set(x_161, 0, x_158);
x_133 = x_161;
x_134 = x_155;
goto lbl_135;
}
else
{
obj* x_164; obj* x_167; obj* x_168; obj* x_170; 
lean::dec(x_153);
lean::dec(x_149);
x_164 = l_lean_ir_cpp_emit__apply___closed__9;
lean::inc(x_2);
lean::inc(x_164);
x_167 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_164, x_2, x_155);
x_168 = lean::cnstr_get(x_167, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_167, 1);
lean::inc(x_170);
lean::dec(x_167);
x_133 = x_168;
x_134 = x_170;
goto lbl_135;
}
}
lbl_126:
{
if (lean::obj_tag(x_124) == 0)
{
obj* x_174; obj* x_176; obj* x_177; obj* x_178; 
lean::dec(x_2);
x_174 = lean::cnstr_get(x_124, 0);
lean::inc(x_174);
if (lean::is_shared(x_124)) {
 lean::dec(x_124);
 x_176 = lean::box(0);
} else {
 lean::cnstr_release(x_124, 0);
 x_176 = x_124;
}
if (lean::is_scalar(x_176)) {
 x_177 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_177 = x_176;
}
lean::cnstr_set(x_177, 0, x_174);
x_178 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_178, 0, x_177);
lean::cnstr_set(x_178, 1, x_125);
return x_178;
}
else
{
obj* x_180; obj* x_182; 
lean::dec(x_124);
x_180 = l_lean_ir_cpp_emit__apply___closed__4;
lean::inc(x_180);
x_182 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_180, x_2, x_125);
return x_182;
}
}
lbl_129:
{
if (lean::obj_tag(x_127) == 0)
{
obj* x_183; obj* x_185; obj* x_186; 
x_183 = lean::cnstr_get(x_127, 0);
lean::inc(x_183);
if (lean::is_shared(x_127)) {
 lean::dec(x_127);
 x_185 = lean::box(0);
} else {
 lean::cnstr_release(x_127, 0);
 x_185 = x_127;
}
if (lean::is_scalar(x_185)) {
 x_186 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_186 = x_185;
}
lean::cnstr_set(x_186, 0, x_183);
x_124 = x_186;
x_125 = x_128;
goto lbl_126;
}
else
{
obj* x_187; obj* x_188; obj* x_191; obj* x_192; obj* x_194; 
if (lean::is_shared(x_127)) {
 lean::dec(x_127);
 x_187 = lean::box(0);
} else {
 lean::cnstr_release(x_127, 0);
 x_187 = x_127;
}
x_188 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_188);
x_191 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_188, x_2, x_128);
x_192 = lean::cnstr_get(x_191, 0);
lean::inc(x_192);
x_194 = lean::cnstr_get(x_191, 1);
lean::inc(x_194);
lean::dec(x_191);
if (lean::obj_tag(x_192) == 0)
{
obj* x_197; obj* x_200; 
x_197 = lean::cnstr_get(x_192, 0);
lean::inc(x_197);
lean::dec(x_192);
if (lean::is_scalar(x_187)) {
 x_200 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_200 = x_187;
 lean::cnstr_set_tag(x_187, 0);
}
lean::cnstr_set(x_200, 0, x_197);
x_124 = x_200;
x_125 = x_194;
goto lbl_126;
}
else
{
obj* x_202; obj* x_205; obj* x_206; obj* x_208; 
lean::dec(x_192);
x_202 = l_lean_ir_cpp_emit__apply___closed__5;
lean::inc(x_2);
lean::inc(x_202);
x_205 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_202, x_2, x_194);
x_206 = lean::cnstr_get(x_205, 0);
lean::inc(x_206);
x_208 = lean::cnstr_get(x_205, 1);
lean::inc(x_208);
lean::dec(x_205);
if (lean::obj_tag(x_206) == 0)
{
obj* x_211; obj* x_214; 
x_211 = lean::cnstr_get(x_206, 0);
lean::inc(x_211);
lean::dec(x_206);
if (lean::is_scalar(x_187)) {
 x_214 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_214 = x_187;
 lean::cnstr_set_tag(x_187, 0);
}
lean::cnstr_set(x_214, 0, x_211);
x_124 = x_214;
x_125 = x_208;
goto lbl_126;
}
else
{
obj* x_215; obj* x_218; obj* x_221; obj* x_222; obj* x_224; 
x_215 = lean::cnstr_get(x_206, 0);
lean::inc(x_215);
lean::dec(x_206);
x_218 = l_option_has__repr___rarg___closed__3;
lean::inc(x_2);
lean::inc(x_218);
x_221 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_218, x_2, x_208);
x_222 = lean::cnstr_get(x_221, 0);
lean::inc(x_222);
x_224 = lean::cnstr_get(x_221, 1);
lean::inc(x_224);
lean::dec(x_221);
if (lean::obj_tag(x_222) == 0)
{
obj* x_228; obj* x_231; 
lean::dec(x_215);
x_228 = lean::cnstr_get(x_222, 0);
lean::inc(x_228);
lean::dec(x_222);
if (lean::is_scalar(x_187)) {
 x_231 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_231 = x_187;
 lean::cnstr_set_tag(x_187, 0);
}
lean::cnstr_set(x_231, 0, x_228);
x_124 = x_231;
x_125 = x_224;
goto lbl_126;
}
else
{
obj* x_233; 
lean::dec(x_222);
if (lean::is_scalar(x_187)) {
 x_233 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_233 = x_187;
}
lean::cnstr_set(x_233, 0, x_215);
x_124 = x_233;
x_125 = x_224;
goto lbl_126;
}
}
}
}
}
lbl_132:
{
if (lean::obj_tag(x_130) == 0)
{
obj* x_236; obj* x_238; obj* x_239; 
lean::dec(x_16);
lean::dec(x_10);
x_236 = lean::cnstr_get(x_130, 0);
lean::inc(x_236);
if (lean::is_shared(x_130)) {
 lean::dec(x_130);
 x_238 = lean::box(0);
} else {
 lean::cnstr_release(x_130, 0);
 x_238 = x_130;
}
if (lean::is_scalar(x_238)) {
 x_239 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_239 = x_238;
}
lean::cnstr_set(x_239, 0, x_236);
x_124 = x_239;
x_125 = x_131;
goto lbl_126;
}
else
{
obj* x_240; obj* x_241; obj* x_244; obj* x_245; obj* x_247; 
if (lean::is_shared(x_130)) {
 lean::dec(x_130);
 x_240 = lean::box(0);
} else {
 lean::cnstr_release(x_130, 0);
 x_240 = x_130;
}
x_241 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_241);
x_244 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_241, x_2, x_131);
x_245 = lean::cnstr_get(x_244, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_244, 1);
lean::inc(x_247);
lean::dec(x_244);
if (lean::obj_tag(x_245) == 0)
{
obj* x_252; obj* x_255; 
lean::dec(x_16);
lean::dec(x_10);
x_252 = lean::cnstr_get(x_245, 0);
lean::inc(x_252);
lean::dec(x_245);
if (lean::is_scalar(x_240)) {
 x_255 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_255 = x_240;
 lean::cnstr_set_tag(x_240, 0);
}
lean::cnstr_set(x_255, 0, x_252);
x_124 = x_255;
x_125 = x_247;
goto lbl_126;
}
else
{
obj* x_258; obj* x_259; obj* x_261; 
lean::dec(x_245);
lean::inc(x_2);
x_258 = l_lean_ir_cpp_emit__var(x_10, x_2, x_247);
x_259 = lean::cnstr_get(x_258, 0);
lean::inc(x_259);
x_261 = lean::cnstr_get(x_258, 1);
lean::inc(x_261);
lean::dec(x_258);
if (lean::obj_tag(x_259) == 0)
{
obj* x_265; obj* x_268; 
lean::dec(x_16);
x_265 = lean::cnstr_get(x_259, 0);
lean::inc(x_265);
lean::dec(x_259);
if (lean::is_scalar(x_240)) {
 x_268 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_268 = x_240;
 lean::cnstr_set_tag(x_240, 0);
}
lean::cnstr_set(x_268, 0, x_265);
x_127 = x_268;
x_128 = x_261;
goto lbl_129;
}
else
{
obj* x_270; obj* x_273; obj* x_274; obj* x_276; 
lean::dec(x_259);
x_270 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_270);
x_273 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_270, x_2, x_261);
x_274 = lean::cnstr_get(x_273, 0);
lean::inc(x_274);
x_276 = lean::cnstr_get(x_273, 1);
lean::inc(x_276);
lean::dec(x_273);
if (lean::obj_tag(x_274) == 0)
{
obj* x_280; obj* x_283; 
lean::dec(x_16);
x_280 = lean::cnstr_get(x_274, 0);
lean::inc(x_280);
lean::dec(x_274);
if (lean::is_scalar(x_240)) {
 x_283 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_283 = x_240;
 lean::cnstr_set_tag(x_240, 0);
}
lean::cnstr_set(x_283, 0, x_280);
x_127 = x_283;
x_128 = x_276;
goto lbl_129;
}
else
{
obj* x_287; obj* x_288; obj* x_290; 
lean::dec(x_240);
lean::dec(x_274);
lean::inc(x_2);
x_287 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_16, x_2, x_276);
x_288 = lean::cnstr_get(x_287, 0);
lean::inc(x_288);
x_290 = lean::cnstr_get(x_287, 1);
lean::inc(x_290);
lean::dec(x_287);
x_127 = x_288;
x_128 = x_290;
goto lbl_129;
}
}
}
}
}
lbl_135:
{
if (lean::obj_tag(x_133) == 0)
{
obj* x_295; obj* x_297; obj* x_298; 
lean::dec(x_12);
lean::dec(x_0);
x_295 = lean::cnstr_get(x_133, 0);
lean::inc(x_295);
if (lean::is_shared(x_133)) {
 lean::dec(x_133);
 x_297 = lean::box(0);
} else {
 lean::cnstr_release(x_133, 0);
 x_297 = x_133;
}
if (lean::is_scalar(x_297)) {
 x_298 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_298 = x_297;
}
lean::cnstr_set(x_298, 0, x_295);
x_130 = x_298;
x_131 = x_134;
goto lbl_132;
}
else
{
obj* x_299; obj* x_300; obj* x_301; obj* x_305; obj* x_306; obj* x_308; 
if (lean::is_shared(x_133)) {
 lean::dec(x_133);
 x_299 = lean::box(0);
} else {
 lean::cnstr_release(x_133, 0);
 x_299 = x_133;
}
x_300 = l_lean_ir_cpp_emit__apply___closed__2;
x_301 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_2);
lean::inc(x_301);
lean::inc(x_300);
x_305 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_300, x_301, x_12, x_2, x_134);
x_306 = lean::cnstr_get(x_305, 0);
lean::inc(x_306);
x_308 = lean::cnstr_get(x_305, 1);
lean::inc(x_308);
lean::dec(x_305);
if (lean::obj_tag(x_306) == 0)
{
obj* x_312; obj* x_315; 
lean::dec(x_0);
x_312 = lean::cnstr_get(x_306, 0);
lean::inc(x_312);
lean::dec(x_306);
if (lean::is_scalar(x_299)) {
 x_315 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_315 = x_299;
 lean::cnstr_set_tag(x_299, 0);
}
lean::cnstr_set(x_315, 0, x_312);
x_130 = x_315;
x_131 = x_308;
goto lbl_132;
}
else
{
obj* x_317; obj* x_320; obj* x_321; obj* x_323; 
lean::dec(x_306);
x_317 = l_lean_ir_cpp_emit__apply___closed__6;
lean::inc(x_2);
lean::inc(x_317);
x_320 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_317, x_2, x_308);
x_321 = lean::cnstr_get(x_320, 0);
lean::inc(x_321);
x_323 = lean::cnstr_get(x_320, 1);
lean::inc(x_323);
lean::dec(x_320);
if (lean::obj_tag(x_321) == 0)
{
obj* x_327; obj* x_330; 
lean::dec(x_0);
x_327 = lean::cnstr_get(x_321, 0);
lean::inc(x_327);
lean::dec(x_321);
if (lean::is_scalar(x_299)) {
 x_330 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_330 = x_299;
 lean::cnstr_set_tag(x_299, 0);
}
lean::cnstr_set(x_330, 0, x_327);
x_130 = x_330;
x_131 = x_323;
goto lbl_132;
}
else
{
obj* x_333; obj* x_334; obj* x_336; 
lean::dec(x_321);
lean::inc(x_2);
x_333 = l_lean_ir_cpp_emit__var(x_0, x_2, x_323);
x_334 = lean::cnstr_get(x_333, 0);
lean::inc(x_334);
x_336 = lean::cnstr_get(x_333, 1);
lean::inc(x_336);
lean::dec(x_333);
if (lean::obj_tag(x_334) == 0)
{
obj* x_339; obj* x_342; 
x_339 = lean::cnstr_get(x_334, 0);
lean::inc(x_339);
lean::dec(x_334);
if (lean::is_scalar(x_299)) {
 x_342 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_342 = x_299;
 lean::cnstr_set_tag(x_299, 0);
}
lean::cnstr_set(x_342, 0, x_339);
x_130 = x_342;
x_131 = x_336;
goto lbl_132;
}
else
{
obj* x_345; obj* x_348; obj* x_349; obj* x_351; 
lean::dec(x_334);
lean::dec(x_299);
x_345 = l_lean_ir_cpp_emit__apply___closed__7;
lean::inc(x_2);
lean::inc(x_345);
x_348 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_345, x_2, x_336);
x_349 = lean::cnstr_get(x_348, 0);
lean::inc(x_349);
x_351 = lean::cnstr_get(x_348, 1);
lean::inc(x_351);
lean::dec(x_348);
x_130 = x_349;
x_131 = x_351;
goto lbl_132;
}
}
}
}
}
}
}
}
}
obj* _init_l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(";\nlean::closure_set_arg");
return x_0;
}
}
obj* l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
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
x_24 = l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_24);
x_27 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_24, x_3, x_4);
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
x_40 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_40);
x_43 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_40, x_3, x_30);
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
 lean::cnstr_set_tag(x_39, 0);
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
x_58 = l_lean_ir_cpp_emit__var(x_0, x_3, x_46);
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
 lean::cnstr_set_tag(x_39, 0);
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
x_70 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_70);
x_73 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_70, x_3, x_61);
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
 lean::cnstr_set_tag(x_39, 0);
}
lean::cnstr_set(x_83, 0, x_80);
x_21 = x_83;
x_22 = x_76;
goto lbl_23;
}
else
{
obj* x_87; obj* x_88; obj* x_90; 
lean::dec(x_39);
lean::dec(x_74);
lean::inc(x_3);
x_87 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_1, x_3, x_76);
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
lean::dec(x_3);
lean::dec(x_0);
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
lean::dec(x_18);
x_1 = x_16;
x_2 = x_12;
x_4 = x_19;
goto _start;
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
x_110 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_110);
x_113 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_110, x_3, x_22);
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
 lean::cnstr_set_tag(x_109, 0);
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
x_126 = l_lean_ir_cpp_emit__var(x_10, x_3, x_116);
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
 lean::cnstr_set_tag(x_109, 0);
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
x_139 = l_option_has__repr___rarg___closed__3;
lean::inc(x_3);
lean::inc(x_139);
x_142 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_139, x_3, x_129);
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
 lean::cnstr_set_tag(x_109, 0);
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
obj* _init_l_lean_ir_cpp_emit__closure___closed__1() {
_start:
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
obj* _init_l_lean_ir_cpp_emit__closure___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::alloc_closure(");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__closure___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("reinterpret_cast<lean::lean_cfun>(");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__closure___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("uncurry");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__closure(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
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
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_17 = l_lean_ir_cpp_emit__closure___closed__1;
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
x_25 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
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
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
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
x_45 = l_lean_ir_cpp_emit__closure___closed__2;
lean::inc(x_3);
lean::inc(x_45);
x_48 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_45, x_3, x_28);
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
lean::dec(x_41);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
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
x_68 = l_lean_ir_cpp_fid2cpp(x_1, x_3, x_51);
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
lean::dec(x_41);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_80 = lean::cnstr_get(x_69, 0);
lean::inc(x_80);
lean::dec(x_69);
if (lean::is_scalar(x_66)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_66;
 lean::cnstr_set_tag(x_66, 0);
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
obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_93; obj* x_95; obj* x_96; uint8 x_97; obj* x_99; obj* x_100; obj* x_103; obj* x_104; obj* x_105; 
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
x_89 = l_lean_ir_decl_header___main(x_20);
x_90 = lean::cnstr_get(x_89, 1);
lean::inc(x_90);
lean::dec(x_89);
x_93 = lean::mk_nat_obj(0u);
lean::inc(x_93);
x_95 = l_list_length__aux___main___rarg(x_90, x_93);
x_96 = l_lean_closure__max__args;
x_97 = lean::nat_dec_lt(x_96, x_95);
lean::inc(x_2);
x_99 = l_list_length__aux___main___rarg(x_2, x_93);
x_100 = l_lean_ir_cpp_emit__closure___closed__3;
lean::inc(x_3);
lean::inc(x_100);
x_103 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_100, x_3, x_71);
if (x_97 == 0)
{
obj* x_107; obj* x_109; 
x_107 = lean::cnstr_get(x_103, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_103, 1);
lean::inc(x_109);
lean::dec(x_103);
if (lean::obj_tag(x_107) == 0)
{
obj* x_113; obj* x_116; 
lean::dec(x_86);
x_113 = lean::cnstr_get(x_107, 0);
lean::inc(x_113);
lean::dec(x_107);
if (lean::is_scalar(x_88)) {
 x_116 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_116 = x_88;
 lean::cnstr_set_tag(x_88, 0);
}
lean::cnstr_set(x_116, 0, x_113);
x_104 = x_116;
x_105 = x_109;
goto lbl_106;
}
else
{
obj* x_120; obj* x_121; obj* x_123; 
lean::dec(x_88);
lean::dec(x_107);
lean::inc(x_3);
x_120 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_86, x_3, x_109);
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_120, 1);
lean::inc(x_123);
lean::dec(x_120);
x_104 = x_121;
x_105 = x_123;
goto lbl_106;
}
}
else
{
obj* x_126; obj* x_128; 
x_126 = lean::cnstr_get(x_103, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_103, 1);
lean::inc(x_128);
lean::dec(x_103);
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
 lean::cnstr_set_tag(x_88, 0);
}
lean::cnstr_set(x_135, 0, x_132);
x_104 = x_135;
x_105 = x_128;
goto lbl_106;
}
else
{
obj* x_138; obj* x_140; obj* x_143; obj* x_144; obj* x_146; 
lean::dec(x_126);
lean::dec(x_88);
x_138 = l_lean_ir_cpp_emit__closure___closed__4;
lean::inc(x_138);
x_140 = lean::string_append(x_138, x_86);
lean::dec(x_86);
lean::inc(x_3);
x_143 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_140, x_3, x_128);
x_144 = lean::cnstr_get(x_143, 0);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_143, 1);
lean::inc(x_146);
lean::dec(x_143);
x_104 = x_144;
x_105 = x_146;
goto lbl_106;
}
}
lbl_106:
{
if (lean::obj_tag(x_104) == 0)
{
obj* x_151; obj* x_154; 
lean::dec(x_99);
lean::dec(x_95);
x_151 = lean::cnstr_get(x_104, 0);
lean::inc(x_151);
lean::dec(x_104);
if (lean::is_scalar(x_66)) {
 x_154 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_154 = x_66;
 lean::cnstr_set_tag(x_66, 0);
}
lean::cnstr_set(x_154, 0, x_151);
x_42 = x_154;
x_43 = x_105;
goto lbl_44;
}
else
{
obj* x_156; obj* x_159; obj* x_160; obj* x_162; 
lean::dec(x_104);
x_156 = l_option_has__repr___rarg___closed__3;
lean::inc(x_3);
lean::inc(x_156);
x_159 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_156, x_3, x_105);
x_160 = lean::cnstr_get(x_159, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_159, 1);
lean::inc(x_162);
lean::dec(x_159);
if (lean::obj_tag(x_160) == 0)
{
obj* x_167; obj* x_170; 
lean::dec(x_99);
lean::dec(x_95);
x_167 = lean::cnstr_get(x_160, 0);
lean::inc(x_167);
lean::dec(x_160);
if (lean::is_scalar(x_66)) {
 x_170 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_170 = x_66;
 lean::cnstr_set_tag(x_66, 0);
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
x_172 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_172);
x_175 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_172, x_3, x_162);
x_176 = lean::cnstr_get(x_175, 0);
lean::inc(x_176);
x_178 = lean::cnstr_get(x_175, 1);
lean::inc(x_178);
lean::dec(x_175);
if (lean::obj_tag(x_176) == 0)
{
obj* x_183; obj* x_186; 
lean::dec(x_99);
lean::dec(x_95);
x_183 = lean::cnstr_get(x_176, 0);
lean::inc(x_183);
lean::dec(x_176);
if (lean::is_scalar(x_66)) {
 x_186 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_186 = x_66;
 lean::cnstr_set_tag(x_66, 0);
}
lean::cnstr_set(x_186, 0, x_183);
x_42 = x_186;
x_43 = x_178;
goto lbl_44;
}
else
{
obj* x_189; obj* x_190; obj* x_192; 
lean::dec(x_176);
lean::inc(x_3);
x_189 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_95, x_3, x_178);
x_190 = lean::cnstr_get(x_189, 0);
lean::inc(x_190);
x_192 = lean::cnstr_get(x_189, 1);
lean::inc(x_192);
lean::dec(x_189);
if (lean::obj_tag(x_190) == 0)
{
obj* x_196; obj* x_199; 
lean::dec(x_99);
x_196 = lean::cnstr_get(x_190, 0);
lean::inc(x_196);
lean::dec(x_190);
if (lean::is_scalar(x_66)) {
 x_199 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_199 = x_66;
 lean::cnstr_set_tag(x_66, 0);
}
lean::cnstr_set(x_199, 0, x_196);
x_42 = x_199;
x_43 = x_192;
goto lbl_44;
}
else
{
obj* x_203; obj* x_204; obj* x_206; 
lean::dec(x_190);
lean::inc(x_3);
lean::inc(x_172);
x_203 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_172, x_3, x_192);
x_204 = lean::cnstr_get(x_203, 0);
lean::inc(x_204);
x_206 = lean::cnstr_get(x_203, 1);
lean::inc(x_206);
lean::dec(x_203);
if (lean::obj_tag(x_204) == 0)
{
obj* x_210; obj* x_213; 
lean::dec(x_99);
x_210 = lean::cnstr_get(x_204, 0);
lean::inc(x_210);
lean::dec(x_204);
if (lean::is_scalar(x_66)) {
 x_213 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_213 = x_66;
 lean::cnstr_set_tag(x_66, 0);
}
lean::cnstr_set(x_213, 0, x_210);
x_42 = x_213;
x_43 = x_206;
goto lbl_44;
}
else
{
obj* x_217; obj* x_218; obj* x_220; 
lean::dec(x_66);
lean::dec(x_204);
lean::inc(x_3);
x_217 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_99, x_3, x_206);
x_218 = lean::cnstr_get(x_217, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get(x_217, 1);
lean::inc(x_220);
lean::dec(x_217);
x_42 = x_218;
x_43 = x_220;
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
obj* x_226; obj* x_229; obj* x_230; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_226 = lean::cnstr_get(x_42, 0);
lean::inc(x_226);
lean::dec(x_42);
if (lean::is_scalar(x_41)) {
 x_229 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_229 = x_41;
 lean::cnstr_set_tag(x_41, 0);
}
lean::cnstr_set(x_229, 0, x_226);
if (lean::is_scalar(x_30)) {
 x_230 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_230 = x_30;
}
lean::cnstr_set(x_230, 0, x_229);
lean::cnstr_set(x_230, 1, x_43);
return x_230;
}
else
{
obj* x_232; obj* x_235; obj* x_236; obj* x_238; 
lean::dec(x_42);
x_232 = l_option_has__repr___rarg___closed__3;
lean::inc(x_3);
lean::inc(x_232);
x_235 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_232, x_3, x_43);
x_236 = lean::cnstr_get(x_235, 0);
lean::inc(x_236);
x_238 = lean::cnstr_get(x_235, 1);
lean::inc(x_238);
lean::dec(x_235);
if (lean::obj_tag(x_236) == 0)
{
obj* x_244; obj* x_247; obj* x_248; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_244 = lean::cnstr_get(x_236, 0);
lean::inc(x_244);
lean::dec(x_236);
if (lean::is_scalar(x_41)) {
 x_247 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_247 = x_41;
 lean::cnstr_set_tag(x_41, 0);
}
lean::cnstr_set(x_247, 0, x_244);
if (lean::is_scalar(x_30)) {
 x_248 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_248 = x_30;
}
lean::cnstr_set(x_248, 0, x_247);
lean::cnstr_set(x_248, 1, x_238);
return x_248;
}
else
{
obj* x_250; obj* x_251; obj* x_252; obj* x_254; 
lean::dec(x_236);
x_250 = lean::mk_nat_obj(0u);
x_251 = l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1(x_0, x_250, x_2, x_3, x_238);
x_252 = lean::cnstr_get(x_251, 0);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_251, 1);
lean::inc(x_254);
lean::dec(x_251);
if (lean::obj_tag(x_252) == 0)
{
obj* x_257; obj* x_260; obj* x_261; 
x_257 = lean::cnstr_get(x_252, 0);
lean::inc(x_257);
lean::dec(x_252);
if (lean::is_scalar(x_41)) {
 x_260 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_260 = x_41;
 lean::cnstr_set_tag(x_41, 0);
}
lean::cnstr_set(x_260, 0, x_257);
if (lean::is_scalar(x_30)) {
 x_261 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_261 = x_30;
}
lean::cnstr_set(x_261, 0, x_260);
lean::cnstr_set(x_261, 1, x_254);
return x_261;
}
else
{
obj* x_264; obj* x_266; 
lean::dec(x_252);
lean::dec(x_41);
x_264 = l_lean_ir_match__type___closed__5;
lean::inc(x_264);
if (lean::is_scalar(x_30)) {
 x_266 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_266 = x_30;
}
lean::cnstr_set(x_266, 0, x_264);
lean::cnstr_set(x_266, 1, x_254);
return x_266;
}
}
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(usize x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::dec(x_1);
x_4 = lean::usize_to_nat(x_0);
x_5 = l_nat_repr(x_4);
x_6 = lean::string_append(x_2, x_5);
lean::dec(x_5);
x_8 = l_lean_ir_match__type___closed__5;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__2(uint16 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::dec(x_1);
x_4 = lean::uint16_to_nat(x_0);
x_5 = l_nat_repr(x_4);
x_6 = lean::string_append(x_2, x_5);
lean::dec(x_5);
x_8 = l_lean_ir_match__type___closed__5;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(uint16 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::dec(x_1);
x_4 = lean::uint16_to_nat(x_0);
x_5 = l_nat_repr(x_4);
x_6 = lean::string_append(x_2, x_5);
lean::dec(x_5);
x_8 = l_lean_ir_match__type___closed__5;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
}
obj* _init_l_lean_ir_cpp_emit__instr___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::alloc_cnstr");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__instr___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::cnstr_set_obj");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__instr___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::cnstr_obj");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__instr___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::cnstr_set_scalar");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__instr___closed__5() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::cnstr_scalar");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__instr___closed__6() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::alloc_array");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__instr___closed__7() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" = lean::alloc_sarray");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__instr___closed__8() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::sarray_set_data");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__instr___closed__9() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("lean::array_set_obj");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__instr(obj* x_0, obj* x_1, obj* x_2) {
_start:
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
x_10 = l_lean_ir_cpp_emit__var(x_5, x_1, x_2);
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
x_23 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_1);
lean::inc(x_23);
x_26 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_23, x_1, x_13);
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
 lean::cnstr_set_tag(x_22, 0);
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
x_42 = l_lean_ir_cpp_emit__var(x_7, x_1, x_29);
x_3 = x_42;
goto lbl_4;
}
}
}
case 1:
{
obj* x_43; uint8 x_45; obj* x_46; obj* x_49; 
x_43 = lean::cnstr_get(x_0, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_46 = lean::cnstr_get(x_0, 1);
lean::inc(x_46);
lean::inc(x_1);
x_49 = l_lean_ir_cpp_emit__assign__lit(x_43, x_45, x_46, x_1, x_2);
x_3 = x_49;
goto lbl_4;
}
case 2:
{
obj* x_50; uint8 x_52; uint8 x_53; obj* x_54; obj* x_57; 
x_50 = lean::cnstr_get(x_0, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_53 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2 + 1);
x_54 = lean::cnstr_get(x_0, 1);
lean::inc(x_54);
lean::inc(x_1);
x_57 = l_lean_ir_cpp_emit__assign__unop(x_50, x_52, x_53, x_54, x_1, x_2);
x_3 = x_57;
goto lbl_4;
}
case 3:
{
obj* x_58; uint8 x_60; uint8 x_61; obj* x_62; obj* x_64; obj* x_67; 
x_58 = lean::cnstr_get(x_0, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_61 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3 + 1);
x_62 = lean::cnstr_get(x_0, 1);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_0, 2);
lean::inc(x_64);
lean::inc(x_1);
x_67 = l_lean_ir_cpp_emit__assign__binop(x_58, x_60, x_61, x_62, x_64, x_1, x_2);
x_3 = x_67;
goto lbl_4;
}
case 4:
{
uint8 x_68; obj* x_69; obj* x_72; 
x_68 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
x_69 = lean::cnstr_get(x_0, 0);
lean::inc(x_69);
lean::inc(x_1);
x_72 = l_lean_ir_cpp_emit__unop(x_68, x_69, x_1, x_2);
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
x_83 = l_lean_ir_cpp_emit__var(x_73, x_1, x_2);
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
x_94 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_1);
lean::inc(x_94);
x_97 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_94, x_1, x_86);
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
lean::dec(x_77);
lean::dec(x_75);
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
obj* x_110; obj* x_113; obj* x_114; obj* x_116; obj* x_118; obj* x_119; 
if (lean::is_shared(x_79)) {
 lean::dec(x_79);
 x_110 = lean::box(0);
} else {
 lean::cnstr_release(x_79, 0);
 x_110 = x_79;
}
lean::inc(x_1);
lean::inc(x_75);
x_113 = l_lean_ir_cpp_is__const(x_75, x_1, x_80);
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
lean::dec(x_77);
lean::dec(x_75);
lean::dec(x_110);
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
obj* x_130; uint8 x_133; 
x_130 = lean::cnstr_get(x_114, 0);
lean::inc(x_130);
lean::dec(x_114);
x_133 = lean::unbox(x_130);
lean::dec(x_130);
if (x_133 == 0)
{
obj* x_135; 
x_135 = lean::box(0);
x_119 = x_135;
goto lbl_120;
}
else
{
obj* x_140; 
lean::dec(x_77);
lean::dec(x_110);
lean::dec(x_118);
lean::inc(x_1);
x_140 = l_lean_ir_cpp_emit__global(x_75, x_1, x_116);
x_3 = x_140;
goto lbl_4;
}
}
lbl_120:
{
obj* x_143; obj* x_144; obj* x_146; 
lean::dec(x_119);
lean::inc(x_1);
x_143 = l_lean_ir_cpp_emit__fnid(x_75, x_1, x_116);
x_144 = lean::cnstr_get(x_143, 0);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_143, 1);
lean::inc(x_146);
lean::dec(x_143);
if (lean::obj_tag(x_144) == 0)
{
obj* x_150; obj* x_153; obj* x_154; 
lean::dec(x_77);
x_150 = lean::cnstr_get(x_144, 0);
lean::inc(x_150);
lean::dec(x_144);
if (lean::is_scalar(x_110)) {
 x_153 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_153 = x_110;
 lean::cnstr_set_tag(x_110, 0);
}
lean::cnstr_set(x_153, 0, x_150);
if (lean::is_scalar(x_118)) {
 x_154 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_154 = x_118;
}
lean::cnstr_set(x_154, 0, x_153);
lean::cnstr_set(x_154, 1, x_146);
x_3 = x_154;
goto lbl_4;
}
else
{
obj* x_156; obj* x_159; obj* x_160; obj* x_162; 
lean::dec(x_144);
x_156 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_156);
x_159 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_156, x_1, x_146);
x_160 = lean::cnstr_get(x_159, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_159, 1);
lean::inc(x_162);
lean::dec(x_159);
if (lean::obj_tag(x_160) == 0)
{
obj* x_166; obj* x_169; obj* x_170; 
lean::dec(x_77);
x_166 = lean::cnstr_get(x_160, 0);
lean::inc(x_166);
lean::dec(x_160);
if (lean::is_scalar(x_110)) {
 x_169 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_169 = x_110;
 lean::cnstr_set_tag(x_110, 0);
}
lean::cnstr_set(x_169, 0, x_166);
if (lean::is_scalar(x_118)) {
 x_170 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_170 = x_118;
}
lean::cnstr_set(x_170, 0, x_169);
lean::cnstr_set(x_170, 1, x_162);
x_3 = x_170;
goto lbl_4;
}
else
{
obj* x_172; obj* x_173; obj* x_177; obj* x_178; obj* x_180; 
lean::dec(x_160);
x_172 = l_lean_ir_cpp_emit__apply___closed__2;
x_173 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_1);
lean::inc(x_173);
lean::inc(x_172);
x_177 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_172, x_173, x_77, x_1, x_162);
x_178 = lean::cnstr_get(x_177, 0);
lean::inc(x_178);
x_180 = lean::cnstr_get(x_177, 1);
lean::inc(x_180);
lean::dec(x_177);
if (lean::obj_tag(x_178) == 0)
{
obj* x_183; obj* x_186; obj* x_187; 
x_183 = lean::cnstr_get(x_178, 0);
lean::inc(x_183);
lean::dec(x_178);
if (lean::is_scalar(x_110)) {
 x_186 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_186 = x_110;
 lean::cnstr_set_tag(x_110, 0);
}
lean::cnstr_set(x_186, 0, x_183);
if (lean::is_scalar(x_118)) {
 x_187 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_187 = x_118;
}
lean::cnstr_set(x_187, 0, x_186);
lean::cnstr_set(x_187, 1, x_180);
x_3 = x_187;
goto lbl_4;
}
else
{
obj* x_188; obj* x_191; obj* x_194; obj* x_195; obj* x_197; 
x_188 = lean::cnstr_get(x_178, 0);
lean::inc(x_188);
lean::dec(x_178);
x_191 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
lean::inc(x_191);
x_194 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_191, x_1, x_180);
x_195 = lean::cnstr_get(x_194, 0);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_194, 1);
lean::inc(x_197);
lean::dec(x_194);
if (lean::obj_tag(x_195) == 0)
{
obj* x_201; obj* x_204; obj* x_205; 
lean::dec(x_188);
x_201 = lean::cnstr_get(x_195, 0);
lean::inc(x_201);
lean::dec(x_195);
if (lean::is_scalar(x_110)) {
 x_204 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_204 = x_110;
 lean::cnstr_set_tag(x_110, 0);
}
lean::cnstr_set(x_204, 0, x_201);
if (lean::is_scalar(x_118)) {
 x_205 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_205 = x_118;
}
lean::cnstr_set(x_205, 0, x_204);
lean::cnstr_set(x_205, 1, x_197);
x_3 = x_205;
goto lbl_4;
}
else
{
obj* x_207; obj* x_208; 
lean::dec(x_195);
if (lean::is_scalar(x_110)) {
 x_207 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_207 = x_110;
}
lean::cnstr_set(x_207, 0, x_188);
if (lean::is_scalar(x_118)) {
 x_208 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_208 = x_118;
}
lean::cnstr_set(x_208, 0, x_207);
lean::cnstr_set(x_208, 1, x_197);
x_3 = x_208;
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
obj* x_209; uint16 x_211; uint16 x_212; usize x_213; obj* x_214; obj* x_215; obj* x_217; obj* x_218; obj* x_221; obj* x_222; obj* x_224; 
x_209 = lean::cnstr_get(x_0, 0);
lean::inc(x_209);
x_211 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
x_212 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2 + 2);
x_213 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*1);
lean::inc(x_1);
x_221 = l_lean_ir_cpp_emit__var(x_209, x_1, x_2);
x_222 = lean::cnstr_get(x_221, 0);
lean::inc(x_222);
x_224 = lean::cnstr_get(x_221, 1);
lean::inc(x_224);
lean::dec(x_221);
if (lean::obj_tag(x_222) == 0)
{
obj* x_227; obj* x_229; obj* x_230; 
x_227 = lean::cnstr_get(x_222, 0);
lean::inc(x_227);
if (lean::is_shared(x_222)) {
 lean::dec(x_222);
 x_229 = lean::box(0);
} else {
 lean::cnstr_release(x_222, 0);
 x_229 = x_222;
}
if (lean::is_scalar(x_229)) {
 x_230 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_230 = x_229;
}
lean::cnstr_set(x_230, 0, x_227);
x_217 = x_230;
x_218 = x_224;
goto lbl_219;
}
else
{
obj* x_232; obj* x_235; obj* x_236; obj* x_238; 
lean::dec(x_222);
x_232 = l_lean_ir_cpp_emit__instr___closed__1;
lean::inc(x_1);
lean::inc(x_232);
x_235 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_232, x_1, x_224);
x_236 = lean::cnstr_get(x_235, 0);
lean::inc(x_236);
x_238 = lean::cnstr_get(x_235, 1);
lean::inc(x_238);
lean::dec(x_235);
x_217 = x_236;
x_218 = x_238;
goto lbl_219;
}
lbl_216:
{
if (lean::obj_tag(x_214) == 0)
{
obj* x_241; obj* x_243; obj* x_244; obj* x_245; 
x_241 = lean::cnstr_get(x_214, 0);
lean::inc(x_241);
if (lean::is_shared(x_214)) {
 lean::dec(x_214);
 x_243 = lean::box(0);
} else {
 lean::cnstr_release(x_214, 0);
 x_243 = x_214;
}
if (lean::is_scalar(x_243)) {
 x_244 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_244 = x_243;
}
lean::cnstr_set(x_244, 0, x_241);
x_245 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_245, 0, x_244);
lean::cnstr_set(x_245, 1, x_215);
x_3 = x_245;
goto lbl_4;
}
else
{
obj* x_246; obj* x_247; obj* x_250; obj* x_251; obj* x_253; obj* x_255; 
if (lean::is_shared(x_214)) {
 lean::dec(x_214);
 x_246 = lean::box(0);
} else {
 lean::cnstr_release(x_214, 0);
 x_246 = x_214;
}
x_247 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_247);
x_250 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_247, x_1, x_215);
x_251 = lean::cnstr_get(x_250, 0);
lean::inc(x_251);
x_253 = lean::cnstr_get(x_250, 1);
lean::inc(x_253);
if (lean::is_shared(x_250)) {
 lean::dec(x_250);
 x_255 = lean::box(0);
} else {
 lean::cnstr_release(x_250, 0);
 lean::cnstr_release(x_250, 1);
 x_255 = x_250;
}
if (lean::obj_tag(x_251) == 0)
{
obj* x_256; obj* x_259; obj* x_260; 
x_256 = lean::cnstr_get(x_251, 0);
lean::inc(x_256);
lean::dec(x_251);
if (lean::is_scalar(x_246)) {
 x_259 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_259 = x_246;
 lean::cnstr_set_tag(x_246, 0);
}
lean::cnstr_set(x_259, 0, x_256);
if (lean::is_scalar(x_255)) {
 x_260 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_260 = x_255;
}
lean::cnstr_set(x_260, 0, x_259);
lean::cnstr_set(x_260, 1, x_253);
x_3 = x_260;
goto lbl_4;
}
else
{
obj* x_263; obj* x_264; obj* x_266; 
lean::dec(x_251);
lean::inc(x_1);
x_263 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(x_213, x_1, x_253);
x_264 = lean::cnstr_get(x_263, 0);
lean::inc(x_264);
x_266 = lean::cnstr_get(x_263, 1);
lean::inc(x_266);
lean::dec(x_263);
if (lean::obj_tag(x_264) == 0)
{
obj* x_269; obj* x_272; obj* x_273; 
x_269 = lean::cnstr_get(x_264, 0);
lean::inc(x_269);
lean::dec(x_264);
if (lean::is_scalar(x_246)) {
 x_272 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_272 = x_246;
 lean::cnstr_set_tag(x_246, 0);
}
lean::cnstr_set(x_272, 0, x_269);
if (lean::is_scalar(x_255)) {
 x_273 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_273 = x_255;
}
lean::cnstr_set(x_273, 0, x_272);
lean::cnstr_set(x_273, 1, x_266);
x_3 = x_273;
goto lbl_4;
}
else
{
obj* x_274; obj* x_277; obj* x_280; obj* x_281; obj* x_283; 
x_274 = lean::cnstr_get(x_264, 0);
lean::inc(x_274);
lean::dec(x_264);
x_277 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
lean::inc(x_277);
x_280 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_277, x_1, x_266);
x_281 = lean::cnstr_get(x_280, 0);
lean::inc(x_281);
x_283 = lean::cnstr_get(x_280, 1);
lean::inc(x_283);
lean::dec(x_280);
if (lean::obj_tag(x_281) == 0)
{
obj* x_287; obj* x_290; obj* x_291; 
lean::dec(x_274);
x_287 = lean::cnstr_get(x_281, 0);
lean::inc(x_287);
lean::dec(x_281);
if (lean::is_scalar(x_246)) {
 x_290 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_290 = x_246;
 lean::cnstr_set_tag(x_246, 0);
}
lean::cnstr_set(x_290, 0, x_287);
if (lean::is_scalar(x_255)) {
 x_291 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_291 = x_255;
}
lean::cnstr_set(x_291, 0, x_290);
lean::cnstr_set(x_291, 1, x_283);
x_3 = x_291;
goto lbl_4;
}
else
{
obj* x_293; obj* x_294; 
lean::dec(x_281);
if (lean::is_scalar(x_246)) {
 x_293 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_293 = x_246;
}
lean::cnstr_set(x_293, 0, x_274);
if (lean::is_scalar(x_255)) {
 x_294 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_294 = x_255;
}
lean::cnstr_set(x_294, 0, x_293);
lean::cnstr_set(x_294, 1, x_283);
x_3 = x_294;
goto lbl_4;
}
}
}
}
}
lbl_219:
{
if (lean::obj_tag(x_217) == 0)
{
obj* x_295; obj* x_297; obj* x_298; obj* x_299; 
x_295 = lean::cnstr_get(x_217, 0);
lean::inc(x_295);
if (lean::is_shared(x_217)) {
 lean::dec(x_217);
 x_297 = lean::box(0);
} else {
 lean::cnstr_release(x_217, 0);
 x_297 = x_217;
}
if (lean::is_scalar(x_297)) {
 x_298 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_298 = x_297;
}
lean::cnstr_set(x_298, 0, x_295);
x_299 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_299, 0, x_298);
lean::cnstr_set(x_299, 1, x_218);
x_3 = x_299;
goto lbl_4;
}
else
{
obj* x_300; obj* x_301; obj* x_304; obj* x_305; obj* x_307; obj* x_309; 
if (lean::is_shared(x_217)) {
 lean::dec(x_217);
 x_300 = lean::box(0);
} else {
 lean::cnstr_release(x_217, 0);
 x_300 = x_217;
}
x_301 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_301);
x_304 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_301, x_1, x_218);
x_305 = lean::cnstr_get(x_304, 0);
lean::inc(x_305);
x_307 = lean::cnstr_get(x_304, 1);
lean::inc(x_307);
if (lean::is_shared(x_304)) {
 lean::dec(x_304);
 x_309 = lean::box(0);
} else {
 lean::cnstr_release(x_304, 0);
 lean::cnstr_release(x_304, 1);
 x_309 = x_304;
}
if (lean::obj_tag(x_305) == 0)
{
obj* x_310; obj* x_313; obj* x_314; 
x_310 = lean::cnstr_get(x_305, 0);
lean::inc(x_310);
lean::dec(x_305);
if (lean::is_scalar(x_300)) {
 x_313 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_313 = x_300;
 lean::cnstr_set_tag(x_300, 0);
}
lean::cnstr_set(x_313, 0, x_310);
if (lean::is_scalar(x_309)) {
 x_314 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_314 = x_309;
}
lean::cnstr_set(x_314, 0, x_313);
lean::cnstr_set(x_314, 1, x_307);
x_3 = x_314;
goto lbl_4;
}
else
{
obj* x_318; obj* x_319; obj* x_321; 
lean::dec(x_305);
lean::dec(x_309);
lean::inc(x_1);
x_318 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__2(x_211, x_1, x_307);
x_319 = lean::cnstr_get(x_318, 0);
lean::inc(x_319);
x_321 = lean::cnstr_get(x_318, 1);
lean::inc(x_321);
lean::dec(x_318);
if (lean::obj_tag(x_319) == 0)
{
obj* x_324; obj* x_327; 
x_324 = lean::cnstr_get(x_319, 0);
lean::inc(x_324);
lean::dec(x_319);
if (lean::is_scalar(x_300)) {
 x_327 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_327 = x_300;
 lean::cnstr_set_tag(x_300, 0);
}
lean::cnstr_set(x_327, 0, x_324);
x_214 = x_327;
x_215 = x_321;
goto lbl_216;
}
else
{
obj* x_329; obj* x_332; obj* x_333; obj* x_335; 
lean::dec(x_319);
x_329 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_329);
x_332 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_329, x_1, x_321);
x_333 = lean::cnstr_get(x_332, 0);
lean::inc(x_333);
x_335 = lean::cnstr_get(x_332, 1);
lean::inc(x_335);
lean::dec(x_332);
if (lean::obj_tag(x_333) == 0)
{
obj* x_338; obj* x_341; 
x_338 = lean::cnstr_get(x_333, 0);
lean::inc(x_338);
lean::dec(x_333);
if (lean::is_scalar(x_300)) {
 x_341 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_341 = x_300;
 lean::cnstr_set_tag(x_300, 0);
}
lean::cnstr_set(x_341, 0, x_338);
x_214 = x_341;
x_215 = x_335;
goto lbl_216;
}
else
{
obj* x_345; obj* x_346; obj* x_348; 
lean::dec(x_333);
lean::dec(x_300);
lean::inc(x_1);
x_345 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_212, x_1, x_335);
x_346 = lean::cnstr_get(x_345, 0);
lean::inc(x_346);
x_348 = lean::cnstr_get(x_345, 1);
lean::inc(x_348);
lean::dec(x_345);
x_214 = x_346;
x_215 = x_348;
goto lbl_216;
}
}
}
}
}
}
case 7:
{
obj* x_351; uint16 x_353; obj* x_354; obj* x_356; obj* x_357; obj* x_359; obj* x_362; obj* x_363; obj* x_365; obj* x_367; 
x_351 = lean::cnstr_get(x_0, 0);
lean::inc(x_351);
x_353 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
x_354 = lean::cnstr_get(x_0, 1);
lean::inc(x_354);
x_359 = l_lean_ir_cpp_emit__instr___closed__2;
lean::inc(x_1);
lean::inc(x_359);
x_362 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_359, x_1, x_2);
x_363 = lean::cnstr_get(x_362, 0);
lean::inc(x_363);
x_365 = lean::cnstr_get(x_362, 1);
lean::inc(x_365);
if (lean::is_shared(x_362)) {
 lean::dec(x_362);
 x_367 = lean::box(0);
} else {
 lean::cnstr_release(x_362, 0);
 lean::cnstr_release(x_362, 1);
 x_367 = x_362;
}
if (lean::obj_tag(x_363) == 0)
{
obj* x_370; obj* x_372; obj* x_373; obj* x_374; 
lean::dec(x_351);
lean::dec(x_354);
x_370 = lean::cnstr_get(x_363, 0);
lean::inc(x_370);
if (lean::is_shared(x_363)) {
 lean::dec(x_363);
 x_372 = lean::box(0);
} else {
 lean::cnstr_release(x_363, 0);
 x_372 = x_363;
}
if (lean::is_scalar(x_372)) {
 x_373 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_373 = x_372;
}
lean::cnstr_set(x_373, 0, x_370);
if (lean::is_scalar(x_367)) {
 x_374 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_374 = x_367;
}
lean::cnstr_set(x_374, 0, x_373);
lean::cnstr_set(x_374, 1, x_365);
x_3 = x_374;
goto lbl_4;
}
else
{
obj* x_375; obj* x_376; obj* x_379; obj* x_380; obj* x_382; 
if (lean::is_shared(x_363)) {
 lean::dec(x_363);
 x_375 = lean::box(0);
} else {
 lean::cnstr_release(x_363, 0);
 x_375 = x_363;
}
x_376 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_376);
x_379 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_376, x_1, x_365);
x_380 = lean::cnstr_get(x_379, 0);
lean::inc(x_380);
x_382 = lean::cnstr_get(x_379, 1);
lean::inc(x_382);
lean::dec(x_379);
if (lean::obj_tag(x_380) == 0)
{
obj* x_387; obj* x_390; obj* x_391; 
lean::dec(x_351);
lean::dec(x_354);
x_387 = lean::cnstr_get(x_380, 0);
lean::inc(x_387);
lean::dec(x_380);
if (lean::is_scalar(x_375)) {
 x_390 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_390 = x_375;
 lean::cnstr_set_tag(x_375, 0);
}
lean::cnstr_set(x_390, 0, x_387);
if (lean::is_scalar(x_367)) {
 x_391 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_391 = x_367;
}
lean::cnstr_set(x_391, 0, x_390);
lean::cnstr_set(x_391, 1, x_382);
x_3 = x_391;
goto lbl_4;
}
else
{
obj* x_395; obj* x_396; obj* x_398; 
lean::dec(x_380);
lean::dec(x_367);
lean::inc(x_1);
x_395 = l_lean_ir_cpp_emit__var(x_351, x_1, x_382);
x_396 = lean::cnstr_get(x_395, 0);
lean::inc(x_396);
x_398 = lean::cnstr_get(x_395, 1);
lean::inc(x_398);
lean::dec(x_395);
if (lean::obj_tag(x_396) == 0)
{
obj* x_401; obj* x_404; 
x_401 = lean::cnstr_get(x_396, 0);
lean::inc(x_401);
lean::dec(x_396);
if (lean::is_scalar(x_375)) {
 x_404 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_404 = x_375;
 lean::cnstr_set_tag(x_375, 0);
}
lean::cnstr_set(x_404, 0, x_401);
x_356 = x_404;
x_357 = x_398;
goto lbl_358;
}
else
{
obj* x_406; obj* x_409; obj* x_410; obj* x_412; 
lean::dec(x_396);
x_406 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_406);
x_409 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_406, x_1, x_398);
x_410 = lean::cnstr_get(x_409, 0);
lean::inc(x_410);
x_412 = lean::cnstr_get(x_409, 1);
lean::inc(x_412);
lean::dec(x_409);
if (lean::obj_tag(x_410) == 0)
{
obj* x_415; obj* x_418; 
x_415 = lean::cnstr_get(x_410, 0);
lean::inc(x_415);
lean::dec(x_410);
if (lean::is_scalar(x_375)) {
 x_418 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_418 = x_375;
 lean::cnstr_set_tag(x_375, 0);
}
lean::cnstr_set(x_418, 0, x_415);
x_356 = x_418;
x_357 = x_412;
goto lbl_358;
}
else
{
obj* x_422; obj* x_423; obj* x_425; 
lean::dec(x_375);
lean::dec(x_410);
lean::inc(x_1);
x_422 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_353, x_1, x_412);
x_423 = lean::cnstr_get(x_422, 0);
lean::inc(x_423);
x_425 = lean::cnstr_get(x_422, 1);
lean::inc(x_425);
lean::dec(x_422);
x_356 = x_423;
x_357 = x_425;
goto lbl_358;
}
}
}
}
lbl_358:
{
if (lean::obj_tag(x_356) == 0)
{
obj* x_429; obj* x_431; obj* x_432; obj* x_433; 
lean::dec(x_354);
x_429 = lean::cnstr_get(x_356, 0);
lean::inc(x_429);
if (lean::is_shared(x_356)) {
 lean::dec(x_356);
 x_431 = lean::box(0);
} else {
 lean::cnstr_release(x_356, 0);
 x_431 = x_356;
}
if (lean::is_scalar(x_431)) {
 x_432 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_432 = x_431;
}
lean::cnstr_set(x_432, 0, x_429);
x_433 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_433, 0, x_432);
lean::cnstr_set(x_433, 1, x_357);
x_3 = x_433;
goto lbl_4;
}
else
{
obj* x_434; obj* x_435; obj* x_438; obj* x_439; obj* x_441; obj* x_443; 
if (lean::is_shared(x_356)) {
 lean::dec(x_356);
 x_434 = lean::box(0);
} else {
 lean::cnstr_release(x_356, 0);
 x_434 = x_356;
}
x_435 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_435);
x_438 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_435, x_1, x_357);
x_439 = lean::cnstr_get(x_438, 0);
lean::inc(x_439);
x_441 = lean::cnstr_get(x_438, 1);
lean::inc(x_441);
if (lean::is_shared(x_438)) {
 lean::dec(x_438);
 x_443 = lean::box(0);
} else {
 lean::cnstr_release(x_438, 0);
 lean::cnstr_release(x_438, 1);
 x_443 = x_438;
}
if (lean::obj_tag(x_439) == 0)
{
obj* x_445; obj* x_448; obj* x_449; 
lean::dec(x_354);
x_445 = lean::cnstr_get(x_439, 0);
lean::inc(x_445);
lean::dec(x_439);
if (lean::is_scalar(x_434)) {
 x_448 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_448 = x_434;
 lean::cnstr_set_tag(x_434, 0);
}
lean::cnstr_set(x_448, 0, x_445);
if (lean::is_scalar(x_443)) {
 x_449 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_449 = x_443;
}
lean::cnstr_set(x_449, 0, x_448);
lean::cnstr_set(x_449, 1, x_441);
x_3 = x_449;
goto lbl_4;
}
else
{
obj* x_452; obj* x_453; obj* x_455; 
lean::dec(x_439);
lean::inc(x_1);
x_452 = l_lean_ir_cpp_emit__var(x_354, x_1, x_441);
x_453 = lean::cnstr_get(x_452, 0);
lean::inc(x_453);
x_455 = lean::cnstr_get(x_452, 1);
lean::inc(x_455);
lean::dec(x_452);
if (lean::obj_tag(x_453) == 0)
{
obj* x_458; obj* x_461; obj* x_462; 
x_458 = lean::cnstr_get(x_453, 0);
lean::inc(x_458);
lean::dec(x_453);
if (lean::is_scalar(x_434)) {
 x_461 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_461 = x_434;
 lean::cnstr_set_tag(x_434, 0);
}
lean::cnstr_set(x_461, 0, x_458);
if (lean::is_scalar(x_443)) {
 x_462 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_462 = x_443;
}
lean::cnstr_set(x_462, 0, x_461);
lean::cnstr_set(x_462, 1, x_455);
x_3 = x_462;
goto lbl_4;
}
else
{
obj* x_463; obj* x_466; obj* x_469; obj* x_470; obj* x_472; 
x_463 = lean::cnstr_get(x_453, 0);
lean::inc(x_463);
lean::dec(x_453);
x_466 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
lean::inc(x_466);
x_469 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_466, x_1, x_455);
x_470 = lean::cnstr_get(x_469, 0);
lean::inc(x_470);
x_472 = lean::cnstr_get(x_469, 1);
lean::inc(x_472);
lean::dec(x_469);
if (lean::obj_tag(x_470) == 0)
{
obj* x_476; obj* x_479; obj* x_480; 
lean::dec(x_463);
x_476 = lean::cnstr_get(x_470, 0);
lean::inc(x_476);
lean::dec(x_470);
if (lean::is_scalar(x_434)) {
 x_479 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_479 = x_434;
 lean::cnstr_set_tag(x_434, 0);
}
lean::cnstr_set(x_479, 0, x_476);
if (lean::is_scalar(x_443)) {
 x_480 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_480 = x_443;
}
lean::cnstr_set(x_480, 0, x_479);
lean::cnstr_set(x_480, 1, x_472);
x_3 = x_480;
goto lbl_4;
}
else
{
obj* x_482; obj* x_483; 
lean::dec(x_470);
if (lean::is_scalar(x_434)) {
 x_482 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_482 = x_434;
}
lean::cnstr_set(x_482, 0, x_463);
if (lean::is_scalar(x_443)) {
 x_483 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_483 = x_443;
}
lean::cnstr_set(x_483, 0, x_482);
lean::cnstr_set(x_483, 1, x_472);
x_3 = x_483;
goto lbl_4;
}
}
}
}
}
}
case 8:
{
obj* x_484; obj* x_486; uint16 x_488; obj* x_489; obj* x_490; obj* x_493; obj* x_494; obj* x_496; 
x_484 = lean::cnstr_get(x_0, 0);
lean::inc(x_484);
x_486 = lean::cnstr_get(x_0, 1);
lean::inc(x_486);
x_488 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
lean::inc(x_1);
x_493 = l_lean_ir_cpp_emit__var(x_484, x_1, x_2);
x_494 = lean::cnstr_get(x_493, 0);
lean::inc(x_494);
x_496 = lean::cnstr_get(x_493, 1);
lean::inc(x_496);
lean::dec(x_493);
if (lean::obj_tag(x_494) == 0)
{
obj* x_499; obj* x_501; obj* x_502; 
x_499 = lean::cnstr_get(x_494, 0);
lean::inc(x_499);
if (lean::is_shared(x_494)) {
 lean::dec(x_494);
 x_501 = lean::box(0);
} else {
 lean::cnstr_release(x_494, 0);
 x_501 = x_494;
}
if (lean::is_scalar(x_501)) {
 x_502 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_502 = x_501;
}
lean::cnstr_set(x_502, 0, x_499);
x_489 = x_502;
x_490 = x_496;
goto lbl_491;
}
else
{
obj* x_504; obj* x_507; obj* x_508; obj* x_510; 
lean::dec(x_494);
x_504 = l_lean_ir_cpp_emit__instr___closed__3;
lean::inc(x_1);
lean::inc(x_504);
x_507 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_504, x_1, x_496);
x_508 = lean::cnstr_get(x_507, 0);
lean::inc(x_508);
x_510 = lean::cnstr_get(x_507, 1);
lean::inc(x_510);
lean::dec(x_507);
x_489 = x_508;
x_490 = x_510;
goto lbl_491;
}
lbl_491:
{
if (lean::obj_tag(x_489) == 0)
{
obj* x_514; obj* x_516; obj* x_517; obj* x_518; 
lean::dec(x_486);
x_514 = lean::cnstr_get(x_489, 0);
lean::inc(x_514);
if (lean::is_shared(x_489)) {
 lean::dec(x_489);
 x_516 = lean::box(0);
} else {
 lean::cnstr_release(x_489, 0);
 x_516 = x_489;
}
if (lean::is_scalar(x_516)) {
 x_517 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_517 = x_516;
}
lean::cnstr_set(x_517, 0, x_514);
x_518 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_518, 0, x_517);
lean::cnstr_set(x_518, 1, x_490);
x_3 = x_518;
goto lbl_4;
}
else
{
obj* x_519; obj* x_520; obj* x_523; obj* x_524; obj* x_526; obj* x_528; 
if (lean::is_shared(x_489)) {
 lean::dec(x_489);
 x_519 = lean::box(0);
} else {
 lean::cnstr_release(x_489, 0);
 x_519 = x_489;
}
x_520 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_520);
x_523 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_520, x_1, x_490);
x_524 = lean::cnstr_get(x_523, 0);
lean::inc(x_524);
x_526 = lean::cnstr_get(x_523, 1);
lean::inc(x_526);
if (lean::is_shared(x_523)) {
 lean::dec(x_523);
 x_528 = lean::box(0);
} else {
 lean::cnstr_release(x_523, 0);
 lean::cnstr_release(x_523, 1);
 x_528 = x_523;
}
if (lean::obj_tag(x_524) == 0)
{
obj* x_530; obj* x_533; obj* x_534; 
lean::dec(x_486);
x_530 = lean::cnstr_get(x_524, 0);
lean::inc(x_530);
lean::dec(x_524);
if (lean::is_scalar(x_519)) {
 x_533 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_533 = x_519;
 lean::cnstr_set_tag(x_519, 0);
}
lean::cnstr_set(x_533, 0, x_530);
if (lean::is_scalar(x_528)) {
 x_534 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_534 = x_528;
}
lean::cnstr_set(x_534, 0, x_533);
lean::cnstr_set(x_534, 1, x_526);
x_3 = x_534;
goto lbl_4;
}
else
{
obj* x_537; obj* x_538; obj* x_540; 
lean::dec(x_524);
lean::inc(x_1);
x_537 = l_lean_ir_cpp_emit__var(x_486, x_1, x_526);
x_538 = lean::cnstr_get(x_537, 0);
lean::inc(x_538);
x_540 = lean::cnstr_get(x_537, 1);
lean::inc(x_540);
lean::dec(x_537);
if (lean::obj_tag(x_538) == 0)
{
obj* x_543; obj* x_546; obj* x_547; 
x_543 = lean::cnstr_get(x_538, 0);
lean::inc(x_543);
lean::dec(x_538);
if (lean::is_scalar(x_519)) {
 x_546 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_546 = x_519;
 lean::cnstr_set_tag(x_519, 0);
}
lean::cnstr_set(x_546, 0, x_543);
if (lean::is_scalar(x_528)) {
 x_547 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_547 = x_528;
}
lean::cnstr_set(x_547, 0, x_546);
lean::cnstr_set(x_547, 1, x_540);
x_3 = x_547;
goto lbl_4;
}
else
{
obj* x_549; obj* x_552; obj* x_553; obj* x_555; 
lean::dec(x_538);
x_549 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_549);
x_552 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_549, x_1, x_540);
x_553 = lean::cnstr_get(x_552, 0);
lean::inc(x_553);
x_555 = lean::cnstr_get(x_552, 1);
lean::inc(x_555);
lean::dec(x_552);
if (lean::obj_tag(x_553) == 0)
{
obj* x_558; obj* x_561; obj* x_562; 
x_558 = lean::cnstr_get(x_553, 0);
lean::inc(x_558);
lean::dec(x_553);
if (lean::is_scalar(x_519)) {
 x_561 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_561 = x_519;
 lean::cnstr_set_tag(x_519, 0);
}
lean::cnstr_set(x_561, 0, x_558);
if (lean::is_scalar(x_528)) {
 x_562 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_562 = x_528;
}
lean::cnstr_set(x_562, 0, x_561);
lean::cnstr_set(x_562, 1, x_555);
x_3 = x_562;
goto lbl_4;
}
else
{
obj* x_565; obj* x_566; obj* x_568; 
lean::dec(x_553);
lean::inc(x_1);
x_565 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_488, x_1, x_555);
x_566 = lean::cnstr_get(x_565, 0);
lean::inc(x_566);
x_568 = lean::cnstr_get(x_565, 1);
lean::inc(x_568);
lean::dec(x_565);
if (lean::obj_tag(x_566) == 0)
{
obj* x_571; obj* x_574; obj* x_575; 
x_571 = lean::cnstr_get(x_566, 0);
lean::inc(x_571);
lean::dec(x_566);
if (lean::is_scalar(x_519)) {
 x_574 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_574 = x_519;
 lean::cnstr_set_tag(x_519, 0);
}
lean::cnstr_set(x_574, 0, x_571);
if (lean::is_scalar(x_528)) {
 x_575 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_575 = x_528;
}
lean::cnstr_set(x_575, 0, x_574);
lean::cnstr_set(x_575, 1, x_568);
x_3 = x_575;
goto lbl_4;
}
else
{
obj* x_576; obj* x_579; obj* x_582; obj* x_583; obj* x_585; 
x_576 = lean::cnstr_get(x_566, 0);
lean::inc(x_576);
lean::dec(x_566);
x_579 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
lean::inc(x_579);
x_582 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_579, x_1, x_568);
x_583 = lean::cnstr_get(x_582, 0);
lean::inc(x_583);
x_585 = lean::cnstr_get(x_582, 1);
lean::inc(x_585);
lean::dec(x_582);
if (lean::obj_tag(x_583) == 0)
{
obj* x_589; obj* x_592; obj* x_593; 
lean::dec(x_576);
x_589 = lean::cnstr_get(x_583, 0);
lean::inc(x_589);
lean::dec(x_583);
if (lean::is_scalar(x_519)) {
 x_592 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_592 = x_519;
 lean::cnstr_set_tag(x_519, 0);
}
lean::cnstr_set(x_592, 0, x_589);
if (lean::is_scalar(x_528)) {
 x_593 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_593 = x_528;
}
lean::cnstr_set(x_593, 0, x_592);
lean::cnstr_set(x_593, 1, x_585);
x_3 = x_593;
goto lbl_4;
}
else
{
obj* x_595; obj* x_596; 
lean::dec(x_583);
if (lean::is_scalar(x_519)) {
 x_595 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_595 = x_519;
}
lean::cnstr_set(x_595, 0, x_576);
if (lean::is_scalar(x_528)) {
 x_596 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_596 = x_528;
}
lean::cnstr_set(x_596, 0, x_595);
lean::cnstr_set(x_596, 1, x_585);
x_3 = x_596;
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
obj* x_597; usize x_599; obj* x_600; obj* x_602; obj* x_603; obj* x_605; obj* x_608; obj* x_609; obj* x_611; obj* x_613; 
x_597 = lean::cnstr_get(x_0, 0);
lean::inc(x_597);
x_599 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
x_600 = lean::cnstr_get(x_0, 1);
lean::inc(x_600);
x_605 = l_lean_ir_cpp_emit__instr___closed__4;
lean::inc(x_1);
lean::inc(x_605);
x_608 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_605, x_1, x_2);
x_609 = lean::cnstr_get(x_608, 0);
lean::inc(x_609);
x_611 = lean::cnstr_get(x_608, 1);
lean::inc(x_611);
if (lean::is_shared(x_608)) {
 lean::dec(x_608);
 x_613 = lean::box(0);
} else {
 lean::cnstr_release(x_608, 0);
 lean::cnstr_release(x_608, 1);
 x_613 = x_608;
}
if (lean::obj_tag(x_609) == 0)
{
obj* x_616; obj* x_618; obj* x_619; obj* x_620; 
lean::dec(x_600);
lean::dec(x_597);
x_616 = lean::cnstr_get(x_609, 0);
lean::inc(x_616);
if (lean::is_shared(x_609)) {
 lean::dec(x_609);
 x_618 = lean::box(0);
} else {
 lean::cnstr_release(x_609, 0);
 x_618 = x_609;
}
if (lean::is_scalar(x_618)) {
 x_619 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_619 = x_618;
}
lean::cnstr_set(x_619, 0, x_616);
if (lean::is_scalar(x_613)) {
 x_620 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_620 = x_613;
}
lean::cnstr_set(x_620, 0, x_619);
lean::cnstr_set(x_620, 1, x_611);
x_3 = x_620;
goto lbl_4;
}
else
{
obj* x_621; obj* x_622; obj* x_625; obj* x_626; obj* x_628; 
if (lean::is_shared(x_609)) {
 lean::dec(x_609);
 x_621 = lean::box(0);
} else {
 lean::cnstr_release(x_609, 0);
 x_621 = x_609;
}
x_622 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_622);
x_625 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_622, x_1, x_611);
x_626 = lean::cnstr_get(x_625, 0);
lean::inc(x_626);
x_628 = lean::cnstr_get(x_625, 1);
lean::inc(x_628);
lean::dec(x_625);
if (lean::obj_tag(x_626) == 0)
{
obj* x_633; obj* x_636; obj* x_637; 
lean::dec(x_600);
lean::dec(x_597);
x_633 = lean::cnstr_get(x_626, 0);
lean::inc(x_633);
lean::dec(x_626);
if (lean::is_scalar(x_621)) {
 x_636 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_636 = x_621;
 lean::cnstr_set_tag(x_621, 0);
}
lean::cnstr_set(x_636, 0, x_633);
if (lean::is_scalar(x_613)) {
 x_637 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_637 = x_613;
}
lean::cnstr_set(x_637, 0, x_636);
lean::cnstr_set(x_637, 1, x_628);
x_3 = x_637;
goto lbl_4;
}
else
{
obj* x_641; obj* x_642; obj* x_644; 
lean::dec(x_613);
lean::dec(x_626);
lean::inc(x_1);
x_641 = l_lean_ir_cpp_emit__var(x_597, x_1, x_628);
x_642 = lean::cnstr_get(x_641, 0);
lean::inc(x_642);
x_644 = lean::cnstr_get(x_641, 1);
lean::inc(x_644);
lean::dec(x_641);
if (lean::obj_tag(x_642) == 0)
{
obj* x_647; obj* x_650; 
x_647 = lean::cnstr_get(x_642, 0);
lean::inc(x_647);
lean::dec(x_642);
if (lean::is_scalar(x_621)) {
 x_650 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_650 = x_621;
 lean::cnstr_set_tag(x_621, 0);
}
lean::cnstr_set(x_650, 0, x_647);
x_602 = x_650;
x_603 = x_644;
goto lbl_604;
}
else
{
obj* x_652; obj* x_655; obj* x_656; obj* x_658; 
lean::dec(x_642);
x_652 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_652);
x_655 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_652, x_1, x_644);
x_656 = lean::cnstr_get(x_655, 0);
lean::inc(x_656);
x_658 = lean::cnstr_get(x_655, 1);
lean::inc(x_658);
lean::dec(x_655);
if (lean::obj_tag(x_656) == 0)
{
obj* x_661; obj* x_664; 
x_661 = lean::cnstr_get(x_656, 0);
lean::inc(x_661);
lean::dec(x_656);
if (lean::is_scalar(x_621)) {
 x_664 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_664 = x_621;
 lean::cnstr_set_tag(x_621, 0);
}
lean::cnstr_set(x_664, 0, x_661);
x_602 = x_664;
x_603 = x_658;
goto lbl_604;
}
else
{
obj* x_668; obj* x_669; obj* x_671; 
lean::dec(x_656);
lean::dec(x_621);
lean::inc(x_1);
x_668 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(x_599, x_1, x_658);
x_669 = lean::cnstr_get(x_668, 0);
lean::inc(x_669);
x_671 = lean::cnstr_get(x_668, 1);
lean::inc(x_671);
lean::dec(x_668);
x_602 = x_669;
x_603 = x_671;
goto lbl_604;
}
}
}
}
lbl_604:
{
if (lean::obj_tag(x_602) == 0)
{
obj* x_675; obj* x_677; obj* x_678; obj* x_679; 
lean::dec(x_600);
x_675 = lean::cnstr_get(x_602, 0);
lean::inc(x_675);
if (lean::is_shared(x_602)) {
 lean::dec(x_602);
 x_677 = lean::box(0);
} else {
 lean::cnstr_release(x_602, 0);
 x_677 = x_602;
}
if (lean::is_scalar(x_677)) {
 x_678 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_678 = x_677;
}
lean::cnstr_set(x_678, 0, x_675);
x_679 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_679, 0, x_678);
lean::cnstr_set(x_679, 1, x_603);
x_3 = x_679;
goto lbl_4;
}
else
{
obj* x_680; obj* x_681; obj* x_684; obj* x_685; obj* x_687; obj* x_689; 
if (lean::is_shared(x_602)) {
 lean::dec(x_602);
 x_680 = lean::box(0);
} else {
 lean::cnstr_release(x_602, 0);
 x_680 = x_602;
}
x_681 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_681);
x_684 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_681, x_1, x_603);
x_685 = lean::cnstr_get(x_684, 0);
lean::inc(x_685);
x_687 = lean::cnstr_get(x_684, 1);
lean::inc(x_687);
if (lean::is_shared(x_684)) {
 lean::dec(x_684);
 x_689 = lean::box(0);
} else {
 lean::cnstr_release(x_684, 0);
 lean::cnstr_release(x_684, 1);
 x_689 = x_684;
}
if (lean::obj_tag(x_685) == 0)
{
obj* x_691; obj* x_694; obj* x_695; 
lean::dec(x_600);
x_691 = lean::cnstr_get(x_685, 0);
lean::inc(x_691);
lean::dec(x_685);
if (lean::is_scalar(x_680)) {
 x_694 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_694 = x_680;
 lean::cnstr_set_tag(x_680, 0);
}
lean::cnstr_set(x_694, 0, x_691);
if (lean::is_scalar(x_689)) {
 x_695 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_695 = x_689;
}
lean::cnstr_set(x_695, 0, x_694);
lean::cnstr_set(x_695, 1, x_687);
x_3 = x_695;
goto lbl_4;
}
else
{
obj* x_698; obj* x_699; obj* x_701; 
lean::dec(x_685);
lean::inc(x_1);
x_698 = l_lean_ir_cpp_emit__var(x_600, x_1, x_687);
x_699 = lean::cnstr_get(x_698, 0);
lean::inc(x_699);
x_701 = lean::cnstr_get(x_698, 1);
lean::inc(x_701);
lean::dec(x_698);
if (lean::obj_tag(x_699) == 0)
{
obj* x_704; obj* x_707; obj* x_708; 
x_704 = lean::cnstr_get(x_699, 0);
lean::inc(x_704);
lean::dec(x_699);
if (lean::is_scalar(x_680)) {
 x_707 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_707 = x_680;
 lean::cnstr_set_tag(x_680, 0);
}
lean::cnstr_set(x_707, 0, x_704);
if (lean::is_scalar(x_689)) {
 x_708 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_708 = x_689;
}
lean::cnstr_set(x_708, 0, x_707);
lean::cnstr_set(x_708, 1, x_701);
x_3 = x_708;
goto lbl_4;
}
else
{
obj* x_709; obj* x_712; obj* x_715; obj* x_716; obj* x_718; 
x_709 = lean::cnstr_get(x_699, 0);
lean::inc(x_709);
lean::dec(x_699);
x_712 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
lean::inc(x_712);
x_715 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_712, x_1, x_701);
x_716 = lean::cnstr_get(x_715, 0);
lean::inc(x_716);
x_718 = lean::cnstr_get(x_715, 1);
lean::inc(x_718);
lean::dec(x_715);
if (lean::obj_tag(x_716) == 0)
{
obj* x_722; obj* x_725; obj* x_726; 
lean::dec(x_709);
x_722 = lean::cnstr_get(x_716, 0);
lean::inc(x_722);
lean::dec(x_716);
if (lean::is_scalar(x_680)) {
 x_725 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_725 = x_680;
 lean::cnstr_set_tag(x_680, 0);
}
lean::cnstr_set(x_725, 0, x_722);
if (lean::is_scalar(x_689)) {
 x_726 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_726 = x_689;
}
lean::cnstr_set(x_726, 0, x_725);
lean::cnstr_set(x_726, 1, x_718);
x_3 = x_726;
goto lbl_4;
}
else
{
obj* x_728; obj* x_729; 
lean::dec(x_716);
if (lean::is_scalar(x_680)) {
 x_728 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_728 = x_680;
}
lean::cnstr_set(x_728, 0, x_709);
if (lean::is_scalar(x_689)) {
 x_729 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_729 = x_689;
}
lean::cnstr_set(x_729, 0, x_728);
lean::cnstr_set(x_729, 1, x_718);
x_3 = x_729;
goto lbl_4;
}
}
}
}
}
}
case 10:
{
obj* x_730; uint8 x_732; obj* x_733; usize x_735; obj* x_736; obj* x_737; obj* x_740; obj* x_741; obj* x_743; 
x_730 = lean::cnstr_get(x_0, 0);
lean::inc(x_730);
x_732 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_733 = lean::cnstr_get(x_0, 1);
lean::inc(x_733);
x_735 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
lean::inc(x_1);
x_740 = l_lean_ir_cpp_emit__var(x_730, x_1, x_2);
x_741 = lean::cnstr_get(x_740, 0);
lean::inc(x_741);
x_743 = lean::cnstr_get(x_740, 1);
lean::inc(x_743);
lean::dec(x_740);
if (lean::obj_tag(x_741) == 0)
{
obj* x_746; obj* x_748; obj* x_749; 
x_746 = lean::cnstr_get(x_741, 0);
lean::inc(x_746);
if (lean::is_shared(x_741)) {
 lean::dec(x_741);
 x_748 = lean::box(0);
} else {
 lean::cnstr_release(x_741, 0);
 x_748 = x_741;
}
if (lean::is_scalar(x_748)) {
 x_749 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_749 = x_748;
}
lean::cnstr_set(x_749, 0, x_746);
x_736 = x_749;
x_737 = x_743;
goto lbl_738;
}
else
{
obj* x_750; obj* x_751; obj* x_754; obj* x_755; obj* x_757; 
if (lean::is_shared(x_741)) {
 lean::dec(x_741);
 x_750 = lean::box(0);
} else {
 lean::cnstr_release(x_741, 0);
 x_750 = x_741;
}
x_751 = l_lean_ir_cpp_emit__instr___closed__5;
lean::inc(x_1);
lean::inc(x_751);
x_754 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_751, x_1, x_743);
x_755 = lean::cnstr_get(x_754, 0);
lean::inc(x_755);
x_757 = lean::cnstr_get(x_754, 1);
lean::inc(x_757);
lean::dec(x_754);
if (lean::obj_tag(x_755) == 0)
{
obj* x_760; obj* x_763; 
x_760 = lean::cnstr_get(x_755, 0);
lean::inc(x_760);
lean::dec(x_755);
if (lean::is_scalar(x_750)) {
 x_763 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_763 = x_750;
 lean::cnstr_set_tag(x_750, 0);
}
lean::cnstr_set(x_763, 0, x_760);
x_736 = x_763;
x_737 = x_757;
goto lbl_738;
}
else
{
obj* x_767; obj* x_768; obj* x_770; 
lean::dec(x_750);
lean::dec(x_755);
lean::inc(x_1);
x_767 = l_lean_ir_cpp_emit__template__param(x_732, x_1, x_757);
x_768 = lean::cnstr_get(x_767, 0);
lean::inc(x_768);
x_770 = lean::cnstr_get(x_767, 1);
lean::inc(x_770);
lean::dec(x_767);
x_736 = x_768;
x_737 = x_770;
goto lbl_738;
}
}
lbl_738:
{
if (lean::obj_tag(x_736) == 0)
{
obj* x_774; obj* x_776; obj* x_777; obj* x_778; 
lean::dec(x_733);
x_774 = lean::cnstr_get(x_736, 0);
lean::inc(x_774);
if (lean::is_shared(x_736)) {
 lean::dec(x_736);
 x_776 = lean::box(0);
} else {
 lean::cnstr_release(x_736, 0);
 x_776 = x_736;
}
if (lean::is_scalar(x_776)) {
 x_777 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_777 = x_776;
}
lean::cnstr_set(x_777, 0, x_774);
x_778 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_778, 0, x_777);
lean::cnstr_set(x_778, 1, x_737);
x_3 = x_778;
goto lbl_4;
}
else
{
obj* x_779; obj* x_780; obj* x_783; obj* x_784; obj* x_786; obj* x_788; 
if (lean::is_shared(x_736)) {
 lean::dec(x_736);
 x_779 = lean::box(0);
} else {
 lean::cnstr_release(x_736, 0);
 x_779 = x_736;
}
x_780 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_780);
x_783 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_780, x_1, x_737);
x_784 = lean::cnstr_get(x_783, 0);
lean::inc(x_784);
x_786 = lean::cnstr_get(x_783, 1);
lean::inc(x_786);
if (lean::is_shared(x_783)) {
 lean::dec(x_783);
 x_788 = lean::box(0);
} else {
 lean::cnstr_release(x_783, 0);
 lean::cnstr_release(x_783, 1);
 x_788 = x_783;
}
if (lean::obj_tag(x_784) == 0)
{
obj* x_790; obj* x_793; obj* x_794; 
lean::dec(x_733);
x_790 = lean::cnstr_get(x_784, 0);
lean::inc(x_790);
lean::dec(x_784);
if (lean::is_scalar(x_779)) {
 x_793 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_793 = x_779;
 lean::cnstr_set_tag(x_779, 0);
}
lean::cnstr_set(x_793, 0, x_790);
if (lean::is_scalar(x_788)) {
 x_794 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_794 = x_788;
}
lean::cnstr_set(x_794, 0, x_793);
lean::cnstr_set(x_794, 1, x_786);
x_3 = x_794;
goto lbl_4;
}
else
{
obj* x_797; obj* x_798; obj* x_800; 
lean::dec(x_784);
lean::inc(x_1);
x_797 = l_lean_ir_cpp_emit__var(x_733, x_1, x_786);
x_798 = lean::cnstr_get(x_797, 0);
lean::inc(x_798);
x_800 = lean::cnstr_get(x_797, 1);
lean::inc(x_800);
lean::dec(x_797);
if (lean::obj_tag(x_798) == 0)
{
obj* x_803; obj* x_806; obj* x_807; 
x_803 = lean::cnstr_get(x_798, 0);
lean::inc(x_803);
lean::dec(x_798);
if (lean::is_scalar(x_779)) {
 x_806 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_806 = x_779;
 lean::cnstr_set_tag(x_779, 0);
}
lean::cnstr_set(x_806, 0, x_803);
if (lean::is_scalar(x_788)) {
 x_807 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_807 = x_788;
}
lean::cnstr_set(x_807, 0, x_806);
lean::cnstr_set(x_807, 1, x_800);
x_3 = x_807;
goto lbl_4;
}
else
{
obj* x_809; obj* x_812; obj* x_813; obj* x_815; 
lean::dec(x_798);
x_809 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_809);
x_812 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_809, x_1, x_800);
x_813 = lean::cnstr_get(x_812, 0);
lean::inc(x_813);
x_815 = lean::cnstr_get(x_812, 1);
lean::inc(x_815);
lean::dec(x_812);
if (lean::obj_tag(x_813) == 0)
{
obj* x_818; obj* x_821; obj* x_822; 
x_818 = lean::cnstr_get(x_813, 0);
lean::inc(x_818);
lean::dec(x_813);
if (lean::is_scalar(x_779)) {
 x_821 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_821 = x_779;
 lean::cnstr_set_tag(x_779, 0);
}
lean::cnstr_set(x_821, 0, x_818);
if (lean::is_scalar(x_788)) {
 x_822 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_822 = x_788;
}
lean::cnstr_set(x_822, 0, x_821);
lean::cnstr_set(x_822, 1, x_815);
x_3 = x_822;
goto lbl_4;
}
else
{
obj* x_825; obj* x_826; obj* x_828; 
lean::dec(x_813);
lean::inc(x_1);
x_825 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(x_735, x_1, x_815);
x_826 = lean::cnstr_get(x_825, 0);
lean::inc(x_826);
x_828 = lean::cnstr_get(x_825, 1);
lean::inc(x_828);
lean::dec(x_825);
if (lean::obj_tag(x_826) == 0)
{
obj* x_831; obj* x_834; obj* x_835; 
x_831 = lean::cnstr_get(x_826, 0);
lean::inc(x_831);
lean::dec(x_826);
if (lean::is_scalar(x_779)) {
 x_834 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_834 = x_779;
 lean::cnstr_set_tag(x_779, 0);
}
lean::cnstr_set(x_834, 0, x_831);
if (lean::is_scalar(x_788)) {
 x_835 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_835 = x_788;
}
lean::cnstr_set(x_835, 0, x_834);
lean::cnstr_set(x_835, 1, x_828);
x_3 = x_835;
goto lbl_4;
}
else
{
obj* x_836; obj* x_839; obj* x_842; obj* x_843; obj* x_845; 
x_836 = lean::cnstr_get(x_826, 0);
lean::inc(x_836);
lean::dec(x_826);
x_839 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
lean::inc(x_839);
x_842 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_839, x_1, x_828);
x_843 = lean::cnstr_get(x_842, 0);
lean::inc(x_843);
x_845 = lean::cnstr_get(x_842, 1);
lean::inc(x_845);
lean::dec(x_842);
if (lean::obj_tag(x_843) == 0)
{
obj* x_849; obj* x_852; obj* x_853; 
lean::dec(x_836);
x_849 = lean::cnstr_get(x_843, 0);
lean::inc(x_849);
lean::dec(x_843);
if (lean::is_scalar(x_779)) {
 x_852 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_852 = x_779;
 lean::cnstr_set_tag(x_779, 0);
}
lean::cnstr_set(x_852, 0, x_849);
if (lean::is_scalar(x_788)) {
 x_853 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_853 = x_788;
}
lean::cnstr_set(x_853, 0, x_852);
lean::cnstr_set(x_853, 1, x_845);
x_3 = x_853;
goto lbl_4;
}
else
{
obj* x_855; obj* x_856; 
lean::dec(x_843);
if (lean::is_scalar(x_779)) {
 x_855 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_855 = x_779;
}
lean::cnstr_set(x_855, 0, x_836);
if (lean::is_scalar(x_788)) {
 x_856 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_856 = x_788;
}
lean::cnstr_set(x_856, 0, x_855);
lean::cnstr_set(x_856, 1, x_845);
x_3 = x_856;
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
obj* x_857; obj* x_859; obj* x_861; obj* x_864; 
x_857 = lean::cnstr_get(x_0, 0);
lean::inc(x_857);
x_859 = lean::cnstr_get(x_0, 1);
lean::inc(x_859);
x_861 = lean::cnstr_get(x_0, 2);
lean::inc(x_861);
lean::inc(x_1);
x_864 = l_lean_ir_cpp_emit__closure(x_857, x_859, x_861, x_1, x_2);
x_3 = x_864;
goto lbl_4;
}
case 12:
{
obj* x_865; obj* x_867; obj* x_870; 
x_865 = lean::cnstr_get(x_0, 0);
lean::inc(x_865);
x_867 = lean::cnstr_get(x_0, 1);
lean::inc(x_867);
lean::inc(x_1);
x_870 = l_lean_ir_cpp_emit__apply(x_865, x_867, x_1, x_2);
x_3 = x_870;
goto lbl_4;
}
case 13:
{
obj* x_871; obj* x_873; obj* x_875; obj* x_877; obj* x_878; obj* x_881; obj* x_882; obj* x_884; 
x_871 = lean::cnstr_get(x_0, 0);
lean::inc(x_871);
x_873 = lean::cnstr_get(x_0, 1);
lean::inc(x_873);
x_875 = lean::cnstr_get(x_0, 2);
lean::inc(x_875);
lean::inc(x_1);
x_881 = l_lean_ir_cpp_emit__var(x_871, x_1, x_2);
x_882 = lean::cnstr_get(x_881, 0);
lean::inc(x_882);
x_884 = lean::cnstr_get(x_881, 1);
lean::inc(x_884);
lean::dec(x_881);
if (lean::obj_tag(x_882) == 0)
{
obj* x_887; obj* x_889; obj* x_890; 
x_887 = lean::cnstr_get(x_882, 0);
lean::inc(x_887);
if (lean::is_shared(x_882)) {
 lean::dec(x_882);
 x_889 = lean::box(0);
} else {
 lean::cnstr_release(x_882, 0);
 x_889 = x_882;
}
if (lean::is_scalar(x_889)) {
 x_890 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_890 = x_889;
}
lean::cnstr_set(x_890, 0, x_887);
x_877 = x_890;
x_878 = x_884;
goto lbl_879;
}
else
{
obj* x_892; obj* x_895; obj* x_896; obj* x_898; 
lean::dec(x_882);
x_892 = l_lean_ir_cpp_emit__instr___closed__6;
lean::inc(x_1);
lean::inc(x_892);
x_895 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_892, x_1, x_884);
x_896 = lean::cnstr_get(x_895, 0);
lean::inc(x_896);
x_898 = lean::cnstr_get(x_895, 1);
lean::inc(x_898);
lean::dec(x_895);
x_877 = x_896;
x_878 = x_898;
goto lbl_879;
}
lbl_879:
{
if (lean::obj_tag(x_877) == 0)
{
obj* x_903; obj* x_905; obj* x_906; obj* x_907; 
lean::dec(x_875);
lean::dec(x_873);
x_903 = lean::cnstr_get(x_877, 0);
lean::inc(x_903);
if (lean::is_shared(x_877)) {
 lean::dec(x_877);
 x_905 = lean::box(0);
} else {
 lean::cnstr_release(x_877, 0);
 x_905 = x_877;
}
if (lean::is_scalar(x_905)) {
 x_906 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_906 = x_905;
}
lean::cnstr_set(x_906, 0, x_903);
x_907 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_907, 0, x_906);
lean::cnstr_set(x_907, 1, x_878);
x_3 = x_907;
goto lbl_4;
}
else
{
obj* x_908; obj* x_909; obj* x_912; obj* x_913; obj* x_915; obj* x_917; 
if (lean::is_shared(x_877)) {
 lean::dec(x_877);
 x_908 = lean::box(0);
} else {
 lean::cnstr_release(x_877, 0);
 x_908 = x_877;
}
x_909 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_909);
x_912 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_909, x_1, x_878);
x_913 = lean::cnstr_get(x_912, 0);
lean::inc(x_913);
x_915 = lean::cnstr_get(x_912, 1);
lean::inc(x_915);
if (lean::is_shared(x_912)) {
 lean::dec(x_912);
 x_917 = lean::box(0);
} else {
 lean::cnstr_release(x_912, 0);
 lean::cnstr_release(x_912, 1);
 x_917 = x_912;
}
if (lean::obj_tag(x_913) == 0)
{
obj* x_920; obj* x_923; obj* x_924; 
lean::dec(x_875);
lean::dec(x_873);
x_920 = lean::cnstr_get(x_913, 0);
lean::inc(x_920);
lean::dec(x_913);
if (lean::is_scalar(x_908)) {
 x_923 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_923 = x_908;
 lean::cnstr_set_tag(x_908, 0);
}
lean::cnstr_set(x_923, 0, x_920);
if (lean::is_scalar(x_917)) {
 x_924 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_924 = x_917;
}
lean::cnstr_set(x_924, 0, x_923);
lean::cnstr_set(x_924, 1, x_915);
x_3 = x_924;
goto lbl_4;
}
else
{
obj* x_927; obj* x_928; obj* x_930; 
lean::dec(x_913);
lean::inc(x_1);
x_927 = l_lean_ir_cpp_emit__var(x_873, x_1, x_915);
x_928 = lean::cnstr_get(x_927, 0);
lean::inc(x_928);
x_930 = lean::cnstr_get(x_927, 1);
lean::inc(x_930);
lean::dec(x_927);
if (lean::obj_tag(x_928) == 0)
{
obj* x_934; obj* x_937; obj* x_938; 
lean::dec(x_875);
x_934 = lean::cnstr_get(x_928, 0);
lean::inc(x_934);
lean::dec(x_928);
if (lean::is_scalar(x_908)) {
 x_937 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_937 = x_908;
 lean::cnstr_set_tag(x_908, 0);
}
lean::cnstr_set(x_937, 0, x_934);
if (lean::is_scalar(x_917)) {
 x_938 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_938 = x_917;
}
lean::cnstr_set(x_938, 0, x_937);
lean::cnstr_set(x_938, 1, x_930);
x_3 = x_938;
goto lbl_4;
}
else
{
obj* x_940; obj* x_943; obj* x_944; obj* x_946; 
lean::dec(x_928);
x_940 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_940);
x_943 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_940, x_1, x_930);
x_944 = lean::cnstr_get(x_943, 0);
lean::inc(x_944);
x_946 = lean::cnstr_get(x_943, 1);
lean::inc(x_946);
lean::dec(x_943);
if (lean::obj_tag(x_944) == 0)
{
obj* x_950; obj* x_953; obj* x_954; 
lean::dec(x_875);
x_950 = lean::cnstr_get(x_944, 0);
lean::inc(x_950);
lean::dec(x_944);
if (lean::is_scalar(x_908)) {
 x_953 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_953 = x_908;
 lean::cnstr_set_tag(x_908, 0);
}
lean::cnstr_set(x_953, 0, x_950);
if (lean::is_scalar(x_917)) {
 x_954 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_954 = x_917;
}
lean::cnstr_set(x_954, 0, x_953);
lean::cnstr_set(x_954, 1, x_946);
x_3 = x_954;
goto lbl_4;
}
else
{
obj* x_957; obj* x_958; obj* x_960; 
lean::dec(x_944);
lean::inc(x_1);
x_957 = l_lean_ir_cpp_emit__var(x_875, x_1, x_946);
x_958 = lean::cnstr_get(x_957, 0);
lean::inc(x_958);
x_960 = lean::cnstr_get(x_957, 1);
lean::inc(x_960);
lean::dec(x_957);
if (lean::obj_tag(x_958) == 0)
{
obj* x_963; obj* x_966; obj* x_967; 
x_963 = lean::cnstr_get(x_958, 0);
lean::inc(x_963);
lean::dec(x_958);
if (lean::is_scalar(x_908)) {
 x_966 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_966 = x_908;
 lean::cnstr_set_tag(x_908, 0);
}
lean::cnstr_set(x_966, 0, x_963);
if (lean::is_scalar(x_917)) {
 x_967 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_967 = x_917;
}
lean::cnstr_set(x_967, 0, x_966);
lean::cnstr_set(x_967, 1, x_960);
x_3 = x_967;
goto lbl_4;
}
else
{
obj* x_968; obj* x_971; obj* x_974; obj* x_975; obj* x_977; 
x_968 = lean::cnstr_get(x_958, 0);
lean::inc(x_968);
lean::dec(x_958);
x_971 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
lean::inc(x_971);
x_974 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_971, x_1, x_960);
x_975 = lean::cnstr_get(x_974, 0);
lean::inc(x_975);
x_977 = lean::cnstr_get(x_974, 1);
lean::inc(x_977);
lean::dec(x_974);
if (lean::obj_tag(x_975) == 0)
{
obj* x_981; obj* x_984; obj* x_985; 
lean::dec(x_968);
x_981 = lean::cnstr_get(x_975, 0);
lean::inc(x_981);
lean::dec(x_975);
if (lean::is_scalar(x_908)) {
 x_984 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_984 = x_908;
 lean::cnstr_set_tag(x_908, 0);
}
lean::cnstr_set(x_984, 0, x_981);
if (lean::is_scalar(x_917)) {
 x_985 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_985 = x_917;
}
lean::cnstr_set(x_985, 0, x_984);
lean::cnstr_set(x_985, 1, x_977);
x_3 = x_985;
goto lbl_4;
}
else
{
obj* x_987; obj* x_988; 
lean::dec(x_975);
if (lean::is_scalar(x_908)) {
 x_987 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_987 = x_908;
}
lean::cnstr_set(x_987, 0, x_968);
if (lean::is_scalar(x_917)) {
 x_988 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_988 = x_917;
}
lean::cnstr_set(x_988, 0, x_987);
lean::cnstr_set(x_988, 1, x_977);
x_3 = x_988;
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
obj* x_989; uint8 x_991; obj* x_992; obj* x_994; obj* x_996; obj* x_997; obj* x_999; obj* x_1000; obj* x_1003; obj* x_1004; obj* x_1006; 
x_989 = lean::cnstr_get(x_0, 0);
lean::inc(x_989);
x_991 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_992 = lean::cnstr_get(x_0, 1);
lean::inc(x_992);
x_994 = lean::cnstr_get(x_0, 2);
lean::inc(x_994);
lean::inc(x_1);
x_1003 = l_lean_ir_cpp_emit__var(x_989, x_1, x_2);
x_1004 = lean::cnstr_get(x_1003, 0);
lean::inc(x_1004);
x_1006 = lean::cnstr_get(x_1003, 1);
lean::inc(x_1006);
lean::dec(x_1003);
if (lean::obj_tag(x_1004) == 0)
{
obj* x_1009; obj* x_1011; obj* x_1012; 
x_1009 = lean::cnstr_get(x_1004, 0);
lean::inc(x_1009);
if (lean::is_shared(x_1004)) {
 lean::dec(x_1004);
 x_1011 = lean::box(0);
} else {
 lean::cnstr_release(x_1004, 0);
 x_1011 = x_1004;
}
if (lean::is_scalar(x_1011)) {
 x_1012 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1012 = x_1011;
}
lean::cnstr_set(x_1012, 0, x_1009);
x_999 = x_1012;
x_1000 = x_1006;
goto lbl_1001;
}
else
{
obj* x_1014; obj* x_1017; obj* x_1018; obj* x_1020; 
lean::dec(x_1004);
x_1014 = l_lean_ir_cpp_emit__instr___closed__7;
lean::inc(x_1);
lean::inc(x_1014);
x_1017 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1014, x_1, x_1006);
x_1018 = lean::cnstr_get(x_1017, 0);
lean::inc(x_1018);
x_1020 = lean::cnstr_get(x_1017, 1);
lean::inc(x_1020);
lean::dec(x_1017);
x_999 = x_1018;
x_1000 = x_1020;
goto lbl_1001;
}
lbl_998:
{
if (lean::obj_tag(x_996) == 0)
{
obj* x_1024; obj* x_1026; obj* x_1027; obj* x_1028; 
lean::dec(x_994);
x_1024 = lean::cnstr_get(x_996, 0);
lean::inc(x_1024);
if (lean::is_shared(x_996)) {
 lean::dec(x_996);
 x_1026 = lean::box(0);
} else {
 lean::cnstr_release(x_996, 0);
 x_1026 = x_996;
}
if (lean::is_scalar(x_1026)) {
 x_1027 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1027 = x_1026;
}
lean::cnstr_set(x_1027, 0, x_1024);
x_1028 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1028, 0, x_1027);
lean::cnstr_set(x_1028, 1, x_997);
x_3 = x_1028;
goto lbl_4;
}
else
{
obj* x_1029; obj* x_1030; obj* x_1033; obj* x_1034; obj* x_1036; obj* x_1038; 
if (lean::is_shared(x_996)) {
 lean::dec(x_996);
 x_1029 = lean::box(0);
} else {
 lean::cnstr_release(x_996, 0);
 x_1029 = x_996;
}
x_1030 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_1030);
x_1033 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1030, x_1, x_997);
x_1034 = lean::cnstr_get(x_1033, 0);
lean::inc(x_1034);
x_1036 = lean::cnstr_get(x_1033, 1);
lean::inc(x_1036);
if (lean::is_shared(x_1033)) {
 lean::dec(x_1033);
 x_1038 = lean::box(0);
} else {
 lean::cnstr_release(x_1033, 0);
 lean::cnstr_release(x_1033, 1);
 x_1038 = x_1033;
}
if (lean::obj_tag(x_1034) == 0)
{
obj* x_1040; obj* x_1043; obj* x_1044; 
lean::dec(x_994);
x_1040 = lean::cnstr_get(x_1034, 0);
lean::inc(x_1040);
lean::dec(x_1034);
if (lean::is_scalar(x_1029)) {
 x_1043 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1043 = x_1029;
 lean::cnstr_set_tag(x_1029, 0);
}
lean::cnstr_set(x_1043, 0, x_1040);
if (lean::is_scalar(x_1038)) {
 x_1044 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1044 = x_1038;
}
lean::cnstr_set(x_1044, 0, x_1043);
lean::cnstr_set(x_1044, 1, x_1036);
x_3 = x_1044;
goto lbl_4;
}
else
{
obj* x_1047; obj* x_1048; obj* x_1050; 
lean::dec(x_1034);
lean::inc(x_1);
x_1047 = l_lean_ir_cpp_emit__var(x_994, x_1, x_1036);
x_1048 = lean::cnstr_get(x_1047, 0);
lean::inc(x_1048);
x_1050 = lean::cnstr_get(x_1047, 1);
lean::inc(x_1050);
lean::dec(x_1047);
if (lean::obj_tag(x_1048) == 0)
{
obj* x_1053; obj* x_1056; obj* x_1057; 
x_1053 = lean::cnstr_get(x_1048, 0);
lean::inc(x_1053);
lean::dec(x_1048);
if (lean::is_scalar(x_1029)) {
 x_1056 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1056 = x_1029;
 lean::cnstr_set_tag(x_1029, 0);
}
lean::cnstr_set(x_1056, 0, x_1053);
if (lean::is_scalar(x_1038)) {
 x_1057 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1057 = x_1038;
}
lean::cnstr_set(x_1057, 0, x_1056);
lean::cnstr_set(x_1057, 1, x_1050);
x_3 = x_1057;
goto lbl_4;
}
else
{
obj* x_1058; obj* x_1061; obj* x_1064; obj* x_1065; obj* x_1067; 
x_1058 = lean::cnstr_get(x_1048, 0);
lean::inc(x_1058);
lean::dec(x_1048);
x_1061 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
lean::inc(x_1061);
x_1064 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1061, x_1, x_1050);
x_1065 = lean::cnstr_get(x_1064, 0);
lean::inc(x_1065);
x_1067 = lean::cnstr_get(x_1064, 1);
lean::inc(x_1067);
lean::dec(x_1064);
if (lean::obj_tag(x_1065) == 0)
{
obj* x_1071; obj* x_1074; obj* x_1075; 
lean::dec(x_1058);
x_1071 = lean::cnstr_get(x_1065, 0);
lean::inc(x_1071);
lean::dec(x_1065);
if (lean::is_scalar(x_1029)) {
 x_1074 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1074 = x_1029;
 lean::cnstr_set_tag(x_1029, 0);
}
lean::cnstr_set(x_1074, 0, x_1071);
if (lean::is_scalar(x_1038)) {
 x_1075 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1075 = x_1038;
}
lean::cnstr_set(x_1075, 0, x_1074);
lean::cnstr_set(x_1075, 1, x_1067);
x_3 = x_1075;
goto lbl_4;
}
else
{
obj* x_1077; obj* x_1078; 
lean::dec(x_1065);
if (lean::is_scalar(x_1029)) {
 x_1077 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1077 = x_1029;
}
lean::cnstr_set(x_1077, 0, x_1058);
if (lean::is_scalar(x_1038)) {
 x_1078 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1078 = x_1038;
}
lean::cnstr_set(x_1078, 0, x_1077);
lean::cnstr_set(x_1078, 1, x_1067);
x_3 = x_1078;
goto lbl_4;
}
}
}
}
}
lbl_1001:
{
if (lean::obj_tag(x_999) == 0)
{
obj* x_1081; obj* x_1083; obj* x_1084; obj* x_1085; 
lean::dec(x_992);
lean::dec(x_994);
x_1081 = lean::cnstr_get(x_999, 0);
lean::inc(x_1081);
if (lean::is_shared(x_999)) {
 lean::dec(x_999);
 x_1083 = lean::box(0);
} else {
 lean::cnstr_release(x_999, 0);
 x_1083 = x_999;
}
if (lean::is_scalar(x_1083)) {
 x_1084 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1084 = x_1083;
}
lean::cnstr_set(x_1084, 0, x_1081);
x_1085 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1085, 0, x_1084);
lean::cnstr_set(x_1085, 1, x_1000);
x_3 = x_1085;
goto lbl_4;
}
else
{
obj* x_1086; obj* x_1087; obj* x_1090; obj* x_1091; obj* x_1093; obj* x_1095; 
if (lean::is_shared(x_999)) {
 lean::dec(x_999);
 x_1086 = lean::box(0);
} else {
 lean::cnstr_release(x_999, 0);
 x_1086 = x_999;
}
x_1087 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_1087);
x_1090 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1087, x_1, x_1000);
x_1091 = lean::cnstr_get(x_1090, 0);
lean::inc(x_1091);
x_1093 = lean::cnstr_get(x_1090, 1);
lean::inc(x_1093);
if (lean::is_shared(x_1090)) {
 lean::dec(x_1090);
 x_1095 = lean::box(0);
} else {
 lean::cnstr_release(x_1090, 0);
 lean::cnstr_release(x_1090, 1);
 x_1095 = x_1090;
}
if (lean::obj_tag(x_1091) == 0)
{
obj* x_1098; obj* x_1101; obj* x_1102; 
lean::dec(x_992);
lean::dec(x_994);
x_1098 = lean::cnstr_get(x_1091, 0);
lean::inc(x_1098);
lean::dec(x_1091);
if (lean::is_scalar(x_1086)) {
 x_1101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1101 = x_1086;
 lean::cnstr_set_tag(x_1086, 0);
}
lean::cnstr_set(x_1101, 0, x_1098);
if (lean::is_scalar(x_1095)) {
 x_1102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1102 = x_1095;
}
lean::cnstr_set(x_1102, 0, x_1101);
lean::cnstr_set(x_1102, 1, x_1093);
x_3 = x_1102;
goto lbl_4;
}
else
{
obj* x_1106; obj* x_1107; obj* x_1109; 
lean::dec(x_1091);
lean::dec(x_1095);
lean::inc(x_1);
x_1106 = l_lean_ir_cpp_emit__type__size(x_991, x_1, x_1093);
x_1107 = lean::cnstr_get(x_1106, 0);
lean::inc(x_1107);
x_1109 = lean::cnstr_get(x_1106, 1);
lean::inc(x_1109);
lean::dec(x_1106);
if (lean::obj_tag(x_1107) == 0)
{
obj* x_1113; obj* x_1116; 
lean::dec(x_992);
x_1113 = lean::cnstr_get(x_1107, 0);
lean::inc(x_1113);
lean::dec(x_1107);
if (lean::is_scalar(x_1086)) {
 x_1116 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1116 = x_1086;
 lean::cnstr_set_tag(x_1086, 0);
}
lean::cnstr_set(x_1116, 0, x_1113);
x_996 = x_1116;
x_997 = x_1109;
goto lbl_998;
}
else
{
obj* x_1118; obj* x_1121; obj* x_1122; obj* x_1124; 
lean::dec(x_1107);
x_1118 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_1118);
x_1121 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1118, x_1, x_1109);
x_1122 = lean::cnstr_get(x_1121, 0);
lean::inc(x_1122);
x_1124 = lean::cnstr_get(x_1121, 1);
lean::inc(x_1124);
lean::dec(x_1121);
if (lean::obj_tag(x_1122) == 0)
{
obj* x_1128; obj* x_1131; 
lean::dec(x_992);
x_1128 = lean::cnstr_get(x_1122, 0);
lean::inc(x_1128);
lean::dec(x_1122);
if (lean::is_scalar(x_1086)) {
 x_1131 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1131 = x_1086;
 lean::cnstr_set_tag(x_1086, 0);
}
lean::cnstr_set(x_1131, 0, x_1128);
x_996 = x_1131;
x_997 = x_1124;
goto lbl_998;
}
else
{
obj* x_1135; obj* x_1136; obj* x_1138; 
lean::dec(x_1122);
lean::dec(x_1086);
lean::inc(x_1);
x_1135 = l_lean_ir_cpp_emit__var(x_992, x_1, x_1124);
x_1136 = lean::cnstr_get(x_1135, 0);
lean::inc(x_1136);
x_1138 = lean::cnstr_get(x_1135, 1);
lean::inc(x_1138);
lean::dec(x_1135);
x_996 = x_1136;
x_997 = x_1138;
goto lbl_998;
}
}
}
}
}
}
default:
{
obj* x_1141; obj* x_1143; obj* x_1145; obj* x_1147; obj* x_1148; obj* x_1150; obj* x_1152; obj* x_1154; obj* x_1157; 
x_1141 = lean::cnstr_get(x_0, 0);
lean::inc(x_1141);
x_1143 = lean::cnstr_get(x_0, 1);
lean::inc(x_1143);
x_1145 = lean::cnstr_get(x_0, 2);
lean::inc(x_1145);
x_1154 = lean::cnstr_get(x_1, 1);
lean::inc(x_1154);
lean::inc(x_1145);
x_1157 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_1154, x_1145);
if (lean::obj_tag(x_1157) == 0)
{
obj* x_1159; 
lean::dec(x_1157);
x_1159 = lean::box(0);
x_1150 = x_1159;
goto lbl_1151;
}
else
{
obj* x_1160; uint8 x_1163; obj* x_1165; obj* x_1166; uint8 x_1167; 
x_1160 = lean::cnstr_get(x_1157, 0);
lean::inc(x_1160);
lean::dec(x_1157);
x_1163 = lean::unbox(x_1160);
lean::dec(x_1160);
x_1165 = l_lean_ir_type2id___main(x_1163);
x_1166 = l_lean_ir_valid__assign__unop__types___closed__1;
x_1167 = lean::nat_dec_eq(x_1165, x_1166);
lean::dec(x_1165);
if (x_1167 == 0)
{
obj* x_1169; 
x_1169 = lean::box(0);
x_1150 = x_1169;
goto lbl_1151;
}
else
{
obj* x_1170; 
x_1170 = lean::box(0);
x_1152 = x_1170;
goto lbl_1153;
}
}
lbl_1149:
{
if (lean::obj_tag(x_1147) == 0)
{
obj* x_1172; obj* x_1174; obj* x_1175; obj* x_1176; 
lean::dec(x_1145);
x_1172 = lean::cnstr_get(x_1147, 0);
lean::inc(x_1172);
if (lean::is_shared(x_1147)) {
 lean::dec(x_1147);
 x_1174 = lean::box(0);
} else {
 lean::cnstr_release(x_1147, 0);
 x_1174 = x_1147;
}
if (lean::is_scalar(x_1174)) {
 x_1175 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1175 = x_1174;
}
lean::cnstr_set(x_1175, 0, x_1172);
x_1176 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1176, 0, x_1175);
lean::cnstr_set(x_1176, 1, x_1148);
x_3 = x_1176;
goto lbl_4;
}
else
{
obj* x_1177; obj* x_1178; obj* x_1181; obj* x_1182; obj* x_1184; obj* x_1186; 
if (lean::is_shared(x_1147)) {
 lean::dec(x_1147);
 x_1177 = lean::box(0);
} else {
 lean::cnstr_release(x_1147, 0);
 x_1177 = x_1147;
}
x_1178 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_1178);
x_1181 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1178, x_1, x_1148);
x_1182 = lean::cnstr_get(x_1181, 0);
lean::inc(x_1182);
x_1184 = lean::cnstr_get(x_1181, 1);
lean::inc(x_1184);
if (lean::is_shared(x_1181)) {
 lean::dec(x_1181);
 x_1186 = lean::box(0);
} else {
 lean::cnstr_release(x_1181, 0);
 lean::cnstr_release(x_1181, 1);
 x_1186 = x_1181;
}
if (lean::obj_tag(x_1182) == 0)
{
obj* x_1188; obj* x_1191; obj* x_1192; 
lean::dec(x_1145);
x_1188 = lean::cnstr_get(x_1182, 0);
lean::inc(x_1188);
lean::dec(x_1182);
if (lean::is_scalar(x_1177)) {
 x_1191 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1191 = x_1177;
 lean::cnstr_set_tag(x_1177, 0);
}
lean::cnstr_set(x_1191, 0, x_1188);
if (lean::is_scalar(x_1186)) {
 x_1192 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1192 = x_1186;
}
lean::cnstr_set(x_1192, 0, x_1191);
lean::cnstr_set(x_1192, 1, x_1184);
x_3 = x_1192;
goto lbl_4;
}
else
{
obj* x_1195; obj* x_1196; obj* x_1198; 
lean::dec(x_1182);
lean::inc(x_1);
x_1195 = l_lean_ir_cpp_emit__var(x_1145, x_1, x_1184);
x_1196 = lean::cnstr_get(x_1195, 0);
lean::inc(x_1196);
x_1198 = lean::cnstr_get(x_1195, 1);
lean::inc(x_1198);
lean::dec(x_1195);
if (lean::obj_tag(x_1196) == 0)
{
obj* x_1201; obj* x_1204; obj* x_1205; 
x_1201 = lean::cnstr_get(x_1196, 0);
lean::inc(x_1201);
lean::dec(x_1196);
if (lean::is_scalar(x_1177)) {
 x_1204 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1204 = x_1177;
 lean::cnstr_set_tag(x_1177, 0);
}
lean::cnstr_set(x_1204, 0, x_1201);
if (lean::is_scalar(x_1186)) {
 x_1205 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1205 = x_1186;
}
lean::cnstr_set(x_1205, 0, x_1204);
lean::cnstr_set(x_1205, 1, x_1198);
x_3 = x_1205;
goto lbl_4;
}
else
{
obj* x_1206; obj* x_1209; obj* x_1212; obj* x_1213; obj* x_1215; 
x_1206 = lean::cnstr_get(x_1196, 0);
lean::inc(x_1206);
lean::dec(x_1196);
x_1209 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
lean::inc(x_1209);
x_1212 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1209, x_1, x_1198);
x_1213 = lean::cnstr_get(x_1212, 0);
lean::inc(x_1213);
x_1215 = lean::cnstr_get(x_1212, 1);
lean::inc(x_1215);
lean::dec(x_1212);
if (lean::obj_tag(x_1213) == 0)
{
obj* x_1219; obj* x_1222; obj* x_1223; 
lean::dec(x_1206);
x_1219 = lean::cnstr_get(x_1213, 0);
lean::inc(x_1219);
lean::dec(x_1213);
if (lean::is_scalar(x_1177)) {
 x_1222 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1222 = x_1177;
 lean::cnstr_set_tag(x_1177, 0);
}
lean::cnstr_set(x_1222, 0, x_1219);
if (lean::is_scalar(x_1186)) {
 x_1223 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1223 = x_1186;
}
lean::cnstr_set(x_1223, 0, x_1222);
lean::cnstr_set(x_1223, 1, x_1215);
x_3 = x_1223;
goto lbl_4;
}
else
{
obj* x_1225; obj* x_1226; 
lean::dec(x_1213);
if (lean::is_scalar(x_1177)) {
 x_1225 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1225 = x_1177;
}
lean::cnstr_set(x_1225, 0, x_1206);
if (lean::is_scalar(x_1186)) {
 x_1226 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1226 = x_1186;
}
lean::cnstr_set(x_1226, 0, x_1225);
lean::cnstr_set(x_1226, 1, x_1215);
x_3 = x_1226;
goto lbl_4;
}
}
}
}
}
lbl_1151:
{
obj* x_1228; obj* x_1231; obj* x_1232; obj* x_1234; obj* x_1236; 
lean::dec(x_1150);
x_1228 = l_lean_ir_cpp_emit__instr___closed__8;
lean::inc(x_1);
lean::inc(x_1228);
x_1231 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1228, x_1, x_2);
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
lean::dec(x_1145);
lean::dec(x_1141);
lean::dec(x_1143);
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
x_1246 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_1246);
x_1249 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1246, x_1, x_1234);
x_1250 = lean::cnstr_get(x_1249, 0);
lean::inc(x_1250);
x_1252 = lean::cnstr_get(x_1249, 1);
lean::inc(x_1252);
lean::dec(x_1249);
if (lean::obj_tag(x_1250) == 0)
{
obj* x_1258; obj* x_1261; obj* x_1262; 
lean::dec(x_1145);
lean::dec(x_1141);
lean::dec(x_1143);
x_1258 = lean::cnstr_get(x_1250, 0);
lean::inc(x_1258);
lean::dec(x_1250);
if (lean::is_scalar(x_1245)) {
 x_1261 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1261 = x_1245;
 lean::cnstr_set_tag(x_1245, 0);
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
x_1266 = l_lean_ir_cpp_emit__var(x_1141, x_1, x_1252);
x_1267 = lean::cnstr_get(x_1266, 0);
lean::inc(x_1267);
x_1269 = lean::cnstr_get(x_1266, 1);
lean::inc(x_1269);
lean::dec(x_1266);
if (lean::obj_tag(x_1267) == 0)
{
obj* x_1273; obj* x_1276; 
lean::dec(x_1143);
x_1273 = lean::cnstr_get(x_1267, 0);
lean::inc(x_1273);
lean::dec(x_1267);
if (lean::is_scalar(x_1245)) {
 x_1276 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1276 = x_1245;
 lean::cnstr_set_tag(x_1245, 0);
}
lean::cnstr_set(x_1276, 0, x_1273);
x_1147 = x_1276;
x_1148 = x_1269;
goto lbl_1149;
}
else
{
obj* x_1278; obj* x_1281; obj* x_1282; obj* x_1284; 
lean::dec(x_1267);
x_1278 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_1278);
x_1281 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1278, x_1, x_1269);
x_1282 = lean::cnstr_get(x_1281, 0);
lean::inc(x_1282);
x_1284 = lean::cnstr_get(x_1281, 1);
lean::inc(x_1284);
lean::dec(x_1281);
if (lean::obj_tag(x_1282) == 0)
{
obj* x_1288; obj* x_1291; 
lean::dec(x_1143);
x_1288 = lean::cnstr_get(x_1282, 0);
lean::inc(x_1288);
lean::dec(x_1282);
if (lean::is_scalar(x_1245)) {
 x_1291 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1291 = x_1245;
 lean::cnstr_set_tag(x_1245, 0);
}
lean::cnstr_set(x_1291, 0, x_1288);
x_1147 = x_1291;
x_1148 = x_1284;
goto lbl_1149;
}
else
{
obj* x_1295; obj* x_1296; obj* x_1298; 
lean::dec(x_1282);
lean::dec(x_1245);
lean::inc(x_1);
x_1295 = l_lean_ir_cpp_emit__var(x_1143, x_1, x_1284);
x_1296 = lean::cnstr_get(x_1295, 0);
lean::inc(x_1296);
x_1298 = lean::cnstr_get(x_1295, 1);
lean::inc(x_1298);
lean::dec(x_1295);
x_1147 = x_1296;
x_1148 = x_1298;
goto lbl_1149;
}
}
}
}
}
lbl_1153:
{
obj* x_1302; obj* x_1305; obj* x_1306; obj* x_1308; obj* x_1310; 
lean::dec(x_1152);
x_1302 = l_lean_ir_cpp_emit__instr___closed__9;
lean::inc(x_1);
lean::inc(x_1302);
x_1305 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1302, x_1, x_2);
x_1306 = lean::cnstr_get(x_1305, 0);
lean::inc(x_1306);
x_1308 = lean::cnstr_get(x_1305, 1);
lean::inc(x_1308);
if (lean::is_shared(x_1305)) {
 lean::dec(x_1305);
 x_1310 = lean::box(0);
} else {
 lean::cnstr_release(x_1305, 0);
 lean::cnstr_release(x_1305, 1);
 x_1310 = x_1305;
}
if (lean::obj_tag(x_1306) == 0)
{
obj* x_1314; obj* x_1316; obj* x_1317; obj* x_1318; 
lean::dec(x_1145);
lean::dec(x_1141);
lean::dec(x_1143);
x_1314 = lean::cnstr_get(x_1306, 0);
lean::inc(x_1314);
if (lean::is_shared(x_1306)) {
 lean::dec(x_1306);
 x_1316 = lean::box(0);
} else {
 lean::cnstr_release(x_1306, 0);
 x_1316 = x_1306;
}
if (lean::is_scalar(x_1316)) {
 x_1317 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1317 = x_1316;
}
lean::cnstr_set(x_1317, 0, x_1314);
if (lean::is_scalar(x_1310)) {
 x_1318 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1318 = x_1310;
}
lean::cnstr_set(x_1318, 0, x_1317);
lean::cnstr_set(x_1318, 1, x_1308);
x_3 = x_1318;
goto lbl_4;
}
else
{
obj* x_1319; obj* x_1320; obj* x_1323; obj* x_1324; obj* x_1326; 
if (lean::is_shared(x_1306)) {
 lean::dec(x_1306);
 x_1319 = lean::box(0);
} else {
 lean::cnstr_release(x_1306, 0);
 x_1319 = x_1306;
}
x_1320 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_1320);
x_1323 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1320, x_1, x_1308);
x_1324 = lean::cnstr_get(x_1323, 0);
lean::inc(x_1324);
x_1326 = lean::cnstr_get(x_1323, 1);
lean::inc(x_1326);
lean::dec(x_1323);
if (lean::obj_tag(x_1324) == 0)
{
obj* x_1332; obj* x_1335; obj* x_1336; 
lean::dec(x_1145);
lean::dec(x_1141);
lean::dec(x_1143);
x_1332 = lean::cnstr_get(x_1324, 0);
lean::inc(x_1332);
lean::dec(x_1324);
if (lean::is_scalar(x_1319)) {
 x_1335 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1335 = x_1319;
 lean::cnstr_set_tag(x_1319, 0);
}
lean::cnstr_set(x_1335, 0, x_1332);
if (lean::is_scalar(x_1310)) {
 x_1336 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1336 = x_1310;
}
lean::cnstr_set(x_1336, 0, x_1335);
lean::cnstr_set(x_1336, 1, x_1326);
x_3 = x_1336;
goto lbl_4;
}
else
{
obj* x_1340; obj* x_1341; obj* x_1343; 
lean::dec(x_1324);
lean::dec(x_1310);
lean::inc(x_1);
x_1340 = l_lean_ir_cpp_emit__var(x_1141, x_1, x_1326);
x_1341 = lean::cnstr_get(x_1340, 0);
lean::inc(x_1341);
x_1343 = lean::cnstr_get(x_1340, 1);
lean::inc(x_1343);
lean::dec(x_1340);
if (lean::obj_tag(x_1341) == 0)
{
obj* x_1347; obj* x_1350; 
lean::dec(x_1143);
x_1347 = lean::cnstr_get(x_1341, 0);
lean::inc(x_1347);
lean::dec(x_1341);
if (lean::is_scalar(x_1319)) {
 x_1350 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1350 = x_1319;
 lean::cnstr_set_tag(x_1319, 0);
}
lean::cnstr_set(x_1350, 0, x_1347);
x_1147 = x_1350;
x_1148 = x_1343;
goto lbl_1149;
}
else
{
obj* x_1352; obj* x_1355; obj* x_1356; obj* x_1358; 
lean::dec(x_1341);
x_1352 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_1352);
x_1355 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1352, x_1, x_1343);
x_1356 = lean::cnstr_get(x_1355, 0);
lean::inc(x_1356);
x_1358 = lean::cnstr_get(x_1355, 1);
lean::inc(x_1358);
lean::dec(x_1355);
if (lean::obj_tag(x_1356) == 0)
{
obj* x_1362; obj* x_1365; 
lean::dec(x_1143);
x_1362 = lean::cnstr_get(x_1356, 0);
lean::inc(x_1362);
lean::dec(x_1356);
if (lean::is_scalar(x_1319)) {
 x_1365 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1365 = x_1319;
 lean::cnstr_set_tag(x_1319, 0);
}
lean::cnstr_set(x_1365, 0, x_1362);
x_1147 = x_1365;
x_1148 = x_1358;
goto lbl_1149;
}
else
{
obj* x_1369; obj* x_1370; obj* x_1372; 
lean::dec(x_1319);
lean::dec(x_1356);
lean::inc(x_1);
x_1369 = l_lean_ir_cpp_emit__var(x_1143, x_1, x_1358);
x_1370 = lean::cnstr_get(x_1369, 0);
lean::inc(x_1370);
x_1372 = lean::cnstr_get(x_1369, 1);
lean::inc(x_1372);
lean::dec(x_1369);
x_1147 = x_1370;
x_1148 = x_1372;
goto lbl_1149;
}
}
}
}
}
}
}
lbl_4:
{
obj* x_1375; obj* x_1377; obj* x_1379; 
x_1375 = lean::cnstr_get(x_3, 0);
lean::inc(x_1375);
x_1377 = lean::cnstr_get(x_3, 1);
lean::inc(x_1377);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_1379 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_1379 = x_3;
}
if (lean::obj_tag(x_1375) == 0)
{
obj* x_1381; obj* x_1383; obj* x_1384; uint8 x_1385; obj* x_1386; obj* x_1388; obj* x_1389; obj* x_1390; obj* x_1392; obj* x_1393; obj* x_1394; obj* x_1395; obj* x_1396; obj* x_1397; obj* x_1398; obj* x_1399; obj* x_1400; 
lean::dec(x_1);
x_1381 = lean::cnstr_get(x_1375, 0);
lean::inc(x_1381);
if (lean::is_shared(x_1375)) {
 lean::dec(x_1375);
 x_1383 = lean::box(0);
} else {
 lean::cnstr_release(x_1375, 0);
 x_1383 = x_1375;
}
x_1384 = l_lean_ir_instr_to__format___main(x_0);
x_1385 = 0;
x_1386 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_1386);
x_1388 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1388, 0, x_1386);
lean::cnstr_set(x_1388, 1, x_1384);
lean::cnstr_set_scalar(x_1388, sizeof(void*)*2, x_1385);
x_1389 = x_1388;
x_1390 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_1390);
x_1392 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1392, 0, x_1389);
lean::cnstr_set(x_1392, 1, x_1390);
lean::cnstr_set_scalar(x_1392, sizeof(void*)*2, x_1385);
x_1393 = x_1392;
x_1394 = lean::box(1);
x_1395 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1395, 0, x_1393);
lean::cnstr_set(x_1395, 1, x_1394);
lean::cnstr_set_scalar(x_1395, sizeof(void*)*2, x_1385);
x_1396 = x_1395;
x_1397 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1397, 0, x_1396);
lean::cnstr_set(x_1397, 1, x_1381);
lean::cnstr_set_scalar(x_1397, sizeof(void*)*2, x_1385);
x_1398 = x_1397;
if (lean::is_scalar(x_1383)) {
 x_1399 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1399 = x_1383;
}
lean::cnstr_set(x_1399, 0, x_1398);
if (lean::is_scalar(x_1379)) {
 x_1400 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1400 = x_1379;
}
lean::cnstr_set(x_1400, 0, x_1399);
lean::cnstr_set(x_1400, 1, x_1377);
return x_1400;
}
else
{
obj* x_1401; obj* x_1402; obj* x_1403; obj* x_1405; 
if (lean::is_shared(x_1375)) {
 lean::dec(x_1375);
 x_1401 = lean::box(0);
} else {
 lean::cnstr_release(x_1375, 0);
 x_1401 = x_1375;
}
x_1402 = l_lean_ir_cpp_emit__eos(x_1, x_1377);
x_1403 = lean::cnstr_get(x_1402, 0);
lean::inc(x_1403);
x_1405 = lean::cnstr_get(x_1402, 1);
lean::inc(x_1405);
lean::dec(x_1402);
if (lean::obj_tag(x_1403) == 0)
{
obj* x_1408; obj* x_1411; uint8 x_1412; obj* x_1413; obj* x_1415; obj* x_1416; obj* x_1417; obj* x_1419; obj* x_1420; obj* x_1421; obj* x_1422; obj* x_1423; obj* x_1424; obj* x_1425; obj* x_1426; obj* x_1427; 
x_1408 = lean::cnstr_get(x_1403, 0);
lean::inc(x_1408);
lean::dec(x_1403);
x_1411 = l_lean_ir_instr_to__format___main(x_0);
x_1412 = 0;
x_1413 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_1413);
x_1415 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1415, 0, x_1413);
lean::cnstr_set(x_1415, 1, x_1411);
lean::cnstr_set_scalar(x_1415, sizeof(void*)*2, x_1412);
x_1416 = x_1415;
x_1417 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_1417);
x_1419 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1419, 0, x_1416);
lean::cnstr_set(x_1419, 1, x_1417);
lean::cnstr_set_scalar(x_1419, sizeof(void*)*2, x_1412);
x_1420 = x_1419;
x_1421 = lean::box(1);
x_1422 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1422, 0, x_1420);
lean::cnstr_set(x_1422, 1, x_1421);
lean::cnstr_set_scalar(x_1422, sizeof(void*)*2, x_1412);
x_1423 = x_1422;
x_1424 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1424, 0, x_1423);
lean::cnstr_set(x_1424, 1, x_1408);
lean::cnstr_set_scalar(x_1424, sizeof(void*)*2, x_1412);
x_1425 = x_1424;
if (lean::is_scalar(x_1401)) {
 x_1426 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1426 = x_1401;
 lean::cnstr_set_tag(x_1401, 0);
}
lean::cnstr_set(x_1426, 0, x_1425);
if (lean::is_scalar(x_1379)) {
 x_1427 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1427 = x_1379;
}
lean::cnstr_set(x_1427, 0, x_1426);
lean::cnstr_set(x_1427, 1, x_1405);
return x_1427;
}
else
{
obj* x_1430; 
lean::dec(x_1401);
lean::dec(x_0);
if (lean::is_scalar(x_1379)) {
 x_1430 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1430 = x_1379;
}
lean::cnstr_set(x_1430, 0, x_1403);
lean::cnstr_set(x_1430, 1, x_1405);
return x_1430;
}
}
}
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
usize x_3; obj* x_4; 
x_3 = lean::unbox_size_t(x_0);
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint16 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__2(x_3, x_1, x_2);
return x_4;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint16 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_3, x_1, x_2);
return x_4;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__block___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
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
x_14 = l_lean_ir_cpp_emit__instr(x_8, x_1, x_2);
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
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* _init_l_lean_ir_cpp_emit__block___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(":");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__block___closed__2() {
_start:
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
obj* l_lean_ir_cpp_emit__block(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = l_list_empty___main___rarg(x_3);
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
x_16 = l_lean_ir_cpp_emit__block___closed__2;
lean::inc(x_16);
x_13 = x_16;
x_14 = x_2;
goto lbl_15;
}
else
{
obj* x_18; 
x_18 = l_lean_ir_match__type___closed__5;
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
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
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
x_31 = l_lean_ir_cpp_emit__blockid(x_6, x_1, x_14);
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
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
x_40 = lean::cnstr_get(x_32, 0);
lean::inc(x_40);
lean::dec(x_32);
if (lean::is_scalar(x_29)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_29;
 lean::cnstr_set_tag(x_29, 0);
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
x_46 = l_lean_ir_cpp_emit__block___closed__1;
lean::inc(x_1);
lean::inc(x_46);
x_49 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_46, x_1, x_34);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_58; obj* x_61; obj* x_62; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
x_58 = lean::cnstr_get(x_50, 0);
lean::inc(x_58);
lean::dec(x_50);
if (lean::is_scalar(x_29)) {
 x_61 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_61 = x_29;
 lean::cnstr_set_tag(x_29, 0);
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
x_64 = l_lean_format_be___main___closed__1;
lean::inc(x_1);
lean::inc(x_64);
x_67 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_64, x_1, x_52);
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
if (lean::obj_tag(x_68) == 0)
{
obj* x_76; obj* x_79; obj* x_80; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
x_76 = lean::cnstr_get(x_68, 0);
lean::inc(x_76);
lean::dec(x_68);
if (lean::is_scalar(x_29)) {
 x_79 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_79 = x_29;
 lean::cnstr_set_tag(x_29, 0);
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
x_83 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__block___spec__1(x_8, x_1, x_70);
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
 lean::cnstr_set_tag(x_29, 0);
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
lean::dec(x_29);
lean::dec(x_84);
lean::dec(x_36);
x_99 = l_lean_ir_cpp_emit__terminator(x_10, x_1, x_86);
return x_99;
}
}
}
}
}
}
}
}
obj* _init_l_lean_ir_cpp_emit__header___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__arg__list___lambda__1), 3, 0);
return x_0;
}
}
obj* l_lean_ir_cpp_emit__header(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; uint8 x_13; obj* x_16; obj* x_17; obj* x_19; 
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
x_16 = l_lean_ir_cpp_emit__type(x_13, x_1, x_2);
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
x_27 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_27);
x_30 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_27, x_1, x_19);
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
lean::dec(x_7);
lean::dec(x_5);
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
x_46 = l_lean_ir_cpp_emit__fnid(x_5, x_1, x_11);
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
 lean::cnstr_set_tag(x_44, 0);
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
x_60 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_60);
x_63 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_60, x_1, x_49);
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
 lean::cnstr_set_tag(x_44, 0);
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
x_77 = l_lean_ir_cpp_emit__header___closed__1;
x_78 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_1);
lean::inc(x_78);
lean::inc(x_77);
x_82 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_77, x_78, x_7, x_1, x_66);
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
 lean::cnstr_set_tag(x_44, 0);
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
x_97 = l_option_has__repr___rarg___closed__3;
lean::inc(x_97);
x_99 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_97, x_1, x_85);
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
 lean::cnstr_set_tag(x_44, 0);
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
obj* l_lean_ir_cpp_decl__local(obj* x_0, uint8 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::inc(x_2);
x_5 = l_lean_ir_cpp_emit__type(x_1, x_2, x_3);
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
x_19 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_19);
x_22 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_2, x_8);
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
 lean::cnstr_set_tag(x_18, 0);
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
x_37 = l_lean_ir_cpp_emit__var(x_0, x_2, x_25);
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
 lean::cnstr_set_tag(x_18, 0);
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
lean::dec(x_10);
lean::dec(x_18);
lean::dec(x_38);
x_52 = l_lean_ir_cpp_emit__eos(x_2, x_40);
return x_52;
}
}
}
}
}
obj* l_lean_ir_cpp_decl__local___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_1);
x_5 = l_lean_ir_cpp_decl__local(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; obj* x_5; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = 0;
x_5 = lean::box(x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; uint8 x_14; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
x_14 = lean::name_dec_eq(x_11, x_0);
lean::dec(x_11);
if (x_14 == 0)
{
x_1 = x_8;
goto _start;
}
else
{
uint8 x_19; obj* x_20; 
lean::dec(x_8);
lean::dec(x_0);
x_19 = 1;
x_20 = lean::box(x_19);
return x_20;
}
}
}
}
obj* l_rbnode_mfold___main___at_lean_ir_cpp_decl__locals___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
return x_9;
}
case 1:
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_21; obj* x_22; obj* x_24; obj* x_26; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_1, 2);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_1, 3);
lean::inc(x_16);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_0);
x_21 = l_rbnode_mfold___main___at_lean_ir_cpp_decl__locals___spec__2(x_0, x_10, x_2, x_3, x_4);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_26 = x_21;
}
if (lean::obj_tag(x_22) == 0)
{
obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
x_32 = lean::cnstr_get(x_22, 0);
lean::inc(x_32);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_34 = x_22;
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
if (lean::is_scalar(x_26)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_26;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_24);
return x_36;
}
else
{
obj* x_37; obj* x_40; uint8 x_41; 
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_37 = x_22;
}
lean::inc(x_0);
lean::inc(x_12);
x_40 = l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1(x_12, x_0);
x_41 = lean::unbox(x_40);
lean::dec(x_40);
if (x_41 == 0)
{
uint8 x_43; obj* x_46; obj* x_47; obj* x_49; 
x_43 = lean::unbox(x_14);
lean::dec(x_14);
lean::inc(x_3);
x_46 = l_lean_ir_cpp_decl__local(x_12, x_43, x_3, x_24);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_55; obj* x_58; obj* x_59; 
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_0);
x_55 = lean::cnstr_get(x_47, 0);
lean::inc(x_55);
lean::dec(x_47);
if (lean::is_scalar(x_37)) {
 x_58 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_58 = x_37;
 lean::cnstr_set_tag(x_37, 0);
}
lean::cnstr_set(x_58, 0, x_55);
if (lean::is_scalar(x_26)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_26;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_49);
return x_59;
}
else
{
obj* x_63; 
lean::dec(x_26);
lean::dec(x_37);
lean::dec(x_47);
x_63 = lean::box(0);
x_1 = x_16;
x_2 = x_63;
x_4 = x_49;
goto _start;
}
}
else
{
obj* x_69; 
lean::dec(x_26);
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_37);
x_69 = lean::box(0);
x_1 = x_16;
x_2 = x_69;
x_4 = x_24;
goto _start;
}
}
}
default:
{
obj* x_71; obj* x_73; obj* x_75; obj* x_77; obj* x_82; obj* x_83; obj* x_85; obj* x_87; 
x_71 = lean::cnstr_get(x_1, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_1, 1);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_1, 2);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_1, 3);
lean::inc(x_77);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_0);
x_82 = l_rbnode_mfold___main___at_lean_ir_cpp_decl__locals___spec__2(x_0, x_71, x_2, x_3, x_4);
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
if (lean::is_shared(x_82)) {
 lean::dec(x_82);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_82, 0);
 lean::cnstr_release(x_82, 1);
 x_87 = x_82;
}
if (lean::obj_tag(x_83) == 0)
{
obj* x_93; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_77);
lean::dec(x_75);
lean::dec(x_73);
x_93 = lean::cnstr_get(x_83, 0);
lean::inc(x_93);
if (lean::is_shared(x_83)) {
 lean::dec(x_83);
 x_95 = lean::box(0);
} else {
 lean::cnstr_release(x_83, 0);
 x_95 = x_83;
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_93);
if (lean::is_scalar(x_87)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_87;
}
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_85);
return x_97;
}
else
{
obj* x_98; obj* x_101; uint8 x_102; 
if (lean::is_shared(x_83)) {
 lean::dec(x_83);
 x_98 = lean::box(0);
} else {
 lean::cnstr_release(x_83, 0);
 x_98 = x_83;
}
lean::inc(x_0);
lean::inc(x_73);
x_101 = l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1(x_73, x_0);
x_102 = lean::unbox(x_101);
lean::dec(x_101);
if (x_102 == 0)
{
uint8 x_104; obj* x_107; obj* x_108; obj* x_110; 
x_104 = lean::unbox(x_75);
lean::dec(x_75);
lean::inc(x_3);
x_107 = l_lean_ir_cpp_decl__local(x_73, x_104, x_3, x_85);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_107, 1);
lean::inc(x_110);
lean::dec(x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_116; obj* x_119; obj* x_120; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_77);
x_116 = lean::cnstr_get(x_108, 0);
lean::inc(x_116);
lean::dec(x_108);
if (lean::is_scalar(x_98)) {
 x_119 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_119 = x_98;
 lean::cnstr_set_tag(x_98, 0);
}
lean::cnstr_set(x_119, 0, x_116);
if (lean::is_scalar(x_87)) {
 x_120 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_120 = x_87;
}
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_110);
return x_120;
}
else
{
obj* x_124; 
lean::dec(x_87);
lean::dec(x_108);
lean::dec(x_98);
x_124 = lean::box(0);
x_1 = x_77;
x_2 = x_124;
x_4 = x_110;
goto _start;
}
}
else
{
obj* x_130; 
lean::dec(x_75);
lean::dec(x_87);
lean::dec(x_98);
lean::dec(x_73);
x_130 = lean::box(0);
x_1 = x_77;
x_2 = x_130;
x_4 = x_85;
goto _start;
}
}
}
}
}
}
obj* l_lean_ir_cpp_decl__locals(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
x_5 = lean::box(0);
x_6 = l_rbnode_mfold___main___at_lean_ir_cpp_decl__locals___spec__2(x_0, x_3, x_5, x_1, x_2);
return x_6;
}
}
obj* l_list_foldr___main___at_lean_ir_cpp_need__uncurry___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_2; obj* x_3; 
lean::dec(x_0);
x_2 = 1;
x_3 = lean::box(x_2);
return x_3;
}
else
{
obj* x_4; obj* x_6; uint8 x_9; obj* x_11; obj* x_12; uint8 x_13; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
lean::dec(x_4);
x_11 = l_lean_ir_type2id___main(x_9);
x_12 = l_lean_ir_valid__assign__unop__types___closed__1;
x_13 = lean::nat_dec_eq(x_11, x_12);
lean::dec(x_11);
if (x_13 == 0)
{
uint8 x_16; obj* x_17; 
lean::dec(x_6);
x_16 = 0;
x_17 = lean::box(x_16);
return x_17;
}
else
{
x_0 = x_6;
goto _start;
}
}
}
}
obj* l_lean_ir_cpp_need__uncurry(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; uint8 x_8; 
x_1 = l_lean_ir_decl_header___main(x_0);
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_4 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_6 = l_list_length__aux___main___rarg(x_2, x_4);
x_7 = l_lean_closure__max__args;
x_8 = lean::nat_dec_lt(x_7, x_6);
lean::dec(x_6);
if (x_8 == 0)
{
uint8 x_12; obj* x_13; 
lean::dec(x_1);
lean::dec(x_2);
x_12 = 0;
x_13 = lean::box(x_12);
return x_13;
}
else
{
obj* x_14; uint8 x_17; obj* x_19; obj* x_20; uint8 x_21; 
x_14 = lean::cnstr_get(x_1, 2);
lean::inc(x_14);
lean::dec(x_1);
x_17 = lean::unbox(x_14);
lean::dec(x_14);
x_19 = l_lean_ir_type2id___main(x_17);
x_20 = l_lean_ir_valid__assign__unop__types___closed__1;
x_21 = lean::nat_dec_eq(x_19, x_20);
lean::dec(x_19);
if (x_21 == 0)
{
uint8 x_24; obj* x_25; 
lean::dec(x_2);
x_24 = 0;
x_25 = lean::box(x_24);
return x_25;
}
else
{
obj* x_26; 
x_26 = l_list_foldr___main___at_lean_ir_cpp_need__uncurry___spec__1(x_2);
return x_26;
}
}
}
}
obj* _init_l_lean_ir_cpp_emit__uncurry__header___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("obj* uncurry");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__uncurry__header___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("(obj** as)");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__uncurry__header(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = l_lean_ir_cpp_emit__uncurry__header___closed__1;
lean::inc(x_1);
lean::inc(x_3);
x_6 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
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
lean::dec(x_0);
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
x_20 = l_lean_ir_decl_header___main(x_0);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
lean::dec(x_20);
lean::inc(x_1);
x_25 = l_lean_ir_cpp_emit__fnid(x_21, x_1, x_9);
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
 lean::cnstr_set_tag(x_19, 0);
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
x_40 = l_lean_ir_cpp_emit__uncurry__header___closed__2;
lean::inc(x_40);
x_42 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_40, x_1, x_28);
return x_42;
}
}
}
}
obj* l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
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
obj* l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_18; obj* x_21; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
lean::inc(x_0);
x_10 = l_lean_ir_decl_header___main(x_0);
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
x_14 = l_list_length__aux___main___rarg(x_11, x_5);
x_15 = lean::nat_sub(x_14, x_7);
lean::dec(x_7);
lean::dec(x_14);
x_18 = lean::nat_sub(x_15, x_1);
lean::dec(x_1);
lean::dec(x_15);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1), 4, 2);
lean::closure_set(x_21, 0, x_2);
lean::closure_set(x_21, 1, x_18);
x_1 = x_8;
x_2 = x_21;
goto _start;
}
else
{
obj* x_26; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
x_26 = lean::apply_2(x_2, x_3, x_4);
return x_26;
}
}
}
obj* _init_l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("as[");
return x_0;
}
}
obj* l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
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
x_19 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_19);
x_22 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_2, x_8);
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
 lean::cnstr_set_tag(x_18, 0);
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
obj* x_36; obj* x_39; obj* x_40; obj* x_42; 
lean::dec(x_23);
x_36 = l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___closed__1;
lean::inc(x_2);
lean::inc(x_36);
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_36, x_2, x_25);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
if (lean::obj_tag(x_40) == 0)
{
obj* x_47; obj* x_50; obj* x_51; 
lean::dec(x_1);
lean::dec(x_2);
x_47 = lean::cnstr_get(x_40, 0);
lean::inc(x_47);
lean::dec(x_40);
if (lean::is_scalar(x_18)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_50, 0, x_47);
if (lean::is_scalar(x_10)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_10;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_42);
return x_51;
}
else
{
obj* x_53; obj* x_54; obj* x_58; obj* x_59; obj* x_61; 
lean::dec(x_40);
x_53 = lean::mk_nat_obj(1u);
x_54 = lean::nat_add(x_1, x_53);
lean::dec(x_53);
lean::dec(x_1);
lean::inc(x_2);
x_58 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_54, x_2, x_42);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
if (lean::obj_tag(x_59) == 0)
{
obj* x_65; obj* x_68; obj* x_69; 
lean::dec(x_2);
x_65 = lean::cnstr_get(x_59, 0);
lean::inc(x_65);
lean::dec(x_59);
if (lean::is_scalar(x_18)) {
 x_68 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_68 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_68, 0, x_65);
if (lean::is_scalar(x_10)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_10;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_61);
return x_69;
}
else
{
obj* x_73; obj* x_75; 
lean::dec(x_10);
lean::dec(x_18);
lean::dec(x_59);
x_73 = l_list_repr___main___rarg___closed__3;
lean::inc(x_73);
x_75 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_73, x_2, x_61);
return x_75;
}
}
}
}
}
}
obj* _init_l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2___rarg), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_16; 
lean::inc(x_0);
x_4 = l_lean_ir_decl_header___main(x_0);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_list_length__aux___main___rarg(x_5, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_9, x_10);
lean::dec(x_10);
lean::dec(x_9);
x_14 = l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1___closed__1;
lean::inc(x_14);
x_16 = l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3(x_0, x_11, x_14, x_1, x_2);
return x_16;
}
}
obj* _init_l_lean_ir_cpp_emit__uncurry___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("}\n");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__uncurry___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("as[0]");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__uncurry___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" {\n");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__uncurry(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_1);
lean::inc(x_0);
x_11 = l_lean_ir_cpp_emit__uncurry__header(x_0, x_1, x_2);
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
x_22 = l_lean_ir_cpp_emit__uncurry___closed__3;
lean::inc(x_1);
lean::inc(x_22);
x_25 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_1, x_14);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
lean::inc(x_0);
x_32 = l_lean_ir_decl_header___main(x_0);
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
 lean::cnstr_set_tag(x_21, 0);
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
x_42 = l_lean_ir_cpp_emit__terminator___closed__1;
lean::inc(x_1);
lean::inc(x_42);
x_45 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_42, x_1, x_28);
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
 lean::cnstr_set_tag(x_21, 0);
}
lean::cnstr_set(x_55, 0, x_52);
x_6 = x_55;
x_7 = x_48;
goto lbl_8;
}
else
{
obj* x_59; obj* x_60; obj* x_62; 
lean::dec(x_21);
lean::dec(x_46);
lean::inc(x_1);
x_59 = l_lean_ir_cpp_emit__fnid(x_39, x_1, x_48);
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
x_73 = l_lean_ir_cpp_emit__eos(x_1, x_4);
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
 lean::cnstr_set_tag(x_71, 0);
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
lean::dec(x_74);
lean::dec(x_71);
lean::dec(x_78);
x_88 = l_lean_ir_cpp_emit__uncurry___closed__1;
lean::inc(x_88);
x_90 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_88, x_1, x_76);
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
x_97 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_97);
x_100 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_97, x_1, x_7);
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
 lean::cnstr_set_tag(x_96, 0);
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
x_112 = l_lean_ir_cpp_emit__uncurry___closed__2;
lean::inc(x_1);
lean::inc(x_112);
x_115 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_112, x_1, x_103);
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
 lean::cnstr_set_tag(x_96, 0);
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
x_128 = l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1(x_0, x_1, x_118);
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
 lean::cnstr_set_tag(x_96, 0);
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
x_141 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
lean::inc(x_141);
x_144 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_141, x_1, x_131);
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
 lean::cnstr_set_tag(x_96, 0);
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
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__def__core___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
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
x_14 = l_lean_ir_cpp_emit__block(x_8, x_1, x_2);
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
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* l_lean_ir_cpp_emit__def__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_lean_ir_decl_header___main(x_0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_10; 
lean::dec(x_1);
lean::dec(x_0);
x_10 = l_lean_ir_match__type___closed__5;
lean::inc(x_10);
x_5 = x_10;
x_6 = x_2;
goto lbl_7;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_19; uint8 x_20; uint8 x_22; 
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_12, 1);
lean::inc(x_16);
lean::inc(x_0);
x_19 = l_lean_ir_cpp_need__uncurry(x_0);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
uint8 x_24; 
x_24 = 0;
x_22 = x_24;
goto lbl_23;
}
else
{
uint8 x_25; 
x_25 = 1;
x_22 = x_25;
goto lbl_23;
}
lbl_23:
{
obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_33; 
lean::inc(x_1);
x_30 = l_lean_ir_cpp_emit__header(x_12, x_1, x_2);
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
x_42 = l_lean_ir_cpp_emit__case___main___closed__1;
lean::inc(x_1);
lean::inc(x_42);
x_45 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_42, x_1, x_33);
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
 lean::cnstr_set_tag(x_41, 0);
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
x_57 = l_lean_format_be___main___closed__1;
lean::inc(x_1);
lean::inc(x_57);
x_60 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_57, x_1, x_48);
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
 lean::cnstr_set_tag(x_41, 0);
}
lean::cnstr_set(x_70, 0, x_67);
x_26 = x_70;
x_27 = x_63;
goto lbl_28;
}
else
{
obj* x_74; obj* x_75; obj* x_77; 
lean::dec(x_41);
lean::dec(x_61);
lean::inc(x_1);
x_74 = l_lean_ir_cpp_decl__locals(x_16, x_1, x_63);
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
obj* x_83; obj* x_85; obj* x_86; 
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_0);
x_83 = lean::cnstr_get(x_26, 0);
lean::inc(x_83);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_85 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_85 = x_26;
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_83);
x_5 = x_86;
x_6 = x_27;
goto lbl_7;
}
else
{
obj* x_87; obj* x_89; obj* x_90; obj* x_92; 
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_87 = x_26;
}
lean::inc(x_1);
x_89 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__def__core___spec__1(x_14, x_1, x_27);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_89, 1);
lean::inc(x_92);
lean::dec(x_89);
if (lean::obj_tag(x_90) == 0)
{
obj* x_97; obj* x_100; 
lean::dec(x_1);
lean::dec(x_0);
x_97 = lean::cnstr_get(x_90, 0);
lean::inc(x_97);
lean::dec(x_90);
if (lean::is_scalar(x_87)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_87;
 lean::cnstr_set_tag(x_87, 0);
}
lean::cnstr_set(x_100, 0, x_97);
x_5 = x_100;
x_6 = x_92;
goto lbl_7;
}
else
{
obj* x_102; obj* x_105; obj* x_106; obj* x_108; 
lean::dec(x_90);
x_102 = l_lean_ir_cpp_emit__case___main___closed__2;
lean::inc(x_1);
lean::inc(x_102);
x_105 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_102, x_1, x_92);
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_105, 1);
lean::inc(x_108);
lean::dec(x_105);
if (lean::obj_tag(x_106) == 0)
{
obj* x_113; obj* x_116; 
lean::dec(x_1);
lean::dec(x_0);
x_113 = lean::cnstr_get(x_106, 0);
lean::inc(x_113);
lean::dec(x_106);
if (lean::is_scalar(x_87)) {
 x_116 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_116 = x_87;
 lean::cnstr_set_tag(x_87, 0);
}
lean::cnstr_set(x_116, 0, x_113);
x_5 = x_116;
x_6 = x_108;
goto lbl_7;
}
else
{
obj* x_118; obj* x_121; obj* x_122; obj* x_124; 
lean::dec(x_106);
x_118 = l_lean_format_be___main___closed__1;
lean::inc(x_1);
lean::inc(x_118);
x_121 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_118, x_1, x_108);
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_121, 1);
lean::inc(x_124);
lean::dec(x_121);
if (lean::obj_tag(x_122) == 0)
{
obj* x_129; obj* x_132; 
lean::dec(x_1);
lean::dec(x_0);
x_129 = lean::cnstr_get(x_122, 0);
lean::inc(x_129);
lean::dec(x_122);
if (lean::is_scalar(x_87)) {
 x_132 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_132 = x_87;
 lean::cnstr_set_tag(x_87, 0);
}
lean::cnstr_set(x_132, 0, x_129);
x_5 = x_132;
x_6 = x_124;
goto lbl_7;
}
else
{
lean::dec(x_122);
lean::dec(x_87);
if (x_22 == 0)
{
obj* x_137; 
lean::dec(x_1);
lean::dec(x_0);
x_137 = l_lean_ir_match__type___closed__5;
lean::inc(x_137);
x_5 = x_137;
x_6 = x_124;
goto lbl_7;
}
else
{
obj* x_139; obj* x_140; obj* x_142; 
x_139 = l_lean_ir_cpp_emit__uncurry(x_0, x_1, x_124);
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_139, 1);
lean::inc(x_142);
lean::dec(x_139);
x_5 = x_140;
x_6 = x_142;
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
obj* x_145; obj* x_147; obj* x_148; obj* x_151; uint8 x_152; obj* x_153; obj* x_155; obj* x_156; obj* x_157; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
x_145 = lean::cnstr_get(x_5, 0);
lean::inc(x_145);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_147 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_147 = x_5;
}
x_148 = lean::cnstr_get(x_4, 0);
lean::inc(x_148);
lean::dec(x_4);
x_151 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_148);
x_152 = 0;
x_153 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_153);
x_155 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_155, 0, x_153);
lean::cnstr_set(x_155, 1, x_151);
lean::cnstr_set_scalar(x_155, sizeof(void*)*2, x_152);
x_156 = x_155;
x_157 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_157);
x_159 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_159, 0, x_156);
lean::cnstr_set(x_159, 1, x_157);
lean::cnstr_set_scalar(x_159, sizeof(void*)*2, x_152);
x_160 = x_159;
x_161 = lean::box(1);
x_162 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_162, 0, x_160);
lean::cnstr_set(x_162, 1, x_161);
lean::cnstr_set_scalar(x_162, sizeof(void*)*2, x_152);
x_163 = x_162;
x_164 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_164, 0, x_163);
lean::cnstr_set(x_164, 1, x_145);
lean::cnstr_set_scalar(x_164, sizeof(void*)*2, x_152);
x_165 = x_164;
if (lean::is_scalar(x_147)) {
 x_166 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_166 = x_147;
}
lean::cnstr_set(x_166, 0, x_165);
x_167 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_167, 0, x_166);
lean::cnstr_set(x_167, 1, x_6);
return x_167;
}
else
{
obj* x_169; 
lean::dec(x_4);
x_169 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_169, 0, x_5);
lean::cnstr_set(x_169, 1, x_6);
return x_169;
}
}
}
}
obj* l_lean_ir_cpp_emit__def(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 3);
lean::inc(x_6);
lean::inc(x_0);
x_9 = l_lean_ir_infer__types(x_0, x_6);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_3);
lean::dec(x_0);
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
x_21 = l_lean_ir_cpp_emit__def__core(x_0, x_20, x_2);
return x_21;
}
}
}
obj* l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = l_lean_name_quick__lt___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; uint8 x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = l_lean_name_quick__lt___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_9);
lean::dec(x_7);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_7);
lean::cnstr_set(x_28, 2, x_9);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; uint8 x_43; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = l_lean_name_quick__lt___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; uint8 x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = l_lean_name_quick__lt___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_33);
lean::dec(x_35);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_31);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_37);
return x_52;
}
else
{
uint8 x_54; 
lean::inc(x_37);
x_54 = l_rbnode_get__color___main___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_37, x_1, x_2);
x_57 = l_rbnode_balance2__node___main___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_39;
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_33);
lean::cnstr_set(x_59, 2, x_35);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
uint8 x_61; 
lean::inc(x_31);
x_61 = l_rbnode_get__color___main___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_31, x_1, x_2);
x_64 = l_rbnode_balance1__node___main___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_cpp_collect__used___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = l_rbnode_get__color___main___rarg(x_0);
x_5 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_0, x_1, x_2);
x_6 = l_rbnode_mk__insert__result___main___rarg(x_4, x_5);
return x_6;
}
}
obj* l_rbmap_insert___main___at_lean_ir_cpp_collect__used___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_ir_cpp_collect__used___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__4(obj* x_0, obj* x_1) {
_start:
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
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
case 1:
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
case 2:
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
case 3:
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
case 4:
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
case 5:
{
obj* x_18; obj* x_21; obj* x_22; 
x_18 = lean::cnstr_get(x_3, 1);
lean::inc(x_18);
lean::dec(x_3);
x_21 = lean::box(0);
x_22 = l_rbnode_insert___at_lean_ir_cpp_collect__used___spec__2(x_0, x_18, x_21);
x_0 = x_22;
x_1 = x_5;
goto _start;
}
case 6:
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
case 7:
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
case 8:
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
case 9:
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
case 10:
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
case 11:
{
obj* x_34; obj* x_37; obj* x_38; 
x_34 = lean::cnstr_get(x_3, 1);
lean::inc(x_34);
lean::dec(x_3);
x_37 = lean::box(0);
x_38 = l_rbnode_insert___at_lean_ir_cpp_collect__used___spec__2(x_0, x_34, x_37);
x_0 = x_38;
x_1 = x_5;
goto _start;
}
case 12:
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
case 13:
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
case 14:
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
default:
{
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
}
}
}
}
obj* l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__5(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_1);
return x_0;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__4(x_0, x_8);
x_0 = x_11;
x_1 = x_5;
goto _start;
}
}
}
obj* l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__6(obj* x_0, obj* x_1) {
_start:
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
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
else
{
obj* x_10; obj* x_13; 
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__5(x_0, x_10);
x_0 = x_13;
x_1 = x_5;
goto _start;
}
}
}
}
obj* l_lean_ir_cpp_collect__used(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_ir_mk__fnid__set;
lean::inc(x_1);
x_3 = l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__6(x_1, x_0);
return x_3;
}
}
obj* _init_l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(";\n");
return x_0;
}
}
obj* _init_l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("extern \"C\" ");
return x_0;
}
}
obj* l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
return x_9;
}
case 1:
{
obj* x_10; obj* x_12; obj* x_14; obj* x_19; obj* x_20; obj* x_22; obj* x_24; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_1, 3);
lean::inc(x_14);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_0);
x_19 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1(x_0, x_10, x_2, x_3, x_4);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 lean::cnstr_release(x_19, 1);
 x_24 = x_19;
}
if (lean::obj_tag(x_20) == 0)
{
obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_3);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_31 = x_20;
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_24)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_24;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_22);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_38; obj* x_40; obj* x_43; 
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_34 = x_20;
}
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_38, 3);
lean::inc(x_40);
lean::inc(x_12);
x_43 = lean::apply_1(x_40, x_12);
if (lean::obj_tag(x_43) == 0)
{
obj* x_47; 
lean::dec(x_12);
lean::dec(x_38);
lean::dec(x_43);
x_47 = l_lean_ir_match__type___closed__5;
lean::inc(x_47);
x_35 = x_47;
x_36 = x_22;
goto lbl_37;
}
else
{
obj* x_49; obj* x_52; obj* x_55; 
x_49 = lean::cnstr_get(x_43, 0);
lean::inc(x_49);
lean::dec(x_43);
x_52 = lean::cnstr_get(x_38, 4);
lean::inc(x_52);
lean::dec(x_38);
x_55 = lean::apply_1(x_52, x_12);
if (lean::obj_tag(x_55) == 0)
{
obj* x_58; obj* x_60; uint8 x_61; obj* x_64; 
lean::dec(x_55);
lean::inc(x_49);
x_58 = l_lean_ir_decl_header___main(x_49);
lean::inc(x_49);
x_60 = l_lean_ir_cpp_need__uncurry(x_49);
x_61 = lean::unbox(x_60);
lean::dec(x_60);
lean::inc(x_3);
x_64 = l_lean_ir_cpp_emit__header(x_58, x_3, x_22);
if (x_61 == 0)
{
obj* x_66; obj* x_68; 
lean::dec(x_49);
x_66 = lean::cnstr_get(x_64, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_64, 1);
lean::inc(x_68);
lean::dec(x_64);
if (lean::obj_tag(x_66) == 0)
{
obj* x_71; obj* x_73; obj* x_74; 
x_71 = lean::cnstr_get(x_66, 0);
lean::inc(x_71);
if (lean::is_shared(x_66)) {
 lean::dec(x_66);
 x_73 = lean::box(0);
} else {
 lean::cnstr_release(x_66, 0);
 x_73 = x_66;
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_71);
x_35 = x_74;
x_36 = x_68;
goto lbl_37;
}
else
{
obj* x_75; obj* x_76; obj* x_79; obj* x_80; obj* x_82; 
if (lean::is_shared(x_66)) {
 lean::dec(x_66);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_66, 0);
 x_75 = x_66;
}
x_76 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_76);
x_79 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_76, x_3, x_68);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
if (lean::obj_tag(x_80) == 0)
{
obj* x_85; obj* x_88; 
x_85 = lean::cnstr_get(x_80, 0);
lean::inc(x_85);
lean::dec(x_80);
if (lean::is_scalar(x_75)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_75;
 lean::cnstr_set_tag(x_75, 0);
}
lean::cnstr_set(x_88, 0, x_85);
x_35 = x_88;
x_36 = x_82;
goto lbl_37;
}
else
{
obj* x_91; 
lean::dec(x_80);
lean::dec(x_75);
x_91 = l_lean_ir_match__type___closed__5;
lean::inc(x_91);
x_35 = x_91;
x_36 = x_82;
goto lbl_37;
}
}
}
else
{
obj* x_93; obj* x_95; 
x_93 = lean::cnstr_get(x_64, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_64, 1);
lean::inc(x_95);
lean::dec(x_64);
if (lean::obj_tag(x_93) == 0)
{
obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_49);
x_99 = lean::cnstr_get(x_93, 0);
lean::inc(x_99);
if (lean::is_shared(x_93)) {
 lean::dec(x_93);
 x_101 = lean::box(0);
} else {
 lean::cnstr_release(x_93, 0);
 x_101 = x_93;
}
if (lean::is_scalar(x_101)) {
 x_102 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_102 = x_101;
}
lean::cnstr_set(x_102, 0, x_99);
x_35 = x_102;
x_36 = x_95;
goto lbl_37;
}
else
{
obj* x_103; obj* x_104; obj* x_107; obj* x_108; obj* x_110; 
if (lean::is_shared(x_93)) {
 lean::dec(x_93);
 x_103 = lean::box(0);
} else {
 lean::cnstr_release(x_93, 0);
 x_103 = x_93;
}
x_104 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_104);
x_107 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_104, x_3, x_95);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_107, 1);
lean::inc(x_110);
lean::dec(x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_114; obj* x_117; 
lean::dec(x_49);
x_114 = lean::cnstr_get(x_108, 0);
lean::inc(x_114);
lean::dec(x_108);
if (lean::is_scalar(x_103)) {
 x_117 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_117 = x_103;
 lean::cnstr_set_tag(x_103, 0);
}
lean::cnstr_set(x_117, 0, x_114);
x_35 = x_117;
x_36 = x_110;
goto lbl_37;
}
else
{
obj* x_120; obj* x_121; obj* x_123; 
lean::dec(x_108);
lean::inc(x_3);
x_120 = l_lean_ir_cpp_emit__uncurry__header(x_49, x_3, x_110);
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_120, 1);
lean::inc(x_123);
lean::dec(x_120);
if (lean::obj_tag(x_121) == 0)
{
obj* x_126; obj* x_129; 
x_126 = lean::cnstr_get(x_121, 0);
lean::inc(x_126);
lean::dec(x_121);
if (lean::is_scalar(x_103)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_103;
 lean::cnstr_set_tag(x_103, 0);
}
lean::cnstr_set(x_129, 0, x_126);
x_35 = x_129;
x_36 = x_123;
goto lbl_37;
}
else
{
obj* x_134; obj* x_135; obj* x_137; 
lean::dec(x_121);
lean::dec(x_103);
lean::inc(x_3);
lean::inc(x_104);
x_134 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_104, x_3, x_123);
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_134, 1);
lean::inc(x_137);
lean::dec(x_134);
x_35 = x_135;
x_36 = x_137;
goto lbl_37;
}
}
}
}
}
else
{
obj* x_141; obj* x_144; obj* x_145; obj* x_147; 
lean::dec(x_55);
x_141 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2;
lean::inc(x_3);
lean::inc(x_141);
x_144 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_141, x_3, x_22);
x_145 = lean::cnstr_get(x_144, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_144, 1);
lean::inc(x_147);
lean::dec(x_144);
if (lean::obj_tag(x_145) == 0)
{
obj* x_151; obj* x_153; obj* x_154; 
lean::dec(x_49);
x_151 = lean::cnstr_get(x_145, 0);
lean::inc(x_151);
if (lean::is_shared(x_145)) {
 lean::dec(x_145);
 x_153 = lean::box(0);
} else {
 lean::cnstr_release(x_145, 0);
 x_153 = x_145;
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_154 = x_153;
}
lean::cnstr_set(x_154, 0, x_151);
x_35 = x_154;
x_36 = x_147;
goto lbl_37;
}
else
{
obj* x_155; obj* x_157; obj* x_159; uint8 x_160; obj* x_163; 
if (lean::is_shared(x_145)) {
 lean::dec(x_145);
 x_155 = lean::box(0);
} else {
 lean::cnstr_release(x_145, 0);
 x_155 = x_145;
}
lean::inc(x_49);
x_157 = l_lean_ir_decl_header___main(x_49);
lean::inc(x_49);
x_159 = l_lean_ir_cpp_need__uncurry(x_49);
x_160 = lean::unbox(x_159);
lean::dec(x_159);
lean::inc(x_3);
x_163 = l_lean_ir_cpp_emit__header(x_157, x_3, x_147);
if (x_160 == 0)
{
obj* x_165; obj* x_167; 
lean::dec(x_49);
x_165 = lean::cnstr_get(x_163, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_163, 1);
lean::inc(x_167);
lean::dec(x_163);
if (lean::obj_tag(x_165) == 0)
{
obj* x_170; obj* x_173; 
x_170 = lean::cnstr_get(x_165, 0);
lean::inc(x_170);
lean::dec(x_165);
if (lean::is_scalar(x_155)) {
 x_173 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_173 = x_155;
 lean::cnstr_set_tag(x_155, 0);
}
lean::cnstr_set(x_173, 0, x_170);
x_35 = x_173;
x_36 = x_167;
goto lbl_37;
}
else
{
obj* x_175; obj* x_178; obj* x_179; obj* x_181; 
lean::dec(x_165);
x_175 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_175);
x_178 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_175, x_3, x_167);
x_179 = lean::cnstr_get(x_178, 0);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_178, 1);
lean::inc(x_181);
lean::dec(x_178);
if (lean::obj_tag(x_179) == 0)
{
obj* x_184; obj* x_187; 
x_184 = lean::cnstr_get(x_179, 0);
lean::inc(x_184);
lean::dec(x_179);
if (lean::is_scalar(x_155)) {
 x_187 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_187 = x_155;
 lean::cnstr_set_tag(x_155, 0);
}
lean::cnstr_set(x_187, 0, x_184);
x_35 = x_187;
x_36 = x_181;
goto lbl_37;
}
else
{
obj* x_190; 
lean::dec(x_179);
lean::dec(x_155);
x_190 = l_lean_ir_match__type___closed__5;
lean::inc(x_190);
x_35 = x_190;
x_36 = x_181;
goto lbl_37;
}
}
}
else
{
obj* x_192; obj* x_194; 
x_192 = lean::cnstr_get(x_163, 0);
lean::inc(x_192);
x_194 = lean::cnstr_get(x_163, 1);
lean::inc(x_194);
lean::dec(x_163);
if (lean::obj_tag(x_192) == 0)
{
obj* x_198; obj* x_201; 
lean::dec(x_49);
x_198 = lean::cnstr_get(x_192, 0);
lean::inc(x_198);
lean::dec(x_192);
if (lean::is_scalar(x_155)) {
 x_201 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_201 = x_155;
 lean::cnstr_set_tag(x_155, 0);
}
lean::cnstr_set(x_201, 0, x_198);
x_35 = x_201;
x_36 = x_194;
goto lbl_37;
}
else
{
obj* x_203; obj* x_206; obj* x_207; obj* x_209; 
lean::dec(x_192);
x_203 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_203);
x_206 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_203, x_3, x_194);
x_207 = lean::cnstr_get(x_206, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_206, 1);
lean::inc(x_209);
lean::dec(x_206);
if (lean::obj_tag(x_207) == 0)
{
obj* x_213; obj* x_216; 
lean::dec(x_49);
x_213 = lean::cnstr_get(x_207, 0);
lean::inc(x_213);
lean::dec(x_207);
if (lean::is_scalar(x_155)) {
 x_216 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_216 = x_155;
 lean::cnstr_set_tag(x_155, 0);
}
lean::cnstr_set(x_216, 0, x_213);
x_35 = x_216;
x_36 = x_209;
goto lbl_37;
}
else
{
obj* x_219; obj* x_220; obj* x_222; 
lean::dec(x_207);
lean::inc(x_3);
x_219 = l_lean_ir_cpp_emit__uncurry__header(x_49, x_3, x_209);
x_220 = lean::cnstr_get(x_219, 0);
lean::inc(x_220);
x_222 = lean::cnstr_get(x_219, 1);
lean::inc(x_222);
lean::dec(x_219);
if (lean::obj_tag(x_220) == 0)
{
obj* x_225; obj* x_228; 
x_225 = lean::cnstr_get(x_220, 0);
lean::inc(x_225);
lean::dec(x_220);
if (lean::is_scalar(x_155)) {
 x_228 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_228 = x_155;
 lean::cnstr_set_tag(x_155, 0);
}
lean::cnstr_set(x_228, 0, x_225);
x_35 = x_228;
x_36 = x_222;
goto lbl_37;
}
else
{
obj* x_233; obj* x_234; obj* x_236; 
lean::dec(x_220);
lean::dec(x_155);
lean::inc(x_3);
lean::inc(x_203);
x_233 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_203, x_3, x_222);
x_234 = lean::cnstr_get(x_233, 0);
lean::inc(x_234);
x_236 = lean::cnstr_get(x_233, 1);
lean::inc(x_236);
lean::dec(x_233);
x_35 = x_234;
x_36 = x_236;
goto lbl_37;
}
}
}
}
}
}
}
lbl_37:
{
if (lean::obj_tag(x_35) == 0)
{
obj* x_242; obj* x_245; obj* x_246; 
lean::dec(x_14);
lean::dec(x_3);
lean::dec(x_0);
x_242 = lean::cnstr_get(x_35, 0);
lean::inc(x_242);
lean::dec(x_35);
if (lean::is_scalar(x_34)) {
 x_245 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_245 = x_34;
 lean::cnstr_set_tag(x_34, 0);
}
lean::cnstr_set(x_245, 0, x_242);
if (lean::is_scalar(x_24)) {
 x_246 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_246 = x_24;
}
lean::cnstr_set(x_246, 0, x_245);
lean::cnstr_set(x_246, 1, x_36);
return x_246;
}
else
{
obj* x_250; 
lean::dec(x_35);
lean::dec(x_24);
lean::dec(x_34);
x_250 = lean::box(0);
x_1 = x_14;
x_2 = x_250;
x_4 = x_36;
goto _start;
}
}
}
}
default:
{
obj* x_252; obj* x_254; obj* x_256; obj* x_261; obj* x_262; obj* x_264; obj* x_266; 
x_252 = lean::cnstr_get(x_1, 0);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_1, 1);
lean::inc(x_254);
x_256 = lean::cnstr_get(x_1, 3);
lean::inc(x_256);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_0);
x_261 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1(x_0, x_252, x_2, x_3, x_4);
x_262 = lean::cnstr_get(x_261, 0);
lean::inc(x_262);
x_264 = lean::cnstr_get(x_261, 1);
lean::inc(x_264);
if (lean::is_shared(x_261)) {
 lean::dec(x_261);
 x_266 = lean::box(0);
} else {
 lean::cnstr_release(x_261, 0);
 lean::cnstr_release(x_261, 1);
 x_266 = x_261;
}
if (lean::obj_tag(x_262) == 0)
{
obj* x_271; obj* x_273; obj* x_274; obj* x_275; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_254);
lean::dec(x_256);
x_271 = lean::cnstr_get(x_262, 0);
lean::inc(x_271);
if (lean::is_shared(x_262)) {
 lean::dec(x_262);
 x_273 = lean::box(0);
} else {
 lean::cnstr_release(x_262, 0);
 x_273 = x_262;
}
if (lean::is_scalar(x_273)) {
 x_274 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_274 = x_273;
}
lean::cnstr_set(x_274, 0, x_271);
if (lean::is_scalar(x_266)) {
 x_275 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_275 = x_266;
}
lean::cnstr_set(x_275, 0, x_274);
lean::cnstr_set(x_275, 1, x_264);
return x_275;
}
else
{
obj* x_276; obj* x_277; obj* x_278; obj* x_280; obj* x_282; obj* x_285; 
if (lean::is_shared(x_262)) {
 lean::dec(x_262);
 x_276 = lean::box(0);
} else {
 lean::cnstr_release(x_262, 0);
 x_276 = x_262;
}
x_280 = lean::cnstr_get(x_0, 0);
lean::inc(x_280);
x_282 = lean::cnstr_get(x_280, 3);
lean::inc(x_282);
lean::inc(x_254);
x_285 = lean::apply_1(x_282, x_254);
if (lean::obj_tag(x_285) == 0)
{
obj* x_289; 
lean::dec(x_254);
lean::dec(x_280);
lean::dec(x_285);
x_289 = l_lean_ir_match__type___closed__5;
lean::inc(x_289);
x_277 = x_289;
x_278 = x_264;
goto lbl_279;
}
else
{
obj* x_291; obj* x_294; obj* x_297; 
x_291 = lean::cnstr_get(x_285, 0);
lean::inc(x_291);
lean::dec(x_285);
x_294 = lean::cnstr_get(x_280, 4);
lean::inc(x_294);
lean::dec(x_280);
x_297 = lean::apply_1(x_294, x_254);
if (lean::obj_tag(x_297) == 0)
{
obj* x_300; obj* x_302; uint8 x_303; obj* x_306; 
lean::dec(x_297);
lean::inc(x_291);
x_300 = l_lean_ir_decl_header___main(x_291);
lean::inc(x_291);
x_302 = l_lean_ir_cpp_need__uncurry(x_291);
x_303 = lean::unbox(x_302);
lean::dec(x_302);
lean::inc(x_3);
x_306 = l_lean_ir_cpp_emit__header(x_300, x_3, x_264);
if (x_303 == 0)
{
obj* x_308; obj* x_310; 
lean::dec(x_291);
x_308 = lean::cnstr_get(x_306, 0);
lean::inc(x_308);
x_310 = lean::cnstr_get(x_306, 1);
lean::inc(x_310);
lean::dec(x_306);
if (lean::obj_tag(x_308) == 0)
{
obj* x_313; obj* x_315; obj* x_316; 
x_313 = lean::cnstr_get(x_308, 0);
lean::inc(x_313);
if (lean::is_shared(x_308)) {
 lean::dec(x_308);
 x_315 = lean::box(0);
} else {
 lean::cnstr_release(x_308, 0);
 x_315 = x_308;
}
if (lean::is_scalar(x_315)) {
 x_316 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_316 = x_315;
}
lean::cnstr_set(x_316, 0, x_313);
x_277 = x_316;
x_278 = x_310;
goto lbl_279;
}
else
{
obj* x_317; obj* x_318; obj* x_321; obj* x_322; obj* x_324; 
if (lean::is_shared(x_308)) {
 lean::dec(x_308);
 x_317 = lean::box(0);
} else {
 lean::cnstr_release(x_308, 0);
 x_317 = x_308;
}
x_318 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_318);
x_321 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_318, x_3, x_310);
x_322 = lean::cnstr_get(x_321, 0);
lean::inc(x_322);
x_324 = lean::cnstr_get(x_321, 1);
lean::inc(x_324);
lean::dec(x_321);
if (lean::obj_tag(x_322) == 0)
{
obj* x_327; obj* x_330; 
x_327 = lean::cnstr_get(x_322, 0);
lean::inc(x_327);
lean::dec(x_322);
if (lean::is_scalar(x_317)) {
 x_330 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_330 = x_317;
 lean::cnstr_set_tag(x_317, 0);
}
lean::cnstr_set(x_330, 0, x_327);
x_277 = x_330;
x_278 = x_324;
goto lbl_279;
}
else
{
obj* x_333; 
lean::dec(x_322);
lean::dec(x_317);
x_333 = l_lean_ir_match__type___closed__5;
lean::inc(x_333);
x_277 = x_333;
x_278 = x_324;
goto lbl_279;
}
}
}
else
{
obj* x_335; obj* x_337; 
x_335 = lean::cnstr_get(x_306, 0);
lean::inc(x_335);
x_337 = lean::cnstr_get(x_306, 1);
lean::inc(x_337);
lean::dec(x_306);
if (lean::obj_tag(x_335) == 0)
{
obj* x_341; obj* x_343; obj* x_344; 
lean::dec(x_291);
x_341 = lean::cnstr_get(x_335, 0);
lean::inc(x_341);
if (lean::is_shared(x_335)) {
 lean::dec(x_335);
 x_343 = lean::box(0);
} else {
 lean::cnstr_release(x_335, 0);
 x_343 = x_335;
}
if (lean::is_scalar(x_343)) {
 x_344 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_344 = x_343;
}
lean::cnstr_set(x_344, 0, x_341);
x_277 = x_344;
x_278 = x_337;
goto lbl_279;
}
else
{
obj* x_345; obj* x_346; obj* x_349; obj* x_350; obj* x_352; 
if (lean::is_shared(x_335)) {
 lean::dec(x_335);
 x_345 = lean::box(0);
} else {
 lean::cnstr_release(x_335, 0);
 x_345 = x_335;
}
x_346 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_346);
x_349 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_346, x_3, x_337);
x_350 = lean::cnstr_get(x_349, 0);
lean::inc(x_350);
x_352 = lean::cnstr_get(x_349, 1);
lean::inc(x_352);
lean::dec(x_349);
if (lean::obj_tag(x_350) == 0)
{
obj* x_356; obj* x_359; 
lean::dec(x_291);
x_356 = lean::cnstr_get(x_350, 0);
lean::inc(x_356);
lean::dec(x_350);
if (lean::is_scalar(x_345)) {
 x_359 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_359 = x_345;
 lean::cnstr_set_tag(x_345, 0);
}
lean::cnstr_set(x_359, 0, x_356);
x_277 = x_359;
x_278 = x_352;
goto lbl_279;
}
else
{
obj* x_362; obj* x_363; obj* x_365; 
lean::dec(x_350);
lean::inc(x_3);
x_362 = l_lean_ir_cpp_emit__uncurry__header(x_291, x_3, x_352);
x_363 = lean::cnstr_get(x_362, 0);
lean::inc(x_363);
x_365 = lean::cnstr_get(x_362, 1);
lean::inc(x_365);
lean::dec(x_362);
if (lean::obj_tag(x_363) == 0)
{
obj* x_368; obj* x_371; 
x_368 = lean::cnstr_get(x_363, 0);
lean::inc(x_368);
lean::dec(x_363);
if (lean::is_scalar(x_345)) {
 x_371 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_371 = x_345;
 lean::cnstr_set_tag(x_345, 0);
}
lean::cnstr_set(x_371, 0, x_368);
x_277 = x_371;
x_278 = x_365;
goto lbl_279;
}
else
{
obj* x_376; obj* x_377; obj* x_379; 
lean::dec(x_363);
lean::dec(x_345);
lean::inc(x_3);
lean::inc(x_346);
x_376 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_346, x_3, x_365);
x_377 = lean::cnstr_get(x_376, 0);
lean::inc(x_377);
x_379 = lean::cnstr_get(x_376, 1);
lean::inc(x_379);
lean::dec(x_376);
x_277 = x_377;
x_278 = x_379;
goto lbl_279;
}
}
}
}
}
else
{
obj* x_383; obj* x_386; obj* x_387; obj* x_389; 
lean::dec(x_297);
x_383 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2;
lean::inc(x_3);
lean::inc(x_383);
x_386 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_383, x_3, x_264);
x_387 = lean::cnstr_get(x_386, 0);
lean::inc(x_387);
x_389 = lean::cnstr_get(x_386, 1);
lean::inc(x_389);
lean::dec(x_386);
if (lean::obj_tag(x_387) == 0)
{
obj* x_393; obj* x_395; obj* x_396; 
lean::dec(x_291);
x_393 = lean::cnstr_get(x_387, 0);
lean::inc(x_393);
if (lean::is_shared(x_387)) {
 lean::dec(x_387);
 x_395 = lean::box(0);
} else {
 lean::cnstr_release(x_387, 0);
 x_395 = x_387;
}
if (lean::is_scalar(x_395)) {
 x_396 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_396 = x_395;
}
lean::cnstr_set(x_396, 0, x_393);
x_277 = x_396;
x_278 = x_389;
goto lbl_279;
}
else
{
obj* x_397; obj* x_399; obj* x_401; uint8 x_402; obj* x_405; 
if (lean::is_shared(x_387)) {
 lean::dec(x_387);
 x_397 = lean::box(0);
} else {
 lean::cnstr_release(x_387, 0);
 x_397 = x_387;
}
lean::inc(x_291);
x_399 = l_lean_ir_decl_header___main(x_291);
lean::inc(x_291);
x_401 = l_lean_ir_cpp_need__uncurry(x_291);
x_402 = lean::unbox(x_401);
lean::dec(x_401);
lean::inc(x_3);
x_405 = l_lean_ir_cpp_emit__header(x_399, x_3, x_389);
if (x_402 == 0)
{
obj* x_407; obj* x_409; 
lean::dec(x_291);
x_407 = lean::cnstr_get(x_405, 0);
lean::inc(x_407);
x_409 = lean::cnstr_get(x_405, 1);
lean::inc(x_409);
lean::dec(x_405);
if (lean::obj_tag(x_407) == 0)
{
obj* x_412; obj* x_415; 
x_412 = lean::cnstr_get(x_407, 0);
lean::inc(x_412);
lean::dec(x_407);
if (lean::is_scalar(x_397)) {
 x_415 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_415 = x_397;
 lean::cnstr_set_tag(x_397, 0);
}
lean::cnstr_set(x_415, 0, x_412);
x_277 = x_415;
x_278 = x_409;
goto lbl_279;
}
else
{
obj* x_417; obj* x_420; obj* x_421; obj* x_423; 
lean::dec(x_407);
x_417 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_417);
x_420 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_417, x_3, x_409);
x_421 = lean::cnstr_get(x_420, 0);
lean::inc(x_421);
x_423 = lean::cnstr_get(x_420, 1);
lean::inc(x_423);
lean::dec(x_420);
if (lean::obj_tag(x_421) == 0)
{
obj* x_426; obj* x_429; 
x_426 = lean::cnstr_get(x_421, 0);
lean::inc(x_426);
lean::dec(x_421);
if (lean::is_scalar(x_397)) {
 x_429 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_429 = x_397;
 lean::cnstr_set_tag(x_397, 0);
}
lean::cnstr_set(x_429, 0, x_426);
x_277 = x_429;
x_278 = x_423;
goto lbl_279;
}
else
{
obj* x_432; 
lean::dec(x_397);
lean::dec(x_421);
x_432 = l_lean_ir_match__type___closed__5;
lean::inc(x_432);
x_277 = x_432;
x_278 = x_423;
goto lbl_279;
}
}
}
else
{
obj* x_434; obj* x_436; 
x_434 = lean::cnstr_get(x_405, 0);
lean::inc(x_434);
x_436 = lean::cnstr_get(x_405, 1);
lean::inc(x_436);
lean::dec(x_405);
if (lean::obj_tag(x_434) == 0)
{
obj* x_440; obj* x_443; 
lean::dec(x_291);
x_440 = lean::cnstr_get(x_434, 0);
lean::inc(x_440);
lean::dec(x_434);
if (lean::is_scalar(x_397)) {
 x_443 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_443 = x_397;
 lean::cnstr_set_tag(x_397, 0);
}
lean::cnstr_set(x_443, 0, x_440);
x_277 = x_443;
x_278 = x_436;
goto lbl_279;
}
else
{
obj* x_445; obj* x_448; obj* x_449; obj* x_451; 
lean::dec(x_434);
x_445 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_445);
x_448 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_445, x_3, x_436);
x_449 = lean::cnstr_get(x_448, 0);
lean::inc(x_449);
x_451 = lean::cnstr_get(x_448, 1);
lean::inc(x_451);
lean::dec(x_448);
if (lean::obj_tag(x_449) == 0)
{
obj* x_455; obj* x_458; 
lean::dec(x_291);
x_455 = lean::cnstr_get(x_449, 0);
lean::inc(x_455);
lean::dec(x_449);
if (lean::is_scalar(x_397)) {
 x_458 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_458 = x_397;
 lean::cnstr_set_tag(x_397, 0);
}
lean::cnstr_set(x_458, 0, x_455);
x_277 = x_458;
x_278 = x_451;
goto lbl_279;
}
else
{
obj* x_461; obj* x_462; obj* x_464; 
lean::dec(x_449);
lean::inc(x_3);
x_461 = l_lean_ir_cpp_emit__uncurry__header(x_291, x_3, x_451);
x_462 = lean::cnstr_get(x_461, 0);
lean::inc(x_462);
x_464 = lean::cnstr_get(x_461, 1);
lean::inc(x_464);
lean::dec(x_461);
if (lean::obj_tag(x_462) == 0)
{
obj* x_467; obj* x_470; 
x_467 = lean::cnstr_get(x_462, 0);
lean::inc(x_467);
lean::dec(x_462);
if (lean::is_scalar(x_397)) {
 x_470 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_470 = x_397;
 lean::cnstr_set_tag(x_397, 0);
}
lean::cnstr_set(x_470, 0, x_467);
x_277 = x_470;
x_278 = x_464;
goto lbl_279;
}
else
{
obj* x_475; obj* x_476; obj* x_478; 
lean::dec(x_397);
lean::dec(x_462);
lean::inc(x_3);
lean::inc(x_445);
x_475 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_445, x_3, x_464);
x_476 = lean::cnstr_get(x_475, 0);
lean::inc(x_476);
x_478 = lean::cnstr_get(x_475, 1);
lean::inc(x_478);
lean::dec(x_475);
x_277 = x_476;
x_278 = x_478;
goto lbl_279;
}
}
}
}
}
}
}
lbl_279:
{
if (lean::obj_tag(x_277) == 0)
{
obj* x_484; obj* x_487; obj* x_488; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_256);
x_484 = lean::cnstr_get(x_277, 0);
lean::inc(x_484);
lean::dec(x_277);
if (lean::is_scalar(x_276)) {
 x_487 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_487 = x_276;
 lean::cnstr_set_tag(x_276, 0);
}
lean::cnstr_set(x_487, 0, x_484);
if (lean::is_scalar(x_266)) {
 x_488 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_488 = x_266;
}
lean::cnstr_set(x_488, 0, x_487);
lean::cnstr_set(x_488, 1, x_278);
return x_488;
}
else
{
obj* x_492; 
lean::dec(x_277);
lean::dec(x_276);
lean::dec(x_266);
x_492 = lean::box(0);
x_1 = x_256;
x_2 = x_492;
x_4 = x_278;
goto _start;
}
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__used__headers(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_3 = l_lean_ir_mk__fnid__set;
lean::inc(x_3);
x_5 = l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__6(x_3, x_0);
x_6 = lean::box(0);
lean::inc(x_1);
x_8 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1(x_1, x_5, x_6, x_1, x_2);
return x_8;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__global__var__decls___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; uint8 x_14; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = l_lean_ir_decl_header___main(x_8);
x_14 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*3);
if (x_14 == 0)
{
lean::dec(x_13);
x_0 = x_10;
goto _start;
}
else
{
obj* x_17; uint8 x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_27; 
x_17 = lean::cnstr_get(x_13, 2);
lean::inc(x_17);
x_19 = lean::unbox(x_17);
lean::dec(x_17);
lean::inc(x_1);
x_22 = l_lean_ir_cpp_emit__type(x_19, x_1, x_2);
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
x_37 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_37);
x_40 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_37, x_1, x_25);
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
 lean::cnstr_set_tag(x_36, 0);
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
x_59 = l_lean_ir_cpp_emit__global(x_55, x_1, x_43);
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
 lean::cnstr_set_tag(x_36, 0);
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
x_73 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_1);
lean::inc(x_73);
x_76 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_73, x_1, x_62);
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
 lean::cnstr_set_tag(x_36, 0);
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
lean::dec(x_36);
lean::dec(x_27);
lean::dec(x_77);
x_0 = x_10;
x_2 = x_79;
goto _start;
}
}
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__global__var__decls(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__global__var__decls___spec__1(x_0, x_1, x_2);
return x_3;
}
}
obj* _init_l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("();\n");
return x_0;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
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
x_13 = l_lean_ir_cpp_initialize__prefix;
lean::inc(x_1);
lean::inc(x_13);
x_16 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_13, x_1, x_2);
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
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
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
x_32 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_8, x_1, x_19);
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
 lean::cnstr_set_tag(x_30, 0);
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
x_46 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_1);
lean::inc(x_46);
x_49 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_46, x_1, x_35);
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
 lean::cnstr_set_tag(x_30, 0);
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
lean::dec(x_21);
lean::dec(x_30);
lean::dec(x_50);
x_0 = x_10;
x_2 = x_52;
goto _start;
}
}
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; uint8 x_14; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = l_lean_ir_decl_header___main(x_8);
x_14 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*3);
if (x_14 == 0)
{
lean::dec(x_13);
x_0 = x_10;
goto _start;
}
else
{
obj* x_17; obj* x_22; obj* x_23; obj* x_25; obj* x_27; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
lean::dec(x_13);
lean::inc(x_1);
lean::inc(x_17);
x_22 = l_lean_ir_cpp_emit__global(x_17, x_1, x_2);
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
x_37 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_1);
lean::inc(x_37);
x_40 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_37, x_1, x_25);
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
 lean::cnstr_set_tag(x_36, 0);
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
x_56 = l_lean_ir_cpp_emit__fnid(x_17, x_1, x_43);
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
 lean::cnstr_set_tag(x_36, 0);
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
x_70 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_1);
lean::inc(x_70);
x_73 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_70, x_1, x_59);
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
 lean::cnstr_set_tag(x_36, 0);
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
lean::dec(x_27);
lean::dec(x_36);
lean::dec(x_74);
x_0 = x_10;
x_2 = x_76;
goto _start;
}
}
}
}
}
}
}
}
obj* _init_l_lean_ir_cpp_emit__initialize__proc___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("void ");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__initialize__proc___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("() {\n");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__initialize__proc___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("if (_G_initialized) return;\n");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__initialize__proc___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_G_initialized = true;\n");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__initialize__proc(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = l_lean_ir_cpp_emit__initialize__proc___closed__1;
lean::inc(x_1);
lean::inc(x_3);
x_6 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
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
lean::dec(x_0);
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
x_20 = l_lean_ir_cpp_initialize__prefix;
lean::inc(x_1);
lean::inc(x_20);
x_23 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_20, x_1, x_9);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_31; obj* x_34; obj* x_35; 
lean::dec(x_1);
lean::dec(x_0);
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
lean::dec(x_24);
if (lean::is_scalar(x_19)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_19;
 lean::cnstr_set_tag(x_19, 0);
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
x_42 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_39, x_1, x_26);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_51; obj* x_54; obj* x_55; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
x_51 = lean::cnstr_get(x_43, 0);
lean::inc(x_51);
lean::dec(x_43);
if (lean::is_scalar(x_19)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_19;
 lean::cnstr_set_tag(x_19, 0);
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
x_57 = l_lean_ir_cpp_emit__initialize__proc___closed__2;
lean::inc(x_1);
lean::inc(x_57);
x_60 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_57, x_1, x_45);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_69; obj* x_72; obj* x_73; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
x_69 = lean::cnstr_get(x_61, 0);
lean::inc(x_69);
lean::dec(x_61);
if (lean::is_scalar(x_19)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_19;
 lean::cnstr_set_tag(x_19, 0);
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
x_75 = l_lean_ir_cpp_emit__initialize__proc___closed__3;
lean::inc(x_1);
lean::inc(x_75);
x_78 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_75, x_1, x_63);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
lean::dec(x_78);
if (lean::obj_tag(x_79) == 0)
{
obj* x_87; obj* x_90; obj* x_91; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
x_87 = lean::cnstr_get(x_79, 0);
lean::inc(x_87);
lean::dec(x_79);
if (lean::is_scalar(x_19)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_19;
 lean::cnstr_set_tag(x_19, 0);
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
x_93 = l_lean_ir_cpp_emit__initialize__proc___closed__4;
lean::inc(x_1);
lean::inc(x_93);
x_96 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_93, x_1, x_81);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
lean::dec(x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_105; obj* x_108; obj* x_109; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
x_105 = lean::cnstr_get(x_97, 0);
lean::inc(x_105);
lean::dec(x_97);
if (lean::is_scalar(x_19)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_19;
 lean::cnstr_set_tag(x_19, 0);
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
x_115 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1(x_111, x_1, x_99);
x_116 = lean::cnstr_get(x_115, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_115, 1);
lean::inc(x_118);
lean::dec(x_115);
if (lean::obj_tag(x_116) == 0)
{
obj* x_123; obj* x_126; obj* x_127; 
lean::dec(x_1);
lean::dec(x_0);
x_123 = lean::cnstr_get(x_116, 0);
lean::inc(x_123);
lean::dec(x_116);
if (lean::is_scalar(x_19)) {
 x_126 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_126 = x_19;
 lean::cnstr_set_tag(x_19, 0);
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
x_130 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__2(x_0, x_1, x_118);
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
 lean::cnstr_set_tag(x_19, 0);
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
lean::dec(x_11);
lean::dec(x_19);
lean::dec(x_131);
x_145 = l_lean_ir_cpp_emit__uncurry___closed__1;
lean::inc(x_145);
x_147 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_145, x_1, x_133);
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
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
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
x_13 = l_lean_ir_cpp_finalize__prefix;
lean::inc(x_1);
lean::inc(x_13);
x_16 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_13, x_1, x_2);
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
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
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
x_32 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_8, x_1, x_19);
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
 lean::cnstr_set_tag(x_30, 0);
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
x_46 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_1);
lean::inc(x_46);
x_49 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_46, x_1, x_35);
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
 lean::cnstr_set_tag(x_30, 0);
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
lean::dec(x_21);
lean::dec(x_30);
lean::dec(x_50);
x_0 = x_10;
x_2 = x_52;
goto _start;
}
}
}
}
}
}
obj* _init_l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("if (!is_scalar(");
return x_0;
}
}
obj* _init_l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(")) lean::dec_ref(");
return x_0;
}
}
obj* _init_l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(");\n");
return x_0;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
lean::inc(x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_16; obj* x_17; uint8 x_19; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_16 = l_lean_ir_decl_header___main(x_8);
x_19 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*3);
if (x_19 == 0)
{
if (x_19 == 0)
{
obj* x_21; 
lean::dec(x_16);
x_21 = l_lean_ir_match__type___closed__5;
lean::inc(x_21);
x_13 = x_21;
x_14 = x_2;
goto lbl_15;
}
else
{
obj* x_23; 
x_23 = lean::box(0);
x_17 = x_23;
goto lbl_18;
}
}
else
{
obj* x_24; uint8 x_26; obj* x_28; obj* x_29; uint8 x_30; 
x_24 = lean::cnstr_get(x_16, 2);
lean::inc(x_24);
x_26 = lean::unbox(x_24);
lean::dec(x_24);
x_28 = l_lean_ir_type2id___main(x_26);
x_29 = l_lean_ir_valid__assign__unop__types___closed__1;
x_30 = lean::nat_dec_eq(x_28, x_29);
lean::dec(x_28);
if (x_30 == 0)
{
obj* x_33; 
lean::dec(x_16);
x_33 = l_lean_ir_match__type___closed__5;
lean::inc(x_33);
x_13 = x_33;
x_14 = x_2;
goto lbl_15;
}
else
{
if (x_19 == 0)
{
obj* x_36; 
lean::dec(x_16);
x_36 = l_lean_ir_match__type___closed__5;
lean::inc(x_36);
x_13 = x_36;
x_14 = x_2;
goto lbl_15;
}
else
{
obj* x_38; 
x_38 = lean::box(0);
x_17 = x_38;
goto lbl_18;
}
}
}
lbl_15:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_41; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_10);
lean::dec(x_1);
x_41 = lean::cnstr_get(x_13, 0);
lean::inc(x_41);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_43 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_43 = x_13;
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_41);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_14);
return x_45;
}
else
{
lean::dec(x_13);
x_0 = x_10;
x_2 = x_14;
goto _start;
}
}
lbl_18:
{
obj* x_49; obj* x_52; obj* x_53; obj* x_55; 
lean::dec(x_17);
x_49 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__1;
lean::inc(x_1);
lean::inc(x_49);
x_52 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_49, x_1, x_2);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
if (lean::obj_tag(x_53) == 0)
{
obj* x_59; obj* x_61; obj* x_62; 
lean::dec(x_16);
x_59 = lean::cnstr_get(x_53, 0);
lean::inc(x_59);
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_61 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 x_61 = x_53;
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_59);
x_13 = x_62;
x_14 = x_55;
goto lbl_15;
}
else
{
obj* x_63; obj* x_64; obj* x_69; obj* x_70; obj* x_72; 
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_63 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 x_63 = x_53;
}
x_64 = lean::cnstr_get(x_16, 0);
lean::inc(x_64);
lean::dec(x_16);
lean::inc(x_1);
lean::inc(x_64);
x_69 = l_lean_ir_cpp_emit__global(x_64, x_1, x_55);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
lean::dec(x_69);
if (lean::obj_tag(x_70) == 0)
{
obj* x_76; obj* x_79; 
lean::dec(x_64);
x_76 = lean::cnstr_get(x_70, 0);
lean::inc(x_76);
lean::dec(x_70);
if (lean::is_scalar(x_63)) {
 x_79 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_79 = x_63;
 lean::cnstr_set_tag(x_63, 0);
}
lean::cnstr_set(x_79, 0, x_76);
x_13 = x_79;
x_14 = x_72;
goto lbl_15;
}
else
{
obj* x_81; obj* x_84; obj* x_85; obj* x_87; 
lean::dec(x_70);
x_81 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__2;
lean::inc(x_1);
lean::inc(x_81);
x_84 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_81, x_1, x_72);
x_85 = lean::cnstr_get(x_84, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_84, 1);
lean::inc(x_87);
lean::dec(x_84);
if (lean::obj_tag(x_85) == 0)
{
obj* x_91; obj* x_94; 
lean::dec(x_64);
x_91 = lean::cnstr_get(x_85, 0);
lean::inc(x_91);
lean::dec(x_85);
if (lean::is_scalar(x_63)) {
 x_94 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_94 = x_63;
 lean::cnstr_set_tag(x_63, 0);
}
lean::cnstr_set(x_94, 0, x_91);
x_13 = x_94;
x_14 = x_87;
goto lbl_15;
}
else
{
obj* x_97; obj* x_98; obj* x_100; 
lean::dec(x_85);
lean::inc(x_1);
x_97 = l_lean_ir_cpp_emit__global(x_64, x_1, x_87);
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_97, 1);
lean::inc(x_100);
lean::dec(x_97);
if (lean::obj_tag(x_98) == 0)
{
obj* x_103; obj* x_106; 
x_103 = lean::cnstr_get(x_98, 0);
lean::inc(x_103);
lean::dec(x_98);
if (lean::is_scalar(x_63)) {
 x_106 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_106 = x_63;
 lean::cnstr_set_tag(x_63, 0);
}
lean::cnstr_set(x_106, 0, x_103);
x_13 = x_106;
x_14 = x_100;
goto lbl_15;
}
else
{
obj* x_109; obj* x_112; obj* x_113; obj* x_115; 
lean::dec(x_98);
lean::dec(x_63);
x_109 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__3;
lean::inc(x_1);
lean::inc(x_109);
x_112 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_109, x_1, x_100);
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_112, 1);
lean::inc(x_115);
lean::dec(x_112);
x_13 = x_113;
x_14 = x_115;
goto lbl_15;
}
}
}
}
}
}
}
}
obj* _init_l_lean_ir_cpp_emit__finalize__proc___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("if (_G_finalized) return;\n");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__finalize__proc___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("_G_finalized = true;\n");
return x_0;
}
}
obj* l_lean_ir_cpp_emit__finalize__proc(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = l_lean_ir_cpp_emit__initialize__proc___closed__1;
lean::inc(x_1);
lean::inc(x_3);
x_6 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
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
lean::dec(x_0);
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
x_20 = l_lean_ir_cpp_finalize__prefix;
lean::inc(x_1);
lean::inc(x_20);
x_23 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_20, x_1, x_9);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_31; obj* x_34; obj* x_35; 
lean::dec(x_1);
lean::dec(x_0);
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
lean::dec(x_24);
if (lean::is_scalar(x_19)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_19;
 lean::cnstr_set_tag(x_19, 0);
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
x_42 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_39, x_1, x_26);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_51; obj* x_54; obj* x_55; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
x_51 = lean::cnstr_get(x_43, 0);
lean::inc(x_51);
lean::dec(x_43);
if (lean::is_scalar(x_19)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_19;
 lean::cnstr_set_tag(x_19, 0);
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
x_57 = l_lean_ir_cpp_emit__initialize__proc___closed__2;
lean::inc(x_1);
lean::inc(x_57);
x_60 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_57, x_1, x_45);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_69; obj* x_72; obj* x_73; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
x_69 = lean::cnstr_get(x_61, 0);
lean::inc(x_69);
lean::dec(x_61);
if (lean::is_scalar(x_19)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_19;
 lean::cnstr_set_tag(x_19, 0);
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
x_75 = l_lean_ir_cpp_emit__finalize__proc___closed__1;
lean::inc(x_1);
lean::inc(x_75);
x_78 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_75, x_1, x_63);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
lean::dec(x_78);
if (lean::obj_tag(x_79) == 0)
{
obj* x_87; obj* x_90; obj* x_91; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
x_87 = lean::cnstr_get(x_79, 0);
lean::inc(x_87);
lean::dec(x_79);
if (lean::is_scalar(x_19)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_19;
 lean::cnstr_set_tag(x_19, 0);
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
x_93 = l_lean_ir_cpp_emit__finalize__proc___closed__2;
lean::inc(x_1);
lean::inc(x_93);
x_96 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_93, x_1, x_81);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
lean::dec(x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_105; obj* x_108; obj* x_109; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
x_105 = lean::cnstr_get(x_97, 0);
lean::inc(x_105);
lean::dec(x_97);
if (lean::is_scalar(x_19)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_19;
 lean::cnstr_set_tag(x_19, 0);
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
x_115 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__1(x_111, x_1, x_99);
x_116 = lean::cnstr_get(x_115, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_115, 1);
lean::inc(x_118);
lean::dec(x_115);
if (lean::obj_tag(x_116) == 0)
{
obj* x_123; obj* x_126; obj* x_127; 
lean::dec(x_1);
lean::dec(x_0);
x_123 = lean::cnstr_get(x_116, 0);
lean::inc(x_123);
lean::dec(x_116);
if (lean::is_scalar(x_19)) {
 x_126 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_126 = x_19;
 lean::cnstr_set_tag(x_19, 0);
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
x_130 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2(x_0, x_1, x_118);
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
 lean::cnstr_set_tag(x_19, 0);
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
lean::dec(x_11);
lean::dec(x_19);
lean::dec(x_131);
x_145 = l_lean_ir_cpp_emit__uncurry___closed__1;
lean::inc(x_145);
x_147 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_145, x_1, x_133);
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
obj* _init_l_lean_ir_cpp_emit__main__proc___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("unknown main function '");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_cpp_emit__main__proc___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("return r;\n}\n");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__main__proc___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("int r = ");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__main__proc___closed__4() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("int main() {\n");
return x_0;
}
}
obj* _init_l_lean_ir_cpp_emit__main__proc___closed__5() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("invalid main function '");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_cpp_emit__main__proc___closed__6() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("', it must not take any arguments");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_ir_cpp_emit__main__proc___closed__7() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("', return type must be int32");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_ir_cpp_emit__main__proc(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_2, 5);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_11; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_2);
x_9 = l_lean_ir_match__type___closed__5;
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
obj* x_22; obj* x_23; uint8 x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_18);
lean::dec(x_0);
lean::dec(x_2);
x_22 = l_lean_ir_id_to__string___main(x_12);
x_23 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = 0;
x_25 = l_lean_ir_cpp_emit__main__proc___closed__1;
lean::inc(x_25);
x_27 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_24);
x_28 = x_27;
x_29 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
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
obj* x_35; obj* x_38; obj* x_39; obj* x_41; obj* x_43; uint8 x_44; obj* x_47; uint8 x_50; obj* x_52; obj* x_53; uint8 x_54; obj* x_56; uint8 x_59; 
x_35 = lean::cnstr_get(x_18, 0);
lean::inc(x_35);
lean::dec(x_18);
x_38 = l_lean_ir_decl_header___main(x_35);
x_39 = lean::cnstr_get(x_38, 1);
lean::inc(x_39);
x_41 = lean::mk_nat_obj(0u);
lean::inc(x_41);
x_43 = l_list_length__aux___main___rarg(x_39, x_41);
x_44 = lean::nat_dec_eq(x_43, x_41);
lean::dec(x_41);
lean::dec(x_43);
x_47 = lean::cnstr_get(x_38, 2);
lean::inc(x_47);
lean::dec(x_38);
x_50 = lean::unbox(x_47);
lean::dec(x_47);
x_52 = l_lean_ir_type2id___main(x_50);
x_53 = l_lean_ir_valid__assign__unop__types___closed__4;
x_54 = lean::nat_dec_eq(x_52, x_53);
lean::dec(x_52);
x_56 = lean::cnstr_get(x_2, 0);
lean::inc(x_56);
lean::dec(x_2);
if (x_54 == 0)
{
uint8 x_61; 
x_61 = 0;
x_59 = x_61;
goto lbl_60;
}
else
{
uint8 x_62; 
x_62 = 1;
x_59 = x_62;
goto lbl_60;
}
lbl_60:
{
obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_69; obj* x_70; 
if (x_44 == 0)
{
obj* x_73; obj* x_74; uint8 x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_82; obj* x_83; obj* x_84; 
lean::inc(x_12);
x_73 = l_lean_ir_id_to__string___main(x_12);
x_74 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_74, 0, x_73);
x_75 = 0;
x_76 = l_lean_ir_cpp_emit__main__proc___closed__5;
lean::inc(x_76);
x_78 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_74);
lean::cnstr_set_scalar(x_78, sizeof(void*)*2, x_75);
x_79 = x_78;
x_80 = l_lean_ir_cpp_emit__main__proc___closed__6;
lean::inc(x_80);
x_82 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_82, 0, x_79);
lean::cnstr_set(x_82, 1, x_80);
lean::cnstr_set_scalar(x_82, sizeof(void*)*2, x_75);
x_83 = x_82;
x_84 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_84, 0, x_83);
x_69 = x_84;
x_70 = x_1;
goto lbl_71;
}
else
{
if (x_59 == 0)
{
obj* x_86; obj* x_87; uint8 x_88; obj* x_89; obj* x_91; obj* x_92; obj* x_93; obj* x_95; obj* x_96; obj* x_97; 
lean::inc(x_12);
x_86 = l_lean_ir_id_to__string___main(x_12);
x_87 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
x_88 = 0;
x_89 = l_lean_ir_cpp_emit__main__proc___closed__5;
lean::inc(x_89);
x_91 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_91, 0, x_89);
lean::cnstr_set(x_91, 1, x_87);
lean::cnstr_set_scalar(x_91, sizeof(void*)*2, x_88);
x_92 = x_91;
x_93 = l_lean_ir_cpp_emit__main__proc___closed__7;
lean::inc(x_93);
x_95 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_95, 0, x_92);
lean::cnstr_set(x_95, 1, x_93);
lean::cnstr_set_scalar(x_95, sizeof(void*)*2, x_88);
x_96 = x_95;
x_97 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_97, 0, x_96);
x_69 = x_97;
x_70 = x_1;
goto lbl_71;
}
else
{
obj* x_98; 
x_98 = l_lean_ir_match__type___closed__5;
lean::inc(x_98);
x_69 = x_98;
x_70 = x_1;
goto lbl_71;
}
}
lbl_65:
{
if (lean::obj_tag(x_63) == 0)
{
obj* x_102; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_0);
lean::dec(x_56);
x_102 = lean::cnstr_get(x_63, 0);
lean::inc(x_102);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_104 = x_63;
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_102);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_64);
return x_106;
}
else
{
obj* x_107; obj* x_108; obj* x_111; obj* x_112; obj* x_114; obj* x_116; 
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_107 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_107 = x_63;
}
x_108 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_0);
lean::inc(x_108);
x_111 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_108, x_0, x_64);
x_112 = lean::cnstr_get(x_111, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_111, 1);
lean::inc(x_114);
if (lean::is_shared(x_111)) {
 lean::dec(x_111);
 x_116 = lean::box(0);
} else {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 x_116 = x_111;
}
if (lean::obj_tag(x_112) == 0)
{
obj* x_119; obj* x_122; obj* x_123; 
lean::dec(x_0);
lean::dec(x_56);
x_119 = lean::cnstr_get(x_112, 0);
lean::inc(x_119);
lean::dec(x_112);
if (lean::is_scalar(x_107)) {
 x_122 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_122 = x_107;
 lean::cnstr_set_tag(x_107, 0);
}
lean::cnstr_set(x_122, 0, x_119);
if (lean::is_scalar(x_116)) {
 x_123 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_123 = x_116;
}
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_114);
return x_123;
}
else
{
obj* x_125; obj* x_128; obj* x_129; obj* x_131; 
lean::dec(x_112);
x_125 = l_lean_ir_cpp_finalize__prefix;
lean::inc(x_0);
lean::inc(x_125);
x_128 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_125, x_0, x_114);
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_128, 1);
lean::inc(x_131);
lean::dec(x_128);
if (lean::obj_tag(x_129) == 0)
{
obj* x_136; obj* x_139; obj* x_140; 
lean::dec(x_0);
lean::dec(x_56);
x_136 = lean::cnstr_get(x_129, 0);
lean::inc(x_136);
lean::dec(x_129);
if (lean::is_scalar(x_107)) {
 x_139 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_139 = x_107;
 lean::cnstr_set_tag(x_107, 0);
}
lean::cnstr_set(x_139, 0, x_136);
if (lean::is_scalar(x_116)) {
 x_140 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_140 = x_116;
}
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_131);
return x_140;
}
else
{
obj* x_143; obj* x_144; obj* x_146; 
lean::dec(x_129);
lean::inc(x_0);
x_143 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_56, x_0, x_131);
x_144 = lean::cnstr_get(x_143, 0);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_143, 1);
lean::inc(x_146);
lean::dec(x_143);
if (lean::obj_tag(x_144) == 0)
{
obj* x_150; obj* x_153; obj* x_154; 
lean::dec(x_0);
x_150 = lean::cnstr_get(x_144, 0);
lean::inc(x_150);
lean::dec(x_144);
if (lean::is_scalar(x_107)) {
 x_153 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_153 = x_107;
 lean::cnstr_set_tag(x_107, 0);
}
lean::cnstr_set(x_153, 0, x_150);
if (lean::is_scalar(x_116)) {
 x_154 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_154 = x_116;
}
lean::cnstr_set(x_154, 0, x_153);
lean::cnstr_set(x_154, 1, x_146);
return x_154;
}
else
{
obj* x_158; obj* x_159; obj* x_161; 
lean::dec(x_144);
lean::inc(x_0);
lean::inc(x_108);
x_158 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_108, x_0, x_146);
x_159 = lean::cnstr_get(x_158, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_158, 1);
lean::inc(x_161);
lean::dec(x_158);
if (lean::obj_tag(x_159) == 0)
{
obj* x_165; obj* x_168; obj* x_169; 
lean::dec(x_0);
x_165 = lean::cnstr_get(x_159, 0);
lean::inc(x_165);
lean::dec(x_159);
if (lean::is_scalar(x_107)) {
 x_168 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_168 = x_107;
 lean::cnstr_set_tag(x_107, 0);
}
lean::cnstr_set(x_168, 0, x_165);
if (lean::is_scalar(x_116)) {
 x_169 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_169 = x_116;
}
lean::cnstr_set(x_169, 0, x_168);
lean::cnstr_set(x_169, 1, x_161);
return x_169;
}
else
{
obj* x_173; obj* x_175; 
lean::dec(x_159);
lean::dec(x_107);
lean::dec(x_116);
x_173 = l_lean_ir_cpp_emit__main__proc___closed__2;
lean::inc(x_173);
x_175 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_173, x_0, x_161);
return x_175;
}
}
}
}
}
}
lbl_68:
{
if (lean::obj_tag(x_66) == 0)
{
obj* x_177; obj* x_179; obj* x_180; 
lean::dec(x_12);
x_177 = lean::cnstr_get(x_66, 0);
lean::inc(x_177);
if (lean::is_shared(x_66)) {
 lean::dec(x_66);
 x_179 = lean::box(0);
} else {
 lean::cnstr_release(x_66, 0);
 x_179 = x_66;
}
if (lean::is_scalar(x_179)) {
 x_180 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_180 = x_179;
}
lean::cnstr_set(x_180, 0, x_177);
x_63 = x_180;
x_64 = x_67;
goto lbl_65;
}
else
{
obj* x_181; obj* x_184; obj* x_185; obj* x_187; 
if (lean::is_shared(x_66)) {
 lean::dec(x_66);
 x_181 = lean::box(0);
} else {
 lean::cnstr_release(x_66, 0);
 x_181 = x_66;
}
lean::inc(x_0);
lean::inc(x_56);
x_184 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_56, x_0, x_67);
x_185 = lean::cnstr_get(x_184, 0);
lean::inc(x_185);
x_187 = lean::cnstr_get(x_184, 1);
lean::inc(x_187);
lean::dec(x_184);
if (lean::obj_tag(x_185) == 0)
{
obj* x_191; obj* x_194; 
lean::dec(x_12);
x_191 = lean::cnstr_get(x_185, 0);
lean::inc(x_191);
lean::dec(x_185);
if (lean::is_scalar(x_181)) {
 x_194 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_194 = x_181;
 lean::cnstr_set_tag(x_181, 0);
}
lean::cnstr_set(x_194, 0, x_191);
x_63 = x_194;
x_64 = x_187;
goto lbl_65;
}
else
{
obj* x_196; obj* x_199; obj* x_200; obj* x_202; 
lean::dec(x_185);
x_196 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_0);
lean::inc(x_196);
x_199 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_196, x_0, x_187);
x_200 = lean::cnstr_get(x_199, 0);
lean::inc(x_200);
x_202 = lean::cnstr_get(x_199, 1);
lean::inc(x_202);
lean::dec(x_199);
if (lean::obj_tag(x_200) == 0)
{
obj* x_206; obj* x_209; 
lean::dec(x_12);
x_206 = lean::cnstr_get(x_200, 0);
lean::inc(x_206);
lean::dec(x_200);
if (lean::is_scalar(x_181)) {
 x_209 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_209 = x_181;
 lean::cnstr_set_tag(x_181, 0);
}
lean::cnstr_set(x_209, 0, x_206);
x_63 = x_209;
x_64 = x_202;
goto lbl_65;
}
else
{
obj* x_211; obj* x_214; obj* x_215; obj* x_217; 
lean::dec(x_200);
x_211 = l_lean_ir_cpp_emit__main__proc___closed__3;
lean::inc(x_0);
lean::inc(x_211);
x_214 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_211, x_0, x_202);
x_215 = lean::cnstr_get(x_214, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_214, 1);
lean::inc(x_217);
lean::dec(x_214);
if (lean::obj_tag(x_215) == 0)
{
obj* x_221; obj* x_224; 
lean::dec(x_12);
x_221 = lean::cnstr_get(x_215, 0);
lean::inc(x_221);
lean::dec(x_215);
if (lean::is_scalar(x_181)) {
 x_224 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_224 = x_181;
 lean::cnstr_set_tag(x_181, 0);
}
lean::cnstr_set(x_224, 0, x_221);
x_63 = x_224;
x_64 = x_217;
goto lbl_65;
}
else
{
obj* x_228; obj* x_229; obj* x_231; 
lean::dec(x_215);
lean::dec(x_181);
lean::inc(x_0);
x_228 = l_lean_ir_cpp_emit__fnid(x_12, x_0, x_217);
x_229 = lean::cnstr_get(x_228, 0);
lean::inc(x_229);
x_231 = lean::cnstr_get(x_228, 1);
lean::inc(x_231);
lean::dec(x_228);
x_63 = x_229;
x_64 = x_231;
goto lbl_65;
}
}
}
}
}
lbl_71:
{
if (lean::obj_tag(x_69) == 0)
{
obj* x_234; obj* x_236; obj* x_237; 
x_234 = lean::cnstr_get(x_69, 0);
lean::inc(x_234);
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_236 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 x_236 = x_69;
}
if (lean::is_scalar(x_236)) {
 x_237 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_237 = x_236;
}
lean::cnstr_set(x_237, 0, x_234);
x_66 = x_237;
x_67 = x_70;
goto lbl_68;
}
else
{
obj* x_238; obj* x_239; obj* x_242; obj* x_243; obj* x_245; 
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_238 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 x_238 = x_69;
}
x_239 = l_lean_ir_cpp_emit__main__proc___closed__4;
lean::inc(x_0);
lean::inc(x_239);
x_242 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_239, x_0, x_70);
x_243 = lean::cnstr_get(x_242, 0);
lean::inc(x_243);
x_245 = lean::cnstr_get(x_242, 1);
lean::inc(x_245);
lean::dec(x_242);
if (lean::obj_tag(x_243) == 0)
{
obj* x_248; obj* x_251; 
x_248 = lean::cnstr_get(x_243, 0);
lean::inc(x_248);
lean::dec(x_243);
if (lean::is_scalar(x_238)) {
 x_251 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_251 = x_238;
 lean::cnstr_set_tag(x_238, 0);
}
lean::cnstr_set(x_251, 0, x_248);
x_66 = x_251;
x_67 = x_245;
goto lbl_68;
}
else
{
obj* x_254; obj* x_257; obj* x_258; obj* x_260; 
lean::dec(x_243);
lean::dec(x_238);
x_254 = l_lean_ir_cpp_initialize__prefix;
lean::inc(x_0);
lean::inc(x_254);
x_257 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_254, x_0, x_245);
x_258 = lean::cnstr_get(x_257, 0);
lean::inc(x_258);
x_260 = lean::cnstr_get(x_257, 1);
lean::inc(x_260);
lean::dec(x_257);
x_66 = x_258;
x_67 = x_260;
goto lbl_68;
}
}
}
}
}
}
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_extract__cpp___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_5 = l_lean_ir_match__type___closed__5;
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
x_14 = l_lean_ir_cpp_emit__def(x_8, x_1, x_2);
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
lean::dec(x_15);
lean::dec(x_19);
x_0 = x_10;
x_2 = x_17;
goto _start;
}
}
}
}
obj* _init_l_lean_ir_extract__cpp___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("static bool _G_initialized = false;\n");
return x_0;
}
}
obj* _init_l_lean_ir_extract__cpp___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("static bool _G_finalized = false;\n");
return x_0;
}
}
obj* l_lean_ir_extract__cpp(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_15; obj* x_16; obj* x_18; 
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
x_4 = l_lean_ir_cpp_file__header(x_2);
x_5 = l_lean_format_be___main___closed__1;
x_6 = lean::string_append(x_4, x_5);
x_7 = l_lean_ir_mk__context;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_7);
lean::inc(x_9);
lean::inc(x_0);
x_15 = l_lean_ir_cpp_emit__used__headers(x_0, x_9, x_6);
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
x_26 = l_lean_ir_extract__cpp___closed__1;
lean::inc(x_9);
lean::inc(x_26);
x_29 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_26, x_9, x_18);
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
 lean::cnstr_set_tag(x_25, 0);
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
x_41 = l_lean_ir_extract__cpp___closed__2;
lean::inc(x_9);
lean::inc(x_41);
x_44 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_41, x_9, x_32);
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
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_11);
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
x_60 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__global__var__decls___spec__1(x_0, x_9, x_11);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_69; obj* x_72; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_63);
x_69 = lean::cnstr_get(x_61, 0);
lean::inc(x_69);
lean::dec(x_61);
if (lean::is_scalar(x_57)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_57;
 lean::cnstr_set_tag(x_57, 0);
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
x_76 = l_lean_ir_cpp_emit__initialize__proc(x_0, x_9, x_63);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
if (lean::obj_tag(x_77) == 0)
{
obj* x_85; obj* x_88; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_79);
x_85 = lean::cnstr_get(x_77, 0);
lean::inc(x_85);
lean::dec(x_77);
if (lean::is_scalar(x_57)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_57;
 lean::cnstr_set_tag(x_57, 0);
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
x_92 = l_lean_ir_cpp_emit__finalize__proc(x_0, x_9, x_79);
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_92, 1);
lean::inc(x_95);
lean::dec(x_92);
if (lean::obj_tag(x_93) == 0)
{
obj* x_101; obj* x_104; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_95);
x_101 = lean::cnstr_get(x_93, 0);
lean::inc(x_101);
lean::dec(x_93);
if (lean::is_scalar(x_57)) {
 x_104 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_104 = x_57;
 lean::cnstr_set_tag(x_57, 0);
}
lean::cnstr_set(x_104, 0, x_101);
return x_104;
}
else
{
obj* x_107; obj* x_108; obj* x_110; 
lean::dec(x_93);
lean::inc(x_9);
x_107 = l_list_mmap_x_27___main___at_lean_ir_extract__cpp___spec__1(x_0, x_9, x_95);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_107, 1);
lean::inc(x_110);
lean::dec(x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_115; obj* x_118; 
lean::dec(x_9);
lean::dec(x_110);
x_115 = lean::cnstr_get(x_108, 0);
lean::inc(x_115);
lean::dec(x_108);
if (lean::is_scalar(x_57)) {
 x_118 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_118 = x_57;
 lean::cnstr_set_tag(x_57, 0);
}
lean::cnstr_set(x_118, 0, x_115);
return x_118;
}
else
{
obj* x_120; obj* x_121; obj* x_123; 
lean::dec(x_108);
x_120 = l_lean_ir_cpp_emit__main__proc(x_9, x_110);
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
 lean::cnstr_set_tag(x_57, 0);
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
void initialize_init_lean_name__mangling();
void initialize_init_lean_config();
void initialize_init_lean_ir_type__check();
static bool _G_initialized = false;
void initialize_init_lean_ir_extract__cpp() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_name__mangling();
 initialize_init_lean_config();
 initialize_init_lean_ir_type__check();
 l_lean_ir_cpp_initialize__prefix = _init_l_lean_ir_cpp_initialize__prefix();
 l_lean_ir_cpp_finalize__prefix = _init_l_lean_ir_cpp_finalize__prefix();
 l_lean_ir_cpp_file__header___closed__1 = _init_l_lean_ir_cpp_file__header___closed__1();
 l_lean_ir_cpp_file__header___closed__2 = _init_l_lean_ir_cpp_file__header___closed__2();
 l_lean_ir_cpp_file__header___closed__3 = _init_l_lean_ir_cpp_file__header___closed__3();
 l_lean_ir_cpp_file__header___closed__4 = _init_l_lean_ir_cpp_file__header___closed__4();
 l_lean_ir_cpp_extract__m_monad__run = _init_l_lean_ir_cpp_extract__m_monad__run();
 l_lean_ir_cpp_extract__m_monad__reader = _init_l_lean_ir_cpp_extract__m_monad__reader();
 l_lean_ir_cpp_extract__m_monad__state = _init_l_lean_ir_cpp_extract__m_monad__state();
 l_lean_ir_cpp_extract__m_monad__except = _init_l_lean_ir_cpp_extract__m_monad__except();
 l_lean_ir_cpp_extract__m_monad = _init_l_lean_ir_cpp_extract__m_monad();
 l_lean_ir_cpp_extract__m = _init_l_lean_ir_cpp_extract__m();
 l_lean_ir_cpp_emit__blockid___closed__1 = _init_l_lean_ir_cpp_emit__blockid___closed__1();
 l_lean_ir_cpp_fid2cpp___closed__1 = _init_l_lean_ir_cpp_fid2cpp___closed__1();
 l_lean_ir_cpp_is__const___closed__1 = _init_l_lean_ir_cpp_is__const___closed__1();
 l_lean_ir_cpp_global2cpp___closed__1 = _init_l_lean_ir_cpp_global2cpp___closed__1();
 l_lean_ir_cpp_type2cpp___main___closed__1 = _init_l_lean_ir_cpp_type2cpp___main___closed__1();
 l_lean_ir_cpp_type2cpp___main___closed__2 = _init_l_lean_ir_cpp_type2cpp___main___closed__2();
 l_lean_ir_cpp_type2cpp___main___closed__3 = _init_l_lean_ir_cpp_type2cpp___main___closed__3();
 l_lean_ir_cpp_type2cpp___main___closed__4 = _init_l_lean_ir_cpp_type2cpp___main___closed__4();
 l_lean_ir_cpp_type2cpp___main___closed__5 = _init_l_lean_ir_cpp_type2cpp___main___closed__5();
 l_lean_ir_cpp_type2cpp___main___closed__6 = _init_l_lean_ir_cpp_type2cpp___main___closed__6();
 l_lean_ir_cpp_type2cpp___main___closed__7 = _init_l_lean_ir_cpp_type2cpp___main___closed__7();
 l_lean_ir_cpp_type2cpp___main___closed__8 = _init_l_lean_ir_cpp_type2cpp___main___closed__8();
 l_lean_ir_cpp_type2cpp___main___closed__9 = _init_l_lean_ir_cpp_type2cpp___main___closed__9();
 l_lean_ir_cpp_type2cpp___main___closed__10 = _init_l_lean_ir_cpp_type2cpp___main___closed__10();
 l_lean_ir_cpp_type2cpp___main___closed__11 = _init_l_lean_ir_cpp_type2cpp___main___closed__11();
 l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1 = _init_l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1();
 l_lean_ir_cpp_emit__template__params___closed__1 = _init_l_lean_ir_cpp_emit__template__params___closed__1();
 l_lean_ir_cpp_emit__template__params___closed__2 = _init_l_lean_ir_cpp_emit__template__params___closed__2();
 l_lean_ir_cpp_emit__template__params___closed__3 = _init_l_lean_ir_cpp_emit__template__params___closed__3();
 l_lean_ir_cpp_emit__template__params___closed__4 = _init_l_lean_ir_cpp_emit__template__params___closed__4();
 l_lean_ir_cpp_emit__eos___closed__1 = _init_l_lean_ir_cpp_emit__eos___closed__1();
 l_lean_ir_cpp_emit__cases___main___closed__1 = _init_l_lean_ir_cpp_emit__cases___main___closed__1();
 l_lean_ir_cpp_emit__cases___main___closed__2 = _init_l_lean_ir_cpp_emit__cases___main___closed__2();
 l_lean_ir_cpp_emit__cases___main___closed__3 = _init_l_lean_ir_cpp_emit__cases___main___closed__3();
 l_lean_ir_cpp_emit__cases___main___closed__4 = _init_l_lean_ir_cpp_emit__cases___main___closed__4();
 l_lean_ir_cpp_emit__case___main___closed__1 = _init_l_lean_ir_cpp_emit__case___main___closed__1();
 l_lean_ir_cpp_emit__case___main___closed__2 = _init_l_lean_ir_cpp_emit__case___main___closed__2();
 l_lean_ir_cpp_emit__case___main___closed__3 = _init_l_lean_ir_cpp_emit__case___main___closed__3();
 l_lean_ir_cpp_emit__case___main___closed__4 = _init_l_lean_ir_cpp_emit__case___main___closed__4();
 l_lean_ir_cpp_emit__case___main___closed__5 = _init_l_lean_ir_cpp_emit__case___main___closed__5();
 l_lean_ir_cpp_emit__case___main___closed__6 = _init_l_lean_ir_cpp_emit__case___main___closed__6();
 l_lean_ir_cpp_emit__case___main___closed__7 = _init_l_lean_ir_cpp_emit__case___main___closed__7();
 l_lean_ir_cpp_emit__case___main___closed__8 = _init_l_lean_ir_cpp_emit__case___main___closed__8();
 l_lean_ir_cpp_emit__case___main___closed__9 = _init_l_lean_ir_cpp_emit__case___main___closed__9();
 l_lean_ir_cpp_emit__terminator___closed__1 = _init_l_lean_ir_cpp_emit__terminator___closed__1();
 l_lean_ir_cpp_emit__type__size___closed__1 = _init_l_lean_ir_cpp_emit__type__size___closed__1();
 l_lean_ir_cpp_emit__infix___closed__1 = _init_l_lean_ir_cpp_emit__infix___closed__1();
 l_lean_ir_cpp_emit__assign__binop___closed__1 = _init_l_lean_ir_cpp_emit__assign__binop___closed__1();
 l_lean_ir_cpp_emit__assign__binop___closed__2 = _init_l_lean_ir_cpp_emit__assign__binop___closed__2();
 l_lean_ir_cpp_emit__assign__binop___closed__3 = _init_l_lean_ir_cpp_emit__assign__binop___closed__3();
 l_lean_ir_cpp_emit__assign__binop___closed__4 = _init_l_lean_ir_cpp_emit__assign__binop___closed__4();
 l_lean_ir_cpp_emit__assign__binop___closed__5 = _init_l_lean_ir_cpp_emit__assign__binop___closed__5();
 l_lean_ir_cpp_emit__assign__binop___closed__6 = _init_l_lean_ir_cpp_emit__assign__binop___closed__6();
 l_lean_ir_cpp_emit__assign__binop___closed__7 = _init_l_lean_ir_cpp_emit__assign__binop___closed__7();
 l_lean_ir_cpp_emit__assign__binop___closed__8 = _init_l_lean_ir_cpp_emit__assign__binop___closed__8();
 l_lean_ir_cpp_emit__assign__binop___closed__9 = _init_l_lean_ir_cpp_emit__assign__binop___closed__9();
 l_lean_ir_cpp_emit__assign__binop___closed__10 = _init_l_lean_ir_cpp_emit__assign__binop___closed__10();
 l_lean_ir_cpp_emit__assign__binop___closed__11 = _init_l_lean_ir_cpp_emit__assign__binop___closed__11();
 l_lean_ir_cpp_emit__assign__binop___closed__12 = _init_l_lean_ir_cpp_emit__assign__binop___closed__12();
 l_lean_ir_cpp_emit__assign__binop___closed__13 = _init_l_lean_ir_cpp_emit__assign__binop___closed__13();
 l_lean_ir_cpp_emit__assign__binop___closed__14 = _init_l_lean_ir_cpp_emit__assign__binop___closed__14();
 l_lean_ir_cpp_emit__assign__binop___closed__15 = _init_l_lean_ir_cpp_emit__assign__binop___closed__15();
 l_lean_ir_cpp_emit__assign__binop___closed__16 = _init_l_lean_ir_cpp_emit__assign__binop___closed__16();
 l_lean_ir_cpp_emit__assign__binop___closed__17 = _init_l_lean_ir_cpp_emit__assign__binop___closed__17();
 l_lean_ir_cpp_emit__assign__binop___closed__18 = _init_l_lean_ir_cpp_emit__assign__binop___closed__18();
 l_lean_ir_cpp_emit__assign__binop___closed__19 = _init_l_lean_ir_cpp_emit__assign__binop___closed__19();
 l_lean_ir_cpp_emit__assign__binop___closed__20 = _init_l_lean_ir_cpp_emit__assign__binop___closed__20();
 l_lean_ir_cpp_emit__assign__binop___closed__21 = _init_l_lean_ir_cpp_emit__assign__binop___closed__21();
 l_lean_ir_cpp_emit__assign__binop___closed__22 = _init_l_lean_ir_cpp_emit__assign__binop___closed__22();
 l_lean_ir_cpp_emit__assign__binop___closed__23 = _init_l_lean_ir_cpp_emit__assign__binop___closed__23();
 l_lean_ir_cpp_emit__assign__binop___closed__24 = _init_l_lean_ir_cpp_emit__assign__binop___closed__24();
 l_lean_ir_cpp_emit__assign__binop___closed__25 = _init_l_lean_ir_cpp_emit__assign__binop___closed__25();
 l_lean_ir_cpp_emit__assign__binop___closed__26 = _init_l_lean_ir_cpp_emit__assign__binop___closed__26();
 l_lean_ir_cpp_emit__assign__binop___closed__27 = _init_l_lean_ir_cpp_emit__assign__binop___closed__27();
 l_lean_ir_cpp_emit__assign__binop___closed__28 = _init_l_lean_ir_cpp_emit__assign__binop___closed__28();
 l_lean_ir_cpp_emit__assign__binop___closed__29 = _init_l_lean_ir_cpp_emit__assign__binop___closed__29();
 l_lean_ir_cpp_emit__assign__binop___closed__30 = _init_l_lean_ir_cpp_emit__assign__binop___closed__30();
 l_lean_ir_cpp_emit__assign__binop___closed__31 = _init_l_lean_ir_cpp_emit__assign__binop___closed__31();
 l_lean_ir_cpp_emit__assign__binop___closed__32 = _init_l_lean_ir_cpp_emit__assign__binop___closed__32();
 l_lean_ir_cpp_emit__assign__binop___closed__33 = _init_l_lean_ir_cpp_emit__assign__binop___closed__33();
 l_lean_ir_cpp_emit__assign__binop___closed__34 = _init_l_lean_ir_cpp_emit__assign__binop___closed__34();
 l_lean_ir_cpp_emit__assign__binop___closed__35 = _init_l_lean_ir_cpp_emit__assign__binop___closed__35();
 l_lean_ir_cpp_emit__assign__binop___closed__36 = _init_l_lean_ir_cpp_emit__assign__binop___closed__36();
 l_lean_ir_cpp_emit__assign__binop___closed__37 = _init_l_lean_ir_cpp_emit__assign__binop___closed__37();
 l_lean_ir_cpp_emit__assign__binop___closed__38 = _init_l_lean_ir_cpp_emit__assign__binop___closed__38();
 l_lean_ir_cpp_emit__assign__binop___closed__39 = _init_l_lean_ir_cpp_emit__assign__binop___closed__39();
 l_lean_ir_cpp_emit__assign__binop___closed__40 = _init_l_lean_ir_cpp_emit__assign__binop___closed__40();
 l_lean_ir_cpp_emit__assign__binop___closed__41 = _init_l_lean_ir_cpp_emit__assign__binop___closed__41();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__1 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__1();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__2 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__2();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__3 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__3();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__4 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__4();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__5 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__5();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__6 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__6();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__7 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__7();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__8 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__8();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__9 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__9();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__10 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__10();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__11 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__11();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__12 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__12();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__13 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__13();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__14 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__14();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__15 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__15();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__16 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__16();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__17 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__17();
 l_lean_ir_cpp_assign__unop2cpp___main___closed__18 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__18();
 l_lean_ir_cpp_emit__num__suffix___main___closed__1 = _init_l_lean_ir_cpp_emit__num__suffix___main___closed__1();
 l_lean_ir_cpp_emit__num__suffix___main___closed__2 = _init_l_lean_ir_cpp_emit__num__suffix___main___closed__2();
 l_lean_ir_cpp_emit__num__suffix___main___closed__3 = _init_l_lean_ir_cpp_emit__num__suffix___main___closed__3();
 l_lean_ir_cpp_emit__assign__lit___closed__1 = _init_l_lean_ir_cpp_emit__assign__lit___closed__1();
 l_lean_ir_cpp_emit__assign__lit___closed__2 = _init_l_lean_ir_cpp_emit__assign__lit___closed__2();
 l_lean_ir_cpp_emit__assign__lit___closed__3 = _init_l_lean_ir_cpp_emit__assign__lit___closed__3();
 l_lean_ir_cpp_emit__assign__lit___closed__4 = _init_l_lean_ir_cpp_emit__assign__lit___closed__4();
 l_lean_ir_cpp_emit__assign__lit___closed__5 = _init_l_lean_ir_cpp_emit__assign__lit___closed__5();
 l_lean_ir_cpp_emit__assign__lit___closed__6 = _init_l_lean_ir_cpp_emit__assign__lit___closed__6();
 l_lean_ir_cpp_emit__assign__lit___closed__7 = _init_l_lean_ir_cpp_emit__assign__lit___closed__7();
 l_lean_ir_cpp_unop2cpp___main___closed__1 = _init_l_lean_ir_cpp_unop2cpp___main___closed__1();
 l_lean_ir_cpp_unop2cpp___main___closed__2 = _init_l_lean_ir_cpp_unop2cpp___main___closed__2();
 l_lean_ir_cpp_unop2cpp___main___closed__3 = _init_l_lean_ir_cpp_unop2cpp___main___closed__3();
 l_lean_ir_cpp_unop2cpp___main___closed__4 = _init_l_lean_ir_cpp_unop2cpp___main___closed__4();
 l_lean_ir_cpp_unop2cpp___main___closed__5 = _init_l_lean_ir_cpp_unop2cpp___main___closed__5();
 l_lean_ir_cpp_unop2cpp___main___closed__6 = _init_l_lean_ir_cpp_unop2cpp___main___closed__6();
 l_lean_ir_cpp_unop2cpp___main___closed__7 = _init_l_lean_ir_cpp_unop2cpp___main___closed__7();
 l_lean_ir_cpp_unop2cpp___main___closed__8 = _init_l_lean_ir_cpp_unop2cpp___main___closed__8();
 l_lean_ir_cpp_unop2cpp___main___closed__9 = _init_l_lean_ir_cpp_unop2cpp___main___closed__9();
 l_lean_ir_cpp_emit__apply___closed__1 = _init_l_lean_ir_cpp_emit__apply___closed__1();
 l_lean_ir_cpp_emit__apply___closed__2 = _init_l_lean_ir_cpp_emit__apply___closed__2();
 l_lean_ir_cpp_emit__apply___closed__3 = _init_l_lean_ir_cpp_emit__apply___closed__3();
 l_lean_ir_cpp_emit__apply___closed__4 = _init_l_lean_ir_cpp_emit__apply___closed__4();
 l_lean_ir_cpp_emit__apply___closed__5 = _init_l_lean_ir_cpp_emit__apply___closed__5();
 l_lean_ir_cpp_emit__apply___closed__6 = _init_l_lean_ir_cpp_emit__apply___closed__6();
 l_lean_ir_cpp_emit__apply___closed__7 = _init_l_lean_ir_cpp_emit__apply___closed__7();
 l_lean_ir_cpp_emit__apply___closed__8 = _init_l_lean_ir_cpp_emit__apply___closed__8();
 l_lean_ir_cpp_emit__apply___closed__9 = _init_l_lean_ir_cpp_emit__apply___closed__9();
 l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___closed__1 = _init_l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___closed__1();
 l_lean_ir_cpp_emit__closure___closed__1 = _init_l_lean_ir_cpp_emit__closure___closed__1();
 l_lean_ir_cpp_emit__closure___closed__2 = _init_l_lean_ir_cpp_emit__closure___closed__2();
 l_lean_ir_cpp_emit__closure___closed__3 = _init_l_lean_ir_cpp_emit__closure___closed__3();
 l_lean_ir_cpp_emit__closure___closed__4 = _init_l_lean_ir_cpp_emit__closure___closed__4();
 l_lean_ir_cpp_emit__instr___closed__1 = _init_l_lean_ir_cpp_emit__instr___closed__1();
 l_lean_ir_cpp_emit__instr___closed__2 = _init_l_lean_ir_cpp_emit__instr___closed__2();
 l_lean_ir_cpp_emit__instr___closed__3 = _init_l_lean_ir_cpp_emit__instr___closed__3();
 l_lean_ir_cpp_emit__instr___closed__4 = _init_l_lean_ir_cpp_emit__instr___closed__4();
 l_lean_ir_cpp_emit__instr___closed__5 = _init_l_lean_ir_cpp_emit__instr___closed__5();
 l_lean_ir_cpp_emit__instr___closed__6 = _init_l_lean_ir_cpp_emit__instr___closed__6();
 l_lean_ir_cpp_emit__instr___closed__7 = _init_l_lean_ir_cpp_emit__instr___closed__7();
 l_lean_ir_cpp_emit__instr___closed__8 = _init_l_lean_ir_cpp_emit__instr___closed__8();
 l_lean_ir_cpp_emit__instr___closed__9 = _init_l_lean_ir_cpp_emit__instr___closed__9();
 l_lean_ir_cpp_emit__block___closed__1 = _init_l_lean_ir_cpp_emit__block___closed__1();
 l_lean_ir_cpp_emit__block___closed__2 = _init_l_lean_ir_cpp_emit__block___closed__2();
 l_lean_ir_cpp_emit__header___closed__1 = _init_l_lean_ir_cpp_emit__header___closed__1();
 l_lean_ir_cpp_emit__uncurry__header___closed__1 = _init_l_lean_ir_cpp_emit__uncurry__header___closed__1();
 l_lean_ir_cpp_emit__uncurry__header___closed__2 = _init_l_lean_ir_cpp_emit__uncurry__header___closed__2();
 l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___closed__1 = _init_l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___closed__1();
 l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1___closed__1 = _init_l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1___closed__1();
 l_lean_ir_cpp_emit__uncurry___closed__1 = _init_l_lean_ir_cpp_emit__uncurry___closed__1();
 l_lean_ir_cpp_emit__uncurry___closed__2 = _init_l_lean_ir_cpp_emit__uncurry___closed__2();
 l_lean_ir_cpp_emit__uncurry___closed__3 = _init_l_lean_ir_cpp_emit__uncurry___closed__3();
 l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1 = _init_l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1();
 l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2 = _init_l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2();
 l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1 = _init_l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1();
 l_lean_ir_cpp_emit__initialize__proc___closed__1 = _init_l_lean_ir_cpp_emit__initialize__proc___closed__1();
 l_lean_ir_cpp_emit__initialize__proc___closed__2 = _init_l_lean_ir_cpp_emit__initialize__proc___closed__2();
 l_lean_ir_cpp_emit__initialize__proc___closed__3 = _init_l_lean_ir_cpp_emit__initialize__proc___closed__3();
 l_lean_ir_cpp_emit__initialize__proc___closed__4 = _init_l_lean_ir_cpp_emit__initialize__proc___closed__4();
 l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__1 = _init_l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__1();
 l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__2 = _init_l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__2();
 l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__3 = _init_l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__3();
 l_lean_ir_cpp_emit__finalize__proc___closed__1 = _init_l_lean_ir_cpp_emit__finalize__proc___closed__1();
 l_lean_ir_cpp_emit__finalize__proc___closed__2 = _init_l_lean_ir_cpp_emit__finalize__proc___closed__2();
 l_lean_ir_cpp_emit__main__proc___closed__1 = _init_l_lean_ir_cpp_emit__main__proc___closed__1();
 l_lean_ir_cpp_emit__main__proc___closed__2 = _init_l_lean_ir_cpp_emit__main__proc___closed__2();
 l_lean_ir_cpp_emit__main__proc___closed__3 = _init_l_lean_ir_cpp_emit__main__proc___closed__3();
 l_lean_ir_cpp_emit__main__proc___closed__4 = _init_l_lean_ir_cpp_emit__main__proc___closed__4();
 l_lean_ir_cpp_emit__main__proc___closed__5 = _init_l_lean_ir_cpp_emit__main__proc___closed__5();
 l_lean_ir_cpp_emit__main__proc___closed__6 = _init_l_lean_ir_cpp_emit__main__proc___closed__6();
 l_lean_ir_cpp_emit__main__proc___closed__7 = _init_l_lean_ir_cpp_emit__main__proc___closed__7();
 l_lean_ir_extract__cpp___closed__1 = _init_l_lean_ir_extract__cpp___closed__1();
 l_lean_ir_extract__cpp___closed__2 = _init_l_lean_ir_extract__cpp___closed__2();
}
