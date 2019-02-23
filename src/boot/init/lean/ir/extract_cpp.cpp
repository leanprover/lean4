// Lean compiler output
// Module: init.lean.ir.extract_cpp
// Imports: init.lean.name_mangling init.lean.config init.lean.ir.type_check
#include "runtime/object.h"
#include "runtime/apply.h"
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
obj* l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1(obj*, obj*);
obj* l_lean_ir_cpp_emit(obj*);
namespace lean {
obj* nat2int(obj*);
}
obj* l_lean_ir_cpp_emit__uncurry__header(obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___boxed(obj*, obj*);
obj* l_lean_ir_cpp_emit__cases___main(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(uint16, obj*, obj*);
obj* l_lean_ir_cpp_emit__arg__list___lambda__1(obj*, obj*, obj*);
extern obj* l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
obj* l_state__t_monad__run___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__num__suffix___main___closed__1;
obj* l_lean_ir_cpp_emit__global__var__decls___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__block(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__7;
obj* l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___closed__1;
extern obj* l_lean_ir_valid__assign__unop__types___closed__4;
obj* l_lean_ir_cpp_emit__infix(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_id___boxed(obj*);
obj* l_lean_ir_cpp_emit__case___main___closed__6;
obj* l_lean_ir_cpp_emit__sep___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__case___main___closed__9;
obj* l_lean_ir_terminator_to__format___main(obj*);
obj* l_lean_ir_cpp_extract__m_monad;
obj* l_lean_ir_cpp_emit__template__param(uint8, obj*, obj*);
obj* l_lean_ir_cpp_emit__arg__list___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
obj* l_lean_ir_cpp_file__header___closed__4;
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__global__var__decls___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__main__proc___closed__4;
extern obj* l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
namespace lean {
obj* uint16_to_nat(uint16);
}
obj* l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__4(obj*, obj*);
obj* l_lean_ir_cpp_emit__infix___closed__1;
obj* l_rbnode_insert___at_lean_ir_cpp_collect__used___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__block___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__14;
obj* l_id_run___boxed(obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__4;
obj* l_lean_ir_cpp_emit__finalize__proc___closed__2;
obj* l_lean_ir_cpp_emit__template__params___closed__2;
obj* l_lean_ir_cpp_emit__assign__binop___closed__38;
obj* l_lean_ir_instr_to__format___main(obj*);
obj* l_lean_ir_cpp_emit__instr___closed__1;
obj* l_lean_ir_cpp_unop2cpp___main___closed__9;
extern obj* l_lean_ir_match__type___closed__5;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_lean_ir_cpp_emit__case___main___closed__7;
obj* l_lean_ir_cpp_emit__sep__aux___boxed(obj*);
obj* l_lean_ir_cpp_emit__eos___closed__1;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__8;
obj* l_lean_ir_cpp_initialize__prefix;
obj* l_lean_ir_cpp_emit__assign__binop___closed__37;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__17;
obj* l_lean_ir_cpp_emit__initialize__proc___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__3;
obj* l_lean_ir_cpp_emit__def__core(obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__6;
obj* l_lean_ir_extract__cpp___closed__1;
obj* l_lean_ir_cpp_emit__apply___closed__1;
obj* l_lean_ir_cpp_assign__unop2cpp___main(uint8, uint8);
uint8 l_list_empty___main___rarg(obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__20;
obj* l_lean_ir_cpp_emit__arith___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__sep__aux___main___boxed(obj*);
obj* l_lean_ir_cpp_emit__assign__lit___closed__4;
obj* l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___closed__1;
obj* l_lean_ir_cpp_emit__case___main(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__main__proc___closed__6;
obj* l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_unop2cpp___boxed(obj*);
obj* l_reader__t_lift___boxed(obj*, obj*, obj*, obj*);
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
obj* l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_fid2cpp___closed__1;
obj* l_lean_ir_cpp_fid2cpp(obj*, obj*, obj*);
obj* l_list_foldr___main___at_lean_ir_cpp_need__uncurry___spec__1___boxed(obj*);
obj* l_lean_ir_cpp_emit__instr___closed__9;
obj* l_lean_ir_cpp_emit__num__suffix___main(uint8, obj*, obj*);
obj* l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___boxed(obj*, obj*, obj*, obj*);
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
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__instr___closed__5;
obj* l_lean_ir_cpp_emit__num__suffix___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__instr___closed__3;
extern obj* l_lean_ir_mk__fnid__set;
obj* l_lean_ir_cpp_emit__template__params(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__cases___main___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__template__param___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__type__size___closed__1;
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1___boxed(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_ir_cpp_emit__main__proc___closed__2;
obj* l_except__t_monad__except___rarg(obj*);
obj* l_lean_ir_cpp_emit__uncurry___closed__1;
obj* l_lean_ir_cpp_paren___boxed(obj*);
obj* l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__18;
obj* l_lean_ir_cpp_emit__sep___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__27;
obj* l_lean_ir_cpp_emit__assign__binop___closed__1;
obj* l_lean_ir_cpp_type2cpp___main___closed__3;
obj* l_lean_ir_cpp_decl__locals(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__case(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__closure___closed__2;
obj* l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(obj*);
obj* l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2___boxed(obj*);
obj* l_lean_ir_cpp_type2cpp___main___closed__7;
obj* l_lean_ir_cpp_file__header___boxed(obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__9;
extern obj* l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_cpp_emit__sep__aux___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__2___boxed(obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___boxed(obj*, obj*, obj*);
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
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__1___boxed(obj*, obj*, obj*);
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
obj* l_lean_ir_cpp_emit__assign__binop___closed__9;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__15;
extern obj* l_list_repr__aux___main___rarg___closed__1;
obj* l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__cases(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__13;
obj* l_lean_ir_cpp_emit__main__proc___closed__7;
obj* l_lean_ir_cpp_emit__cases___main___closed__4;
obj* l_lean_ir_cpp_emit__used__headers(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__initialize__proc___closed__4;
obj* l_lean_ir_cpp_emit__blockid___closed__1;
obj* l_lean_ir_cpp_type2cpp___main(uint8);
obj* l_lean_ir_cpp_emit__uncurry___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__arg__list(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__41;
obj* l_lean_ir_cpp_emit__assign__binop___closed__12;
obj* l_lean_ir_cpp_emit__main__proc(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_ir_cpp_collect__used___spec__1(obj*, obj*, obj*);
extern obj* l_list_repr___main___rarg___closed__3;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_ir_cpp_emit__infix___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_format_be___main___closed__1;
obj* l_lean_ir_cpp_emit__uncurry__header___closed__1;
obj* l_lean_ir_cpp_emit__assign__binop___closed__23;
obj* l_lean_ir_cpp_extract__m_monad__except;
obj* l_lean_ir_cpp_emit__apply___closed__6;
obj* l_lean_ir_cpp_emit__op__x___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__sep(obj*);
obj* l_lean_ir_infer__types(obj*, obj*);
extern obj* l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
obj* l_lean_ir_cpp_emit__closure___closed__3;
obj* l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1___boxed(obj*, obj*);
obj* l_lean_ir_cpp_emit__closure___closed__4;
obj* l_lean_ir_cpp_unop2cpp___main___closed__4;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__10;
obj* l_lean_ir_cpp_emit__sep__aux(obj*);
obj* l_lean_ir_cpp_emit___boxed(obj*);
obj* l_lean_ir_cpp_emit__case___main___closed__8;
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_type2cpp___main___closed__2;
obj* l_lean_ir_cpp_emit__sep___boxed(obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__block___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__fnid(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__line___boxed(obj*, obj*);
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
obj* l_lean_ir_cpp_emit__x__op__y___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_monad__state__trans___rarg(obj*, obj*);
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
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
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__12;
obj* l_lean_ir_cpp_emit__case___main___closed__1;
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_lean_ir_cpp_emit__big__binop___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_extract__m_monad__reader;
obj* l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__28;
obj* l_lean_ir_cpp_emit__assign__binop___closed__10;
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3___boxed(obj*, obj*, obj*);
obj* l_id_monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__2(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__initialize__proc___closed__3;
obj* l_lean_ir_cpp_emit__case___main___closed__5;
obj* l_lean_ir_cpp_paren___rarg(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__header(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__blockid___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__34;
obj* l_lean_ir_cpp_emit__assign__binop___closed__26;
obj* l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1___closed__1;
obj* l_lean_ir_cpp_emit__num__suffix___main___closed__2;
obj* l_state__t_monad___rarg(obj*);
obj* l_lean_ir_cpp_emit__blockid(obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_lean_ir_cpp_decl__locals___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__template__params___closed__4;
obj* l_lean_ir_cpp_emit__cases___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__main__proc___closed__3;
obj* l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__initialize__proc(obj*, obj*, obj*);
obj* l_lean_ir_cpp_type2cpp___main___closed__5;
obj* l_lean_ir_cpp_type2cpp___main___closed__8;
obj* l_lean_ir_cpp_emit__terminator___closed__1;
obj* l___private_init_lean_name__mangling_4__name_mangle__aux___main(obj*, obj*);
obj* l_lean_ir_cpp_file__header___closed__3;
obj* l_lean_ir_cpp_emit__logical__arith___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_extract__m_monad__state;
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___boxed(obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__17;
obj* l_lean_ir_cpp_type2cpp___main___closed__4;
obj* l_lean_ir_cpp_emit__instr___closed__6;
obj* l_lean_ir_cpp_emit__sep__aux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__uncurry__header___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__block___closed__1;
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__template__params___closed__1;
obj* l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__6(obj*, obj*);
obj* l_lean_ir_cpp_unop2cpp___main___closed__2;
obj* l_lean_ir_cpp_unop2cpp___main___closed__5;
extern obj* l_prod_has__repr___rarg___closed__1;
obj* l_lean_ir_cpp_emit__sep__aux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_decl__local___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__eos(obj*, obj*);
obj* l_lean_ir_cpp_emit__instr___closed__8;
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
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__2;
obj* l_lean_ir_cpp_emit__type__size(uint8, obj*, obj*);
obj* l_lean_ir_cpp_decl__locals___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__35;
obj* l_list_length__aux___main___rarg(obj*, obj*);
obj* l_lean_ir_cpp_emit__type(uint8, obj*, obj*);
obj* l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2___rarg(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__16;
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
obj* l_reader__t_monad__run___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__5;
obj* l_lean_ir_cpp_decl__local(obj*, uint8, obj*, obj*);
extern obj* l_int_repr___main___closed__2;
obj* l_lean_ir_cpp_emit__apply___closed__2;
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_ir_cpp_type2cpp___main___boxed(obj*);
obj* l_lean_ir_cpp_collect__used(obj*);
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__var___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__11;
obj* l_list_mmap_x_27___main___at_lean_ir_extract__cpp___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__lit___closed__6;
extern obj* l_lean_ir_valid__assign__unop__types___closed__1;
obj* l_nat_repr(obj*);
obj* l_lean_ir_cpp_emit__main__proc___closed__5;
obj* l_id_bind___boxed(obj*, obj*);
obj* l_lean_ir_cpp_global2cpp(obj*, obj*, obj*);
obj* l_lean_ir_cpp_unop2cpp___main___closed__3;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__14;
obj* l_lean_ir_cpp_emit__assign__lit___closed__7;
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__global__var__decls___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__lit(obj*, uint8, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__eos___boxed(obj*, obj*);
obj* l_lean_ir_cpp_emit__op__x(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_file__header___closed__2;
obj* l_lean_ir_cpp_emit__closure___closed__1;
obj* l_lean_ir_cpp_assign__unop2cpp___main___boxed(obj*, obj*);
obj* l_lean_ir_cpp_need__uncurry___boxed(obj*);
obj* l_lean_ir_cpp_emit__num__suffix___main___boxed(obj*, obj*, obj*);
extern obj* l_lean_ir_mk__context;
namespace lean {
obj* nat_sub(obj*, obj*);
}
extern obj* l_option_has__repr___rarg___closed__3;
obj* l_lean_ir_cpp_emit__assign__binop___closed__39;
obj* l_lean_ir_cpp_emit__big__binop(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2;
uint8 l_rbnode_is__red___main___rarg(obj*);
obj* l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__x__op__y(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__19;
obj* l_lean_ir_cpp_emit__assign__binop___closed__30;
obj* l_lean_ir_cpp_type2cpp___main___closed__1;
obj* l_lean_ir_cpp_assign__unop2cpp___main___closed__3;
obj* l_lean_ir_cpp_emit__assign__binop___closed__36;
obj* l_except__t_lift___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_ir_cpp_unop2cpp(uint8);
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__num__suffix___main___closed__3;
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1(obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__lit___closed__1;
obj* l_lean_ir_cpp_emit__finalize__proc___boxed(obj*, obj*, obj*);
obj* l_id_monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_file__header(obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__2;
obj* l_except__t_monad__run___rarg___boxed(obj*, obj*, obj*);
obj* l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
obj* l_lean_ir_cpp_emit__instr___closed__4;
namespace lean {
obj* usize_to_nat(usize);
}
obj* l_lean_ir_cpp_emit__apply___closed__3;
namespace lean {
uint8 int_dec_lt(obj*, obj*);
}
obj* l_lean_ir_cpp_emit__assign__binop___closed__32;
obj* l_id_monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_emit__assign__binop___closed__22;
extern obj* l_lean_closure__max__args;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_lean_ir_cpp_emit__assign__binop___closed__6;
extern obj* l_lean_ir_is__arith__ty___closed__1;
obj* l_rbnode_set__black___main___rarg(obj*);
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
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = l_lean_ir_cpp_file__header___closed__1;
x_2 = lean::string_append(x_1, x_0);
x_3 = l_lean_ir_cpp_file__header___closed__2;
x_4 = lean::string_append(x_2, x_3);
x_5 = lean::string_append(x_4, x_1);
x_6 = lean::string_append(x_5, x_0);
x_7 = l_lean_ir_cpp_file__header___closed__3;
x_8 = lean::string_append(x_6, x_7);
x_9 = l_lean_ir_cpp_file__header___closed__4;
x_10 = lean::string_append(x_8, x_9);
return x_10;
}
}
obj* l_lean_ir_cpp_file__header___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_cpp_file__header(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_ir_cpp_extract__m_monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_state__t_monad___rarg(x_9);
x_11 = l_except__t_monad___rarg(x_10);
x_12 = l_reader__t_monad___rarg(x_11);
return x_12;
}
}
obj* _init_l_lean_ir_cpp_extract__m_monad__except() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_state__t_monad___rarg(x_9);
x_11 = l_except__t_monad__except___rarg(x_10);
x_12 = l_reader__t_monad__except___rarg(x_11);
return x_12;
}
}
obj* _init_l_lean_ir_cpp_extract__m_monad__state() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
x_11 = l_state__t_monad___rarg(x_9);
lean::inc(x_11);
x_13 = l_except__t_monad___rarg(x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_14, 0, lean::box(0));
lean::closure_set(x_14, 1, lean::box(0));
lean::closure_set(x_14, 2, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_lift___rarg___boxed), 3, 1);
lean::closure_set(x_15, 0, x_11);
x_16 = l_state__t_monad__state___rarg(x_9);
x_17 = l_monad__state__trans___rarg(x_15, x_16);
x_18 = l_monad__state__trans___rarg(x_14, x_17);
return x_18;
}
}
obj* _init_l_lean_ir_cpp_extract__m_monad__reader() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
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
obj* _init_l_lean_ir_cpp_extract__m_monad__run() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_id_run___boxed), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__run___rarg___boxed), 5, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_except__t_monad__run___rarg___boxed), 3, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad__run___rarg___boxed), 4, 1);
lean::closure_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init_l_lean_ir_cpp_extract__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_lean_ir_cpp_emit___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_4 = lean::apply_1(x_0, x_1);
x_5 = lean::string_append(x_3, x_4);
lean::dec(x_4);
x_7 = l_lean_ir_match__type___closed__5;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
}
obj* l_lean_ir_cpp_emit(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_lean_ir_cpp_emit___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_cpp_emit___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_ir_cpp_emit___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_cpp_emit(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::string_append(x_2, x_0);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* l_lean_ir_cpp_emit__line(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_lean_format_be___main___closed__1;
x_3 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_2, x_0, x_1);
return x_3;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_cpp_emit__line___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_cpp_emit__line(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_ir_cpp_paren___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_prod_has__repr___rarg___closed__1;
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_14 = x_5;
} else {
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_12);
if (lean::is_scalar(x_11)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_11;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_9);
return x_16;
}
else
{
obj* x_18; obj* x_22; obj* x_23; 
lean::dec(x_5);
x_18 = lean::cnstr_get(x_4, 1);
lean::inc(x_18);
lean::dec(x_4);
lean::inc(x_1);
x_22 = lean::apply_2(x_0, x_1, x_18);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_26 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_28 = x_22;
} else {
 lean::inc(x_26);
 lean::dec(x_22);
 x_28 = lean::box(0);
}
x_29 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_31 = x_23;
} else {
 lean::inc(x_29);
 lean::dec(x_23);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_28)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_28;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_26);
return x_33;
}
else
{
obj* x_34; obj* x_37; obj* x_40; obj* x_41; obj* x_43; 
x_34 = lean::cnstr_get(x_22, 1);
lean::inc(x_34);
lean::dec(x_22);
x_37 = lean::cnstr_get(x_23, 0);
lean::inc(x_37);
lean::dec(x_23);
x_40 = l_option_has__repr___rarg___closed__3;
x_41 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_40, x_1, x_34);
lean::dec(x_1);
x_43 = lean::cnstr_get(x_41, 0);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; obj* x_48; obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_37);
x_46 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_48 = x_41;
} else {
 lean::inc(x_46);
 lean::dec(x_41);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_51 = x_43;
} else {
 lean::inc(x_49);
 lean::dec(x_43);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
if (lean::is_scalar(x_48)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_48;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_46);
return x_53;
}
else
{
obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_54 = x_43;
} else {
 lean::dec(x_43);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_57 = x_41;
} else {
 lean::inc(x_55);
 lean::dec(x_41);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_58 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_58 = x_54;
}
lean::cnstr_set(x_58, 0, x_37);
if (lean::is_scalar(x_57)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_57;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_55);
return x_59;
}
}
}
}
}
obj* l_lean_ir_cpp_paren(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_paren___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_ir_cpp_paren___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_cpp_paren(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_cpp_comma(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = lean::apply_2(x_0, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_12 = x_5;
} else {
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_15 = x_6;
} else {
 lean::inc(x_13);
 lean::dec(x_6);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
if (lean::is_scalar(x_12)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_12;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_6);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_list_repr__aux___main___rarg___closed__1;
x_23 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_2, x_19);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
lean::dec(x_2);
x_28 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_30 = x_23;
} else {
 lean::inc(x_28);
 lean::dec(x_23);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_33 = x_24;
} else {
 lean::inc(x_31);
 lean::dec(x_24);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_31);
if (lean::is_scalar(x_30)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_30;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_28);
return x_35;
}
else
{
obj* x_37; obj* x_40; 
lean::dec(x_24);
x_37 = lean::cnstr_get(x_23, 1);
lean::inc(x_37);
lean::dec(x_23);
x_40 = lean::apply_2(x_1, x_2, x_37);
return x_40;
}
}
}
}
obj* l_lean_ir_cpp_emit__var(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
x_4 = l___private_init_lean_name__mangling_4__name_mangle__aux___main(x_3, x_0);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_4, x_1, x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_ir_cpp_emit__var___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_emit__var(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_ir_cpp_emit__blockid___closed__1;
x_4 = l___private_init_lean_name__mangling_4__name_mangle__aux___main(x_3, x_0);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_4, x_1, x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_ir_cpp_emit__blockid___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_emit__blockid(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = l_lean_ir_cpp_fid2cpp___closed__1;
x_12 = l___private_init_lean_name__mangling_4__name_mangle__aux___main(x_11, x_0);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_2);
return x_14;
}
else
{
obj* x_16; obj* x_19; obj* x_20; 
lean::dec(x_0);
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_16);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
return x_20;
}
}
}
obj* l_lean_ir_cpp_emit__fnid(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_1);
x_4 = l_lean_ir_cpp_fid2cpp(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
} else {
 lean::inc(x_8);
 lean::dec(x_4);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_13 = x_5;
} else {
 lean::inc(x_11);
 lean::dec(x_5);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
if (lean::is_scalar(x_10)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_10;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_8);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_22; 
x_16 = lean::cnstr_get(x_4, 1);
lean::inc(x_16);
lean::dec(x_4);
x_19 = lean::cnstr_get(x_5, 0);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_1, x_16);
lean::dec(x_1);
lean::dec(x_19);
return x_22;
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
obj* x_10; obj* x_11; 
x_10 = l_lean_ir_cpp_is__const___closed__1;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_15; uint8 x_17; obj* x_19; obj* x_20; obj* x_21; 
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_lean_ir_decl_header___main(x_12);
lean::dec(x_12);
x_17 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*3);
lean::dec(x_15);
x_19 = lean::box(x_17);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_2);
return x_21;
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
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_cpp_fid2cpp(x_0, x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_8 = x_3;
} else {
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
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
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; 
x_14 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_16 = x_3;
} else {
 lean::inc(x_14);
 lean::dec(x_3);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_19 = x_4;
} else {
 lean::inc(x_17);
 lean::dec(x_4);
 x_19 = lean::box(0);
}
x_20 = l_lean_ir_cpp_global2cpp___closed__1;
x_21 = lean::string_append(x_20, x_17);
lean::dec(x_17);
if (lean::is_scalar(x_19)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_19;
}
lean::cnstr_set(x_23, 0, x_21);
if (lean::is_scalar(x_16)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_16;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_14);
return x_24;
}
}
}
obj* l_lean_ir_cpp_emit__global(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_1);
x_4 = l_lean_ir_cpp_global2cpp(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
} else {
 lean::inc(x_8);
 lean::dec(x_4);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_13 = x_5;
} else {
 lean::inc(x_11);
 lean::dec(x_5);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
if (lean::is_scalar(x_10)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_10;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_8);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_22; 
x_16 = lean::cnstr_get(x_4, 1);
lean::inc(x_16);
lean::dec(x_4);
x_19 = lean::cnstr_get(x_5, 0);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_1, x_16);
lean::dec(x_1);
lean::dec(x_19);
return x_22;
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
case 2:
{
obj* x_1; 
x_1 = l_lean_ir_cpp_type2cpp___main___closed__2;
return x_1;
}
case 3:
{
obj* x_2; 
x_2 = l_lean_ir_cpp_type2cpp___main___closed__3;
return x_2;
}
case 4:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_type2cpp___main___closed__4;
return x_3;
}
case 5:
{
obj* x_4; 
x_4 = l_lean_ir_cpp_type2cpp___main___closed__5;
return x_4;
}
case 6:
{
obj* x_5; 
x_5 = l_lean_ir_cpp_type2cpp___main___closed__6;
return x_5;
}
case 7:
{
obj* x_6; 
x_6 = l_lean_ir_cpp_type2cpp___main___closed__7;
return x_6;
}
case 8:
{
obj* x_7; 
x_7 = l_lean_ir_cpp_type2cpp___main___closed__8;
return x_7;
}
case 9:
{
obj* x_8; 
x_8 = l_lean_ir_cpp_type2cpp___main___closed__9;
return x_8;
}
case 10:
{
obj* x_9; 
x_9 = l_lean_ir_cpp_type2cpp___main___closed__10;
return x_9;
}
case 11:
{
obj* x_10; 
x_10 = l_lean_ir_cpp_type2cpp___main___closed__11;
return x_10;
}
default:
{
obj* x_11; 
x_11 = l_lean_ir_cpp_type2cpp___main___closed__1;
return x_11;
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
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_ir_cpp_emit__type___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_ir_cpp_emit__type(x_3, x_1, x_2);
lean::dec(x_1);
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
obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = l_lean_ir_match__type___closed__5;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; 
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_14; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
lean::dec(x_2);
x_14 = lean::apply_3(x_0, x_11, x_3, x_4);
return x_14;
}
else
{
obj* x_15; obj* x_20; obj* x_21; 
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
lean::dec(x_2);
lean::inc(x_3);
lean::inc(x_0);
x_20 = lean::apply_3(x_0, x_15, x_3, x_4);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
x_26 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 x_28 = x_20;
} else {
 lean::inc(x_26);
 lean::dec(x_20);
 x_28 = lean::box(0);
}
x_29 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_31 = x_21;
} else {
 lean::inc(x_29);
 lean::dec(x_21);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_28)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_28;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_26);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_39; 
lean::dec(x_21);
x_35 = lean::cnstr_get(x_20, 1);
lean::inc(x_35);
lean::dec(x_20);
x_38 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1, x_3, x_35);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
if (lean::obj_tag(x_39) == 0)
{
obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
x_44 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_46 = x_38;
} else {
 lean::inc(x_44);
 lean::dec(x_38);
 x_46 = lean::box(0);
}
x_47 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_49 = x_39;
} else {
 lean::inc(x_47);
 lean::dec(x_39);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_47);
if (lean::is_scalar(x_46)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_46;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_44);
return x_51;
}
else
{
obj* x_53; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_39);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
x_57 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_56, x_3, x_53);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
if (lean::obj_tag(x_58) == 0)
{
obj* x_63; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
x_63 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 x_65 = x_57;
} else {
 lean::inc(x_63);
 lean::dec(x_57);
 x_65 = lean::box(0);
}
x_66 = lean::cnstr_get(x_58, 0);
if (lean::is_exclusive(x_58)) {
 x_68 = x_58;
} else {
 lean::inc(x_66);
 lean::dec(x_58);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_66);
if (lean::is_scalar(x_65)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_65;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_63);
return x_70;
}
else
{
obj* x_72; 
lean::dec(x_58);
x_72 = lean::cnstr_get(x_57, 1);
lean::inc(x_72);
lean::dec(x_57);
x_2 = x_9;
x_4 = x_72;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__sep__aux___main___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_lean_ir_cpp_emit__sep__aux___main___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_ir_cpp_emit__sep__aux___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_cpp_emit__sep__aux___main(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__sep__aux___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_lean_ir_cpp_emit__sep__aux___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_ir_cpp_emit__sep__aux___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_ir_cpp_emit__sep__aux___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_cpp_emit__sep__aux(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__sep___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_lean_ir_cpp_emit__sep___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_ir_cpp_emit__sep___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_lean_ir_cpp_emit__sep___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_cpp_emit__sep(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_cpp_emit__var__list(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__var___boxed), 3, 0);
x_4 = lean::mk_string(",");
x_5 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_3, x_4, x_0, x_1, x_2);
lean::dec(x_4);
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
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_ir_cpp_emit__template__params___closed__1;
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_14 = x_5;
} else {
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_12);
if (lean::is_scalar(x_11)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_11;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_9);
return x_16;
}
else
{
obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_5);
x_18 = lean::cnstr_get(x_4, 1);
lean::inc(x_18);
lean::dec(x_4);
x_21 = l_lean_ir_cpp_emit__template__params___closed__2;
x_22 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_1);
x_24 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_21, x_22, x_0, x_1, x_18);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
x_28 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_30 = x_24;
} else {
 lean::inc(x_28);
 lean::dec(x_24);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_33 = x_25;
} else {
 lean::inc(x_31);
 lean::dec(x_25);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_31);
if (lean::is_scalar(x_30)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_30;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_28);
return x_35;
}
else
{
obj* x_37; obj* x_40; obj* x_41; 
lean::dec(x_25);
x_37 = lean::cnstr_get(x_24, 1);
lean::inc(x_37);
lean::dec(x_24);
x_40 = l_lean_ir_cpp_emit__template__params___closed__4;
x_41 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_40, x_1, x_37);
lean::dec(x_1);
return x_41;
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
obj* l_lean_ir_cpp_emit__arg__list___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
x_4 = l_lean_ir_cpp_emit__type(x_3, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_0);
x_8 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
} else {
 lean::inc(x_8);
 lean::dec(x_4);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_13 = x_5;
} else {
 lean::inc(x_11);
 lean::dec(x_5);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
if (lean::is_scalar(x_10)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_10;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_8);
return x_15;
}
else
{
obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_5);
x_17 = lean::cnstr_get(x_4, 1);
lean::inc(x_17);
lean::dec(x_4);
x_20 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_20, x_1, x_17);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_0);
x_25 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_27 = x_21;
} else {
 lean::inc(x_25);
 lean::dec(x_21);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_30 = x_22;
} else {
 lean::inc(x_28);
 lean::dec(x_22);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
if (lean::is_scalar(x_27)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_27;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_25);
return x_32;
}
else
{
obj* x_34; obj* x_37; obj* x_40; 
lean::dec(x_22);
x_34 = lean::cnstr_get(x_21, 1);
lean::inc(x_34);
lean::dec(x_21);
x_37 = lean::cnstr_get(x_0, 0);
lean::inc(x_37);
lean::dec(x_0);
x_40 = l_lean_ir_cpp_emit__var(x_37, x_1, x_34);
return x_40;
}
}
}
}
obj* l_lean_ir_cpp_emit__arg__list(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__arg__list___lambda__1___boxed), 3, 0);
x_4 = lean::mk_string(",");
x_5 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_3, x_4, x_0, x_1, x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_ir_cpp_emit__arg__list___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_emit__arg__list___lambda__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
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
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_lean_ir_cpp_emit__eos___closed__1;
x_3 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_2, x_0, x_1);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_8 = x_3;
} else {
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
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
obj* x_15; obj* x_18; obj* x_19; 
lean::dec(x_4);
x_15 = lean::cnstr_get(x_3, 1);
lean::inc(x_15);
lean::dec(x_3);
x_18 = l_lean_format_be___main___closed__1;
x_19 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_18, x_0, x_15);
return x_19;
}
}
}
obj* l_lean_ir_cpp_emit__eos___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_ir_cpp_emit__eos(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_3 = l_nat_repr(x_0);
x_4 = lean::string_append(x_2, x_3);
lean::dec(x_3);
x_6 = l_lean_ir_match__type___closed__5;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
return x_7;
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
obj* x_5; obj* x_6; 
lean::dec(x_1);
x_5 = l_lean_ir_cpp_emit__cases___main___closed__1;
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = l_lean_ir_cpp_emit__cases___main___closed__2;
x_14 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_13, x_2, x_3);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_10);
x_18 = lean::cnstr_get(x_14, 1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_20 = x_14;
} else {
 lean::inc(x_18);
 lean::dec(x_14);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_23 = x_15;
} else {
 lean::inc(x_21);
 lean::dec(x_15);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_20)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_20;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_18);
return x_25;
}
else
{
obj* x_27; obj* x_30; obj* x_31; 
lean::dec(x_15);
x_27 = lean::cnstr_get(x_14, 1);
lean::inc(x_27);
lean::dec(x_14);
x_30 = l_lean_ir_cpp_emit__blockid(x_10, x_2, x_27);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; 
x_33 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_35 = x_30;
} else {
 lean::inc(x_33);
 lean::dec(x_30);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_31, 0);
if (lean::is_exclusive(x_31)) {
 x_38 = x_31;
} else {
 lean::inc(x_36);
 lean::dec(x_31);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
if (lean::is_scalar(x_35)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_35;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_33);
return x_40;
}
else
{
obj* x_42; obj* x_45; 
lean::dec(x_31);
x_42 = lean::cnstr_get(x_30, 1);
lean::inc(x_42);
lean::dec(x_30);
x_45 = l_lean_ir_cpp_emit__eos(x_2, x_42);
return x_45;
}
}
}
else
{
obj* x_46; obj* x_49; obj* x_50; obj* x_51; 
x_46 = lean::cnstr_get(x_0, 0);
lean::inc(x_46);
lean::dec(x_0);
x_49 = l_lean_ir_cpp_emit__cases___main___closed__3;
x_50 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_49, x_2, x_3);
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
if (lean::obj_tag(x_51) == 0)
{
obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_46);
x_56 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_58 = x_50;
} else {
 lean::inc(x_56);
 lean::dec(x_50);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_61 = x_51;
} else {
 lean::inc(x_59);
 lean::dec(x_51);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_59);
if (lean::is_scalar(x_58)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_58;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_56);
return x_63;
}
else
{
obj* x_65; obj* x_69; obj* x_70; 
lean::dec(x_51);
x_65 = lean::cnstr_get(x_50, 1);
lean::inc(x_65);
lean::dec(x_50);
lean::inc(x_1);
x_69 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_1, x_2, x_65);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_7);
lean::dec(x_1);
lean::dec(x_46);
x_75 = lean::cnstr_get(x_69, 1);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 x_77 = x_69;
} else {
 lean::inc(x_75);
 lean::dec(x_69);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_70, 0);
if (lean::is_exclusive(x_70)) {
 x_80 = x_70;
} else {
 lean::inc(x_78);
 lean::dec(x_70);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
if (lean::is_scalar(x_77)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_77;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_75);
return x_82;
}
else
{
obj* x_84; obj* x_87; obj* x_88; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_70);
x_84 = lean::cnstr_get(x_69, 1);
lean::inc(x_84);
lean::dec(x_69);
x_87 = lean::mk_nat_obj(1u);
x_88 = lean::nat_add(x_1, x_87);
lean::dec(x_1);
x_90 = l_lean_ir_cpp_emit__cases___main___closed__4;
x_91 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_90, x_2, x_84);
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
if (lean::obj_tag(x_92) == 0)
{
obj* x_97; obj* x_99; obj* x_100; obj* x_102; obj* x_103; obj* x_104; 
lean::dec(x_7);
lean::dec(x_46);
lean::dec(x_88);
x_97 = lean::cnstr_get(x_91, 1);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 x_99 = x_91;
} else {
 lean::inc(x_97);
 lean::dec(x_91);
 x_99 = lean::box(0);
}
x_100 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_102 = x_92;
} else {
 lean::inc(x_100);
 lean::dec(x_92);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_100);
if (lean::is_scalar(x_99)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_99;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_97);
return x_104;
}
else
{
obj* x_106; obj* x_109; obj* x_110; 
lean::dec(x_92);
x_106 = lean::cnstr_get(x_91, 1);
lean::inc(x_106);
lean::dec(x_91);
x_109 = l_lean_ir_cpp_emit__blockid(x_46, x_2, x_106);
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
if (lean::obj_tag(x_110) == 0)
{
obj* x_114; obj* x_116; obj* x_117; obj* x_119; obj* x_120; obj* x_121; 
lean::dec(x_7);
lean::dec(x_88);
x_114 = lean::cnstr_get(x_109, 1);
if (lean::is_exclusive(x_109)) {
 lean::cnstr_release(x_109, 0);
 x_116 = x_109;
} else {
 lean::inc(x_114);
 lean::dec(x_109);
 x_116 = lean::box(0);
}
x_117 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
 x_119 = x_110;
} else {
 lean::inc(x_117);
 lean::dec(x_110);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_117);
if (lean::is_scalar(x_116)) {
 x_121 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_121 = x_116;
}
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_114);
return x_121;
}
else
{
obj* x_123; obj* x_126; obj* x_127; 
lean::dec(x_110);
x_123 = lean::cnstr_get(x_109, 1);
lean::inc(x_123);
lean::dec(x_109);
x_126 = l_lean_ir_cpp_emit__eos(x_2, x_123);
x_127 = lean::cnstr_get(x_126, 0);
lean::inc(x_127);
if (lean::obj_tag(x_127) == 0)
{
obj* x_131; obj* x_133; obj* x_134; obj* x_136; obj* x_137; obj* x_138; 
lean::dec(x_7);
lean::dec(x_88);
x_131 = lean::cnstr_get(x_126, 1);
if (lean::is_exclusive(x_126)) {
 lean::cnstr_release(x_126, 0);
 x_133 = x_126;
} else {
 lean::inc(x_131);
 lean::dec(x_126);
 x_133 = lean::box(0);
}
x_134 = lean::cnstr_get(x_127, 0);
if (lean::is_exclusive(x_127)) {
 x_136 = x_127;
} else {
 lean::inc(x_134);
 lean::dec(x_127);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_134);
if (lean::is_scalar(x_133)) {
 x_138 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_138 = x_133;
}
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_131);
return x_138;
}
else
{
obj* x_140; 
lean::dec(x_127);
x_140 = lean::cnstr_get(x_126, 1);
lean::inc(x_140);
lean::dec(x_126);
x_0 = x_7;
x_1 = x_88;
x_3 = x_140;
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
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_cpp_emit__cases___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_cpp_emit__cases___main(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
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
obj* l_lean_ir_cpp_emit__cases___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_cpp_emit__cases(x_0, x_1, x_2, x_3);
lean::dec(x_2);
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
obj* x_10; 
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_0);
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_16 = l_lean_ir_cpp_emit__case___main___closed__4;
x_17 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_16, x_2, x_3);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_13);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_24 = x_17;
} else {
 lean::inc(x_22);
 lean::dec(x_17);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_27 = x_18;
} else {
 lean::inc(x_25);
 lean::dec(x_18);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
if (lean::is_scalar(x_24)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_24;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_22);
return x_29;
}
else
{
obj* x_31; obj* x_34; obj* x_35; 
lean::dec(x_18);
x_31 = lean::cnstr_get(x_17, 1);
lean::inc(x_31);
lean::dec(x_17);
x_34 = l_lean_ir_cpp_emit__blockid(x_13, x_2, x_31);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
if (lean::obj_tag(x_35) == 0)
{
obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_2);
x_38 = lean::cnstr_get(x_34, 1);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 x_40 = x_34;
} else {
 lean::inc(x_38);
 lean::dec(x_34);
 x_40 = lean::box(0);
}
x_41 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 x_43 = x_35;
} else {
 lean::inc(x_41);
 lean::dec(x_35);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_41);
if (lean::is_scalar(x_40)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_40;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_38);
return x_45;
}
else
{
obj* x_47; obj* x_50; 
lean::dec(x_35);
x_47 = lean::cnstr_get(x_34, 1);
lean::inc(x_47);
lean::dec(x_34);
x_50 = l_lean_ir_cpp_emit__eos(x_2, x_47);
lean::dec(x_2);
return x_50;
}
}
}
else
{
obj* x_52; 
x_52 = lean::cnstr_get(x_10, 1);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_54; obj* x_57; obj* x_60; obj* x_61; obj* x_63; obj* x_65; 
x_54 = lean::cnstr_get(x_1, 0);
lean::inc(x_54);
lean::dec(x_1);
x_57 = lean::cnstr_get(x_10, 0);
lean::inc(x_57);
lean::dec(x_10);
x_63 = lean::cnstr_get(x_2, 1);
lean::inc(x_63);
x_65 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_63, x_0);
if (lean::obj_tag(x_65) == 0)
{
obj* x_69; 
lean::dec(x_0);
lean::dec(x_54);
lean::dec(x_57);
x_69 = l_lean_ir_cpp_emit__case___main___closed__5;
x_60 = x_69;
x_61 = x_3;
goto lbl_62;
}
else
{
obj* x_70; uint8 x_73; 
x_70 = lean::cnstr_get(x_65, 0);
lean::inc(x_70);
lean::dec(x_65);
x_73 = lean::unbox(x_70);
switch (x_73) {
case 0:
{
obj* x_74; obj* x_75; obj* x_76; 
x_74 = l_lean_ir_cpp_emit__case___main___closed__6;
x_75 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_74, x_2, x_3);
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
if (lean::obj_tag(x_76) == 0)
{
obj* x_81; obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_0);
lean::dec(x_54);
lean::dec(x_57);
x_81 = lean::cnstr_get(x_75, 1);
lean::inc(x_81);
lean::dec(x_75);
x_84 = lean::cnstr_get(x_76, 0);
if (lean::is_exclusive(x_76)) {
 x_86 = x_76;
} else {
 lean::inc(x_84);
 lean::dec(x_76);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_84);
x_60 = x_87;
x_61 = x_81;
goto lbl_62;
}
else
{
obj* x_89; obj* x_92; obj* x_93; 
lean::dec(x_76);
x_89 = lean::cnstr_get(x_75, 1);
lean::inc(x_89);
lean::dec(x_75);
x_92 = l_lean_ir_cpp_emit__var(x_0, x_2, x_89);
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
if (lean::obj_tag(x_93) == 0)
{
obj* x_97; obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_54);
lean::dec(x_57);
x_97 = lean::cnstr_get(x_92, 1);
lean::inc(x_97);
lean::dec(x_92);
x_100 = lean::cnstr_get(x_93, 0);
if (lean::is_exclusive(x_93)) {
 x_102 = x_93;
} else {
 lean::inc(x_100);
 lean::dec(x_93);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_100);
x_60 = x_103;
x_61 = x_97;
goto lbl_62;
}
else
{
obj* x_105; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_93);
x_105 = lean::cnstr_get(x_92, 1);
lean::inc(x_105);
lean::dec(x_92);
x_108 = l_lean_ir_cpp_emit__case___main___closed__7;
x_109 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_108, x_2, x_105);
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
if (lean::obj_tag(x_110) == 0)
{
obj* x_114; obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_54);
lean::dec(x_57);
x_114 = lean::cnstr_get(x_109, 1);
lean::inc(x_114);
lean::dec(x_109);
x_117 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
 x_119 = x_110;
} else {
 lean::inc(x_117);
 lean::dec(x_110);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_117);
x_60 = x_120;
x_61 = x_114;
goto lbl_62;
}
else
{
obj* x_122; obj* x_125; obj* x_126; 
lean::dec(x_110);
x_122 = lean::cnstr_get(x_109, 1);
lean::inc(x_122);
lean::dec(x_109);
x_125 = l_lean_ir_cpp_emit__blockid(x_57, x_2, x_122);
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
if (lean::obj_tag(x_126) == 0)
{
obj* x_129; obj* x_132; obj* x_134; obj* x_135; 
lean::dec(x_54);
x_129 = lean::cnstr_get(x_125, 1);
lean::inc(x_129);
lean::dec(x_125);
x_132 = lean::cnstr_get(x_126, 0);
if (lean::is_exclusive(x_126)) {
 x_134 = x_126;
} else {
 lean::inc(x_132);
 lean::dec(x_126);
 x_134 = lean::box(0);
}
if (lean::is_scalar(x_134)) {
 x_135 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_135 = x_134;
}
lean::cnstr_set(x_135, 0, x_132);
x_60 = x_135;
x_61 = x_129;
goto lbl_62;
}
else
{
obj* x_137; obj* x_140; obj* x_141; obj* x_142; 
lean::dec(x_126);
x_137 = lean::cnstr_get(x_125, 1);
lean::inc(x_137);
lean::dec(x_125);
x_140 = l_lean_ir_cpp_emit__case___main___closed__8;
x_141 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_140, x_2, x_137);
x_142 = lean::cnstr_get(x_141, 0);
lean::inc(x_142);
if (lean::obj_tag(x_142) == 0)
{
obj* x_145; obj* x_148; obj* x_150; obj* x_151; 
lean::dec(x_54);
x_145 = lean::cnstr_get(x_141, 1);
lean::inc(x_145);
lean::dec(x_141);
x_148 = lean::cnstr_get(x_142, 0);
if (lean::is_exclusive(x_142)) {
 x_150 = x_142;
} else {
 lean::inc(x_148);
 lean::dec(x_142);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_148);
x_60 = x_151;
x_61 = x_145;
goto lbl_62;
}
else
{
obj* x_153; obj* x_156; obj* x_157; obj* x_159; 
lean::dec(x_142);
x_153 = lean::cnstr_get(x_141, 1);
lean::inc(x_153);
lean::dec(x_141);
x_156 = l_lean_ir_cpp_emit__blockid(x_54, x_2, x_153);
x_157 = lean::cnstr_get(x_156, 0);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_156, 1);
lean::inc(x_159);
lean::dec(x_156);
x_60 = x_157;
x_61 = x_159;
goto lbl_62;
}
}
}
}
}
}
case 3:
{
obj* x_162; obj* x_163; obj* x_164; 
x_162 = l_lean_ir_cpp_emit__case___main___closed__6;
x_163 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_162, x_2, x_3);
x_164 = lean::cnstr_get(x_163, 0);
lean::inc(x_164);
if (lean::obj_tag(x_164) == 0)
{
obj* x_169; obj* x_172; obj* x_174; obj* x_175; 
lean::dec(x_0);
lean::dec(x_54);
lean::dec(x_57);
x_169 = lean::cnstr_get(x_163, 1);
lean::inc(x_169);
lean::dec(x_163);
x_172 = lean::cnstr_get(x_164, 0);
if (lean::is_exclusive(x_164)) {
 x_174 = x_164;
} else {
 lean::inc(x_172);
 lean::dec(x_164);
 x_174 = lean::box(0);
}
if (lean::is_scalar(x_174)) {
 x_175 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_175 = x_174;
}
lean::cnstr_set(x_175, 0, x_172);
x_60 = x_175;
x_61 = x_169;
goto lbl_62;
}
else
{
obj* x_177; obj* x_180; obj* x_181; 
lean::dec(x_164);
x_177 = lean::cnstr_get(x_163, 1);
lean::inc(x_177);
lean::dec(x_163);
x_180 = l_lean_ir_cpp_emit__var(x_0, x_2, x_177);
x_181 = lean::cnstr_get(x_180, 0);
lean::inc(x_181);
if (lean::obj_tag(x_181) == 0)
{
obj* x_185; obj* x_188; obj* x_190; obj* x_191; 
lean::dec(x_54);
lean::dec(x_57);
x_185 = lean::cnstr_get(x_180, 1);
lean::inc(x_185);
lean::dec(x_180);
x_188 = lean::cnstr_get(x_181, 0);
if (lean::is_exclusive(x_181)) {
 x_190 = x_181;
} else {
 lean::inc(x_188);
 lean::dec(x_181);
 x_190 = lean::box(0);
}
if (lean::is_scalar(x_190)) {
 x_191 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_191 = x_190;
}
lean::cnstr_set(x_191, 0, x_188);
x_60 = x_191;
x_61 = x_185;
goto lbl_62;
}
else
{
obj* x_193; obj* x_196; obj* x_197; obj* x_198; 
lean::dec(x_181);
x_193 = lean::cnstr_get(x_180, 1);
lean::inc(x_193);
lean::dec(x_180);
x_196 = l_lean_ir_cpp_emit__case___main___closed__9;
x_197 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_196, x_2, x_193);
x_198 = lean::cnstr_get(x_197, 0);
lean::inc(x_198);
if (lean::obj_tag(x_198) == 0)
{
obj* x_202; obj* x_205; obj* x_207; obj* x_208; 
lean::dec(x_54);
lean::dec(x_57);
x_202 = lean::cnstr_get(x_197, 1);
lean::inc(x_202);
lean::dec(x_197);
x_205 = lean::cnstr_get(x_198, 0);
if (lean::is_exclusive(x_198)) {
 x_207 = x_198;
} else {
 lean::inc(x_205);
 lean::dec(x_198);
 x_207 = lean::box(0);
}
if (lean::is_scalar(x_207)) {
 x_208 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_208 = x_207;
}
lean::cnstr_set(x_208, 0, x_205);
x_60 = x_208;
x_61 = x_202;
goto lbl_62;
}
else
{
obj* x_210; obj* x_213; obj* x_214; 
lean::dec(x_198);
x_210 = lean::cnstr_get(x_197, 1);
lean::inc(x_210);
lean::dec(x_197);
x_213 = l_lean_ir_cpp_emit__blockid(x_54, x_2, x_210);
x_214 = lean::cnstr_get(x_213, 0);
lean::inc(x_214);
if (lean::obj_tag(x_214) == 0)
{
obj* x_217; obj* x_220; obj* x_222; obj* x_223; 
lean::dec(x_57);
x_217 = lean::cnstr_get(x_213, 1);
lean::inc(x_217);
lean::dec(x_213);
x_220 = lean::cnstr_get(x_214, 0);
if (lean::is_exclusive(x_214)) {
 x_222 = x_214;
} else {
 lean::inc(x_220);
 lean::dec(x_214);
 x_222 = lean::box(0);
}
if (lean::is_scalar(x_222)) {
 x_223 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_223 = x_222;
}
lean::cnstr_set(x_223, 0, x_220);
x_60 = x_223;
x_61 = x_217;
goto lbl_62;
}
else
{
obj* x_225; obj* x_228; obj* x_229; obj* x_230; 
lean::dec(x_214);
x_225 = lean::cnstr_get(x_213, 1);
lean::inc(x_225);
lean::dec(x_213);
x_228 = l_lean_ir_cpp_emit__case___main___closed__8;
x_229 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_228, x_2, x_225);
x_230 = lean::cnstr_get(x_229, 0);
lean::inc(x_230);
if (lean::obj_tag(x_230) == 0)
{
obj* x_233; obj* x_236; obj* x_238; obj* x_239; 
lean::dec(x_57);
x_233 = lean::cnstr_get(x_229, 1);
lean::inc(x_233);
lean::dec(x_229);
x_236 = lean::cnstr_get(x_230, 0);
if (lean::is_exclusive(x_230)) {
 x_238 = x_230;
} else {
 lean::inc(x_236);
 lean::dec(x_230);
 x_238 = lean::box(0);
}
if (lean::is_scalar(x_238)) {
 x_239 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_239 = x_238;
}
lean::cnstr_set(x_239, 0, x_236);
x_60 = x_239;
x_61 = x_233;
goto lbl_62;
}
else
{
obj* x_241; obj* x_244; obj* x_245; obj* x_247; 
lean::dec(x_230);
x_241 = lean::cnstr_get(x_229, 1);
lean::inc(x_241);
lean::dec(x_229);
x_244 = l_lean_ir_cpp_emit__blockid(x_57, x_2, x_241);
x_245 = lean::cnstr_get(x_244, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_244, 1);
lean::inc(x_247);
lean::dec(x_244);
x_60 = x_245;
x_61 = x_247;
goto lbl_62;
}
}
}
}
}
}
default:
{
obj* x_253; 
lean::dec(x_0);
lean::dec(x_54);
lean::dec(x_57);
x_253 = l_lean_ir_cpp_emit__case___main___closed__5;
x_60 = x_253;
x_61 = x_3;
goto lbl_62;
}
}
}
lbl_62:
{
if (lean::obj_tag(x_60) == 0)
{
obj* x_255; obj* x_257; obj* x_258; obj* x_259; 
lean::dec(x_2);
x_255 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_257 = x_60;
} else {
 lean::inc(x_255);
 lean::dec(x_60);
 x_257 = lean::box(0);
}
if (lean::is_scalar(x_257)) {
 x_258 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_258 = x_257;
}
lean::cnstr_set(x_258, 0, x_255);
x_259 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_259, 0, x_258);
lean::cnstr_set(x_259, 1, x_61);
return x_259;
}
else
{
obj* x_261; 
lean::dec(x_60);
x_261 = l_lean_ir_cpp_emit__eos(x_2, x_61);
lean::dec(x_2);
return x_261;
}
}
}
else
{
obj* x_265; 
lean::dec(x_10);
lean::dec(x_52);
x_265 = lean::box(0);
x_7 = x_265;
goto lbl_8;
}
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_268; obj* x_270; obj* x_271; obj* x_272; 
lean::dec(x_1);
lean::dec(x_2);
x_268 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_270 = x_4;
} else {
 lean::inc(x_268);
 lean::dec(x_4);
 x_270 = lean::box(0);
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_268);
x_272 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_272, 0, x_271);
lean::cnstr_set(x_272, 1, x_5);
return x_272;
}
else
{
obj* x_274; obj* x_275; obj* x_276; 
lean::dec(x_4);
x_274 = l_lean_ir_cpp_emit__case___main___closed__1;
x_275 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_274, x_2, x_5);
x_276 = lean::cnstr_get(x_275, 0);
lean::inc(x_276);
if (lean::obj_tag(x_276) == 0)
{
obj* x_280; obj* x_282; obj* x_283; obj* x_285; obj* x_286; obj* x_287; 
lean::dec(x_1);
lean::dec(x_2);
x_280 = lean::cnstr_get(x_275, 1);
if (lean::is_exclusive(x_275)) {
 lean::cnstr_release(x_275, 0);
 x_282 = x_275;
} else {
 lean::inc(x_280);
 lean::dec(x_275);
 x_282 = lean::box(0);
}
x_283 = lean::cnstr_get(x_276, 0);
if (lean::is_exclusive(x_276)) {
 x_285 = x_276;
} else {
 lean::inc(x_283);
 lean::dec(x_276);
 x_285 = lean::box(0);
}
if (lean::is_scalar(x_285)) {
 x_286 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_286 = x_285;
}
lean::cnstr_set(x_286, 0, x_283);
if (lean::is_scalar(x_282)) {
 x_287 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_287 = x_282;
}
lean::cnstr_set(x_287, 0, x_286);
lean::cnstr_set(x_287, 1, x_280);
return x_287;
}
else
{
obj* x_289; obj* x_292; obj* x_293; obj* x_294; 
lean::dec(x_276);
x_289 = lean::cnstr_get(x_275, 1);
lean::inc(x_289);
lean::dec(x_275);
x_292 = l_lean_format_be___main___closed__1;
x_293 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_292, x_2, x_289);
x_294 = lean::cnstr_get(x_293, 0);
lean::inc(x_294);
if (lean::obj_tag(x_294) == 0)
{
obj* x_298; obj* x_300; obj* x_301; obj* x_303; obj* x_304; obj* x_305; 
lean::dec(x_1);
lean::dec(x_2);
x_298 = lean::cnstr_get(x_293, 1);
if (lean::is_exclusive(x_293)) {
 lean::cnstr_release(x_293, 0);
 x_300 = x_293;
} else {
 lean::inc(x_298);
 lean::dec(x_293);
 x_300 = lean::box(0);
}
x_301 = lean::cnstr_get(x_294, 0);
if (lean::is_exclusive(x_294)) {
 x_303 = x_294;
} else {
 lean::inc(x_301);
 lean::dec(x_294);
 x_303 = lean::box(0);
}
if (lean::is_scalar(x_303)) {
 x_304 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_304 = x_303;
}
lean::cnstr_set(x_304, 0, x_301);
if (lean::is_scalar(x_300)) {
 x_305 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_305 = x_300;
}
lean::cnstr_set(x_305, 0, x_304);
lean::cnstr_set(x_305, 1, x_298);
return x_305;
}
else
{
obj* x_307; obj* x_310; obj* x_311; obj* x_312; 
lean::dec(x_294);
x_307 = lean::cnstr_get(x_293, 1);
lean::inc(x_307);
lean::dec(x_293);
x_310 = lean::mk_nat_obj(0u);
x_311 = l_lean_ir_cpp_emit__cases___main(x_1, x_310, x_2, x_307);
x_312 = lean::cnstr_get(x_311, 0);
lean::inc(x_312);
if (lean::obj_tag(x_312) == 0)
{
obj* x_315; obj* x_317; obj* x_318; obj* x_320; obj* x_321; obj* x_322; 
lean::dec(x_2);
x_315 = lean::cnstr_get(x_311, 1);
if (lean::is_exclusive(x_311)) {
 lean::cnstr_release(x_311, 0);
 x_317 = x_311;
} else {
 lean::inc(x_315);
 lean::dec(x_311);
 x_317 = lean::box(0);
}
x_318 = lean::cnstr_get(x_312, 0);
if (lean::is_exclusive(x_312)) {
 x_320 = x_312;
} else {
 lean::inc(x_318);
 lean::dec(x_312);
 x_320 = lean::box(0);
}
if (lean::is_scalar(x_320)) {
 x_321 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_321 = x_320;
}
lean::cnstr_set(x_321, 0, x_318);
if (lean::is_scalar(x_317)) {
 x_322 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_322 = x_317;
}
lean::cnstr_set(x_322, 0, x_321);
lean::cnstr_set(x_322, 1, x_315);
return x_322;
}
else
{
obj* x_324; obj* x_327; obj* x_328; obj* x_329; 
lean::dec(x_312);
x_324 = lean::cnstr_get(x_311, 1);
lean::inc(x_324);
lean::dec(x_311);
x_327 = l_lean_ir_cpp_emit__case___main___closed__2;
x_328 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_327, x_2, x_324);
x_329 = lean::cnstr_get(x_328, 0);
lean::inc(x_329);
if (lean::obj_tag(x_329) == 0)
{
obj* x_332; obj* x_334; obj* x_335; obj* x_337; obj* x_338; obj* x_339; 
lean::dec(x_2);
x_332 = lean::cnstr_get(x_328, 1);
if (lean::is_exclusive(x_328)) {
 lean::cnstr_release(x_328, 0);
 x_334 = x_328;
} else {
 lean::inc(x_332);
 lean::dec(x_328);
 x_334 = lean::box(0);
}
x_335 = lean::cnstr_get(x_329, 0);
if (lean::is_exclusive(x_329)) {
 x_337 = x_329;
} else {
 lean::inc(x_335);
 lean::dec(x_329);
 x_337 = lean::box(0);
}
if (lean::is_scalar(x_337)) {
 x_338 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_338 = x_337;
}
lean::cnstr_set(x_338, 0, x_335);
if (lean::is_scalar(x_334)) {
 x_339 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_339 = x_334;
}
lean::cnstr_set(x_339, 0, x_338);
lean::cnstr_set(x_339, 1, x_332);
return x_339;
}
else
{
obj* x_341; obj* x_344; 
lean::dec(x_329);
x_341 = lean::cnstr_get(x_328, 1);
lean::inc(x_341);
lean::dec(x_328);
x_344 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_292, x_2, x_341);
lean::dec(x_2);
return x_344;
}
}
}
}
}
}
lbl_8:
{
obj* x_347; obj* x_348; obj* x_349; 
lean::dec(x_7);
x_347 = l_lean_ir_cpp_emit__case___main___closed__3;
x_348 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_347, x_2, x_3);
x_349 = lean::cnstr_get(x_348, 0);
lean::inc(x_349);
if (lean::obj_tag(x_349) == 0)
{
obj* x_354; obj* x_356; obj* x_357; obj* x_359; obj* x_360; obj* x_361; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_354 = lean::cnstr_get(x_348, 1);
if (lean::is_exclusive(x_348)) {
 lean::cnstr_release(x_348, 0);
 x_356 = x_348;
} else {
 lean::inc(x_354);
 lean::dec(x_348);
 x_356 = lean::box(0);
}
x_357 = lean::cnstr_get(x_349, 0);
if (lean::is_exclusive(x_349)) {
 x_359 = x_349;
} else {
 lean::inc(x_357);
 lean::dec(x_349);
 x_359 = lean::box(0);
}
if (lean::is_scalar(x_359)) {
 x_360 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_360 = x_359;
}
lean::cnstr_set(x_360, 0, x_357);
if (lean::is_scalar(x_356)) {
 x_361 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_361 = x_356;
}
lean::cnstr_set(x_361, 0, x_360);
lean::cnstr_set(x_361, 1, x_354);
return x_361;
}
else
{
obj* x_363; obj* x_366; obj* x_367; obj* x_368; 
lean::dec(x_349);
x_363 = lean::cnstr_get(x_348, 1);
lean::inc(x_363);
lean::dec(x_348);
x_366 = l_prod_has__repr___rarg___closed__1;
x_367 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_366, x_2, x_363);
x_368 = lean::cnstr_get(x_367, 0);
lean::inc(x_368);
if (lean::obj_tag(x_368) == 0)
{
obj* x_371; obj* x_374; obj* x_376; obj* x_377; 
lean::dec(x_0);
x_371 = lean::cnstr_get(x_367, 1);
lean::inc(x_371);
lean::dec(x_367);
x_374 = lean::cnstr_get(x_368, 0);
if (lean::is_exclusive(x_368)) {
 x_376 = x_368;
} else {
 lean::inc(x_374);
 lean::dec(x_368);
 x_376 = lean::box(0);
}
if (lean::is_scalar(x_376)) {
 x_377 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_377 = x_376;
}
lean::cnstr_set(x_377, 0, x_374);
x_4 = x_377;
x_5 = x_371;
goto lbl_6;
}
else
{
obj* x_379; obj* x_382; obj* x_383; 
lean::dec(x_368);
x_379 = lean::cnstr_get(x_367, 1);
lean::inc(x_379);
lean::dec(x_367);
x_382 = l_lean_ir_cpp_emit__var(x_0, x_2, x_379);
x_383 = lean::cnstr_get(x_382, 0);
lean::inc(x_383);
if (lean::obj_tag(x_383) == 0)
{
obj* x_385; obj* x_388; obj* x_390; obj* x_391; 
x_385 = lean::cnstr_get(x_382, 1);
lean::inc(x_385);
lean::dec(x_382);
x_388 = lean::cnstr_get(x_383, 0);
if (lean::is_exclusive(x_383)) {
 x_390 = x_383;
} else {
 lean::inc(x_388);
 lean::dec(x_383);
 x_390 = lean::box(0);
}
if (lean::is_scalar(x_390)) {
 x_391 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_391 = x_390;
}
lean::cnstr_set(x_391, 0, x_388);
x_4 = x_391;
x_5 = x_385;
goto lbl_6;
}
else
{
obj* x_392; obj* x_395; obj* x_398; obj* x_399; obj* x_400; 
x_392 = lean::cnstr_get(x_382, 1);
lean::inc(x_392);
lean::dec(x_382);
x_395 = lean::cnstr_get(x_383, 0);
lean::inc(x_395);
lean::dec(x_383);
x_398 = l_option_has__repr___rarg___closed__3;
x_399 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_398, x_2, x_392);
x_400 = lean::cnstr_get(x_399, 0);
lean::inc(x_400);
if (lean::obj_tag(x_400) == 0)
{
obj* x_403; obj* x_406; obj* x_408; obj* x_409; 
lean::dec(x_395);
x_403 = lean::cnstr_get(x_399, 1);
lean::inc(x_403);
lean::dec(x_399);
x_406 = lean::cnstr_get(x_400, 0);
if (lean::is_exclusive(x_400)) {
 x_408 = x_400;
} else {
 lean::inc(x_406);
 lean::dec(x_400);
 x_408 = lean::box(0);
}
if (lean::is_scalar(x_408)) {
 x_409 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_409 = x_408;
}
lean::cnstr_set(x_409, 0, x_406);
x_4 = x_409;
x_5 = x_403;
goto lbl_6;
}
else
{
obj* x_410; obj* x_411; obj* x_414; 
if (lean::is_exclusive(x_400)) {
 lean::cnstr_release(x_400, 0);
 x_410 = x_400;
} else {
 lean::dec(x_400);
 x_410 = lean::box(0);
}
x_411 = lean::cnstr_get(x_399, 1);
lean::inc(x_411);
lean::dec(x_399);
if (lean::is_scalar(x_410)) {
 x_414 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_414 = x_410;
}
lean::cnstr_set(x_414, 0, x_395);
x_4 = x_414;
x_5 = x_411;
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
obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = l_lean_ir_cpp_emit__terminator___closed__1;
x_9 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_8, x_1, x_2);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_6);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
lean::dec(x_9);
x_17 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_19 = x_10;
} else {
 lean::inc(x_17);
 lean::dec(x_10);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
x_3 = x_20;
x_4 = x_14;
goto lbl_5;
}
else
{
obj* x_22; obj* x_25; obj* x_26; 
lean::dec(x_10);
x_22 = lean::cnstr_get(x_9, 1);
lean::inc(x_22);
lean::dec(x_9);
x_25 = l_lean_ir_cpp_emit__var(x_6, x_1, x_22);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_1);
x_29 = lean::cnstr_get(x_25, 1);
lean::inc(x_29);
lean::dec(x_25);
x_32 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_34 = x_26;
} else {
 lean::inc(x_32);
 lean::dec(x_26);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
x_3 = x_35;
x_4 = x_29;
goto lbl_5;
}
else
{
obj* x_37; obj* x_40; obj* x_42; obj* x_44; 
lean::dec(x_26);
x_37 = lean::cnstr_get(x_25, 1);
lean::inc(x_37);
lean::dec(x_25);
x_40 = l_lean_ir_cpp_emit__eos(x_1, x_37);
lean::dec(x_1);
x_42 = lean::cnstr_get(x_40, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_40, 1);
lean::inc(x_44);
lean::dec(x_40);
x_3 = x_42;
x_4 = x_44;
goto lbl_5;
}
}
}
case 1:
{
obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_54; 
x_47 = lean::cnstr_get(x_0, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_0, 1);
lean::inc(x_49);
x_51 = l_lean_ir_cpp_emit__case___main(x_47, x_49, x_1, x_2);
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
lean::dec(x_51);
x_3 = x_52;
x_4 = x_54;
goto lbl_5;
}
default:
{
obj* x_57; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::cnstr_get(x_0, 0);
lean::inc(x_57);
x_59 = l_lean_ir_cpp_emit__case___main___closed__4;
x_60 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_59, x_1, x_2);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
if (lean::obj_tag(x_61) == 0)
{
obj* x_65; obj* x_68; obj* x_70; obj* x_71; 
lean::dec(x_1);
lean::dec(x_57);
x_65 = lean::cnstr_get(x_60, 1);
lean::inc(x_65);
lean::dec(x_60);
x_68 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_70 = x_61;
} else {
 lean::inc(x_68);
 lean::dec(x_61);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_68);
x_3 = x_71;
x_4 = x_65;
goto lbl_5;
}
else
{
obj* x_73; obj* x_76; obj* x_77; 
lean::dec(x_61);
x_73 = lean::cnstr_get(x_60, 1);
lean::inc(x_73);
lean::dec(x_60);
x_76 = l_lean_ir_cpp_emit__blockid(x_57, x_1, x_73);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
if (lean::obj_tag(x_77) == 0)
{
obj* x_80; obj* x_83; obj* x_85; obj* x_86; 
lean::dec(x_1);
x_80 = lean::cnstr_get(x_76, 1);
lean::inc(x_80);
lean::dec(x_76);
x_83 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_85 = x_77;
} else {
 lean::inc(x_83);
 lean::dec(x_77);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_83);
x_3 = x_86;
x_4 = x_80;
goto lbl_5;
}
else
{
obj* x_88; obj* x_91; obj* x_93; obj* x_95; 
lean::dec(x_77);
x_88 = lean::cnstr_get(x_76, 1);
lean::inc(x_88);
lean::dec(x_76);
x_91 = l_lean_ir_cpp_emit__eos(x_1, x_88);
lean::dec(x_1);
x_93 = lean::cnstr_get(x_91, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_91, 1);
lean::inc(x_95);
lean::dec(x_91);
x_3 = x_93;
x_4 = x_95;
goto lbl_5;
}
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_98; obj* x_100; obj* x_101; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
x_98 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_100 = x_3;
} else {
 lean::inc(x_98);
 lean::dec(x_3);
 x_100 = lean::box(0);
}
x_101 = l_lean_ir_terminator_to__format___main(x_0);
x_102 = 0;
x_103 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
x_104 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_101);
lean::cnstr_set_scalar(x_104, sizeof(void*)*2, x_102);
x_105 = x_104;
x_106 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_107 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_107, 0, x_105);
lean::cnstr_set(x_107, 1, x_106);
lean::cnstr_set_scalar(x_107, sizeof(void*)*2, x_102);
x_108 = x_107;
x_109 = lean::box(1);
x_110 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_110, 0, x_108);
lean::cnstr_set(x_110, 1, x_109);
lean::cnstr_set_scalar(x_110, sizeof(void*)*2, x_102);
x_111 = x_110;
x_112 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_98);
lean::cnstr_set_scalar(x_112, sizeof(void*)*2, x_102);
x_113 = x_112;
if (lean::is_scalar(x_100)) {
 x_114 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_114 = x_100;
}
lean::cnstr_set(x_114, 0, x_113);
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_4);
return x_115;
}
else
{
obj* x_117; 
lean::dec(x_0);
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_3);
lean::cnstr_set(x_117, 1, x_4);
return x_117;
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
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_ir_cpp_emit__type__size___closed__1;
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_12 = x_5;
} else {
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
if (lean::is_scalar(x_12)) {
 x_13 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_13 = x_12;
}
lean::cnstr_set(x_13, 0, x_10);
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_5);
x_16 = lean::cnstr_get(x_4, 1);
lean::inc(x_16);
lean::dec(x_4);
x_19 = l_prod_has__repr___rarg___closed__1;
x_20 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_1, x_16);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
x_23 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 x_25 = x_20;
} else {
 lean::inc(x_23);
 lean::dec(x_20);
 x_25 = lean::box(0);
}
x_26 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_28 = x_21;
} else {
 lean::inc(x_26);
 lean::dec(x_21);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_26);
if (lean::is_scalar(x_25)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_25;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_23);
return x_30;
}
else
{
obj* x_32; obj* x_35; obj* x_36; 
lean::dec(x_21);
x_32 = lean::cnstr_get(x_20, 1);
lean::inc(x_32);
lean::dec(x_20);
x_35 = l_lean_ir_cpp_emit__type(x_0, x_1, x_32);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; 
x_38 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 x_40 = x_35;
} else {
 lean::inc(x_38);
 lean::dec(x_35);
 x_40 = lean::box(0);
}
x_41 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_43 = x_36;
} else {
 lean::inc(x_41);
 lean::dec(x_36);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_41);
if (lean::is_scalar(x_40)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_40;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_38);
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_52; obj* x_53; obj* x_54; 
x_46 = lean::cnstr_get(x_35, 1);
lean::inc(x_46);
lean::dec(x_35);
x_49 = lean::cnstr_get(x_36, 0);
lean::inc(x_49);
lean::dec(x_36);
x_52 = l_option_has__repr___rarg___closed__3;
x_53 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_52, x_1, x_46);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_49);
x_57 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 x_59 = x_53;
} else {
 lean::inc(x_57);
 lean::dec(x_53);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_54, 0);
if (lean::is_exclusive(x_54)) {
 x_62 = x_54;
} else {
 lean::inc(x_60);
 lean::dec(x_54);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_60);
if (lean::is_scalar(x_59)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_59;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_57);
return x_64;
}
else
{
obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; 
if (lean::is_exclusive(x_54)) {
 lean::cnstr_release(x_54, 0);
 x_65 = x_54;
} else {
 lean::dec(x_54);
 x_65 = lean::box(0);
}
x_66 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 x_68 = x_53;
} else {
 lean::inc(x_66);
 lean::dec(x_53);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_65;
}
lean::cnstr_set(x_69, 0, x_49);
if (lean::is_scalar(x_68)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_68;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_66);
return x_70;
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
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_ir_cpp_emit__op__x(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_0, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
} else {
 lean::inc(x_8);
 lean::dec(x_4);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_13 = x_5;
} else {
 lean::inc(x_11);
 lean::dec(x_5);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
if (lean::is_scalar(x_10)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_10;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_8);
return x_15;
}
else
{
obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_5);
x_17 = lean::cnstr_get(x_4, 1);
lean::inc(x_17);
lean::dec(x_4);
x_20 = l_prod_has__repr___rarg___closed__1;
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_20, x_2, x_17);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_1);
x_25 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_27 = x_21;
} else {
 lean::inc(x_25);
 lean::dec(x_21);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_30 = x_22;
} else {
 lean::inc(x_28);
 lean::dec(x_22);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
if (lean::is_scalar(x_27)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_27;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_25);
return x_32;
}
else
{
obj* x_34; obj* x_37; obj* x_38; 
lean::dec(x_22);
x_34 = lean::cnstr_get(x_21, 1);
lean::inc(x_34);
lean::dec(x_21);
x_37 = l_lean_ir_cpp_emit__var(x_1, x_2, x_34);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
x_40 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_42 = x_37;
} else {
 lean::inc(x_40);
 lean::dec(x_37);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_45 = x_38;
} else {
 lean::inc(x_43);
 lean::dec(x_38);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_43);
if (lean::is_scalar(x_42)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_42;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_40);
return x_47;
}
else
{
obj* x_48; obj* x_51; obj* x_54; obj* x_55; obj* x_56; 
x_48 = lean::cnstr_get(x_37, 1);
lean::inc(x_48);
lean::dec(x_37);
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
lean::dec(x_38);
x_54 = l_option_has__repr___rarg___closed__3;
x_55 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_54, x_2, x_48);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
if (lean::obj_tag(x_56) == 0)
{
obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_51);
x_59 = lean::cnstr_get(x_55, 1);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_61 = x_55;
} else {
 lean::inc(x_59);
 lean::dec(x_55);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 x_64 = x_56;
} else {
 lean::inc(x_62);
 lean::dec(x_56);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_62);
if (lean::is_scalar(x_61)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_61;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_59);
return x_66;
}
else
{
obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; 
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 x_67 = x_56;
} else {
 lean::dec(x_56);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_55, 1);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_70 = x_55;
} else {
 lean::inc(x_68);
 lean::dec(x_55);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_71 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_71 = x_67;
}
lean::cnstr_set(x_71, 0, x_51);
if (lean::is_scalar(x_70)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_70;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_68);
return x_72;
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__op__x___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_ir_cpp_emit__op__x(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
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
obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_9 = l_lean_ir_cpp_emit__var(x_0, x_4, x_5);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_17; obj* x_18; 
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_17 = x_10;
} else {
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_15);
x_6 = x_18;
x_7 = x_12;
goto lbl_8;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_27; 
lean::dec(x_10);
x_20 = lean::cnstr_get(x_9, 1);
lean::inc(x_20);
lean::dec(x_9);
x_23 = l_lean_ir_cpp_emit__infix___closed__1;
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_23, x_4, x_20);
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
obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
lean::dec(x_2);
x_32 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_34 = x_6;
} else {
 lean::inc(x_32);
 lean::dec(x_6);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_7);
return x_36;
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_6);
x_38 = l_lean_ir_cpp_emit__var(x_1, x_4, x_7);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
if (lean::obj_tag(x_39) == 0)
{
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_2);
x_42 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_44 = x_38;
} else {
 lean::inc(x_42);
 lean::dec(x_38);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_39, 0);
if (lean::is_exclusive(x_39)) {
 x_47 = x_39;
} else {
 lean::inc(x_45);
 lean::dec(x_39);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
if (lean::is_scalar(x_44)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_44;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_42);
return x_49;
}
else
{
obj* x_51; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_39);
x_51 = lean::cnstr_get(x_38, 1);
lean::inc(x_51);
lean::dec(x_38);
x_54 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
x_55 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_54, x_4, x_51);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
if (lean::obj_tag(x_56) == 0)
{
obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_2);
x_59 = lean::cnstr_get(x_55, 1);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_61 = x_55;
} else {
 lean::inc(x_59);
 lean::dec(x_55);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 x_64 = x_56;
} else {
 lean::inc(x_62);
 lean::dec(x_56);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_62);
if (lean::is_scalar(x_61)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_61;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_59);
return x_66;
}
else
{
obj* x_68; obj* x_71; obj* x_72; 
lean::dec(x_56);
x_68 = lean::cnstr_get(x_55, 1);
lean::inc(x_68);
lean::dec(x_55);
x_71 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_4, x_68);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_2);
x_75 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 x_77 = x_71;
} else {
 lean::inc(x_75);
 lean::dec(x_71);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_80 = x_72;
} else {
 lean::inc(x_78);
 lean::dec(x_72);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
if (lean::is_scalar(x_77)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_77;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_75);
return x_82;
}
else
{
obj* x_84; obj* x_87; obj* x_88; 
lean::dec(x_72);
x_84 = lean::cnstr_get(x_71, 1);
lean::inc(x_84);
lean::dec(x_71);
x_87 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_54, x_4, x_84);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
if (lean::obj_tag(x_88) == 0)
{
obj* x_91; obj* x_93; obj* x_94; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_2);
x_91 = lean::cnstr_get(x_87, 1);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 x_93 = x_87;
} else {
 lean::inc(x_91);
 lean::dec(x_87);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_88, 0);
if (lean::is_exclusive(x_88)) {
 x_96 = x_88;
} else {
 lean::inc(x_94);
 lean::dec(x_88);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_94);
if (lean::is_scalar(x_93)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_93;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_91);
return x_98;
}
else
{
obj* x_100; obj* x_103; 
lean::dec(x_88);
x_100 = lean::cnstr_get(x_87, 1);
lean::inc(x_100);
lean::dec(x_87);
x_103 = l_lean_ir_cpp_emit__var(x_2, x_4, x_100);
return x_103;
}
}
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__infix___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_ir_cpp_emit__infix(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_4);
return x_6;
}
}
obj* l_lean_ir_cpp_emit__big__binop(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_9 = l_lean_ir_cpp_emit__var(x_0, x_4, x_5);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_17; obj* x_18; 
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_17 = x_10;
} else {
 lean::inc(x_15);
 lean::dec(x_10);
 x_17 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_15);
x_6 = x_18;
x_7 = x_12;
goto lbl_8;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_10);
x_20 = lean::cnstr_get(x_9, 1);
lean::inc(x_20);
lean::dec(x_9);
x_23 = l_lean_ir_cpp_emit__infix___closed__1;
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_23, x_4, x_20);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_27; obj* x_30; obj* x_32; obj* x_33; 
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_30 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_32 = x_25;
} else {
 lean::inc(x_30);
 lean::dec(x_25);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
x_6 = x_33;
x_7 = x_27;
goto lbl_8;
}
else
{
obj* x_35; obj* x_38; obj* x_39; obj* x_41; 
lean::dec(x_25);
x_35 = lean::cnstr_get(x_24, 1);
lean::inc(x_35);
lean::dec(x_24);
x_38 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_4, x_35);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
x_6 = x_39;
x_7 = x_41;
goto lbl_8;
}
}
lbl_8:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_46; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_1);
lean::dec(x_2);
x_46 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_48 = x_6;
} else {
 lean::inc(x_46);
 lean::dec(x_6);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_46);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_7);
return x_50;
}
else
{
obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_6);
x_52 = l_prod_has__repr___rarg___closed__1;
x_53 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_52, x_4, x_7);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_58; obj* x_60; obj* x_61; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_1);
lean::dec(x_2);
x_58 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 x_60 = x_53;
} else {
 lean::inc(x_58);
 lean::dec(x_53);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_54, 0);
if (lean::is_exclusive(x_54)) {
 x_63 = x_54;
} else {
 lean::inc(x_61);
 lean::dec(x_54);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_61);
if (lean::is_scalar(x_60)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_60;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_58);
return x_65;
}
else
{
obj* x_67; obj* x_70; obj* x_71; 
lean::dec(x_54);
x_67 = lean::cnstr_get(x_53, 1);
lean::inc(x_67);
lean::dec(x_53);
x_70 = l_lean_ir_cpp_emit__var(x_1, x_4, x_67);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
obj* x_74; obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_2);
x_74 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 x_76 = x_70;
} else {
 lean::inc(x_74);
 lean::dec(x_70);
 x_76 = lean::box(0);
}
x_77 = lean::cnstr_get(x_71, 0);
if (lean::is_exclusive(x_71)) {
 x_79 = x_71;
} else {
 lean::inc(x_77);
 lean::dec(x_71);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
if (lean::is_scalar(x_76)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_76;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_74);
return x_81;
}
else
{
obj* x_83; obj* x_86; obj* x_87; obj* x_88; 
lean::dec(x_71);
x_83 = lean::cnstr_get(x_70, 1);
lean::inc(x_83);
lean::dec(x_70);
x_86 = l_list_repr__aux___main___rarg___closed__1;
x_87 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_86, x_4, x_83);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
if (lean::obj_tag(x_88) == 0)
{
obj* x_91; obj* x_93; obj* x_94; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_2);
x_91 = lean::cnstr_get(x_87, 1);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 x_93 = x_87;
} else {
 lean::inc(x_91);
 lean::dec(x_87);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_88, 0);
if (lean::is_exclusive(x_88)) {
 x_96 = x_88;
} else {
 lean::inc(x_94);
 lean::dec(x_88);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_94);
if (lean::is_scalar(x_93)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_93;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_91);
return x_98;
}
else
{
obj* x_100; obj* x_103; obj* x_104; 
lean::dec(x_88);
x_100 = lean::cnstr_get(x_87, 1);
lean::inc(x_100);
lean::dec(x_87);
x_103 = l_lean_ir_cpp_emit__var(x_2, x_4, x_100);
x_104 = lean::cnstr_get(x_103, 0);
lean::inc(x_104);
if (lean::obj_tag(x_104) == 0)
{
obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_112; obj* x_113; 
x_106 = lean::cnstr_get(x_103, 1);
if (lean::is_exclusive(x_103)) {
 lean::cnstr_release(x_103, 0);
 x_108 = x_103;
} else {
 lean::inc(x_106);
 lean::dec(x_103);
 x_108 = lean::box(0);
}
x_109 = lean::cnstr_get(x_104, 0);
if (lean::is_exclusive(x_104)) {
 x_111 = x_104;
} else {
 lean::inc(x_109);
 lean::dec(x_104);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_109);
if (lean::is_scalar(x_108)) {
 x_113 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_113 = x_108;
}
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_106);
return x_113;
}
else
{
obj* x_114; obj* x_117; obj* x_120; obj* x_121; obj* x_122; 
x_114 = lean::cnstr_get(x_103, 1);
lean::inc(x_114);
lean::dec(x_103);
x_117 = lean::cnstr_get(x_104, 0);
lean::inc(x_117);
lean::dec(x_104);
x_120 = l_option_has__repr___rarg___closed__3;
x_121 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_120, x_4, x_114);
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
if (lean::obj_tag(x_122) == 0)
{
obj* x_125; obj* x_127; obj* x_128; obj* x_130; obj* x_131; obj* x_132; 
lean::dec(x_117);
x_125 = lean::cnstr_get(x_121, 1);
if (lean::is_exclusive(x_121)) {
 lean::cnstr_release(x_121, 0);
 x_127 = x_121;
} else {
 lean::inc(x_125);
 lean::dec(x_121);
 x_127 = lean::box(0);
}
x_128 = lean::cnstr_get(x_122, 0);
if (lean::is_exclusive(x_122)) {
 x_130 = x_122;
} else {
 lean::inc(x_128);
 lean::dec(x_122);
 x_130 = lean::box(0);
}
if (lean::is_scalar(x_130)) {
 x_131 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_131 = x_130;
}
lean::cnstr_set(x_131, 0, x_128);
if (lean::is_scalar(x_127)) {
 x_132 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_132 = x_127;
}
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_125);
return x_132;
}
else
{
obj* x_133; obj* x_134; obj* x_136; obj* x_137; obj* x_138; 
if (lean::is_exclusive(x_122)) {
 lean::cnstr_release(x_122, 0);
 x_133 = x_122;
} else {
 lean::dec(x_122);
 x_133 = lean::box(0);
}
x_134 = lean::cnstr_get(x_121, 1);
if (lean::is_exclusive(x_121)) {
 lean::cnstr_release(x_121, 0);
 x_136 = x_121;
} else {
 lean::inc(x_134);
 lean::dec(x_121);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_133)) {
 x_137 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_137 = x_133;
}
lean::cnstr_set(x_137, 0, x_117);
if (lean::is_scalar(x_136)) {
 x_138 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_138 = x_136;
}
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_134);
return x_138;
}
}
}
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__big__binop___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_ir_cpp_emit__big__binop(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_4);
return x_6;
}
}
obj* l_lean_ir_cpp_emit__arith(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
switch (x_0) {
case 11:
{
obj* x_8; 
x_8 = l_lean_ir_cpp_emit__big__binop(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
default:
{
obj* x_9; 
x_9 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_9;
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
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_9;
}
}
obj* l_lean_ir_cpp_emit__logical__arith(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
switch (x_0) {
case 0:
{
obj* x_9; 
x_9 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_7, x_8);
return x_9;
}
case 11:
{
obj* x_10; 
x_10 = l_lean_ir_cpp_emit__big__binop(x_1, x_2, x_3, x_6, x_7, x_8);
return x_10;
}
default:
{
obj* x_11; 
x_11 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_11;
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
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_7);
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
obj* x_12; obj* x_13; obj* x_14; 
x_12 = l_lean_ir_cpp_emit__assign__binop___closed__2;
x_13 = l_lean_ir_cpp_emit__assign__binop___closed__3;
x_14 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_12, x_13, x_5, x_6);
lean::dec(x_5);
return x_14;
}
case 1:
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = l_int_repr___main___closed__2;
x_17 = l_lean_ir_cpp_emit__assign__binop___closed__4;
x_18 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_16, x_17, x_5, x_6);
lean::dec(x_5);
return x_18;
}
case 2:
{
obj* x_20; obj* x_21; obj* x_22; 
x_20 = l_lean_ir_cpp_emit__assign__binop___closed__5;
x_21 = l_lean_ir_cpp_emit__assign__binop___closed__6;
x_22 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_20, x_21, x_5, x_6);
lean::dec(x_5);
return x_22;
}
case 3:
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_lean_ir_cpp_emit__assign__binop___closed__7;
x_25 = l_lean_ir_cpp_emit__assign__binop___closed__8;
x_26 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_24, x_25, x_5, x_6);
lean::dec(x_5);
return x_26;
}
case 4:
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_lean_ir_cpp_emit__assign__binop___closed__9;
x_29 = l_lean_ir_cpp_emit__assign__binop___closed__10;
x_30 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_28, x_29, x_5, x_6);
lean::dec(x_5);
return x_30;
}
case 5:
{
obj* x_32; obj* x_33; 
x_32 = l_lean_ir_cpp_emit__assign__binop___closed__11;
x_33 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_32, x_5, x_6);
lean::dec(x_5);
return x_33;
}
case 6:
{
obj* x_35; obj* x_36; 
x_35 = l_lean_ir_cpp_emit__assign__binop___closed__12;
x_36 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_35, x_5, x_6);
lean::dec(x_5);
return x_36;
}
case 7:
{
obj* x_38; obj* x_39; 
x_38 = l_lean_ir_cpp_emit__assign__binop___closed__13;
x_39 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_38, x_5, x_6);
lean::dec(x_5);
return x_39;
}
case 8:
{
obj* x_41; obj* x_42; 
x_41 = l_lean_ir_cpp_emit__assign__binop___closed__14;
x_42 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_41, x_5, x_6);
lean::dec(x_5);
return x_42;
}
case 9:
{
obj* x_44; obj* x_45; 
x_44 = l_lean_ir_cpp_emit__assign__binop___closed__15;
x_45 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_44, x_5, x_6);
lean::dec(x_5);
return x_45;
}
case 10:
{
obj* x_47; obj* x_48; 
x_47 = l_lean_ir_cpp_emit__assign__binop___closed__16;
x_48 = l_lean_ir_cpp_emit__infix(x_0, x_3, x_4, x_47, x_5, x_6);
lean::dec(x_5);
return x_48;
}
case 11:
{
obj* x_50; obj* x_51; 
x_50 = l_lean_ir_cpp_emit__assign__binop___closed__17;
x_51 = l_lean_ir_cpp_emit__infix(x_0, x_3, x_4, x_50, x_5, x_6);
lean::dec(x_5);
return x_51;
}
case 12:
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_53 = l_lean_ir_cpp_emit__assign__binop___closed__18;
x_54 = l_lean_ir_cpp_emit__assign__binop___closed__19;
x_55 = l_lean_ir_cpp_emit__assign__binop___closed__20;
x_56 = l_lean_ir_cpp_emit__logical__arith(x_1, x_0, x_3, x_4, x_53, x_54, x_55, x_5, x_6);
lean::dec(x_5);
return x_56;
}
case 13:
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_58 = l_lean_ir_cpp_emit__assign__binop___closed__21;
x_59 = l_lean_ir_cpp_emit__assign__binop___closed__22;
x_60 = l_lean_ir_cpp_emit__assign__binop___closed__23;
x_61 = l_lean_ir_cpp_emit__logical__arith(x_1, x_0, x_3, x_4, x_58, x_59, x_60, x_5, x_6);
lean::dec(x_5);
return x_61;
}
case 14:
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_63 = l_lean_ir_cpp_emit__assign__binop___closed__24;
x_64 = l_lean_ir_cpp_emit__assign__binop___closed__25;
x_65 = l_lean_ir_cpp_emit__assign__binop___closed__26;
x_66 = l_lean_ir_cpp_emit__logical__arith(x_1, x_0, x_3, x_4, x_63, x_64, x_65, x_5, x_6);
lean::dec(x_5);
return x_66;
}
case 15:
{
obj* x_68; obj* x_69; obj* x_70; 
x_68 = l_lean_ir_cpp_emit__assign__binop___closed__27;
x_69 = l_lean_ir_cpp_emit__assign__binop___closed__28;
x_70 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_68, x_69, x_5, x_6);
lean::dec(x_5);
return x_70;
}
case 16:
{
obj* x_72; obj* x_73; obj* x_74; 
x_72 = l_lean_ir_cpp_emit__template__params___closed__1;
x_73 = l_lean_ir_cpp_emit__assign__binop___closed__29;
x_74 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_72, x_73, x_5, x_6);
lean::dec(x_5);
return x_74;
}
case 17:
{
obj* x_76; obj* x_77; obj* x_78; 
x_76 = l_lean_ir_cpp_emit__assign__binop___closed__30;
x_77 = l_lean_ir_cpp_emit__assign__binop___closed__31;
x_78 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_76, x_77, x_5, x_6);
lean::dec(x_5);
return x_78;
}
case 18:
{
obj* x_80; obj* x_81; obj* x_82; 
x_80 = l_lean_ir_cpp_emit__assign__binop___closed__24;
x_81 = l_lean_ir_cpp_emit__assign__binop___closed__32;
x_82 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_80, x_81, x_5, x_6);
lean::dec(x_5);
return x_82;
}
case 19:
{
obj* x_84; obj* x_85; 
x_84 = l_lean_ir_cpp_emit__assign__binop___closed__33;
x_85 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_84, x_5, x_6);
lean::dec(x_5);
return x_85;
}
case 20:
{
obj* x_87; obj* x_88; 
x_87 = l_lean_ir_cpp_emit__assign__binop___closed__34;
x_88 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_87, x_5, x_6);
lean::dec(x_5);
return x_88;
}
case 21:
{
obj* x_90; obj* x_91; 
x_90 = l_lean_ir_cpp_emit__assign__binop___closed__35;
x_91 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_90, x_5, x_6);
lean::dec(x_5);
return x_91;
}
case 22:
{
obj* x_93; obj* x_94; 
x_93 = l_lean_ir_cpp_emit__assign__binop___closed__36;
x_94 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_93, x_5, x_6);
lean::dec(x_5);
return x_94;
}
case 23:
{
switch (x_1) {
case 11:
{
obj* x_96; obj* x_97; 
x_96 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
if (lean::obj_tag(x_97) == 0)
{
obj* x_99; obj* x_102; obj* x_104; obj* x_105; 
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
lean::dec(x_96);
x_102 = lean::cnstr_get(x_97, 0);
if (lean::is_exclusive(x_97)) {
 x_104 = x_97;
} else {
 lean::inc(x_102);
 lean::dec(x_97);
 x_104 = lean::box(0);
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_102);
x_9 = x_105;
x_10 = x_99;
goto lbl_11;
}
else
{
obj* x_107; obj* x_110; obj* x_111; obj* x_112; obj* x_114; 
lean::dec(x_97);
x_107 = lean::cnstr_get(x_96, 1);
lean::inc(x_107);
lean::dec(x_96);
x_110 = l_lean_ir_cpp_emit__assign__binop___closed__37;
x_111 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_110, x_5, x_107);
x_112 = lean::cnstr_get(x_111, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_111, 1);
lean::inc(x_114);
lean::dec(x_111);
x_9 = x_112;
x_10 = x_114;
goto lbl_11;
}
}
default:
{
obj* x_117; 
x_117 = lean::box(0);
x_7 = x_117;
goto lbl_8;
}
}
}
case 24:
{
obj* x_118; obj* x_119; 
x_118 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
if (lean::obj_tag(x_119) == 0)
{
obj* x_124; obj* x_126; obj* x_127; obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_124 = lean::cnstr_get(x_118, 1);
if (lean::is_exclusive(x_118)) {
 lean::cnstr_release(x_118, 0);
 x_126 = x_118;
} else {
 lean::inc(x_124);
 lean::dec(x_118);
 x_126 = lean::box(0);
}
x_127 = lean::cnstr_get(x_119, 0);
if (lean::is_exclusive(x_119)) {
 x_129 = x_119;
} else {
 lean::inc(x_127);
 lean::dec(x_119);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_127);
if (lean::is_scalar(x_126)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_126;
}
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_124);
return x_131;
}
else
{
obj* x_133; obj* x_136; obj* x_137; obj* x_138; 
lean::dec(x_119);
x_133 = lean::cnstr_get(x_118, 1);
lean::inc(x_133);
lean::dec(x_118);
x_136 = l_lean_ir_cpp_emit__infix___closed__1;
x_137 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_136, x_5, x_133);
x_138 = lean::cnstr_get(x_137, 0);
lean::inc(x_138);
if (lean::obj_tag(x_138) == 0)
{
obj* x_143; obj* x_145; obj* x_146; obj* x_148; obj* x_149; obj* x_150; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_143 = lean::cnstr_get(x_137, 1);
if (lean::is_exclusive(x_137)) {
 lean::cnstr_release(x_137, 0);
 x_145 = x_137;
} else {
 lean::inc(x_143);
 lean::dec(x_137);
 x_145 = lean::box(0);
}
x_146 = lean::cnstr_get(x_138, 0);
if (lean::is_exclusive(x_138)) {
 x_148 = x_138;
} else {
 lean::inc(x_146);
 lean::dec(x_138);
 x_148 = lean::box(0);
}
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_146);
if (lean::is_scalar(x_145)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_145;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_143);
return x_150;
}
else
{
obj* x_152; obj* x_155; obj* x_157; 
lean::dec(x_138);
x_152 = lean::cnstr_get(x_137, 1);
lean::inc(x_152);
lean::dec(x_137);
x_155 = lean::cnstr_get(x_5, 1);
lean::inc(x_155);
x_157 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_155, x_4);
if (lean::obj_tag(x_157) == 0)
{
obj* x_158; obj* x_159; obj* x_160; obj* x_162; 
x_158 = l_lean_ir_cpp_emit__assign__binop___closed__38;
x_159 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_158, x_5, x_152);
x_160 = lean::cnstr_get(x_159, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_159, 1);
lean::inc(x_162);
lean::dec(x_159);
x_9 = x_160;
x_10 = x_162;
goto lbl_11;
}
else
{
obj* x_165; uint8 x_168; obj* x_169; obj* x_170; uint8 x_171; 
x_165 = lean::cnstr_get(x_157, 0);
lean::inc(x_165);
lean::dec(x_157);
x_168 = lean::unbox(x_165);
x_169 = l_lean_ir_type2id___main(x_168);
x_170 = l_lean_ir_valid__assign__unop__types___closed__1;
x_171 = lean::nat_dec_eq(x_169, x_170);
lean::dec(x_169);
if (x_171 == 0)
{
obj* x_173; obj* x_174; obj* x_175; obj* x_177; 
x_173 = l_lean_ir_cpp_emit__assign__binop___closed__38;
x_174 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_173, x_5, x_152);
x_175 = lean::cnstr_get(x_174, 0);
lean::inc(x_175);
x_177 = lean::cnstr_get(x_174, 1);
lean::inc(x_177);
lean::dec(x_174);
x_9 = x_175;
x_10 = x_177;
goto lbl_11;
}
else
{
obj* x_180; obj* x_181; obj* x_182; obj* x_184; 
x_180 = l_lean_ir_cpp_emit__assign__binop___closed__39;
x_181 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_180, x_5, x_152);
x_182 = lean::cnstr_get(x_181, 0);
lean::inc(x_182);
x_184 = lean::cnstr_get(x_181, 1);
lean::inc(x_184);
lean::dec(x_181);
x_9 = x_182;
x_10 = x_184;
goto lbl_11;
}
}
}
}
}
case 25:
{
obj* x_187; obj* x_188; 
x_187 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
if (lean::obj_tag(x_188) == 0)
{
obj* x_190; obj* x_193; obj* x_195; obj* x_196; 
x_190 = lean::cnstr_get(x_187, 1);
lean::inc(x_190);
lean::dec(x_187);
x_193 = lean::cnstr_get(x_188, 0);
if (lean::is_exclusive(x_188)) {
 x_195 = x_188;
} else {
 lean::inc(x_193);
 lean::dec(x_188);
 x_195 = lean::box(0);
}
if (lean::is_scalar(x_195)) {
 x_196 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_196 = x_195;
}
lean::cnstr_set(x_196, 0, x_193);
x_9 = x_196;
x_10 = x_190;
goto lbl_11;
}
else
{
obj* x_198; obj* x_201; obj* x_202; obj* x_203; obj* x_205; 
lean::dec(x_188);
x_198 = lean::cnstr_get(x_187, 1);
lean::inc(x_198);
lean::dec(x_187);
x_201 = l_lean_ir_cpp_emit__assign__binop___closed__40;
x_202 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_201, x_5, x_198);
x_203 = lean::cnstr_get(x_202, 0);
lean::inc(x_203);
x_205 = lean::cnstr_get(x_202, 1);
lean::inc(x_205);
lean::dec(x_202);
x_9 = x_203;
x_10 = x_205;
goto lbl_11;
}
}
default:
{
obj* x_208; obj* x_209; 
x_208 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_209 = lean::cnstr_get(x_208, 0);
lean::inc(x_209);
if (lean::obj_tag(x_209) == 0)
{
obj* x_211; obj* x_214; obj* x_216; obj* x_217; 
x_211 = lean::cnstr_get(x_208, 1);
lean::inc(x_211);
lean::dec(x_208);
x_214 = lean::cnstr_get(x_209, 0);
if (lean::is_exclusive(x_209)) {
 x_216 = x_209;
} else {
 lean::inc(x_214);
 lean::dec(x_209);
 x_216 = lean::box(0);
}
if (lean::is_scalar(x_216)) {
 x_217 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_217 = x_216;
}
lean::cnstr_set(x_217, 0, x_214);
x_9 = x_217;
x_10 = x_211;
goto lbl_11;
}
else
{
obj* x_219; obj* x_222; obj* x_223; obj* x_224; obj* x_226; 
lean::dec(x_209);
x_219 = lean::cnstr_get(x_208, 1);
lean::inc(x_219);
lean::dec(x_208);
x_222 = l_lean_ir_cpp_emit__assign__binop___closed__41;
x_223 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_222, x_5, x_219);
x_224 = lean::cnstr_get(x_223, 0);
lean::inc(x_224);
x_226 = lean::cnstr_get(x_223, 1);
lean::inc(x_226);
lean::dec(x_223);
x_9 = x_224;
x_10 = x_226;
goto lbl_11;
}
}
}
lbl_8:
{
obj* x_230; obj* x_231; obj* x_233; obj* x_234; 
lean::dec(x_7);
x_233 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_234 = lean::cnstr_get(x_233, 0);
lean::inc(x_234);
if (lean::obj_tag(x_234) == 0)
{
obj* x_236; obj* x_239; obj* x_241; obj* x_242; 
x_236 = lean::cnstr_get(x_233, 1);
lean::inc(x_236);
lean::dec(x_233);
x_239 = lean::cnstr_get(x_234, 0);
if (lean::is_exclusive(x_234)) {
 x_241 = x_234;
} else {
 lean::inc(x_239);
 lean::dec(x_234);
 x_241 = lean::box(0);
}
if (lean::is_scalar(x_241)) {
 x_242 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_242 = x_241;
}
lean::cnstr_set(x_242, 0, x_239);
x_230 = x_242;
x_231 = x_236;
goto lbl_232;
}
else
{
obj* x_244; obj* x_247; obj* x_248; obj* x_249; 
lean::dec(x_234);
x_244 = lean::cnstr_get(x_233, 1);
lean::inc(x_244);
lean::dec(x_233);
x_247 = l_lean_ir_cpp_emit__assign__binop___closed__1;
x_248 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_247, x_5, x_244);
x_249 = lean::cnstr_get(x_248, 0);
lean::inc(x_249);
if (lean::obj_tag(x_249) == 0)
{
obj* x_251; obj* x_254; obj* x_256; obj* x_257; 
x_251 = lean::cnstr_get(x_248, 1);
lean::inc(x_251);
lean::dec(x_248);
x_254 = lean::cnstr_get(x_249, 0);
if (lean::is_exclusive(x_249)) {
 x_256 = x_249;
} else {
 lean::inc(x_254);
 lean::dec(x_249);
 x_256 = lean::box(0);
}
if (lean::is_scalar(x_256)) {
 x_257 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_257 = x_256;
}
lean::cnstr_set(x_257, 0, x_254);
x_230 = x_257;
x_231 = x_251;
goto lbl_232;
}
else
{
obj* x_259; obj* x_263; obj* x_264; obj* x_266; 
lean::dec(x_249);
x_259 = lean::cnstr_get(x_248, 1);
lean::inc(x_259);
lean::dec(x_248);
lean::inc(x_5);
x_263 = l_lean_ir_cpp_emit__template__param(x_1, x_5, x_259);
x_264 = lean::cnstr_get(x_263, 0);
lean::inc(x_264);
x_266 = lean::cnstr_get(x_263, 1);
lean::inc(x_266);
lean::dec(x_263);
x_230 = x_264;
x_231 = x_266;
goto lbl_232;
}
}
lbl_232:
{
if (lean::obj_tag(x_230) == 0)
{
obj* x_272; obj* x_274; obj* x_275; obj* x_276; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_272 = lean::cnstr_get(x_230, 0);
if (lean::is_exclusive(x_230)) {
 x_274 = x_230;
} else {
 lean::inc(x_272);
 lean::dec(x_230);
 x_274 = lean::box(0);
}
if (lean::is_scalar(x_274)) {
 x_275 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_275 = x_274;
}
lean::cnstr_set(x_275, 0, x_272);
x_276 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_276, 0, x_275);
lean::cnstr_set(x_276, 1, x_231);
return x_276;
}
else
{
obj* x_278; obj* x_279; obj* x_280; 
lean::dec(x_230);
x_278 = l_prod_has__repr___rarg___closed__1;
x_279 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_278, x_5, x_231);
x_280 = lean::cnstr_get(x_279, 0);
lean::inc(x_280);
if (lean::obj_tag(x_280) == 0)
{
obj* x_285; obj* x_287; obj* x_288; obj* x_290; obj* x_291; obj* x_292; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_285 = lean::cnstr_get(x_279, 1);
if (lean::is_exclusive(x_279)) {
 lean::cnstr_release(x_279, 0);
 x_287 = x_279;
} else {
 lean::inc(x_285);
 lean::dec(x_279);
 x_287 = lean::box(0);
}
x_288 = lean::cnstr_get(x_280, 0);
if (lean::is_exclusive(x_280)) {
 x_290 = x_280;
} else {
 lean::inc(x_288);
 lean::dec(x_280);
 x_290 = lean::box(0);
}
if (lean::is_scalar(x_290)) {
 x_291 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_291 = x_290;
}
lean::cnstr_set(x_291, 0, x_288);
if (lean::is_scalar(x_287)) {
 x_292 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_292 = x_287;
}
lean::cnstr_set(x_292, 0, x_291);
lean::cnstr_set(x_292, 1, x_285);
return x_292;
}
else
{
obj* x_294; obj* x_297; obj* x_298; 
lean::dec(x_280);
x_294 = lean::cnstr_get(x_279, 1);
lean::inc(x_294);
lean::dec(x_279);
x_297 = l_lean_ir_cpp_emit__var(x_3, x_5, x_294);
x_298 = lean::cnstr_get(x_297, 0);
lean::inc(x_298);
if (lean::obj_tag(x_298) == 0)
{
obj* x_302; obj* x_304; obj* x_305; obj* x_307; obj* x_308; obj* x_309; 
lean::dec(x_5);
lean::dec(x_4);
x_302 = lean::cnstr_get(x_297, 1);
if (lean::is_exclusive(x_297)) {
 lean::cnstr_release(x_297, 0);
 x_304 = x_297;
} else {
 lean::inc(x_302);
 lean::dec(x_297);
 x_304 = lean::box(0);
}
x_305 = lean::cnstr_get(x_298, 0);
if (lean::is_exclusive(x_298)) {
 x_307 = x_298;
} else {
 lean::inc(x_305);
 lean::dec(x_298);
 x_307 = lean::box(0);
}
if (lean::is_scalar(x_307)) {
 x_308 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_308 = x_307;
}
lean::cnstr_set(x_308, 0, x_305);
if (lean::is_scalar(x_304)) {
 x_309 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_309 = x_304;
}
lean::cnstr_set(x_309, 0, x_308);
lean::cnstr_set(x_309, 1, x_302);
return x_309;
}
else
{
obj* x_311; obj* x_314; obj* x_315; obj* x_316; 
lean::dec(x_298);
x_311 = lean::cnstr_get(x_297, 1);
lean::inc(x_311);
lean::dec(x_297);
x_314 = l_list_repr__aux___main___rarg___closed__1;
x_315 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_314, x_5, x_311);
x_316 = lean::cnstr_get(x_315, 0);
lean::inc(x_316);
if (lean::obj_tag(x_316) == 0)
{
obj* x_320; obj* x_322; obj* x_323; obj* x_325; obj* x_326; obj* x_327; 
lean::dec(x_5);
lean::dec(x_4);
x_320 = lean::cnstr_get(x_315, 1);
if (lean::is_exclusive(x_315)) {
 lean::cnstr_release(x_315, 0);
 x_322 = x_315;
} else {
 lean::inc(x_320);
 lean::dec(x_315);
 x_322 = lean::box(0);
}
x_323 = lean::cnstr_get(x_316, 0);
if (lean::is_exclusive(x_316)) {
 x_325 = x_316;
} else {
 lean::inc(x_323);
 lean::dec(x_316);
 x_325 = lean::box(0);
}
if (lean::is_scalar(x_325)) {
 x_326 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_326 = x_325;
}
lean::cnstr_set(x_326, 0, x_323);
if (lean::is_scalar(x_322)) {
 x_327 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_327 = x_322;
}
lean::cnstr_set(x_327, 0, x_326);
lean::cnstr_set(x_327, 1, x_320);
return x_327;
}
else
{
obj* x_329; obj* x_332; obj* x_333; 
lean::dec(x_316);
x_329 = lean::cnstr_get(x_315, 1);
lean::inc(x_329);
lean::dec(x_315);
x_332 = l_lean_ir_cpp_emit__var(x_4, x_5, x_329);
x_333 = lean::cnstr_get(x_332, 0);
lean::inc(x_333);
if (lean::obj_tag(x_333) == 0)
{
obj* x_336; obj* x_338; obj* x_339; obj* x_341; obj* x_342; obj* x_343; 
lean::dec(x_5);
x_336 = lean::cnstr_get(x_332, 1);
if (lean::is_exclusive(x_332)) {
 lean::cnstr_release(x_332, 0);
 x_338 = x_332;
} else {
 lean::inc(x_336);
 lean::dec(x_332);
 x_338 = lean::box(0);
}
x_339 = lean::cnstr_get(x_333, 0);
if (lean::is_exclusive(x_333)) {
 x_341 = x_333;
} else {
 lean::inc(x_339);
 lean::dec(x_333);
 x_341 = lean::box(0);
}
if (lean::is_scalar(x_341)) {
 x_342 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_342 = x_341;
}
lean::cnstr_set(x_342, 0, x_339);
if (lean::is_scalar(x_338)) {
 x_343 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_343 = x_338;
}
lean::cnstr_set(x_343, 0, x_342);
lean::cnstr_set(x_343, 1, x_336);
return x_343;
}
else
{
obj* x_344; obj* x_347; obj* x_350; obj* x_351; obj* x_353; 
x_344 = lean::cnstr_get(x_332, 1);
lean::inc(x_344);
lean::dec(x_332);
x_347 = lean::cnstr_get(x_333, 0);
lean::inc(x_347);
lean::dec(x_333);
x_350 = l_option_has__repr___rarg___closed__3;
x_351 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_350, x_5, x_344);
lean::dec(x_5);
x_353 = lean::cnstr_get(x_351, 0);
lean::inc(x_353);
if (lean::obj_tag(x_353) == 0)
{
obj* x_356; obj* x_358; obj* x_359; obj* x_361; obj* x_362; obj* x_363; 
lean::dec(x_347);
x_356 = lean::cnstr_get(x_351, 1);
if (lean::is_exclusive(x_351)) {
 lean::cnstr_release(x_351, 0);
 x_358 = x_351;
} else {
 lean::inc(x_356);
 lean::dec(x_351);
 x_358 = lean::box(0);
}
x_359 = lean::cnstr_get(x_353, 0);
if (lean::is_exclusive(x_353)) {
 x_361 = x_353;
} else {
 lean::inc(x_359);
 lean::dec(x_353);
 x_361 = lean::box(0);
}
if (lean::is_scalar(x_361)) {
 x_362 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_362 = x_361;
}
lean::cnstr_set(x_362, 0, x_359);
if (lean::is_scalar(x_358)) {
 x_363 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_363 = x_358;
}
lean::cnstr_set(x_363, 0, x_362);
lean::cnstr_set(x_363, 1, x_356);
return x_363;
}
else
{
obj* x_364; obj* x_365; obj* x_367; obj* x_368; obj* x_369; 
if (lean::is_exclusive(x_353)) {
 lean::cnstr_release(x_353, 0);
 x_364 = x_353;
} else {
 lean::dec(x_353);
 x_364 = lean::box(0);
}
x_365 = lean::cnstr_get(x_351, 1);
if (lean::is_exclusive(x_351)) {
 lean::cnstr_release(x_351, 0);
 x_367 = x_351;
} else {
 lean::inc(x_365);
 lean::dec(x_351);
 x_367 = lean::box(0);
}
if (lean::is_scalar(x_364)) {
 x_368 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_368 = x_364;
}
lean::cnstr_set(x_368, 0, x_347);
if (lean::is_scalar(x_367)) {
 x_369 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_369 = x_367;
}
lean::cnstr_set(x_369, 0, x_368);
lean::cnstr_set(x_369, 1, x_365);
return x_369;
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
obj* x_373; obj* x_375; obj* x_376; obj* x_377; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_373 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_375 = x_9;
} else {
 lean::inc(x_373);
 lean::dec(x_9);
 x_375 = lean::box(0);
}
if (lean::is_scalar(x_375)) {
 x_376 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_376 = x_375;
}
lean::cnstr_set(x_376, 0, x_373);
x_377 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_377, 0, x_376);
lean::cnstr_set(x_377, 1, x_10);
return x_377;
}
else
{
obj* x_379; obj* x_380; obj* x_381; 
lean::dec(x_9);
x_379 = l_prod_has__repr___rarg___closed__1;
x_380 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_379, x_5, x_10);
x_381 = lean::cnstr_get(x_380, 0);
lean::inc(x_381);
if (lean::obj_tag(x_381) == 0)
{
obj* x_386; obj* x_388; obj* x_389; obj* x_391; obj* x_392; obj* x_393; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_386 = lean::cnstr_get(x_380, 1);
if (lean::is_exclusive(x_380)) {
 lean::cnstr_release(x_380, 0);
 x_388 = x_380;
} else {
 lean::inc(x_386);
 lean::dec(x_380);
 x_388 = lean::box(0);
}
x_389 = lean::cnstr_get(x_381, 0);
if (lean::is_exclusive(x_381)) {
 x_391 = x_381;
} else {
 lean::inc(x_389);
 lean::dec(x_381);
 x_391 = lean::box(0);
}
if (lean::is_scalar(x_391)) {
 x_392 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_392 = x_391;
}
lean::cnstr_set(x_392, 0, x_389);
if (lean::is_scalar(x_388)) {
 x_393 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_393 = x_388;
}
lean::cnstr_set(x_393, 0, x_392);
lean::cnstr_set(x_393, 1, x_386);
return x_393;
}
else
{
obj* x_395; obj* x_398; obj* x_399; 
lean::dec(x_381);
x_395 = lean::cnstr_get(x_380, 1);
lean::inc(x_395);
lean::dec(x_380);
x_398 = l_lean_ir_cpp_emit__var(x_3, x_5, x_395);
x_399 = lean::cnstr_get(x_398, 0);
lean::inc(x_399);
if (lean::obj_tag(x_399) == 0)
{
obj* x_403; obj* x_405; obj* x_406; obj* x_408; obj* x_409; obj* x_410; 
lean::dec(x_5);
lean::dec(x_4);
x_403 = lean::cnstr_get(x_398, 1);
if (lean::is_exclusive(x_398)) {
 lean::cnstr_release(x_398, 0);
 x_405 = x_398;
} else {
 lean::inc(x_403);
 lean::dec(x_398);
 x_405 = lean::box(0);
}
x_406 = lean::cnstr_get(x_399, 0);
if (lean::is_exclusive(x_399)) {
 x_408 = x_399;
} else {
 lean::inc(x_406);
 lean::dec(x_399);
 x_408 = lean::box(0);
}
if (lean::is_scalar(x_408)) {
 x_409 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_409 = x_408;
}
lean::cnstr_set(x_409, 0, x_406);
if (lean::is_scalar(x_405)) {
 x_410 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_410 = x_405;
}
lean::cnstr_set(x_410, 0, x_409);
lean::cnstr_set(x_410, 1, x_403);
return x_410;
}
else
{
obj* x_412; obj* x_415; obj* x_416; obj* x_417; 
lean::dec(x_399);
x_412 = lean::cnstr_get(x_398, 1);
lean::inc(x_412);
lean::dec(x_398);
x_415 = l_list_repr__aux___main___rarg___closed__1;
x_416 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_415, x_5, x_412);
x_417 = lean::cnstr_get(x_416, 0);
lean::inc(x_417);
if (lean::obj_tag(x_417) == 0)
{
obj* x_421; obj* x_423; obj* x_424; obj* x_426; obj* x_427; obj* x_428; 
lean::dec(x_5);
lean::dec(x_4);
x_421 = lean::cnstr_get(x_416, 1);
if (lean::is_exclusive(x_416)) {
 lean::cnstr_release(x_416, 0);
 x_423 = x_416;
} else {
 lean::inc(x_421);
 lean::dec(x_416);
 x_423 = lean::box(0);
}
x_424 = lean::cnstr_get(x_417, 0);
if (lean::is_exclusive(x_417)) {
 x_426 = x_417;
} else {
 lean::inc(x_424);
 lean::dec(x_417);
 x_426 = lean::box(0);
}
if (lean::is_scalar(x_426)) {
 x_427 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_427 = x_426;
}
lean::cnstr_set(x_427, 0, x_424);
if (lean::is_scalar(x_423)) {
 x_428 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_428 = x_423;
}
lean::cnstr_set(x_428, 0, x_427);
lean::cnstr_set(x_428, 1, x_421);
return x_428;
}
else
{
obj* x_430; obj* x_433; obj* x_434; 
lean::dec(x_417);
x_430 = lean::cnstr_get(x_416, 1);
lean::inc(x_430);
lean::dec(x_416);
x_433 = l_lean_ir_cpp_emit__var(x_4, x_5, x_430);
x_434 = lean::cnstr_get(x_433, 0);
lean::inc(x_434);
if (lean::obj_tag(x_434) == 0)
{
obj* x_437; obj* x_439; obj* x_440; obj* x_442; obj* x_443; obj* x_444; 
lean::dec(x_5);
x_437 = lean::cnstr_get(x_433, 1);
if (lean::is_exclusive(x_433)) {
 lean::cnstr_release(x_433, 0);
 x_439 = x_433;
} else {
 lean::inc(x_437);
 lean::dec(x_433);
 x_439 = lean::box(0);
}
x_440 = lean::cnstr_get(x_434, 0);
if (lean::is_exclusive(x_434)) {
 x_442 = x_434;
} else {
 lean::inc(x_440);
 lean::dec(x_434);
 x_442 = lean::box(0);
}
if (lean::is_scalar(x_442)) {
 x_443 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_443 = x_442;
}
lean::cnstr_set(x_443, 0, x_440);
if (lean::is_scalar(x_439)) {
 x_444 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_444 = x_439;
}
lean::cnstr_set(x_444, 0, x_443);
lean::cnstr_set(x_444, 1, x_437);
return x_444;
}
else
{
obj* x_445; obj* x_448; obj* x_451; obj* x_452; obj* x_454; 
x_445 = lean::cnstr_get(x_433, 1);
lean::inc(x_445);
lean::dec(x_433);
x_448 = lean::cnstr_get(x_434, 0);
lean::inc(x_448);
lean::dec(x_434);
x_451 = l_option_has__repr___rarg___closed__3;
x_452 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_451, x_5, x_445);
lean::dec(x_5);
x_454 = lean::cnstr_get(x_452, 0);
lean::inc(x_454);
if (lean::obj_tag(x_454) == 0)
{
obj* x_457; obj* x_459; obj* x_460; obj* x_462; obj* x_463; obj* x_464; 
lean::dec(x_448);
x_457 = lean::cnstr_get(x_452, 1);
if (lean::is_exclusive(x_452)) {
 lean::cnstr_release(x_452, 0);
 x_459 = x_452;
} else {
 lean::inc(x_457);
 lean::dec(x_452);
 x_459 = lean::box(0);
}
x_460 = lean::cnstr_get(x_454, 0);
if (lean::is_exclusive(x_454)) {
 x_462 = x_454;
} else {
 lean::inc(x_460);
 lean::dec(x_454);
 x_462 = lean::box(0);
}
if (lean::is_scalar(x_462)) {
 x_463 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_463 = x_462;
}
lean::cnstr_set(x_463, 0, x_460);
if (lean::is_scalar(x_459)) {
 x_464 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_464 = x_459;
}
lean::cnstr_set(x_464, 0, x_463);
lean::cnstr_set(x_464, 1, x_457);
return x_464;
}
else
{
obj* x_465; obj* x_466; obj* x_468; obj* x_469; obj* x_470; 
if (lean::is_exclusive(x_454)) {
 lean::cnstr_release(x_454, 0);
 x_465 = x_454;
} else {
 lean::dec(x_454);
 x_465 = lean::box(0);
}
x_466 = lean::cnstr_get(x_452, 1);
if (lean::is_exclusive(x_452)) {
 lean::cnstr_release(x_452, 0);
 x_468 = x_452;
} else {
 lean::inc(x_466);
 lean::dec(x_452);
 x_468 = lean::box(0);
}
if (lean::is_scalar(x_465)) {
 x_469 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_469 = x_465;
}
lean::cnstr_set(x_469, 0, x_448);
if (lean::is_scalar(x_468)) {
 x_470 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_470 = x_468;
}
lean::cnstr_set(x_470, 0, x_469);
lean::cnstr_set(x_470, 1, x_466);
return x_470;
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_8 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_14; obj* x_16; obj* x_17; 
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
x_5 = x_17;
x_6 = x_11;
goto lbl_7;
}
else
{
obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_26; 
lean::dec(x_9);
x_19 = lean::cnstr_get(x_8, 1);
lean::inc(x_19);
lean::dec(x_8);
x_22 = l_lean_ir_cpp_emit__infix___closed__1;
x_23 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_3, x_19);
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
obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_2);
x_30 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_32 = x_5;
} else {
 lean::inc(x_30);
 lean::dec(x_5);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_6);
return x_34;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_5);
x_36 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1, x_3, x_6);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_2);
x_40 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 x_42 = x_36;
} else {
 lean::inc(x_40);
 lean::dec(x_36);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_43);
if (lean::is_scalar(x_42)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_42;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_40);
return x_47;
}
else
{
obj* x_49; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_37);
x_49 = lean::cnstr_get(x_36, 1);
lean::inc(x_49);
lean::dec(x_36);
x_52 = l_prod_has__repr___rarg___closed__1;
x_53 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_52, x_3, x_49);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_2);
x_57 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 x_59 = x_53;
} else {
 lean::inc(x_57);
 lean::dec(x_53);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_54, 0);
if (lean::is_exclusive(x_54)) {
 x_62 = x_54;
} else {
 lean::inc(x_60);
 lean::dec(x_54);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_60);
if (lean::is_scalar(x_59)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_59;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_57);
return x_64;
}
else
{
obj* x_66; obj* x_69; obj* x_70; 
lean::dec(x_54);
x_66 = lean::cnstr_get(x_53, 1);
lean::inc(x_66);
lean::dec(x_53);
x_69 = l_lean_ir_cpp_emit__var(x_2, x_3, x_66);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_79; 
x_72 = lean::cnstr_get(x_69, 1);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 x_74 = x_69;
} else {
 lean::inc(x_72);
 lean::dec(x_69);
 x_74 = lean::box(0);
}
x_75 = lean::cnstr_get(x_70, 0);
if (lean::is_exclusive(x_70)) {
 x_77 = x_70;
} else {
 lean::inc(x_75);
 lean::dec(x_70);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
if (lean::is_scalar(x_74)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_74;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_72);
return x_79;
}
else
{
obj* x_80; obj* x_83; obj* x_86; obj* x_87; obj* x_88; 
x_80 = lean::cnstr_get(x_69, 1);
lean::inc(x_80);
lean::dec(x_69);
x_83 = lean::cnstr_get(x_70, 0);
lean::inc(x_83);
lean::dec(x_70);
x_86 = l_option_has__repr___rarg___closed__3;
x_87 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_86, x_3, x_80);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
if (lean::obj_tag(x_88) == 0)
{
obj* x_91; obj* x_93; obj* x_94; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_83);
x_91 = lean::cnstr_get(x_87, 1);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 x_93 = x_87;
} else {
 lean::inc(x_91);
 lean::dec(x_87);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_88, 0);
if (lean::is_exclusive(x_88)) {
 x_96 = x_88;
} else {
 lean::inc(x_94);
 lean::dec(x_88);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_94);
if (lean::is_scalar(x_93)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_93;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_91);
return x_98;
}
else
{
obj* x_99; obj* x_100; obj* x_102; obj* x_103; obj* x_104; 
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 x_99 = x_88;
} else {
 lean::dec(x_88);
 x_99 = lean::box(0);
}
x_100 = lean::cnstr_get(x_87, 1);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 x_102 = x_87;
} else {
 lean::inc(x_100);
 lean::dec(x_87);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_103 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_103 = x_99;
}
lean::cnstr_set(x_103, 0, x_83);
if (lean::is_scalar(x_102)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_102;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_100);
return x_104;
}
}
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__x__op__y___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_ir_cpp_emit__x__op__y(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_3);
return x_5;
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
return x_6;
}
else
{
obj* x_7; 
x_7 = l_lean_ir_cpp_assign__unop2cpp___main___closed__2;
return x_7;
}
}
case 1:
{
obj* x_8; 
x_8 = l_int_repr___main___closed__2;
return x_8;
}
case 2:
{
obj* x_9; 
x_9 = l_lean_ir_cpp_assign__unop2cpp___main___closed__3;
return x_9;
}
case 3:
{
obj* x_10; 
x_10 = l_lean_ir_cpp_assign__unop2cpp___main___closed__4;
return x_10;
}
case 4:
{
obj* x_11; 
x_11 = l_lean_ir_cpp_assign__unop2cpp___main___closed__5;
return x_11;
}
case 5:
{
obj* x_12; 
x_12 = l_lean_ir_cpp_assign__unop2cpp___main___closed__6;
return x_12;
}
case 6:
{
obj* x_13; 
x_13 = l_lean_ir_cpp_assign__unop2cpp___main___closed__7;
return x_13;
}
case 7:
{
obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_14 = l_lean_ir_cpp_type2cpp___main(x_0);
x_15 = l_lean_ir_cpp_assign__unop2cpp___main___closed__8;
x_16 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_18 = l_lean_ir_cpp_emit__template__params___closed__4;
x_19 = lean::string_append(x_16, x_18);
return x_19;
}
case 8:
{
obj* x_20; 
x_20 = l_lean_ir_cpp_assign__unop2cpp___main___closed__9;
return x_20;
}
case 9:
{
obj* x_21; 
x_21 = l_lean_ir_cpp_assign__unop2cpp___main___closed__10;
return x_21;
}
case 10:
{
obj* x_22; 
x_22 = l_lean_ir_cpp_assign__unop2cpp___main___closed__11;
return x_22;
}
case 11:
{
obj* x_23; 
x_23 = l_lean_ir_cpp_assign__unop2cpp___main___closed__12;
return x_23;
}
case 12:
{
obj* x_24; 
x_24 = l_lean_ir_cpp_assign__unop2cpp___main___closed__13;
return x_24;
}
case 13:
{
obj* x_25; 
x_25 = l_lean_ir_cpp_assign__unop2cpp___main___closed__14;
return x_25;
}
case 14:
{
obj* x_26; 
x_26 = l_lean_ir_cpp_assign__unop2cpp___main___closed__15;
return x_26;
}
case 15:
{
obj* x_27; 
x_27 = l_lean_ir_cpp_assign__unop2cpp___main___closed__16;
return x_27;
}
case 16:
{
obj* x_28; 
x_28 = l_lean_ir_cpp_assign__unop2cpp___main___closed__17;
return x_28;
}
default:
{
obj* x_29; 
x_29 = l_lean_ir_cpp_assign__unop2cpp___main___closed__18;
return x_29;
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
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_6 = l_lean_ir_cpp_assign__unop2cpp___main(x_1, x_2);
x_10 = l_lean_ir_cpp_emit__var(x_0, x_4, x_5);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_16; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_18 = x_11;
} else {
 lean::inc(x_16);
 lean::dec(x_11);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
x_7 = x_19;
x_8 = x_13;
goto lbl_9;
}
else
{
obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_28; 
lean::dec(x_11);
x_21 = lean::cnstr_get(x_10, 1);
lean::inc(x_21);
lean::dec(x_10);
x_24 = l_lean_ir_cpp_emit__infix___closed__1;
x_25 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_24, x_4, x_21);
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
obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_6);
lean::dec(x_3);
x_33 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_35 = x_7;
} else {
 lean::inc(x_33);
 lean::dec(x_7);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_8);
return x_37;
}
else
{
obj* x_39; obj* x_41; 
lean::dec(x_7);
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_6, x_4, x_8);
lean::dec(x_6);
x_41 = lean::cnstr_get(x_39, 0);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_3);
x_44 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 lean::cnstr_release(x_39, 0);
 x_46 = x_39;
} else {
 lean::inc(x_44);
 lean::dec(x_39);
 x_46 = lean::box(0);
}
x_47 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_49 = x_41;
} else {
 lean::inc(x_47);
 lean::dec(x_41);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_47);
if (lean::is_scalar(x_46)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_46;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_44);
return x_51;
}
else
{
obj* x_53; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_41);
x_53 = lean::cnstr_get(x_39, 1);
lean::inc(x_53);
lean::dec(x_39);
x_56 = l_prod_has__repr___rarg___closed__1;
x_57 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_56, x_4, x_53);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
if (lean::obj_tag(x_58) == 0)
{
obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_3);
x_61 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 x_63 = x_57;
} else {
 lean::inc(x_61);
 lean::dec(x_57);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_58, 0);
if (lean::is_exclusive(x_58)) {
 x_66 = x_58;
} else {
 lean::inc(x_64);
 lean::dec(x_58);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_64);
if (lean::is_scalar(x_63)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_63;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_61);
return x_68;
}
else
{
obj* x_70; obj* x_73; obj* x_74; 
lean::dec(x_58);
x_70 = lean::cnstr_get(x_57, 1);
lean::inc(x_70);
lean::dec(x_57);
x_73 = l_lean_ir_cpp_emit__var(x_3, x_4, x_70);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
if (lean::obj_tag(x_74) == 0)
{
obj* x_76; obj* x_78; obj* x_79; obj* x_81; obj* x_82; obj* x_83; 
x_76 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_78 = x_73;
} else {
 lean::inc(x_76);
 lean::dec(x_73);
 x_78 = lean::box(0);
}
x_79 = lean::cnstr_get(x_74, 0);
if (lean::is_exclusive(x_74)) {
 x_81 = x_74;
} else {
 lean::inc(x_79);
 lean::dec(x_74);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_79);
if (lean::is_scalar(x_78)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_78;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_76);
return x_83;
}
else
{
obj* x_84; obj* x_87; obj* x_90; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_73, 1);
lean::inc(x_84);
lean::dec(x_73);
x_87 = lean::cnstr_get(x_74, 0);
lean::inc(x_87);
lean::dec(x_74);
x_90 = l_option_has__repr___rarg___closed__3;
x_91 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_90, x_4, x_84);
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
if (lean::obj_tag(x_92) == 0)
{
obj* x_95; obj* x_97; obj* x_98; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_87);
x_95 = lean::cnstr_get(x_91, 1);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 x_97 = x_91;
} else {
 lean::inc(x_95);
 lean::dec(x_91);
 x_97 = lean::box(0);
}
x_98 = lean::cnstr_get(x_92, 0);
if (lean::is_exclusive(x_92)) {
 x_100 = x_92;
} else {
 lean::inc(x_98);
 lean::dec(x_92);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
if (lean::is_scalar(x_97)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_97;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_95);
return x_102;
}
else
{
obj* x_103; obj* x_104; obj* x_106; obj* x_107; obj* x_108; 
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 x_103 = x_92;
} else {
 lean::dec(x_92);
 x_103 = lean::box(0);
}
x_104 = lean::cnstr_get(x_91, 1);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 x_106 = x_91;
} else {
 lean::inc(x_104);
 lean::dec(x_91);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_107 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_107 = x_103;
}
lean::cnstr_set(x_107, 0, x_87);
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_106;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_104);
return x_108;
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
lean::dec(x_4);
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
case 3:
{
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_cpp_emit__num__suffix___main___closed__1;
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
return x_4;
}
case 4:
{
obj* x_5; obj* x_6; 
x_5 = l_lean_ir_cpp_emit__num__suffix___main___closed__2;
x_6 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_5, x_1, x_2);
return x_6;
}
case 8:
{
obj* x_7; obj* x_8; 
x_7 = l_lean_ir_cpp_emit__num__suffix___main___closed__3;
x_8 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_7, x_1, x_2);
return x_8;
}
default:
{
obj* x_9; obj* x_10; 
x_9 = l_lean_ir_match__type___closed__5;
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
return x_10;
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
lean::dec(x_1);
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
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_3 = l_int_repr___main(x_0);
x_4 = lean::string_append(x_2, x_3);
lean::dec(x_3);
x_6 = l_lean_ir_match__type___closed__5;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
return x_7;
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
obj* x_7; obj* x_8; 
x_7 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_12 = x_7;
} else {
 lean::inc(x_10);
 lean::dec(x_7);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_15 = x_8;
} else {
 lean::inc(x_13);
 lean::dec(x_8);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
if (lean::is_scalar(x_12)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_12;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_23; 
lean::dec(x_8);
x_19 = lean::cnstr_get(x_7, 1);
lean::inc(x_19);
lean::dec(x_7);
x_22 = l_lean_ir_cpp_emit__assign__lit___closed__1;
x_23 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_3, x_19);
return x_23;
}
}
else
{
obj* x_24; obj* x_25; 
x_24 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
x_27 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_29 = x_24;
} else {
 lean::inc(x_27);
 lean::dec(x_24);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_32 = x_25;
} else {
 lean::inc(x_30);
 lean::dec(x_25);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
if (lean::is_scalar(x_29)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_29;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_27);
return x_34;
}
else
{
obj* x_36; obj* x_39; obj* x_40; 
lean::dec(x_25);
x_36 = lean::cnstr_get(x_24, 1);
lean::inc(x_36);
lean::dec(x_24);
x_39 = l_lean_ir_cpp_emit__assign__lit___closed__2;
x_40 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_39, x_3, x_36);
return x_40;
}
}
}
case 1:
{
obj* x_41; obj* x_44; obj* x_45; 
x_41 = lean::cnstr_get(x_2, 0);
lean::inc(x_41);
lean::dec(x_2);
x_44 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
if (lean::obj_tag(x_45) == 0)
{
obj* x_48; obj* x_50; obj* x_51; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_41);
x_48 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 x_50 = x_44;
} else {
 lean::inc(x_48);
 lean::dec(x_44);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_45, 0);
if (lean::is_exclusive(x_45)) {
 x_53 = x_45;
} else {
 lean::inc(x_51);
 lean::dec(x_45);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
if (lean::is_scalar(x_50)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_50;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_48);
return x_55;
}
else
{
obj* x_57; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_45);
x_57 = lean::cnstr_get(x_44, 1);
lean::inc(x_57);
lean::dec(x_44);
x_60 = l_lean_ir_cpp_emit__assign__lit___closed__3;
x_61 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_60, x_3, x_57);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_41);
x_65 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 x_67 = x_61;
} else {
 lean::inc(x_65);
 lean::dec(x_61);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_70 = x_62;
} else {
 lean::inc(x_68);
 lean::dec(x_62);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_68);
if (lean::is_scalar(x_67)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_67;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_65);
return x_72;
}
else
{
obj* x_74; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_62);
x_74 = lean::cnstr_get(x_61, 1);
lean::inc(x_74);
lean::dec(x_61);
x_77 = l_string_quote(x_41);
x_78 = l_prod_has__repr___rarg___closed__1;
x_79 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_78, x_3, x_74);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
if (lean::obj_tag(x_80) == 0)
{
obj* x_83; obj* x_85; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_77);
x_83 = lean::cnstr_get(x_79, 1);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_release(x_79, 0);
 x_85 = x_79;
} else {
 lean::inc(x_83);
 lean::dec(x_79);
 x_85 = lean::box(0);
}
x_86 = lean::cnstr_get(x_80, 0);
if (lean::is_exclusive(x_80)) {
 x_88 = x_80;
} else {
 lean::inc(x_86);
 lean::dec(x_80);
 x_88 = lean::box(0);
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_86);
if (lean::is_scalar(x_85)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_85;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_83);
return x_90;
}
else
{
obj* x_92; obj* x_95; obj* x_97; 
lean::dec(x_80);
x_92 = lean::cnstr_get(x_79, 1);
lean::inc(x_92);
lean::dec(x_79);
x_95 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_77, x_3, x_92);
lean::dec(x_77);
x_97 = lean::cnstr_get(x_95, 0);
lean::inc(x_97);
if (lean::obj_tag(x_97) == 0)
{
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_105; obj* x_106; 
x_99 = lean::cnstr_get(x_95, 1);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 x_101 = x_95;
} else {
 lean::inc(x_99);
 lean::dec(x_95);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_97, 0);
if (lean::is_exclusive(x_97)) {
 x_104 = x_97;
} else {
 lean::inc(x_102);
 lean::dec(x_97);
 x_104 = lean::box(0);
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_102);
if (lean::is_scalar(x_101)) {
 x_106 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_106 = x_101;
}
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_99);
return x_106;
}
else
{
obj* x_107; obj* x_110; obj* x_113; obj* x_114; obj* x_115; 
x_107 = lean::cnstr_get(x_95, 1);
lean::inc(x_107);
lean::dec(x_95);
x_110 = lean::cnstr_get(x_97, 0);
lean::inc(x_110);
lean::dec(x_97);
x_113 = l_option_has__repr___rarg___closed__3;
x_114 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_113, x_3, x_107);
x_115 = lean::cnstr_get(x_114, 0);
lean::inc(x_115);
if (lean::obj_tag(x_115) == 0)
{
obj* x_118; obj* x_120; obj* x_121; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_110);
x_118 = lean::cnstr_get(x_114, 1);
if (lean::is_exclusive(x_114)) {
 lean::cnstr_release(x_114, 0);
 x_120 = x_114;
} else {
 lean::inc(x_118);
 lean::dec(x_114);
 x_120 = lean::box(0);
}
x_121 = lean::cnstr_get(x_115, 0);
if (lean::is_exclusive(x_115)) {
 x_123 = x_115;
} else {
 lean::inc(x_121);
 lean::dec(x_115);
 x_123 = lean::box(0);
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_121);
if (lean::is_scalar(x_120)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_120;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_118);
return x_125;
}
else
{
obj* x_126; obj* x_127; obj* x_129; obj* x_130; obj* x_131; 
if (lean::is_exclusive(x_115)) {
 lean::cnstr_release(x_115, 0);
 x_126 = x_115;
} else {
 lean::dec(x_115);
 x_126 = lean::box(0);
}
x_127 = lean::cnstr_get(x_114, 1);
if (lean::is_exclusive(x_114)) {
 lean::cnstr_release(x_114, 0);
 x_129 = x_114;
} else {
 lean::inc(x_127);
 lean::dec(x_114);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_130 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_130 = x_126;
}
lean::cnstr_set(x_130, 0, x_110);
if (lean::is_scalar(x_129)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_129;
}
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_127);
return x_131;
}
}
}
}
}
}
case 2:
{
obj* x_132; obj* x_135; 
x_132 = lean::cnstr_get(x_2, 0);
lean::inc(x_132);
lean::dec(x_2);
switch (x_1) {
case 11:
{
obj* x_137; uint8 x_138; obj* x_139; obj* x_140; obj* x_142; obj* x_143; 
x_137 = l_lean_ir_cpp_emit__assign__lit___closed__4;
x_138 = lean::int_dec_lt(x_132, x_137);
x_142 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
if (lean::obj_tag(x_143) == 0)
{
obj* x_145; obj* x_148; obj* x_150; obj* x_151; 
x_145 = lean::cnstr_get(x_142, 1);
lean::inc(x_145);
lean::dec(x_142);
x_148 = lean::cnstr_get(x_143, 0);
if (lean::is_exclusive(x_143)) {
 x_150 = x_143;
} else {
 lean::inc(x_148);
 lean::dec(x_143);
 x_150 = lean::box(0);
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_148);
x_139 = x_151;
x_140 = x_145;
goto lbl_141;
}
else
{
obj* x_153; obj* x_156; obj* x_157; obj* x_158; obj* x_160; 
lean::dec(x_143);
x_153 = lean::cnstr_get(x_142, 1);
lean::inc(x_153);
lean::dec(x_142);
x_156 = l_lean_ir_cpp_emit__infix___closed__1;
x_157 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_156, x_3, x_153);
x_158 = lean::cnstr_get(x_157, 0);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_157, 1);
lean::inc(x_160);
lean::dec(x_157);
x_139 = x_158;
x_140 = x_160;
goto lbl_141;
}
lbl_141:
{
if (lean::obj_tag(x_139) == 0)
{
obj* x_164; obj* x_166; obj* x_167; obj* x_168; 
lean::dec(x_132);
x_164 = lean::cnstr_get(x_139, 0);
if (lean::is_exclusive(x_139)) {
 x_166 = x_139;
} else {
 lean::inc(x_164);
 lean::dec(x_139);
 x_166 = lean::box(0);
}
if (lean::is_scalar(x_166)) {
 x_167 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_167 = x_166;
}
lean::cnstr_set(x_167, 0, x_164);
x_168 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_140);
return x_168;
}
else
{
lean::dec(x_139);
if (x_138 == 0)
{
obj* x_170; obj* x_171; obj* x_172; 
x_170 = l_lean_ir_cpp_emit__assign__lit___closed__5;
x_171 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_170, x_3, x_140);
x_172 = lean::cnstr_get(x_171, 0);
lean::inc(x_172);
if (lean::obj_tag(x_172) == 0)
{
obj* x_175; obj* x_177; obj* x_178; obj* x_180; obj* x_181; obj* x_182; 
lean::dec(x_132);
x_175 = lean::cnstr_get(x_171, 1);
if (lean::is_exclusive(x_171)) {
 lean::cnstr_release(x_171, 0);
 x_177 = x_171;
} else {
 lean::inc(x_175);
 lean::dec(x_171);
 x_177 = lean::box(0);
}
x_178 = lean::cnstr_get(x_172, 0);
if (lean::is_exclusive(x_172)) {
 x_180 = x_172;
} else {
 lean::inc(x_178);
 lean::dec(x_172);
 x_180 = lean::box(0);
}
if (lean::is_scalar(x_180)) {
 x_181 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_181 = x_180;
}
lean::cnstr_set(x_181, 0, x_178);
if (lean::is_scalar(x_177)) {
 x_182 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_182 = x_177;
}
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_175);
return x_182;
}
else
{
obj* x_184; obj* x_187; obj* x_189; 
lean::dec(x_172);
x_184 = lean::cnstr_get(x_171, 1);
lean::inc(x_184);
lean::dec(x_171);
x_187 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_132, x_3, x_184);
lean::dec(x_132);
x_189 = lean::cnstr_get(x_187, 0);
lean::inc(x_189);
if (lean::obj_tag(x_189) == 0)
{
obj* x_191; obj* x_193; obj* x_194; obj* x_196; obj* x_197; obj* x_198; 
x_191 = lean::cnstr_get(x_187, 1);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 x_193 = x_187;
} else {
 lean::inc(x_191);
 lean::dec(x_187);
 x_193 = lean::box(0);
}
x_194 = lean::cnstr_get(x_189, 0);
if (lean::is_exclusive(x_189)) {
 x_196 = x_189;
} else {
 lean::inc(x_194);
 lean::dec(x_189);
 x_196 = lean::box(0);
}
if (lean::is_scalar(x_196)) {
 x_197 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_197 = x_196;
}
lean::cnstr_set(x_197, 0, x_194);
if (lean::is_scalar(x_193)) {
 x_198 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_198 = x_193;
}
lean::cnstr_set(x_198, 0, x_197);
lean::cnstr_set(x_198, 1, x_191);
return x_198;
}
else
{
obj* x_200; obj* x_203; obj* x_204; 
lean::dec(x_189);
x_200 = lean::cnstr_get(x_187, 1);
lean::inc(x_200);
lean::dec(x_187);
x_203 = l_lean_ir_cpp_emit__assign__lit___closed__6;
x_204 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_203, x_3, x_200);
return x_204;
}
}
}
else
{
obj* x_205; obj* x_206; obj* x_207; 
x_205 = l_lean_ir_cpp_emit__assign__lit___closed__7;
x_206 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_205, x_3, x_140);
x_207 = lean::cnstr_get(x_206, 0);
lean::inc(x_207);
if (lean::obj_tag(x_207) == 0)
{
obj* x_210; obj* x_212; obj* x_213; obj* x_215; obj* x_216; obj* x_217; 
lean::dec(x_132);
x_210 = lean::cnstr_get(x_206, 1);
if (lean::is_exclusive(x_206)) {
 lean::cnstr_release(x_206, 0);
 x_212 = x_206;
} else {
 lean::inc(x_210);
 lean::dec(x_206);
 x_212 = lean::box(0);
}
x_213 = lean::cnstr_get(x_207, 0);
if (lean::is_exclusive(x_207)) {
 x_215 = x_207;
} else {
 lean::inc(x_213);
 lean::dec(x_207);
 x_215 = lean::box(0);
}
if (lean::is_scalar(x_215)) {
 x_216 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_216 = x_215;
}
lean::cnstr_set(x_216, 0, x_213);
if (lean::is_scalar(x_212)) {
 x_217 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_217 = x_212;
}
lean::cnstr_set(x_217, 0, x_216);
lean::cnstr_set(x_217, 1, x_210);
return x_217;
}
else
{
obj* x_219; obj* x_222; obj* x_223; obj* x_224; 
lean::dec(x_207);
x_219 = lean::cnstr_get(x_206, 1);
lean::inc(x_219);
lean::dec(x_206);
x_222 = l_prod_has__repr___rarg___closed__1;
x_223 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_222, x_3, x_219);
x_224 = lean::cnstr_get(x_223, 0);
lean::inc(x_224);
if (lean::obj_tag(x_224) == 0)
{
obj* x_227; obj* x_229; obj* x_230; obj* x_232; obj* x_233; obj* x_234; 
lean::dec(x_132);
x_227 = lean::cnstr_get(x_223, 1);
if (lean::is_exclusive(x_223)) {
 lean::cnstr_release(x_223, 0);
 x_229 = x_223;
} else {
 lean::inc(x_227);
 lean::dec(x_223);
 x_229 = lean::box(0);
}
x_230 = lean::cnstr_get(x_224, 0);
if (lean::is_exclusive(x_224)) {
 x_232 = x_224;
} else {
 lean::inc(x_230);
 lean::dec(x_224);
 x_232 = lean::box(0);
}
if (lean::is_scalar(x_232)) {
 x_233 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_233 = x_232;
}
lean::cnstr_set(x_233, 0, x_230);
if (lean::is_scalar(x_229)) {
 x_234 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_234 = x_229;
}
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_227);
return x_234;
}
else
{
obj* x_236; obj* x_239; obj* x_241; 
lean::dec(x_224);
x_236 = lean::cnstr_get(x_223, 1);
lean::inc(x_236);
lean::dec(x_223);
x_239 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_132, x_3, x_236);
lean::dec(x_132);
x_241 = lean::cnstr_get(x_239, 0);
lean::inc(x_241);
if (lean::obj_tag(x_241) == 0)
{
obj* x_243; obj* x_245; obj* x_246; obj* x_248; obj* x_249; obj* x_250; 
x_243 = lean::cnstr_get(x_239, 1);
if (lean::is_exclusive(x_239)) {
 lean::cnstr_release(x_239, 0);
 x_245 = x_239;
} else {
 lean::inc(x_243);
 lean::dec(x_239);
 x_245 = lean::box(0);
}
x_246 = lean::cnstr_get(x_241, 0);
if (lean::is_exclusive(x_241)) {
 x_248 = x_241;
} else {
 lean::inc(x_246);
 lean::dec(x_241);
 x_248 = lean::box(0);
}
if (lean::is_scalar(x_248)) {
 x_249 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_249 = x_248;
}
lean::cnstr_set(x_249, 0, x_246);
if (lean::is_scalar(x_245)) {
 x_250 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_250 = x_245;
}
lean::cnstr_set(x_250, 0, x_249);
lean::cnstr_set(x_250, 1, x_243);
return x_250;
}
else
{
obj* x_252; obj* x_255; obj* x_256; obj* x_257; 
lean::dec(x_241);
x_252 = lean::cnstr_get(x_239, 1);
lean::inc(x_252);
lean::dec(x_239);
x_255 = l_lean_ir_cpp_emit__num__suffix___main___closed__1;
x_256 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_255, x_3, x_252);
x_257 = lean::cnstr_get(x_256, 0);
lean::inc(x_257);
if (lean::obj_tag(x_257) == 0)
{
obj* x_259; obj* x_261; obj* x_262; obj* x_264; obj* x_265; obj* x_266; 
x_259 = lean::cnstr_get(x_256, 1);
if (lean::is_exclusive(x_256)) {
 lean::cnstr_release(x_256, 0);
 x_261 = x_256;
} else {
 lean::inc(x_259);
 lean::dec(x_256);
 x_261 = lean::box(0);
}
x_262 = lean::cnstr_get(x_257, 0);
if (lean::is_exclusive(x_257)) {
 x_264 = x_257;
} else {
 lean::inc(x_262);
 lean::dec(x_257);
 x_264 = lean::box(0);
}
if (lean::is_scalar(x_264)) {
 x_265 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_265 = x_264;
}
lean::cnstr_set(x_265, 0, x_262);
if (lean::is_scalar(x_261)) {
 x_266 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_266 = x_261;
}
lean::cnstr_set(x_266, 0, x_265);
lean::cnstr_set(x_266, 1, x_259);
return x_266;
}
else
{
obj* x_267; obj* x_270; obj* x_273; obj* x_274; obj* x_275; 
x_267 = lean::cnstr_get(x_256, 1);
lean::inc(x_267);
lean::dec(x_256);
x_270 = lean::cnstr_get(x_257, 0);
lean::inc(x_270);
lean::dec(x_257);
x_273 = l_option_has__repr___rarg___closed__3;
x_274 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_273, x_3, x_267);
x_275 = lean::cnstr_get(x_274, 0);
lean::inc(x_275);
if (lean::obj_tag(x_275) == 0)
{
obj* x_278; obj* x_280; obj* x_281; obj* x_283; obj* x_284; obj* x_285; 
lean::dec(x_270);
x_278 = lean::cnstr_get(x_274, 1);
if (lean::is_exclusive(x_274)) {
 lean::cnstr_release(x_274, 0);
 x_280 = x_274;
} else {
 lean::inc(x_278);
 lean::dec(x_274);
 x_280 = lean::box(0);
}
x_281 = lean::cnstr_get(x_275, 0);
if (lean::is_exclusive(x_275)) {
 x_283 = x_275;
} else {
 lean::inc(x_281);
 lean::dec(x_275);
 x_283 = lean::box(0);
}
if (lean::is_scalar(x_283)) {
 x_284 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_284 = x_283;
}
lean::cnstr_set(x_284, 0, x_281);
if (lean::is_scalar(x_280)) {
 x_285 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_285 = x_280;
}
lean::cnstr_set(x_285, 0, x_284);
lean::cnstr_set(x_285, 1, x_278);
return x_285;
}
else
{
obj* x_286; obj* x_287; obj* x_289; obj* x_290; obj* x_291; 
if (lean::is_exclusive(x_275)) {
 lean::cnstr_release(x_275, 0);
 x_286 = x_275;
} else {
 lean::dec(x_275);
 x_286 = lean::box(0);
}
x_287 = lean::cnstr_get(x_274, 1);
if (lean::is_exclusive(x_274)) {
 lean::cnstr_release(x_274, 0);
 x_289 = x_274;
} else {
 lean::inc(x_287);
 lean::dec(x_274);
 x_289 = lean::box(0);
}
if (lean::is_scalar(x_286)) {
 x_290 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_290 = x_286;
}
lean::cnstr_set(x_290, 0, x_270);
if (lean::is_scalar(x_289)) {
 x_291 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_291 = x_289;
}
lean::cnstr_set(x_291, 0, x_290);
lean::cnstr_set(x_291, 1, x_287);
return x_291;
}
}
}
}
}
}
}
}
}
default:
{
obj* x_292; 
x_292 = lean::box(0);
x_135 = x_292;
goto lbl_136;
}
}
lbl_136:
{
obj* x_294; obj* x_295; 
lean::dec(x_135);
x_294 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_295 = lean::cnstr_get(x_294, 0);
lean::inc(x_295);
if (lean::obj_tag(x_295) == 0)
{
obj* x_298; obj* x_300; obj* x_301; obj* x_303; obj* x_304; obj* x_305; 
lean::dec(x_132);
x_298 = lean::cnstr_get(x_294, 1);
if (lean::is_exclusive(x_294)) {
 lean::cnstr_release(x_294, 0);
 x_300 = x_294;
} else {
 lean::inc(x_298);
 lean::dec(x_294);
 x_300 = lean::box(0);
}
x_301 = lean::cnstr_get(x_295, 0);
if (lean::is_exclusive(x_295)) {
 x_303 = x_295;
} else {
 lean::inc(x_301);
 lean::dec(x_295);
 x_303 = lean::box(0);
}
if (lean::is_scalar(x_303)) {
 x_304 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_304 = x_303;
}
lean::cnstr_set(x_304, 0, x_301);
if (lean::is_scalar(x_300)) {
 x_305 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_305 = x_300;
}
lean::cnstr_set(x_305, 0, x_304);
lean::cnstr_set(x_305, 1, x_298);
return x_305;
}
else
{
obj* x_307; obj* x_310; obj* x_311; obj* x_312; 
lean::dec(x_295);
x_307 = lean::cnstr_get(x_294, 1);
lean::inc(x_307);
lean::dec(x_294);
x_310 = l_lean_ir_cpp_emit__infix___closed__1;
x_311 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_310, x_3, x_307);
x_312 = lean::cnstr_get(x_311, 0);
lean::inc(x_312);
if (lean::obj_tag(x_312) == 0)
{
obj* x_315; obj* x_317; obj* x_318; obj* x_320; obj* x_321; obj* x_322; 
lean::dec(x_132);
x_315 = lean::cnstr_get(x_311, 1);
if (lean::is_exclusive(x_311)) {
 lean::cnstr_release(x_311, 0);
 x_317 = x_311;
} else {
 lean::inc(x_315);
 lean::dec(x_311);
 x_317 = lean::box(0);
}
x_318 = lean::cnstr_get(x_312, 0);
if (lean::is_exclusive(x_312)) {
 x_320 = x_312;
} else {
 lean::inc(x_318);
 lean::dec(x_312);
 x_320 = lean::box(0);
}
if (lean::is_scalar(x_320)) {
 x_321 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_321 = x_320;
}
lean::cnstr_set(x_321, 0, x_318);
if (lean::is_scalar(x_317)) {
 x_322 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_322 = x_317;
}
lean::cnstr_set(x_322, 0, x_321);
lean::cnstr_set(x_322, 1, x_315);
return x_322;
}
else
{
obj* x_324; obj* x_327; obj* x_329; 
lean::dec(x_312);
x_324 = lean::cnstr_get(x_311, 1);
lean::inc(x_324);
lean::dec(x_311);
x_327 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_132, x_3, x_324);
lean::dec(x_132);
x_329 = lean::cnstr_get(x_327, 0);
lean::inc(x_329);
if (lean::obj_tag(x_329) == 0)
{
obj* x_331; obj* x_333; obj* x_334; obj* x_336; obj* x_337; obj* x_338; 
x_331 = lean::cnstr_get(x_327, 1);
if (lean::is_exclusive(x_327)) {
 lean::cnstr_release(x_327, 0);
 x_333 = x_327;
} else {
 lean::inc(x_331);
 lean::dec(x_327);
 x_333 = lean::box(0);
}
x_334 = lean::cnstr_get(x_329, 0);
if (lean::is_exclusive(x_329)) {
 x_336 = x_329;
} else {
 lean::inc(x_334);
 lean::dec(x_329);
 x_336 = lean::box(0);
}
if (lean::is_scalar(x_336)) {
 x_337 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_337 = x_336;
}
lean::cnstr_set(x_337, 0, x_334);
if (lean::is_scalar(x_333)) {
 x_338 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_338 = x_333;
}
lean::cnstr_set(x_338, 0, x_337);
lean::cnstr_set(x_338, 1, x_331);
return x_338;
}
else
{
obj* x_340; obj* x_343; 
lean::dec(x_329);
x_340 = lean::cnstr_get(x_327, 1);
lean::inc(x_340);
lean::dec(x_327);
x_343 = l_lean_ir_cpp_emit__num__suffix___main(x_1, x_3, x_340);
return x_343;
}
}
}
}
}
default:
{
obj* x_344; obj* x_347; obj* x_348; 
x_344 = lean::cnstr_get(x_2, 0);
lean::inc(x_344);
lean::dec(x_2);
x_347 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_348 = lean::cnstr_get(x_347, 0);
lean::inc(x_348);
if (lean::obj_tag(x_348) == 0)
{
obj* x_351; obj* x_353; obj* x_354; obj* x_356; obj* x_357; obj* x_358; 
lean::dec(x_344);
x_351 = lean::cnstr_get(x_347, 1);
if (lean::is_exclusive(x_347)) {
 lean::cnstr_release(x_347, 0);
 x_353 = x_347;
} else {
 lean::inc(x_351);
 lean::dec(x_347);
 x_353 = lean::box(0);
}
x_354 = lean::cnstr_get(x_348, 0);
if (lean::is_exclusive(x_348)) {
 x_356 = x_348;
} else {
 lean::inc(x_354);
 lean::dec(x_348);
 x_356 = lean::box(0);
}
if (lean::is_scalar(x_356)) {
 x_357 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_357 = x_356;
}
lean::cnstr_set(x_357, 0, x_354);
if (lean::is_scalar(x_353)) {
 x_358 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_358 = x_353;
}
lean::cnstr_set(x_358, 0, x_357);
lean::cnstr_set(x_358, 1, x_351);
return x_358;
}
else
{
obj* x_360; obj* x_363; obj* x_364; obj* x_365; 
lean::dec(x_348);
x_360 = lean::cnstr_get(x_347, 1);
lean::inc(x_360);
lean::dec(x_347);
x_363 = l_lean_ir_cpp_emit__infix___closed__1;
x_364 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_363, x_3, x_360);
x_365 = lean::cnstr_get(x_364, 0);
lean::inc(x_365);
if (lean::obj_tag(x_365) == 0)
{
obj* x_368; obj* x_370; obj* x_371; obj* x_373; obj* x_374; obj* x_375; 
lean::dec(x_344);
x_368 = lean::cnstr_get(x_364, 1);
if (lean::is_exclusive(x_364)) {
 lean::cnstr_release(x_364, 0);
 x_370 = x_364;
} else {
 lean::inc(x_368);
 lean::dec(x_364);
 x_370 = lean::box(0);
}
x_371 = lean::cnstr_get(x_365, 0);
if (lean::is_exclusive(x_365)) {
 x_373 = x_365;
} else {
 lean::inc(x_371);
 lean::dec(x_365);
 x_373 = lean::box(0);
}
if (lean::is_scalar(x_373)) {
 x_374 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_374 = x_373;
}
lean::cnstr_set(x_374, 0, x_371);
if (lean::is_scalar(x_370)) {
 x_375 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_375 = x_370;
}
lean::cnstr_set(x_375, 0, x_374);
lean::cnstr_set(x_375, 1, x_368);
return x_375;
}
else
{
obj* x_377; obj* x_380; 
lean::dec(x_365);
x_377 = lean::cnstr_get(x_364, 1);
lean::inc(x_377);
lean::dec(x_364);
x_380 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_344, x_3, x_377);
lean::dec(x_344);
return x_380;
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_ir_cpp_emit__assign__lit___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_1);
x_6 = l_lean_ir_cpp_emit__assign__lit(x_0, x_5, x_2, x_3, x_4);
lean::dec(x_3);
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
return x_1;
}
case 1:
{
obj* x_2; 
x_2 = l_lean_ir_cpp_unop2cpp___main___closed__2;
return x_2;
}
case 2:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_unop2cpp___main___closed__3;
return x_3;
}
case 3:
{
obj* x_4; 
x_4 = l_lean_ir_cpp_unop2cpp___main___closed__4;
return x_4;
}
case 4:
{
obj* x_5; 
x_5 = l_lean_ir_cpp_unop2cpp___main___closed__5;
return x_5;
}
case 5:
{
obj* x_6; 
x_6 = l_lean_ir_cpp_unop2cpp___main___closed__6;
return x_6;
}
case 6:
{
obj* x_7; 
x_7 = l_lean_ir_cpp_unop2cpp___main___closed__7;
return x_7;
}
case 7:
{
obj* x_8; 
x_8 = l_lean_ir_cpp_unop2cpp___main___closed__8;
return x_8;
}
default:
{
obj* x_9; 
x_9 = l_lean_ir_cpp_unop2cpp___main___closed__9;
return x_9;
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
obj* x_4; obj* x_5; obj* x_7; 
x_4 = l_lean_ir_cpp_unop2cpp___main(x_0);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_4, x_2, x_3);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_12 = x_5;
} else {
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_15 = x_7;
} else {
 lean::inc(x_13);
 lean::dec(x_7);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
if (lean::is_scalar(x_12)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_12;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_7);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_prod_has__repr___rarg___closed__1;
x_23 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_2, x_19);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_27 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_29 = x_23;
} else {
 lean::inc(x_27);
 lean::dec(x_23);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_32 = x_24;
} else {
 lean::inc(x_30);
 lean::dec(x_24);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
if (lean::is_scalar(x_29)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_29;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_27);
return x_34;
}
else
{
obj* x_36; obj* x_39; obj* x_40; 
lean::dec(x_24);
x_36 = lean::cnstr_get(x_23, 1);
lean::inc(x_36);
lean::dec(x_23);
x_39 = l_lean_ir_cpp_emit__var(x_1, x_2, x_36);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
x_42 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 lean::cnstr_release(x_39, 0);
 x_44 = x_39;
} else {
 lean::inc(x_42);
 lean::dec(x_39);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_47 = x_40;
} else {
 lean::inc(x_45);
 lean::dec(x_40);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
if (lean::is_scalar(x_44)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_44;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_42);
return x_49;
}
else
{
obj* x_50; obj* x_53; obj* x_56; obj* x_57; obj* x_58; 
x_50 = lean::cnstr_get(x_39, 1);
lean::inc(x_50);
lean::dec(x_39);
x_53 = lean::cnstr_get(x_40, 0);
lean::inc(x_53);
lean::dec(x_40);
x_56 = l_option_has__repr___rarg___closed__3;
x_57 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_56, x_2, x_50);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
if (lean::obj_tag(x_58) == 0)
{
obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_53);
x_61 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 x_63 = x_57;
} else {
 lean::inc(x_61);
 lean::dec(x_57);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_58, 0);
if (lean::is_exclusive(x_58)) {
 x_66 = x_58;
} else {
 lean::inc(x_64);
 lean::dec(x_58);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_64);
if (lean::is_scalar(x_63)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_63;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_61);
return x_68;
}
else
{
obj* x_69; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 x_69 = x_58;
} else {
 lean::dec(x_58);
 x_69 = lean::box(0);
}
x_70 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 x_72 = x_57;
} else {
 lean::inc(x_70);
 lean::dec(x_57);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_73 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_73 = x_69;
}
lean::cnstr_set(x_73, 0, x_53);
if (lean::is_scalar(x_72)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_72;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_70);
return x_74;
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
lean::dec(x_2);
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__var___boxed), 3, 0);
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
obj* x_6; obj* x_7; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = l_lean_ir_cpp_emit__apply___closed__1;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
x_12 = lean::mk_nat_obj(0u);
x_13 = l_list_length__aux___main___rarg(x_10, x_12);
x_14 = l_lean_closure__max__args;
x_15 = lean::nat_dec_lt(x_14, x_13);
if (x_15 == 0)
{
obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_10);
lean::dec(x_8);
x_21 = l_lean_ir_cpp_emit__var(x_0, x_2, x_3);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_24; obj* x_27; obj* x_29; obj* x_30; 
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
x_27 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_29 = x_22;
} else {
 lean::inc(x_27);
 lean::dec(x_22);
 x_29 = lean::box(0);
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_27);
x_18 = x_30;
x_19 = x_24;
goto lbl_20;
}
else
{
obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_39; 
lean::dec(x_22);
x_32 = lean::cnstr_get(x_21, 1);
lean::inc(x_32);
lean::dec(x_21);
x_35 = l_lean_ir_cpp_emit__apply___closed__3;
x_36 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_35, x_2, x_32);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_18 = x_37;
x_19 = x_39;
goto lbl_20;
}
lbl_20:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_1);
lean::dec(x_13);
lean::dec(x_2);
x_45 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_47 = x_18;
} else {
 lean::inc(x_45);
 lean::dec(x_18);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_19);
return x_49;
}
else
{
obj* x_51; obj* x_52; 
lean::dec(x_18);
x_51 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_13, x_2, x_19);
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_1);
lean::dec(x_2);
x_56 = lean::cnstr_get(x_51, 1);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 x_58 = x_51;
} else {
 lean::inc(x_56);
 lean::dec(x_51);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get(x_52, 0);
if (lean::is_exclusive(x_52)) {
 x_61 = x_52;
} else {
 lean::inc(x_59);
 lean::dec(x_52);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_59);
if (lean::is_scalar(x_58)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_58;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_56);
return x_63;
}
else
{
obj* x_65; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_52);
x_65 = lean::cnstr_get(x_51, 1);
lean::inc(x_65);
lean::dec(x_51);
x_68 = l_prod_has__repr___rarg___closed__1;
x_69 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_68, x_2, x_65);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_74; obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_1);
lean::dec(x_2);
x_74 = lean::cnstr_get(x_69, 1);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 x_76 = x_69;
} else {
 lean::inc(x_74);
 lean::dec(x_69);
 x_76 = lean::box(0);
}
x_77 = lean::cnstr_get(x_70, 0);
if (lean::is_exclusive(x_70)) {
 x_79 = x_70;
} else {
 lean::inc(x_77);
 lean::dec(x_70);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
if (lean::is_scalar(x_76)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_76;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_74);
return x_81;
}
else
{
obj* x_83; obj* x_86; obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_70);
x_83 = lean::cnstr_get(x_69, 1);
lean::inc(x_83);
lean::dec(x_69);
x_86 = l_lean_ir_cpp_emit__apply___closed__2;
x_87 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_2);
x_89 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_86, x_87, x_1, x_2, x_83);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
if (lean::obj_tag(x_90) == 0)
{
obj* x_93; obj* x_95; obj* x_96; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_2);
x_93 = lean::cnstr_get(x_89, 1);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 x_95 = x_89;
} else {
 lean::inc(x_93);
 lean::dec(x_89);
 x_95 = lean::box(0);
}
x_96 = lean::cnstr_get(x_90, 0);
if (lean::is_exclusive(x_90)) {
 x_98 = x_90;
} else {
 lean::inc(x_96);
 lean::dec(x_90);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
if (lean::is_scalar(x_95)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_95;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_93);
return x_100;
}
else
{
obj* x_101; obj* x_104; obj* x_107; obj* x_108; obj* x_110; 
x_101 = lean::cnstr_get(x_89, 1);
lean::inc(x_101);
lean::dec(x_89);
x_104 = lean::cnstr_get(x_90, 0);
lean::inc(x_104);
lean::dec(x_90);
x_107 = l_option_has__repr___rarg___closed__3;
x_108 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_107, x_2, x_101);
lean::dec(x_2);
x_110 = lean::cnstr_get(x_108, 0);
lean::inc(x_110);
if (lean::obj_tag(x_110) == 0)
{
obj* x_113; obj* x_115; obj* x_116; obj* x_118; obj* x_119; obj* x_120; 
lean::dec(x_104);
x_113 = lean::cnstr_get(x_108, 1);
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 x_115 = x_108;
} else {
 lean::inc(x_113);
 lean::dec(x_108);
 x_115 = lean::box(0);
}
x_116 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
 x_118 = x_110;
} else {
 lean::inc(x_116);
 lean::dec(x_110);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_116);
if (lean::is_scalar(x_115)) {
 x_120 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_120 = x_115;
}
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_113);
return x_120;
}
else
{
obj* x_121; obj* x_122; obj* x_124; obj* x_125; obj* x_126; 
if (lean::is_exclusive(x_110)) {
 lean::cnstr_release(x_110, 0);
 x_121 = x_110;
} else {
 lean::dec(x_110);
 x_121 = lean::box(0);
}
x_122 = lean::cnstr_get(x_108, 1);
if (lean::is_exclusive(x_108)) {
 lean::cnstr_release(x_108, 0);
 x_124 = x_108;
} else {
 lean::inc(x_122);
 lean::dec(x_108);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_121)) {
 x_125 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_125 = x_121;
}
lean::cnstr_set(x_125, 0, x_104);
if (lean::is_scalar(x_124)) {
 x_126 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_126 = x_124;
}
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_122);
return x_126;
}
}
}
}
}
}
}
else
{
obj* x_128; obj* x_129; obj* x_131; obj* x_132; obj* x_134; obj* x_135; obj* x_137; obj* x_138; obj* x_140; obj* x_141; obj* x_142; 
lean::dec(x_1);
x_140 = l_lean_ir_cpp_emit__apply___closed__8;
x_141 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_140, x_2, x_3);
x_142 = lean::cnstr_get(x_141, 0);
lean::inc(x_142);
if (lean::obj_tag(x_142) == 0)
{
obj* x_144; obj* x_147; obj* x_149; obj* x_150; 
x_144 = lean::cnstr_get(x_141, 1);
lean::inc(x_144);
lean::dec(x_141);
x_147 = lean::cnstr_get(x_142, 0);
if (lean::is_exclusive(x_142)) {
 x_149 = x_142;
} else {
 lean::inc(x_147);
 lean::dec(x_142);
 x_149 = lean::box(0);
}
if (lean::is_scalar(x_149)) {
 x_150 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_150 = x_149;
}
lean::cnstr_set(x_150, 0, x_147);
x_137 = x_150;
x_138 = x_144;
goto lbl_139;
}
else
{
obj* x_152; obj* x_156; obj* x_157; 
lean::dec(x_142);
x_152 = lean::cnstr_get(x_141, 1);
lean::inc(x_152);
lean::dec(x_141);
lean::inc(x_13);
x_156 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_13, x_2, x_152);
x_157 = lean::cnstr_get(x_156, 0);
lean::inc(x_157);
if (lean::obj_tag(x_157) == 0)
{
obj* x_159; obj* x_162; obj* x_164; obj* x_165; 
x_159 = lean::cnstr_get(x_156, 1);
lean::inc(x_159);
lean::dec(x_156);
x_162 = lean::cnstr_get(x_157, 0);
if (lean::is_exclusive(x_157)) {
 x_164 = x_157;
} else {
 lean::inc(x_162);
 lean::dec(x_157);
 x_164 = lean::box(0);
}
if (lean::is_scalar(x_164)) {
 x_165 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_165 = x_164;
}
lean::cnstr_set(x_165, 0, x_162);
x_137 = x_165;
x_138 = x_159;
goto lbl_139;
}
else
{
obj* x_167; obj* x_170; obj* x_171; obj* x_172; obj* x_174; 
lean::dec(x_157);
x_167 = lean::cnstr_get(x_156, 1);
lean::inc(x_167);
lean::dec(x_156);
x_170 = l_lean_ir_cpp_emit__apply___closed__9;
x_171 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_170, x_2, x_167);
x_172 = lean::cnstr_get(x_171, 0);
lean::inc(x_172);
x_174 = lean::cnstr_get(x_171, 1);
lean::inc(x_174);
lean::dec(x_171);
x_137 = x_172;
x_138 = x_174;
goto lbl_139;
}
}
lbl_130:
{
if (lean::obj_tag(x_128) == 0)
{
obj* x_178; obj* x_180; obj* x_181; obj* x_182; 
lean::dec(x_2);
x_178 = lean::cnstr_get(x_128, 0);
if (lean::is_exclusive(x_128)) {
 x_180 = x_128;
} else {
 lean::inc(x_178);
 lean::dec(x_128);
 x_180 = lean::box(0);
}
if (lean::is_scalar(x_180)) {
 x_181 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_181 = x_180;
}
lean::cnstr_set(x_181, 0, x_178);
x_182 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_129);
return x_182;
}
else
{
obj* x_184; obj* x_185; 
lean::dec(x_128);
x_184 = l_lean_ir_cpp_emit__apply___closed__4;
x_185 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_184, x_2, x_129);
lean::dec(x_2);
return x_185;
}
}
lbl_133:
{
if (lean::obj_tag(x_131) == 0)
{
obj* x_187; obj* x_189; obj* x_190; 
x_187 = lean::cnstr_get(x_131, 0);
if (lean::is_exclusive(x_131)) {
 x_189 = x_131;
} else {
 lean::inc(x_187);
 lean::dec(x_131);
 x_189 = lean::box(0);
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_187);
x_128 = x_190;
x_129 = x_132;
goto lbl_130;
}
else
{
obj* x_192; obj* x_193; obj* x_194; 
lean::dec(x_131);
x_192 = l_list_repr__aux___main___rarg___closed__1;
x_193 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_192, x_2, x_132);
x_194 = lean::cnstr_get(x_193, 0);
lean::inc(x_194);
if (lean::obj_tag(x_194) == 0)
{
obj* x_196; obj* x_199; obj* x_201; obj* x_202; 
x_196 = lean::cnstr_get(x_193, 1);
lean::inc(x_196);
lean::dec(x_193);
x_199 = lean::cnstr_get(x_194, 0);
if (lean::is_exclusive(x_194)) {
 x_201 = x_194;
} else {
 lean::inc(x_199);
 lean::dec(x_194);
 x_201 = lean::box(0);
}
if (lean::is_scalar(x_201)) {
 x_202 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_202 = x_201;
}
lean::cnstr_set(x_202, 0, x_199);
x_128 = x_202;
x_129 = x_196;
goto lbl_130;
}
else
{
obj* x_204; obj* x_207; obj* x_208; obj* x_209; 
lean::dec(x_194);
x_204 = lean::cnstr_get(x_193, 1);
lean::inc(x_204);
lean::dec(x_193);
x_207 = l_lean_ir_cpp_emit__apply___closed__5;
x_208 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_207, x_2, x_204);
x_209 = lean::cnstr_get(x_208, 0);
lean::inc(x_209);
if (lean::obj_tag(x_209) == 0)
{
obj* x_211; obj* x_214; obj* x_216; obj* x_217; 
x_211 = lean::cnstr_get(x_208, 1);
lean::inc(x_211);
lean::dec(x_208);
x_214 = lean::cnstr_get(x_209, 0);
if (lean::is_exclusive(x_209)) {
 x_216 = x_209;
} else {
 lean::inc(x_214);
 lean::dec(x_209);
 x_216 = lean::box(0);
}
if (lean::is_scalar(x_216)) {
 x_217 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_217 = x_216;
}
lean::cnstr_set(x_217, 0, x_214);
x_128 = x_217;
x_129 = x_211;
goto lbl_130;
}
else
{
obj* x_218; obj* x_221; obj* x_224; obj* x_225; obj* x_226; 
x_218 = lean::cnstr_get(x_208, 1);
lean::inc(x_218);
lean::dec(x_208);
x_221 = lean::cnstr_get(x_209, 0);
lean::inc(x_221);
lean::dec(x_209);
x_224 = l_option_has__repr___rarg___closed__3;
x_225 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_224, x_2, x_218);
x_226 = lean::cnstr_get(x_225, 0);
lean::inc(x_226);
if (lean::obj_tag(x_226) == 0)
{
obj* x_229; obj* x_232; obj* x_234; obj* x_235; 
lean::dec(x_221);
x_229 = lean::cnstr_get(x_225, 1);
lean::inc(x_229);
lean::dec(x_225);
x_232 = lean::cnstr_get(x_226, 0);
if (lean::is_exclusive(x_226)) {
 x_234 = x_226;
} else {
 lean::inc(x_232);
 lean::dec(x_226);
 x_234 = lean::box(0);
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_232);
x_128 = x_235;
x_129 = x_229;
goto lbl_130;
}
else
{
obj* x_236; obj* x_237; obj* x_240; 
if (lean::is_exclusive(x_226)) {
 lean::cnstr_release(x_226, 0);
 x_236 = x_226;
} else {
 lean::dec(x_226);
 x_236 = lean::box(0);
}
x_237 = lean::cnstr_get(x_225, 1);
lean::inc(x_237);
lean::dec(x_225);
if (lean::is_scalar(x_236)) {
 x_240 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_240 = x_236;
}
lean::cnstr_set(x_240, 0, x_221);
x_128 = x_240;
x_129 = x_237;
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
obj* x_243; obj* x_245; obj* x_246; 
lean::dec(x_8);
lean::dec(x_13);
x_243 = lean::cnstr_get(x_134, 0);
if (lean::is_exclusive(x_134)) {
 x_245 = x_134;
} else {
 lean::inc(x_243);
 lean::dec(x_134);
 x_245 = lean::box(0);
}
if (lean::is_scalar(x_245)) {
 x_246 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_246 = x_245;
}
lean::cnstr_set(x_246, 0, x_243);
x_128 = x_246;
x_129 = x_135;
goto lbl_130;
}
else
{
obj* x_248; obj* x_249; obj* x_250; 
lean::dec(x_134);
x_248 = l_prod_has__repr___rarg___closed__1;
x_249 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_248, x_2, x_135);
x_250 = lean::cnstr_get(x_249, 0);
lean::inc(x_250);
if (lean::obj_tag(x_250) == 0)
{
obj* x_254; obj* x_257; obj* x_259; obj* x_260; 
lean::dec(x_8);
lean::dec(x_13);
x_254 = lean::cnstr_get(x_249, 1);
lean::inc(x_254);
lean::dec(x_249);
x_257 = lean::cnstr_get(x_250, 0);
if (lean::is_exclusive(x_250)) {
 x_259 = x_250;
} else {
 lean::inc(x_257);
 lean::dec(x_250);
 x_259 = lean::box(0);
}
if (lean::is_scalar(x_259)) {
 x_260 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_260 = x_259;
}
lean::cnstr_set(x_260, 0, x_257);
x_128 = x_260;
x_129 = x_254;
goto lbl_130;
}
else
{
obj* x_262; obj* x_265; obj* x_266; 
lean::dec(x_250);
x_262 = lean::cnstr_get(x_249, 1);
lean::inc(x_262);
lean::dec(x_249);
x_265 = l_lean_ir_cpp_emit__var(x_8, x_2, x_262);
x_266 = lean::cnstr_get(x_265, 0);
lean::inc(x_266);
if (lean::obj_tag(x_266) == 0)
{
obj* x_269; obj* x_272; obj* x_274; obj* x_275; 
lean::dec(x_13);
x_269 = lean::cnstr_get(x_265, 1);
lean::inc(x_269);
lean::dec(x_265);
x_272 = lean::cnstr_get(x_266, 0);
if (lean::is_exclusive(x_266)) {
 x_274 = x_266;
} else {
 lean::inc(x_272);
 lean::dec(x_266);
 x_274 = lean::box(0);
}
if (lean::is_scalar(x_274)) {
 x_275 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_275 = x_274;
}
lean::cnstr_set(x_275, 0, x_272);
x_131 = x_275;
x_132 = x_269;
goto lbl_133;
}
else
{
obj* x_277; obj* x_280; obj* x_281; obj* x_282; 
lean::dec(x_266);
x_277 = lean::cnstr_get(x_265, 1);
lean::inc(x_277);
lean::dec(x_265);
x_280 = l_list_repr__aux___main___rarg___closed__1;
x_281 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_280, x_2, x_277);
x_282 = lean::cnstr_get(x_281, 0);
lean::inc(x_282);
if (lean::obj_tag(x_282) == 0)
{
obj* x_285; obj* x_288; obj* x_290; obj* x_291; 
lean::dec(x_13);
x_285 = lean::cnstr_get(x_281, 1);
lean::inc(x_285);
lean::dec(x_281);
x_288 = lean::cnstr_get(x_282, 0);
if (lean::is_exclusive(x_282)) {
 x_290 = x_282;
} else {
 lean::inc(x_288);
 lean::dec(x_282);
 x_290 = lean::box(0);
}
if (lean::is_scalar(x_290)) {
 x_291 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_291 = x_290;
}
lean::cnstr_set(x_291, 0, x_288);
x_131 = x_291;
x_132 = x_285;
goto lbl_133;
}
else
{
obj* x_293; obj* x_296; obj* x_297; obj* x_299; 
lean::dec(x_282);
x_293 = lean::cnstr_get(x_281, 1);
lean::inc(x_293);
lean::dec(x_281);
x_296 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_13, x_2, x_293);
x_297 = lean::cnstr_get(x_296, 0);
lean::inc(x_297);
x_299 = lean::cnstr_get(x_296, 1);
lean::inc(x_299);
lean::dec(x_296);
x_131 = x_297;
x_132 = x_299;
goto lbl_133;
}
}
}
}
}
lbl_139:
{
if (lean::obj_tag(x_137) == 0)
{
obj* x_304; obj* x_306; obj* x_307; 
lean::dec(x_10);
lean::dec(x_0);
x_304 = lean::cnstr_get(x_137, 0);
if (lean::is_exclusive(x_137)) {
 x_306 = x_137;
} else {
 lean::inc(x_304);
 lean::dec(x_137);
 x_306 = lean::box(0);
}
if (lean::is_scalar(x_306)) {
 x_307 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_307 = x_306;
}
lean::cnstr_set(x_307, 0, x_304);
x_134 = x_307;
x_135 = x_138;
goto lbl_136;
}
else
{
obj* x_309; obj* x_310; obj* x_312; obj* x_313; 
lean::dec(x_137);
x_309 = l_lean_ir_cpp_emit__apply___closed__2;
x_310 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_2);
x_312 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_309, x_310, x_10, x_2, x_138);
x_313 = lean::cnstr_get(x_312, 0);
lean::inc(x_313);
if (lean::obj_tag(x_313) == 0)
{
obj* x_316; obj* x_319; obj* x_321; obj* x_322; 
lean::dec(x_0);
x_316 = lean::cnstr_get(x_312, 1);
lean::inc(x_316);
lean::dec(x_312);
x_319 = lean::cnstr_get(x_313, 0);
if (lean::is_exclusive(x_313)) {
 x_321 = x_313;
} else {
 lean::inc(x_319);
 lean::dec(x_313);
 x_321 = lean::box(0);
}
if (lean::is_scalar(x_321)) {
 x_322 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_322 = x_321;
}
lean::cnstr_set(x_322, 0, x_319);
x_134 = x_322;
x_135 = x_316;
goto lbl_136;
}
else
{
obj* x_324; obj* x_327; obj* x_328; obj* x_329; 
lean::dec(x_313);
x_324 = lean::cnstr_get(x_312, 1);
lean::inc(x_324);
lean::dec(x_312);
x_327 = l_lean_ir_cpp_emit__apply___closed__6;
x_328 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_327, x_2, x_324);
x_329 = lean::cnstr_get(x_328, 0);
lean::inc(x_329);
if (lean::obj_tag(x_329) == 0)
{
obj* x_332; obj* x_335; obj* x_337; obj* x_338; 
lean::dec(x_0);
x_332 = lean::cnstr_get(x_328, 1);
lean::inc(x_332);
lean::dec(x_328);
x_335 = lean::cnstr_get(x_329, 0);
if (lean::is_exclusive(x_329)) {
 x_337 = x_329;
} else {
 lean::inc(x_335);
 lean::dec(x_329);
 x_337 = lean::box(0);
}
if (lean::is_scalar(x_337)) {
 x_338 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_338 = x_337;
}
lean::cnstr_set(x_338, 0, x_335);
x_134 = x_338;
x_135 = x_332;
goto lbl_136;
}
else
{
obj* x_340; obj* x_343; obj* x_344; 
lean::dec(x_329);
x_340 = lean::cnstr_get(x_328, 1);
lean::inc(x_340);
lean::dec(x_328);
x_343 = l_lean_ir_cpp_emit__var(x_0, x_2, x_340);
x_344 = lean::cnstr_get(x_343, 0);
lean::inc(x_344);
if (lean::obj_tag(x_344) == 0)
{
obj* x_346; obj* x_349; obj* x_351; obj* x_352; 
x_346 = lean::cnstr_get(x_343, 1);
lean::inc(x_346);
lean::dec(x_343);
x_349 = lean::cnstr_get(x_344, 0);
if (lean::is_exclusive(x_344)) {
 x_351 = x_344;
} else {
 lean::inc(x_349);
 lean::dec(x_344);
 x_351 = lean::box(0);
}
if (lean::is_scalar(x_351)) {
 x_352 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_352 = x_351;
}
lean::cnstr_set(x_352, 0, x_349);
x_134 = x_352;
x_135 = x_346;
goto lbl_136;
}
else
{
obj* x_354; obj* x_357; obj* x_358; obj* x_359; obj* x_361; 
lean::dec(x_344);
x_354 = lean::cnstr_get(x_343, 1);
lean::inc(x_354);
lean::dec(x_343);
x_357 = l_lean_ir_cpp_emit__apply___closed__7;
x_358 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_357, x_2, x_354);
x_359 = lean::cnstr_get(x_358, 0);
lean::inc(x_359);
x_361 = lean::cnstr_get(x_358, 1);
lean::inc(x_361);
lean::dec(x_358);
x_134 = x_359;
x_135 = x_361;
goto lbl_136;
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
obj* x_6; obj* x_7; 
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::dec(x_2);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_1, x_13);
x_21 = l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___closed__1;
x_22 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_21, x_3, x_4);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_27; obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_8);
lean::dec(x_1);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_32 = x_23;
} else {
 lean::inc(x_30);
 lean::dec(x_23);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
x_15 = x_33;
x_16 = x_27;
goto lbl_17;
}
else
{
obj* x_35; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_23);
x_35 = lean::cnstr_get(x_22, 1);
lean::inc(x_35);
lean::dec(x_22);
x_38 = l_prod_has__repr___rarg___closed__1;
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_38, x_3, x_35);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_44; obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_8);
lean::dec(x_1);
x_44 = lean::cnstr_get(x_39, 1);
lean::inc(x_44);
lean::dec(x_39);
x_47 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_49 = x_40;
} else {
 lean::inc(x_47);
 lean::dec(x_40);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_47);
x_15 = x_50;
x_16 = x_44;
goto lbl_17;
}
else
{
obj* x_52; obj* x_56; obj* x_57; 
lean::dec(x_40);
x_52 = lean::cnstr_get(x_39, 1);
lean::inc(x_52);
lean::dec(x_39);
lean::inc(x_0);
x_56 = l_lean_ir_cpp_emit__var(x_0, x_3, x_52);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
if (lean::obj_tag(x_57) == 0)
{
obj* x_60; obj* x_63; obj* x_65; obj* x_66; 
lean::dec(x_1);
x_60 = lean::cnstr_get(x_56, 1);
lean::inc(x_60);
lean::dec(x_56);
x_63 = lean::cnstr_get(x_57, 0);
if (lean::is_exclusive(x_57)) {
 x_65 = x_57;
} else {
 lean::inc(x_63);
 lean::dec(x_57);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_63);
x_18 = x_66;
x_19 = x_60;
goto lbl_20;
}
else
{
obj* x_68; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_57);
x_68 = lean::cnstr_get(x_56, 1);
lean::inc(x_68);
lean::dec(x_56);
x_71 = l_list_repr__aux___main___rarg___closed__1;
x_72 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_71, x_3, x_68);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
if (lean::obj_tag(x_73) == 0)
{
obj* x_76; obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_1);
x_76 = lean::cnstr_get(x_72, 1);
lean::inc(x_76);
lean::dec(x_72);
x_79 = lean::cnstr_get(x_73, 0);
if (lean::is_exclusive(x_73)) {
 x_81 = x_73;
} else {
 lean::inc(x_79);
 lean::dec(x_73);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_79);
x_18 = x_82;
x_19 = x_76;
goto lbl_20;
}
else
{
obj* x_84; obj* x_87; obj* x_88; obj* x_90; 
lean::dec(x_73);
x_84 = lean::cnstr_get(x_72, 1);
lean::inc(x_84);
lean::dec(x_72);
x_87 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_1, x_3, x_84);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_87, 1);
lean::inc(x_90);
lean::dec(x_87);
x_18 = x_88;
x_19 = x_90;
goto lbl_20;
}
}
}
}
lbl_17:
{
if (lean::obj_tag(x_15) == 0)
{
obj* x_96; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_10);
x_96 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_98 = x_15;
} else {
 lean::inc(x_96);
 lean::dec(x_15);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_16);
return x_100;
}
else
{
lean::dec(x_15);
x_1 = x_14;
x_2 = x_10;
x_4 = x_16;
goto _start;
}
}
lbl_20:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_104; obj* x_106; obj* x_107; 
lean::dec(x_8);
x_104 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_106 = x_18;
} else {
 lean::inc(x_104);
 lean::dec(x_18);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_104);
x_15 = x_107;
x_16 = x_19;
goto lbl_17;
}
else
{
obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_18);
x_109 = l_list_repr__aux___main___rarg___closed__1;
x_110 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_109, x_3, x_19);
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
obj* x_114; obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_8);
x_114 = lean::cnstr_get(x_110, 1);
lean::inc(x_114);
lean::dec(x_110);
x_117 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 x_119 = x_111;
} else {
 lean::inc(x_117);
 lean::dec(x_111);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_117);
x_15 = x_120;
x_16 = x_114;
goto lbl_17;
}
else
{
obj* x_122; obj* x_125; obj* x_126; 
lean::dec(x_111);
x_122 = lean::cnstr_get(x_110, 1);
lean::inc(x_122);
lean::dec(x_110);
x_125 = l_lean_ir_cpp_emit__var(x_8, x_3, x_122);
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
if (lean::obj_tag(x_126) == 0)
{
obj* x_128; obj* x_131; obj* x_133; obj* x_134; 
x_128 = lean::cnstr_get(x_125, 1);
lean::inc(x_128);
lean::dec(x_125);
x_131 = lean::cnstr_get(x_126, 0);
if (lean::is_exclusive(x_126)) {
 x_133 = x_126;
} else {
 lean::inc(x_131);
 lean::dec(x_126);
 x_133 = lean::box(0);
}
if (lean::is_scalar(x_133)) {
 x_134 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_134 = x_133;
}
lean::cnstr_set(x_134, 0, x_131);
x_15 = x_134;
x_16 = x_128;
goto lbl_17;
}
else
{
obj* x_135; obj* x_138; obj* x_141; obj* x_142; obj* x_143; 
x_135 = lean::cnstr_get(x_125, 1);
lean::inc(x_135);
lean::dec(x_125);
x_138 = lean::cnstr_get(x_126, 0);
lean::inc(x_138);
lean::dec(x_126);
x_141 = l_option_has__repr___rarg___closed__3;
x_142 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_141, x_3, x_135);
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
if (lean::obj_tag(x_143) == 0)
{
obj* x_146; obj* x_149; obj* x_151; obj* x_152; 
lean::dec(x_138);
x_146 = lean::cnstr_get(x_142, 1);
lean::inc(x_146);
lean::dec(x_142);
x_149 = lean::cnstr_get(x_143, 0);
if (lean::is_exclusive(x_143)) {
 x_151 = x_143;
} else {
 lean::inc(x_149);
 lean::dec(x_143);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_149);
x_15 = x_152;
x_16 = x_146;
goto lbl_17;
}
else
{
obj* x_153; obj* x_154; obj* x_157; 
if (lean::is_exclusive(x_143)) {
 lean::cnstr_release(x_143, 0);
 x_153 = x_143;
} else {
 lean::dec(x_143);
 x_153 = lean::box(0);
}
x_154 = lean::cnstr_get(x_142, 1);
lean::inc(x_154);
lean::dec(x_142);
if (lean::is_scalar(x_153)) {
 x_157 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_157 = x_153;
}
lean::cnstr_set(x_157, 0, x_138);
x_15 = x_157;
x_16 = x_154;
goto lbl_17;
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
obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_16 = l_lean_ir_cpp_emit__closure___closed__1;
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_4);
return x_17;
}
else
{
obj* x_18; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
lean::dec(x_11);
lean::inc(x_0);
x_22 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_32 = x_22;
} else {
 lean::inc(x_30);
 lean::dec(x_22);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_35 = x_23;
} else {
 lean::inc(x_33);
 lean::dec(x_23);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
if (lean::is_scalar(x_32)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_32;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_30);
return x_37;
}
else
{
obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_23);
x_39 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_set(x_22, 1, lean::box(0));
 x_41 = x_22;
} else {
 lean::inc(x_39);
 lean::dec(x_22);
 x_41 = lean::box(0);
}
x_45 = l_lean_ir_cpp_emit__closure___closed__2;
x_46 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_45, x_3, x_39);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_55; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_2);
lean::dec(x_41);
x_55 = lean::cnstr_get(x_46, 1);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_57 = x_46;
} else {
 lean::inc(x_55);
 lean::dec(x_46);
 x_57 = lean::box(0);
}
x_58 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 x_60 = x_47;
} else {
 lean::inc(x_58);
 lean::dec(x_47);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_58);
if (lean::is_scalar(x_57)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_57;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_55);
return x_62;
}
else
{
obj* x_64; obj* x_68; obj* x_69; 
lean::dec(x_47);
x_64 = lean::cnstr_get(x_46, 1);
lean::inc(x_64);
lean::dec(x_46);
lean::inc(x_3);
x_68 = l_lean_ir_cpp_fid2cpp(x_1, x_3, x_64);
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
if (lean::obj_tag(x_69) == 0)
{
obj* x_76; obj* x_78; obj* x_79; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_2);
lean::dec(x_41);
x_76 = lean::cnstr_get(x_68, 1);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_78 = x_68;
} else {
 lean::inc(x_76);
 lean::dec(x_68);
 x_78 = lean::box(0);
}
x_79 = lean::cnstr_get(x_69, 0);
if (lean::is_exclusive(x_69)) {
 x_81 = x_69;
} else {
 lean::inc(x_79);
 lean::dec(x_69);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_79);
if (lean::is_scalar(x_78)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_78;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_76);
return x_83;
}
else
{
obj* x_84; obj* x_87; obj* x_90; obj* x_92; obj* x_95; obj* x_96; obj* x_98; uint8 x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_84 = lean::cnstr_get(x_68, 1);
lean::inc(x_84);
lean::dec(x_68);
x_87 = lean::cnstr_get(x_69, 0);
lean::inc(x_87);
lean::dec(x_69);
x_90 = l_lean_ir_decl_header___main(x_18);
lean::dec(x_18);
x_92 = lean::cnstr_get(x_90, 1);
lean::inc(x_92);
lean::dec(x_90);
x_95 = lean::mk_nat_obj(0u);
x_96 = l_list_length__aux___main___rarg(x_92, x_95);
lean::dec(x_92);
x_98 = l_lean_closure__max__args;
x_99 = lean::nat_dec_lt(x_98, x_96);
x_100 = l_list_length__aux___main___rarg(x_2, x_95);
x_101 = l_lean_ir_cpp_emit__closure___closed__3;
x_102 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_101, x_3, x_84);
if (x_99 == 0)
{
obj* x_106; 
x_106 = lean::cnstr_get(x_102, 0);
lean::inc(x_106);
if (lean::obj_tag(x_106) == 0)
{
obj* x_109; obj* x_112; obj* x_114; obj* x_115; 
lean::dec(x_87);
x_109 = lean::cnstr_get(x_102, 1);
lean::inc(x_109);
lean::dec(x_102);
x_112 = lean::cnstr_get(x_106, 0);
if (lean::is_exclusive(x_106)) {
 x_114 = x_106;
} else {
 lean::inc(x_112);
 lean::dec(x_106);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_112);
x_103 = x_115;
x_104 = x_109;
goto lbl_105;
}
else
{
obj* x_117; obj* x_120; obj* x_122; obj* x_124; 
lean::dec(x_106);
x_117 = lean::cnstr_get(x_102, 1);
lean::inc(x_117);
lean::dec(x_102);
x_120 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_87, x_3, x_117);
lean::dec(x_87);
x_122 = lean::cnstr_get(x_120, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_120, 1);
lean::inc(x_124);
lean::dec(x_120);
x_103 = x_122;
x_104 = x_124;
goto lbl_105;
}
}
else
{
obj* x_127; 
x_127 = lean::cnstr_get(x_102, 0);
lean::inc(x_127);
if (lean::obj_tag(x_127) == 0)
{
obj* x_130; obj* x_133; obj* x_135; obj* x_136; 
lean::dec(x_87);
x_130 = lean::cnstr_get(x_102, 1);
lean::inc(x_130);
lean::dec(x_102);
x_133 = lean::cnstr_get(x_127, 0);
if (lean::is_exclusive(x_127)) {
 x_135 = x_127;
} else {
 lean::inc(x_133);
 lean::dec(x_127);
 x_135 = lean::box(0);
}
if (lean::is_scalar(x_135)) {
 x_136 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_136 = x_135;
}
lean::cnstr_set(x_136, 0, x_133);
x_103 = x_136;
x_104 = x_130;
goto lbl_105;
}
else
{
obj* x_138; obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_148; 
lean::dec(x_127);
x_138 = lean::cnstr_get(x_102, 1);
lean::inc(x_138);
lean::dec(x_102);
x_141 = l_lean_ir_cpp_emit__closure___closed__4;
x_142 = lean::string_append(x_141, x_87);
lean::dec(x_87);
x_144 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_142, x_3, x_138);
lean::dec(x_142);
x_146 = lean::cnstr_get(x_144, 0);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_144, 1);
lean::inc(x_148);
lean::dec(x_144);
x_103 = x_146;
x_104 = x_148;
goto lbl_105;
}
}
lbl_105:
{
if (lean::obj_tag(x_103) == 0)
{
obj* x_153; obj* x_155; obj* x_156; 
lean::dec(x_96);
lean::dec(x_100);
x_153 = lean::cnstr_get(x_103, 0);
if (lean::is_exclusive(x_103)) {
 x_155 = x_103;
} else {
 lean::inc(x_153);
 lean::dec(x_103);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
x_42 = x_156;
x_43 = x_104;
goto lbl_44;
}
else
{
obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_103);
x_158 = l_option_has__repr___rarg___closed__3;
x_159 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_158, x_3, x_104);
x_160 = lean::cnstr_get(x_159, 0);
lean::inc(x_160);
if (lean::obj_tag(x_160) == 0)
{
obj* x_164; obj* x_167; obj* x_169; obj* x_170; 
lean::dec(x_96);
lean::dec(x_100);
x_164 = lean::cnstr_get(x_159, 1);
lean::inc(x_164);
lean::dec(x_159);
x_167 = lean::cnstr_get(x_160, 0);
if (lean::is_exclusive(x_160)) {
 x_169 = x_160;
} else {
 lean::inc(x_167);
 lean::dec(x_160);
 x_169 = lean::box(0);
}
if (lean::is_scalar(x_169)) {
 x_170 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_170 = x_169;
}
lean::cnstr_set(x_170, 0, x_167);
x_42 = x_170;
x_43 = x_164;
goto lbl_44;
}
else
{
obj* x_172; obj* x_175; obj* x_176; obj* x_177; 
lean::dec(x_160);
x_172 = lean::cnstr_get(x_159, 1);
lean::inc(x_172);
lean::dec(x_159);
x_175 = l_list_repr__aux___main___rarg___closed__1;
x_176 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_175, x_3, x_172);
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
if (lean::obj_tag(x_177) == 0)
{
obj* x_181; obj* x_184; obj* x_186; obj* x_187; 
lean::dec(x_96);
lean::dec(x_100);
x_181 = lean::cnstr_get(x_176, 1);
lean::inc(x_181);
lean::dec(x_176);
x_184 = lean::cnstr_get(x_177, 0);
if (lean::is_exclusive(x_177)) {
 x_186 = x_177;
} else {
 lean::inc(x_184);
 lean::dec(x_177);
 x_186 = lean::box(0);
}
if (lean::is_scalar(x_186)) {
 x_187 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_187 = x_186;
}
lean::cnstr_set(x_187, 0, x_184);
x_42 = x_187;
x_43 = x_181;
goto lbl_44;
}
else
{
obj* x_189; obj* x_192; obj* x_193; 
lean::dec(x_177);
x_189 = lean::cnstr_get(x_176, 1);
lean::inc(x_189);
lean::dec(x_176);
x_192 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_96, x_3, x_189);
x_193 = lean::cnstr_get(x_192, 0);
lean::inc(x_193);
if (lean::obj_tag(x_193) == 0)
{
obj* x_196; obj* x_199; obj* x_201; obj* x_202; 
lean::dec(x_100);
x_196 = lean::cnstr_get(x_192, 1);
lean::inc(x_196);
lean::dec(x_192);
x_199 = lean::cnstr_get(x_193, 0);
if (lean::is_exclusive(x_193)) {
 x_201 = x_193;
} else {
 lean::inc(x_199);
 lean::dec(x_193);
 x_201 = lean::box(0);
}
if (lean::is_scalar(x_201)) {
 x_202 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_202 = x_201;
}
lean::cnstr_set(x_202, 0, x_199);
x_42 = x_202;
x_43 = x_196;
goto lbl_44;
}
else
{
obj* x_204; obj* x_207; obj* x_208; 
lean::dec(x_193);
x_204 = lean::cnstr_get(x_192, 1);
lean::inc(x_204);
lean::dec(x_192);
x_207 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_175, x_3, x_204);
x_208 = lean::cnstr_get(x_207, 0);
lean::inc(x_208);
if (lean::obj_tag(x_208) == 0)
{
obj* x_211; obj* x_214; obj* x_216; obj* x_217; 
lean::dec(x_100);
x_211 = lean::cnstr_get(x_207, 1);
lean::inc(x_211);
lean::dec(x_207);
x_214 = lean::cnstr_get(x_208, 0);
if (lean::is_exclusive(x_208)) {
 x_216 = x_208;
} else {
 lean::inc(x_214);
 lean::dec(x_208);
 x_216 = lean::box(0);
}
if (lean::is_scalar(x_216)) {
 x_217 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_217 = x_216;
}
lean::cnstr_set(x_217, 0, x_214);
x_42 = x_217;
x_43 = x_211;
goto lbl_44;
}
else
{
obj* x_219; obj* x_222; obj* x_223; obj* x_225; 
lean::dec(x_208);
x_219 = lean::cnstr_get(x_207, 1);
lean::inc(x_219);
lean::dec(x_207);
x_222 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_100, x_3, x_219);
x_223 = lean::cnstr_get(x_222, 0);
lean::inc(x_223);
x_225 = lean::cnstr_get(x_222, 1);
lean::inc(x_225);
lean::dec(x_222);
x_42 = x_223;
x_43 = x_225;
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
obj* x_231; obj* x_233; obj* x_234; obj* x_235; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_231 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_233 = x_42;
} else {
 lean::inc(x_231);
 lean::dec(x_42);
 x_233 = lean::box(0);
}
if (lean::is_scalar(x_233)) {
 x_234 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_234 = x_233;
}
lean::cnstr_set(x_234, 0, x_231);
if (lean::is_scalar(x_41)) {
 x_235 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_235 = x_41;
}
lean::cnstr_set(x_235, 0, x_234);
lean::cnstr_set(x_235, 1, x_43);
return x_235;
}
else
{
obj* x_238; obj* x_239; obj* x_240; 
lean::dec(x_42);
lean::dec(x_41);
x_238 = l_option_has__repr___rarg___closed__3;
x_239 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_238, x_3, x_43);
x_240 = lean::cnstr_get(x_239, 0);
lean::inc(x_240);
if (lean::obj_tag(x_240) == 0)
{
obj* x_245; obj* x_247; obj* x_248; obj* x_250; obj* x_251; obj* x_252; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_245 = lean::cnstr_get(x_239, 1);
if (lean::is_exclusive(x_239)) {
 lean::cnstr_release(x_239, 0);
 x_247 = x_239;
} else {
 lean::inc(x_245);
 lean::dec(x_239);
 x_247 = lean::box(0);
}
x_248 = lean::cnstr_get(x_240, 0);
if (lean::is_exclusive(x_240)) {
 x_250 = x_240;
} else {
 lean::inc(x_248);
 lean::dec(x_240);
 x_250 = lean::box(0);
}
if (lean::is_scalar(x_250)) {
 x_251 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_251 = x_250;
}
lean::cnstr_set(x_251, 0, x_248);
if (lean::is_scalar(x_247)) {
 x_252 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_252 = x_247;
}
lean::cnstr_set(x_252, 0, x_251);
lean::cnstr_set(x_252, 1, x_245);
return x_252;
}
else
{
obj* x_254; obj* x_257; obj* x_258; obj* x_260; 
lean::dec(x_240);
x_254 = lean::cnstr_get(x_239, 1);
lean::inc(x_254);
lean::dec(x_239);
x_257 = lean::mk_nat_obj(0u);
x_258 = l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1(x_0, x_257, x_2, x_3, x_254);
lean::dec(x_3);
x_260 = lean::cnstr_get(x_258, 0);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
obj* x_262; obj* x_264; obj* x_265; obj* x_267; obj* x_268; obj* x_269; 
x_262 = lean::cnstr_get(x_258, 1);
if (lean::is_exclusive(x_258)) {
 lean::cnstr_release(x_258, 0);
 x_264 = x_258;
} else {
 lean::inc(x_262);
 lean::dec(x_258);
 x_264 = lean::box(0);
}
x_265 = lean::cnstr_get(x_260, 0);
if (lean::is_exclusive(x_260)) {
 x_267 = x_260;
} else {
 lean::inc(x_265);
 lean::dec(x_260);
 x_267 = lean::box(0);
}
if (lean::is_scalar(x_267)) {
 x_268 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_268 = x_267;
}
lean::cnstr_set(x_268, 0, x_265);
if (lean::is_scalar(x_264)) {
 x_269 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_269 = x_264;
}
lean::cnstr_set(x_269, 0, x_268);
lean::cnstr_set(x_269, 1, x_262);
return x_269;
}
else
{
obj* x_271; obj* x_273; obj* x_274; obj* x_275; 
lean::dec(x_260);
x_271 = lean::cnstr_get(x_258, 1);
if (lean::is_exclusive(x_258)) {
 lean::cnstr_release(x_258, 0);
 x_273 = x_258;
} else {
 lean::inc(x_271);
 lean::dec(x_258);
 x_273 = lean::box(0);
}
x_274 = l_lean_ir_match__type___closed__5;
if (lean::is_scalar(x_273)) {
 x_275 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_275 = x_273;
}
lean::cnstr_set(x_275, 0, x_274);
lean::cnstr_set(x_275, 1, x_271);
return x_275;
}
}
}
}
}
}
}
}
obj* l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(usize x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::usize_to_nat(x_0);
x_4 = l_nat_repr(x_3);
x_5 = lean::string_append(x_2, x_4);
lean::dec(x_4);
x_7 = l_lean_ir_match__type___closed__5;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__2(uint16 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::uint16_to_nat(x_0);
x_4 = l_nat_repr(x_3);
x_5 = lean::string_append(x_2, x_4);
lean::dec(x_4);
x_7 = l_lean_ir_match__type___closed__5;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(uint16 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::uint16_to_nat(x_0);
x_4 = l_nat_repr(x_3);
x_5 = lean::string_append(x_2, x_4);
lean::dec(x_4);
x_7 = l_lean_ir_match__type___closed__5;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
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
obj* x_5; obj* x_7; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = l_lean_ir_cpp_emit__var(x_5, x_1, x_2);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_7);
x_13 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_15 = x_9;
} else {
 lean::inc(x_13);
 lean::dec(x_9);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_18 = x_10;
} else {
 lean::inc(x_16);
 lean::dec(x_10);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_16);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
x_3 = x_20;
goto lbl_4;
}
else
{
obj* x_22; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_10);
x_22 = lean::cnstr_get(x_9, 1);
lean::inc(x_22);
lean::dec(x_9);
x_25 = l_lean_ir_cpp_emit__infix___closed__1;
x_26 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_25, x_1, x_22);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_7);
x_30 = lean::cnstr_get(x_26, 1);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 x_32 = x_26;
} else {
 lean::inc(x_30);
 lean::dec(x_26);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_35 = x_27;
} else {
 lean::inc(x_33);
 lean::dec(x_27);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
if (lean::is_scalar(x_32)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_32;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_30);
x_3 = x_37;
goto lbl_4;
}
else
{
obj* x_39; obj* x_42; 
lean::dec(x_27);
x_39 = lean::cnstr_get(x_26, 1);
lean::inc(x_39);
lean::dec(x_26);
x_42 = l_lean_ir_cpp_emit__var(x_7, x_1, x_39);
x_3 = x_42;
goto lbl_4;
}
}
}
case 1:
{
obj* x_43; uint8 x_45; obj* x_46; obj* x_48; 
x_43 = lean::cnstr_get(x_0, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_46 = lean::cnstr_get(x_0, 1);
lean::inc(x_46);
x_48 = l_lean_ir_cpp_emit__assign__lit(x_43, x_45, x_46, x_1, x_2);
x_3 = x_48;
goto lbl_4;
}
case 2:
{
obj* x_49; uint8 x_51; uint8 x_52; obj* x_53; obj* x_55; 
x_49 = lean::cnstr_get(x_0, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_52 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2 + 1);
x_53 = lean::cnstr_get(x_0, 1);
lean::inc(x_53);
x_55 = l_lean_ir_cpp_emit__assign__unop(x_49, x_51, x_52, x_53, x_1, x_2);
x_3 = x_55;
goto lbl_4;
}
case 3:
{
obj* x_56; uint8 x_58; uint8 x_59; obj* x_60; obj* x_62; obj* x_65; 
x_56 = lean::cnstr_get(x_0, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_59 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3 + 1);
x_60 = lean::cnstr_get(x_0, 1);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_0, 2);
lean::inc(x_62);
lean::inc(x_1);
x_65 = l_lean_ir_cpp_emit__assign__binop(x_56, x_58, x_59, x_60, x_62, x_1, x_2);
x_3 = x_65;
goto lbl_4;
}
case 4:
{
uint8 x_66; obj* x_67; obj* x_69; 
x_66 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
x_67 = lean::cnstr_get(x_0, 0);
lean::inc(x_67);
x_69 = l_lean_ir_cpp_emit__unop(x_66, x_67, x_1, x_2);
x_3 = x_69;
goto lbl_4;
}
case 5:
{
obj* x_70; obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_79; obj* x_80; 
x_70 = lean::cnstr_get(x_0, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_0, 1);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_0, 2);
lean::inc(x_74);
x_79 = l_lean_ir_cpp_emit__var(x_70, x_1, x_2);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
if (lean::obj_tag(x_80) == 0)
{
obj* x_82; obj* x_85; obj* x_87; obj* x_88; 
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
x_85 = lean::cnstr_get(x_80, 0);
if (lean::is_exclusive(x_80)) {
 x_87 = x_80;
} else {
 lean::inc(x_85);
 lean::dec(x_80);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_85);
x_76 = x_88;
x_77 = x_82;
goto lbl_78;
}
else
{
obj* x_90; obj* x_93; obj* x_94; obj* x_95; obj* x_97; 
lean::dec(x_80);
x_90 = lean::cnstr_get(x_79, 1);
lean::inc(x_90);
lean::dec(x_79);
x_93 = l_lean_ir_cpp_emit__infix___closed__1;
x_94 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_93, x_1, x_90);
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_94, 1);
lean::inc(x_97);
lean::dec(x_94);
x_76 = x_95;
x_77 = x_97;
goto lbl_78;
}
lbl_78:
{
if (lean::obj_tag(x_76) == 0)
{
obj* x_102; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_72);
lean::dec(x_74);
x_102 = lean::cnstr_get(x_76, 0);
if (lean::is_exclusive(x_76)) {
 x_104 = x_76;
} else {
 lean::inc(x_102);
 lean::dec(x_76);
 x_104 = lean::box(0);
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_102);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_77);
x_3 = x_106;
goto lbl_4;
}
else
{
obj* x_110; obj* x_111; obj* x_113; obj* x_115; obj* x_116; 
lean::dec(x_76);
lean::inc(x_1);
lean::inc(x_72);
x_110 = l_lean_ir_cpp_is__const(x_72, x_1, x_77);
x_111 = lean::cnstr_get(x_110, 0);
x_113 = lean::cnstr_get(x_110, 1);
if (lean::is_exclusive(x_110)) {
 lean::cnstr_set(x_110, 0, lean::box(0));
 lean::cnstr_set(x_110, 1, lean::box(0));
 x_115 = x_110;
} else {
 lean::inc(x_111);
 lean::inc(x_113);
 lean::dec(x_110);
 x_115 = lean::box(0);
}
if (lean::obj_tag(x_111) == 0)
{
obj* x_120; obj* x_122; obj* x_123; obj* x_124; 
lean::dec(x_72);
lean::dec(x_74);
x_120 = lean::cnstr_get(x_111, 0);
if (lean::is_exclusive(x_111)) {
 x_122 = x_111;
} else {
 lean::inc(x_120);
 lean::dec(x_111);
 x_122 = lean::box(0);
}
if (lean::is_scalar(x_122)) {
 x_123 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_123 = x_122;
}
lean::cnstr_set(x_123, 0, x_120);
if (lean::is_scalar(x_115)) {
 x_124 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_124 = x_115;
}
lean::cnstr_set(x_124, 0, x_123);
lean::cnstr_set(x_124, 1, x_113);
x_3 = x_124;
goto lbl_4;
}
else
{
obj* x_126; uint8 x_129; 
lean::dec(x_115);
x_126 = lean::cnstr_get(x_111, 0);
lean::inc(x_126);
lean::dec(x_111);
x_129 = lean::unbox(x_126);
if (x_129 == 0)
{
obj* x_130; 
x_130 = lean::box(0);
x_116 = x_130;
goto lbl_117;
}
else
{
obj* x_133; 
lean::dec(x_74);
lean::inc(x_1);
x_133 = l_lean_ir_cpp_emit__global(x_72, x_1, x_113);
x_3 = x_133;
goto lbl_4;
}
}
lbl_117:
{
obj* x_136; obj* x_137; 
lean::dec(x_116);
lean::inc(x_1);
x_136 = l_lean_ir_cpp_emit__fnid(x_72, x_1, x_113);
x_137 = lean::cnstr_get(x_136, 0);
lean::inc(x_137);
if (lean::obj_tag(x_137) == 0)
{
obj* x_140; obj* x_142; obj* x_143; obj* x_145; obj* x_146; obj* x_147; 
lean::dec(x_74);
x_140 = lean::cnstr_get(x_136, 1);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 x_142 = x_136;
} else {
 lean::inc(x_140);
 lean::dec(x_136);
 x_142 = lean::box(0);
}
x_143 = lean::cnstr_get(x_137, 0);
if (lean::is_exclusive(x_137)) {
 x_145 = x_137;
} else {
 lean::inc(x_143);
 lean::dec(x_137);
 x_145 = lean::box(0);
}
if (lean::is_scalar(x_145)) {
 x_146 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_146 = x_145;
}
lean::cnstr_set(x_146, 0, x_143);
if (lean::is_scalar(x_142)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_142;
}
lean::cnstr_set(x_147, 0, x_146);
lean::cnstr_set(x_147, 1, x_140);
x_3 = x_147;
goto lbl_4;
}
else
{
obj* x_149; obj* x_152; obj* x_153; obj* x_154; 
lean::dec(x_137);
x_149 = lean::cnstr_get(x_136, 1);
lean::inc(x_149);
lean::dec(x_136);
x_152 = l_prod_has__repr___rarg___closed__1;
x_153 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_152, x_1, x_149);
x_154 = lean::cnstr_get(x_153, 0);
lean::inc(x_154);
if (lean::obj_tag(x_154) == 0)
{
obj* x_157; obj* x_159; obj* x_160; obj* x_162; obj* x_163; obj* x_164; 
lean::dec(x_74);
x_157 = lean::cnstr_get(x_153, 1);
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 x_159 = x_153;
} else {
 lean::inc(x_157);
 lean::dec(x_153);
 x_159 = lean::box(0);
}
x_160 = lean::cnstr_get(x_154, 0);
if (lean::is_exclusive(x_154)) {
 x_162 = x_154;
} else {
 lean::inc(x_160);
 lean::dec(x_154);
 x_162 = lean::box(0);
}
if (lean::is_scalar(x_162)) {
 x_163 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_163 = x_162;
}
lean::cnstr_set(x_163, 0, x_160);
if (lean::is_scalar(x_159)) {
 x_164 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_164 = x_159;
}
lean::cnstr_set(x_164, 0, x_163);
lean::cnstr_set(x_164, 1, x_157);
x_3 = x_164;
goto lbl_4;
}
else
{
obj* x_166; obj* x_169; obj* x_170; obj* x_172; obj* x_173; 
lean::dec(x_154);
x_166 = lean::cnstr_get(x_153, 1);
lean::inc(x_166);
lean::dec(x_153);
x_169 = l_lean_ir_cpp_emit__apply___closed__2;
x_170 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_1);
x_172 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_169, x_170, x_74, x_1, x_166);
x_173 = lean::cnstr_get(x_172, 0);
lean::inc(x_173);
if (lean::obj_tag(x_173) == 0)
{
obj* x_175; obj* x_177; obj* x_178; obj* x_180; obj* x_181; obj* x_182; 
x_175 = lean::cnstr_get(x_172, 1);
if (lean::is_exclusive(x_172)) {
 lean::cnstr_release(x_172, 0);
 x_177 = x_172;
} else {
 lean::inc(x_175);
 lean::dec(x_172);
 x_177 = lean::box(0);
}
x_178 = lean::cnstr_get(x_173, 0);
if (lean::is_exclusive(x_173)) {
 x_180 = x_173;
} else {
 lean::inc(x_178);
 lean::dec(x_173);
 x_180 = lean::box(0);
}
if (lean::is_scalar(x_180)) {
 x_181 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_181 = x_180;
}
lean::cnstr_set(x_181, 0, x_178);
if (lean::is_scalar(x_177)) {
 x_182 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_182 = x_177;
}
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_175);
x_3 = x_182;
goto lbl_4;
}
else
{
obj* x_183; obj* x_186; obj* x_189; obj* x_190; obj* x_191; 
x_183 = lean::cnstr_get(x_172, 1);
lean::inc(x_183);
lean::dec(x_172);
x_186 = lean::cnstr_get(x_173, 0);
lean::inc(x_186);
lean::dec(x_173);
x_189 = l_option_has__repr___rarg___closed__3;
x_190 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_189, x_1, x_183);
x_191 = lean::cnstr_get(x_190, 0);
lean::inc(x_191);
if (lean::obj_tag(x_191) == 0)
{
obj* x_194; obj* x_196; obj* x_197; obj* x_199; obj* x_200; obj* x_201; 
lean::dec(x_186);
x_194 = lean::cnstr_get(x_190, 1);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 x_196 = x_190;
} else {
 lean::inc(x_194);
 lean::dec(x_190);
 x_196 = lean::box(0);
}
x_197 = lean::cnstr_get(x_191, 0);
if (lean::is_exclusive(x_191)) {
 x_199 = x_191;
} else {
 lean::inc(x_197);
 lean::dec(x_191);
 x_199 = lean::box(0);
}
if (lean::is_scalar(x_199)) {
 x_200 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_200 = x_199;
}
lean::cnstr_set(x_200, 0, x_197);
if (lean::is_scalar(x_196)) {
 x_201 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_201 = x_196;
}
lean::cnstr_set(x_201, 0, x_200);
lean::cnstr_set(x_201, 1, x_194);
x_3 = x_201;
goto lbl_4;
}
else
{
obj* x_202; obj* x_203; obj* x_205; obj* x_206; obj* x_207; 
if (lean::is_exclusive(x_191)) {
 lean::cnstr_release(x_191, 0);
 x_202 = x_191;
} else {
 lean::dec(x_191);
 x_202 = lean::box(0);
}
x_203 = lean::cnstr_get(x_190, 1);
if (lean::is_exclusive(x_190)) {
 lean::cnstr_release(x_190, 0);
 x_205 = x_190;
} else {
 lean::inc(x_203);
 lean::dec(x_190);
 x_205 = lean::box(0);
}
if (lean::is_scalar(x_202)) {
 x_206 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_206 = x_202;
}
lean::cnstr_set(x_206, 0, x_186);
if (lean::is_scalar(x_205)) {
 x_207 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_207 = x_205;
}
lean::cnstr_set(x_207, 0, x_206);
lean::cnstr_set(x_207, 1, x_203);
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
obj* x_208; uint16 x_210; uint16 x_211; usize x_212; obj* x_213; obj* x_214; obj* x_216; obj* x_217; obj* x_219; obj* x_220; 
x_208 = lean::cnstr_get(x_0, 0);
lean::inc(x_208);
x_210 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
x_211 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2 + 2);
x_212 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*1);
x_219 = l_lean_ir_cpp_emit__var(x_208, x_1, x_2);
x_220 = lean::cnstr_get(x_219, 0);
lean::inc(x_220);
if (lean::obj_tag(x_220) == 0)
{
obj* x_222; obj* x_225; obj* x_227; obj* x_228; 
x_222 = lean::cnstr_get(x_219, 1);
lean::inc(x_222);
lean::dec(x_219);
x_225 = lean::cnstr_get(x_220, 0);
if (lean::is_exclusive(x_220)) {
 x_227 = x_220;
} else {
 lean::inc(x_225);
 lean::dec(x_220);
 x_227 = lean::box(0);
}
if (lean::is_scalar(x_227)) {
 x_228 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_228 = x_227;
}
lean::cnstr_set(x_228, 0, x_225);
x_216 = x_228;
x_217 = x_222;
goto lbl_218;
}
else
{
obj* x_230; obj* x_233; obj* x_234; obj* x_235; obj* x_237; 
lean::dec(x_220);
x_230 = lean::cnstr_get(x_219, 1);
lean::inc(x_230);
lean::dec(x_219);
x_233 = l_lean_ir_cpp_emit__instr___closed__1;
x_234 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_233, x_1, x_230);
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
if (lean::is_exclusive(x_213)) {
 x_242 = x_213;
} else {
 lean::inc(x_240);
 lean::dec(x_213);
 x_242 = lean::box(0);
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
obj* x_246; obj* x_247; obj* x_248; 
lean::dec(x_213);
x_246 = l_list_repr__aux___main___rarg___closed__1;
x_247 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_246, x_1, x_214);
x_248 = lean::cnstr_get(x_247, 0);
lean::inc(x_248);
if (lean::obj_tag(x_248) == 0)
{
obj* x_250; obj* x_252; obj* x_253; obj* x_255; obj* x_256; obj* x_257; 
x_250 = lean::cnstr_get(x_247, 1);
if (lean::is_exclusive(x_247)) {
 lean::cnstr_release(x_247, 0);
 x_252 = x_247;
} else {
 lean::inc(x_250);
 lean::dec(x_247);
 x_252 = lean::box(0);
}
x_253 = lean::cnstr_get(x_248, 0);
if (lean::is_exclusive(x_248)) {
 x_255 = x_248;
} else {
 lean::inc(x_253);
 lean::dec(x_248);
 x_255 = lean::box(0);
}
if (lean::is_scalar(x_255)) {
 x_256 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_256 = x_255;
}
lean::cnstr_set(x_256, 0, x_253);
if (lean::is_scalar(x_252)) {
 x_257 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_257 = x_252;
}
lean::cnstr_set(x_257, 0, x_256);
lean::cnstr_set(x_257, 1, x_250);
x_3 = x_257;
goto lbl_4;
}
else
{
obj* x_259; obj* x_262; obj* x_263; 
lean::dec(x_248);
x_259 = lean::cnstr_get(x_247, 1);
lean::inc(x_259);
lean::dec(x_247);
x_262 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(x_212, x_1, x_259);
x_263 = lean::cnstr_get(x_262, 0);
lean::inc(x_263);
if (lean::obj_tag(x_263) == 0)
{
obj* x_265; obj* x_267; obj* x_268; obj* x_270; obj* x_271; obj* x_272; 
x_265 = lean::cnstr_get(x_262, 1);
if (lean::is_exclusive(x_262)) {
 lean::cnstr_release(x_262, 0);
 x_267 = x_262;
} else {
 lean::inc(x_265);
 lean::dec(x_262);
 x_267 = lean::box(0);
}
x_268 = lean::cnstr_get(x_263, 0);
if (lean::is_exclusive(x_263)) {
 x_270 = x_263;
} else {
 lean::inc(x_268);
 lean::dec(x_263);
 x_270 = lean::box(0);
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_268);
if (lean::is_scalar(x_267)) {
 x_272 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_272 = x_267;
}
lean::cnstr_set(x_272, 0, x_271);
lean::cnstr_set(x_272, 1, x_265);
x_3 = x_272;
goto lbl_4;
}
else
{
obj* x_273; obj* x_276; obj* x_279; obj* x_280; obj* x_281; 
x_273 = lean::cnstr_get(x_262, 1);
lean::inc(x_273);
lean::dec(x_262);
x_276 = lean::cnstr_get(x_263, 0);
lean::inc(x_276);
lean::dec(x_263);
x_279 = l_option_has__repr___rarg___closed__3;
x_280 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_279, x_1, x_273);
x_281 = lean::cnstr_get(x_280, 0);
lean::inc(x_281);
if (lean::obj_tag(x_281) == 0)
{
obj* x_284; obj* x_286; obj* x_287; obj* x_289; obj* x_290; obj* x_291; 
lean::dec(x_276);
x_284 = lean::cnstr_get(x_280, 1);
if (lean::is_exclusive(x_280)) {
 lean::cnstr_release(x_280, 0);
 x_286 = x_280;
} else {
 lean::inc(x_284);
 lean::dec(x_280);
 x_286 = lean::box(0);
}
x_287 = lean::cnstr_get(x_281, 0);
if (lean::is_exclusive(x_281)) {
 x_289 = x_281;
} else {
 lean::inc(x_287);
 lean::dec(x_281);
 x_289 = lean::box(0);
}
if (lean::is_scalar(x_289)) {
 x_290 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_290 = x_289;
}
lean::cnstr_set(x_290, 0, x_287);
if (lean::is_scalar(x_286)) {
 x_291 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_291 = x_286;
}
lean::cnstr_set(x_291, 0, x_290);
lean::cnstr_set(x_291, 1, x_284);
x_3 = x_291;
goto lbl_4;
}
else
{
obj* x_292; obj* x_293; obj* x_295; obj* x_296; obj* x_297; 
if (lean::is_exclusive(x_281)) {
 lean::cnstr_release(x_281, 0);
 x_292 = x_281;
} else {
 lean::dec(x_281);
 x_292 = lean::box(0);
}
x_293 = lean::cnstr_get(x_280, 1);
if (lean::is_exclusive(x_280)) {
 lean::cnstr_release(x_280, 0);
 x_295 = x_280;
} else {
 lean::inc(x_293);
 lean::dec(x_280);
 x_295 = lean::box(0);
}
if (lean::is_scalar(x_292)) {
 x_296 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_296 = x_292;
}
lean::cnstr_set(x_296, 0, x_276);
if (lean::is_scalar(x_295)) {
 x_297 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_297 = x_295;
}
lean::cnstr_set(x_297, 0, x_296);
lean::cnstr_set(x_297, 1, x_293);
x_3 = x_297;
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
obj* x_298; obj* x_300; obj* x_301; obj* x_302; 
x_298 = lean::cnstr_get(x_216, 0);
if (lean::is_exclusive(x_216)) {
 x_300 = x_216;
} else {
 lean::inc(x_298);
 lean::dec(x_216);
 x_300 = lean::box(0);
}
if (lean::is_scalar(x_300)) {
 x_301 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_301 = x_300;
}
lean::cnstr_set(x_301, 0, x_298);
x_302 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_302, 0, x_301);
lean::cnstr_set(x_302, 1, x_217);
x_3 = x_302;
goto lbl_4;
}
else
{
obj* x_304; obj* x_305; obj* x_306; 
lean::dec(x_216);
x_304 = l_prod_has__repr___rarg___closed__1;
x_305 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_304, x_1, x_217);
x_306 = lean::cnstr_get(x_305, 0);
lean::inc(x_306);
if (lean::obj_tag(x_306) == 0)
{
obj* x_308; obj* x_310; obj* x_311; obj* x_313; obj* x_314; obj* x_315; 
x_308 = lean::cnstr_get(x_305, 1);
if (lean::is_exclusive(x_305)) {
 lean::cnstr_release(x_305, 0);
 x_310 = x_305;
} else {
 lean::inc(x_308);
 lean::dec(x_305);
 x_310 = lean::box(0);
}
x_311 = lean::cnstr_get(x_306, 0);
if (lean::is_exclusive(x_306)) {
 x_313 = x_306;
} else {
 lean::inc(x_311);
 lean::dec(x_306);
 x_313 = lean::box(0);
}
if (lean::is_scalar(x_313)) {
 x_314 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_314 = x_313;
}
lean::cnstr_set(x_314, 0, x_311);
if (lean::is_scalar(x_310)) {
 x_315 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_315 = x_310;
}
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_308);
x_3 = x_315;
goto lbl_4;
}
else
{
obj* x_317; obj* x_320; obj* x_321; 
lean::dec(x_306);
x_317 = lean::cnstr_get(x_305, 1);
lean::inc(x_317);
lean::dec(x_305);
x_320 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__2(x_210, x_1, x_317);
x_321 = lean::cnstr_get(x_320, 0);
lean::inc(x_321);
if (lean::obj_tag(x_321) == 0)
{
obj* x_323; obj* x_326; obj* x_328; obj* x_329; 
x_323 = lean::cnstr_get(x_320, 1);
lean::inc(x_323);
lean::dec(x_320);
x_326 = lean::cnstr_get(x_321, 0);
if (lean::is_exclusive(x_321)) {
 x_328 = x_321;
} else {
 lean::inc(x_326);
 lean::dec(x_321);
 x_328 = lean::box(0);
}
if (lean::is_scalar(x_328)) {
 x_329 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_329 = x_328;
}
lean::cnstr_set(x_329, 0, x_326);
x_213 = x_329;
x_214 = x_323;
goto lbl_215;
}
else
{
obj* x_331; obj* x_334; obj* x_335; obj* x_336; 
lean::dec(x_321);
x_331 = lean::cnstr_get(x_320, 1);
lean::inc(x_331);
lean::dec(x_320);
x_334 = l_list_repr__aux___main___rarg___closed__1;
x_335 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_334, x_1, x_331);
x_336 = lean::cnstr_get(x_335, 0);
lean::inc(x_336);
if (lean::obj_tag(x_336) == 0)
{
obj* x_338; obj* x_341; obj* x_343; obj* x_344; 
x_338 = lean::cnstr_get(x_335, 1);
lean::inc(x_338);
lean::dec(x_335);
x_341 = lean::cnstr_get(x_336, 0);
if (lean::is_exclusive(x_336)) {
 x_343 = x_336;
} else {
 lean::inc(x_341);
 lean::dec(x_336);
 x_343 = lean::box(0);
}
if (lean::is_scalar(x_343)) {
 x_344 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_344 = x_343;
}
lean::cnstr_set(x_344, 0, x_341);
x_213 = x_344;
x_214 = x_338;
goto lbl_215;
}
else
{
obj* x_346; obj* x_349; obj* x_350; obj* x_352; 
lean::dec(x_336);
x_346 = lean::cnstr_get(x_335, 1);
lean::inc(x_346);
lean::dec(x_335);
x_349 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_211, x_1, x_346);
x_350 = lean::cnstr_get(x_349, 0);
lean::inc(x_350);
x_352 = lean::cnstr_get(x_349, 1);
lean::inc(x_352);
lean::dec(x_349);
x_213 = x_350;
x_214 = x_352;
goto lbl_215;
}
}
}
}
}
}
case 7:
{
obj* x_355; uint16 x_357; obj* x_358; obj* x_360; obj* x_361; obj* x_363; obj* x_364; obj* x_365; 
x_355 = lean::cnstr_get(x_0, 0);
lean::inc(x_355);
x_357 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
x_358 = lean::cnstr_get(x_0, 1);
lean::inc(x_358);
x_363 = l_lean_ir_cpp_emit__instr___closed__2;
x_364 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_363, x_1, x_2);
x_365 = lean::cnstr_get(x_364, 0);
lean::inc(x_365);
if (lean::obj_tag(x_365) == 0)
{
obj* x_369; obj* x_371; obj* x_372; obj* x_374; obj* x_375; obj* x_376; 
lean::dec(x_355);
lean::dec(x_358);
x_369 = lean::cnstr_get(x_364, 1);
if (lean::is_exclusive(x_364)) {
 lean::cnstr_release(x_364, 0);
 x_371 = x_364;
} else {
 lean::inc(x_369);
 lean::dec(x_364);
 x_371 = lean::box(0);
}
x_372 = lean::cnstr_get(x_365, 0);
if (lean::is_exclusive(x_365)) {
 x_374 = x_365;
} else {
 lean::inc(x_372);
 lean::dec(x_365);
 x_374 = lean::box(0);
}
if (lean::is_scalar(x_374)) {
 x_375 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_375 = x_374;
}
lean::cnstr_set(x_375, 0, x_372);
if (lean::is_scalar(x_371)) {
 x_376 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_376 = x_371;
}
lean::cnstr_set(x_376, 0, x_375);
lean::cnstr_set(x_376, 1, x_369);
x_3 = x_376;
goto lbl_4;
}
else
{
obj* x_378; obj* x_381; obj* x_382; obj* x_383; 
lean::dec(x_365);
x_378 = lean::cnstr_get(x_364, 1);
lean::inc(x_378);
lean::dec(x_364);
x_381 = l_prod_has__repr___rarg___closed__1;
x_382 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_381, x_1, x_378);
x_383 = lean::cnstr_get(x_382, 0);
lean::inc(x_383);
if (lean::obj_tag(x_383) == 0)
{
obj* x_387; obj* x_389; obj* x_390; obj* x_392; obj* x_393; obj* x_394; 
lean::dec(x_355);
lean::dec(x_358);
x_387 = lean::cnstr_get(x_382, 1);
if (lean::is_exclusive(x_382)) {
 lean::cnstr_release(x_382, 0);
 x_389 = x_382;
} else {
 lean::inc(x_387);
 lean::dec(x_382);
 x_389 = lean::box(0);
}
x_390 = lean::cnstr_get(x_383, 0);
if (lean::is_exclusive(x_383)) {
 x_392 = x_383;
} else {
 lean::inc(x_390);
 lean::dec(x_383);
 x_392 = lean::box(0);
}
if (lean::is_scalar(x_392)) {
 x_393 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_393 = x_392;
}
lean::cnstr_set(x_393, 0, x_390);
if (lean::is_scalar(x_389)) {
 x_394 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_394 = x_389;
}
lean::cnstr_set(x_394, 0, x_393);
lean::cnstr_set(x_394, 1, x_387);
x_3 = x_394;
goto lbl_4;
}
else
{
obj* x_396; obj* x_399; obj* x_400; 
lean::dec(x_383);
x_396 = lean::cnstr_get(x_382, 1);
lean::inc(x_396);
lean::dec(x_382);
x_399 = l_lean_ir_cpp_emit__var(x_355, x_1, x_396);
x_400 = lean::cnstr_get(x_399, 0);
lean::inc(x_400);
if (lean::obj_tag(x_400) == 0)
{
obj* x_402; obj* x_405; obj* x_407; obj* x_408; 
x_402 = lean::cnstr_get(x_399, 1);
lean::inc(x_402);
lean::dec(x_399);
x_405 = lean::cnstr_get(x_400, 0);
if (lean::is_exclusive(x_400)) {
 x_407 = x_400;
} else {
 lean::inc(x_405);
 lean::dec(x_400);
 x_407 = lean::box(0);
}
if (lean::is_scalar(x_407)) {
 x_408 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_408 = x_407;
}
lean::cnstr_set(x_408, 0, x_405);
x_360 = x_408;
x_361 = x_402;
goto lbl_362;
}
else
{
obj* x_410; obj* x_413; obj* x_414; obj* x_415; 
lean::dec(x_400);
x_410 = lean::cnstr_get(x_399, 1);
lean::inc(x_410);
lean::dec(x_399);
x_413 = l_list_repr__aux___main___rarg___closed__1;
x_414 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_413, x_1, x_410);
x_415 = lean::cnstr_get(x_414, 0);
lean::inc(x_415);
if (lean::obj_tag(x_415) == 0)
{
obj* x_417; obj* x_420; obj* x_422; obj* x_423; 
x_417 = lean::cnstr_get(x_414, 1);
lean::inc(x_417);
lean::dec(x_414);
x_420 = lean::cnstr_get(x_415, 0);
if (lean::is_exclusive(x_415)) {
 x_422 = x_415;
} else {
 lean::inc(x_420);
 lean::dec(x_415);
 x_422 = lean::box(0);
}
if (lean::is_scalar(x_422)) {
 x_423 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_423 = x_422;
}
lean::cnstr_set(x_423, 0, x_420);
x_360 = x_423;
x_361 = x_417;
goto lbl_362;
}
else
{
obj* x_425; obj* x_428; obj* x_429; obj* x_431; 
lean::dec(x_415);
x_425 = lean::cnstr_get(x_414, 1);
lean::inc(x_425);
lean::dec(x_414);
x_428 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_357, x_1, x_425);
x_429 = lean::cnstr_get(x_428, 0);
lean::inc(x_429);
x_431 = lean::cnstr_get(x_428, 1);
lean::inc(x_431);
lean::dec(x_428);
x_360 = x_429;
x_361 = x_431;
goto lbl_362;
}
}
}
}
lbl_362:
{
if (lean::obj_tag(x_360) == 0)
{
obj* x_435; obj* x_437; obj* x_438; obj* x_439; 
lean::dec(x_358);
x_435 = lean::cnstr_get(x_360, 0);
if (lean::is_exclusive(x_360)) {
 x_437 = x_360;
} else {
 lean::inc(x_435);
 lean::dec(x_360);
 x_437 = lean::box(0);
}
if (lean::is_scalar(x_437)) {
 x_438 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_438 = x_437;
}
lean::cnstr_set(x_438, 0, x_435);
x_439 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_439, 0, x_438);
lean::cnstr_set(x_439, 1, x_361);
x_3 = x_439;
goto lbl_4;
}
else
{
obj* x_441; obj* x_442; obj* x_443; 
lean::dec(x_360);
x_441 = l_list_repr__aux___main___rarg___closed__1;
x_442 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_441, x_1, x_361);
x_443 = lean::cnstr_get(x_442, 0);
lean::inc(x_443);
if (lean::obj_tag(x_443) == 0)
{
obj* x_446; obj* x_448; obj* x_449; obj* x_451; obj* x_452; obj* x_453; 
lean::dec(x_358);
x_446 = lean::cnstr_get(x_442, 1);
if (lean::is_exclusive(x_442)) {
 lean::cnstr_release(x_442, 0);
 x_448 = x_442;
} else {
 lean::inc(x_446);
 lean::dec(x_442);
 x_448 = lean::box(0);
}
x_449 = lean::cnstr_get(x_443, 0);
if (lean::is_exclusive(x_443)) {
 x_451 = x_443;
} else {
 lean::inc(x_449);
 lean::dec(x_443);
 x_451 = lean::box(0);
}
if (lean::is_scalar(x_451)) {
 x_452 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_452 = x_451;
}
lean::cnstr_set(x_452, 0, x_449);
if (lean::is_scalar(x_448)) {
 x_453 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_453 = x_448;
}
lean::cnstr_set(x_453, 0, x_452);
lean::cnstr_set(x_453, 1, x_446);
x_3 = x_453;
goto lbl_4;
}
else
{
obj* x_455; obj* x_458; obj* x_459; 
lean::dec(x_443);
x_455 = lean::cnstr_get(x_442, 1);
lean::inc(x_455);
lean::dec(x_442);
x_458 = l_lean_ir_cpp_emit__var(x_358, x_1, x_455);
x_459 = lean::cnstr_get(x_458, 0);
lean::inc(x_459);
if (lean::obj_tag(x_459) == 0)
{
obj* x_461; obj* x_463; obj* x_464; obj* x_466; obj* x_467; obj* x_468; 
x_461 = lean::cnstr_get(x_458, 1);
if (lean::is_exclusive(x_458)) {
 lean::cnstr_release(x_458, 0);
 x_463 = x_458;
} else {
 lean::inc(x_461);
 lean::dec(x_458);
 x_463 = lean::box(0);
}
x_464 = lean::cnstr_get(x_459, 0);
if (lean::is_exclusive(x_459)) {
 x_466 = x_459;
} else {
 lean::inc(x_464);
 lean::dec(x_459);
 x_466 = lean::box(0);
}
if (lean::is_scalar(x_466)) {
 x_467 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_467 = x_466;
}
lean::cnstr_set(x_467, 0, x_464);
if (lean::is_scalar(x_463)) {
 x_468 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_468 = x_463;
}
lean::cnstr_set(x_468, 0, x_467);
lean::cnstr_set(x_468, 1, x_461);
x_3 = x_468;
goto lbl_4;
}
else
{
obj* x_469; obj* x_472; obj* x_475; obj* x_476; obj* x_477; 
x_469 = lean::cnstr_get(x_458, 1);
lean::inc(x_469);
lean::dec(x_458);
x_472 = lean::cnstr_get(x_459, 0);
lean::inc(x_472);
lean::dec(x_459);
x_475 = l_option_has__repr___rarg___closed__3;
x_476 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_475, x_1, x_469);
x_477 = lean::cnstr_get(x_476, 0);
lean::inc(x_477);
if (lean::obj_tag(x_477) == 0)
{
obj* x_480; obj* x_482; obj* x_483; obj* x_485; obj* x_486; obj* x_487; 
lean::dec(x_472);
x_480 = lean::cnstr_get(x_476, 1);
if (lean::is_exclusive(x_476)) {
 lean::cnstr_release(x_476, 0);
 x_482 = x_476;
} else {
 lean::inc(x_480);
 lean::dec(x_476);
 x_482 = lean::box(0);
}
x_483 = lean::cnstr_get(x_477, 0);
if (lean::is_exclusive(x_477)) {
 x_485 = x_477;
} else {
 lean::inc(x_483);
 lean::dec(x_477);
 x_485 = lean::box(0);
}
if (lean::is_scalar(x_485)) {
 x_486 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_486 = x_485;
}
lean::cnstr_set(x_486, 0, x_483);
if (lean::is_scalar(x_482)) {
 x_487 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_487 = x_482;
}
lean::cnstr_set(x_487, 0, x_486);
lean::cnstr_set(x_487, 1, x_480);
x_3 = x_487;
goto lbl_4;
}
else
{
obj* x_488; obj* x_489; obj* x_491; obj* x_492; obj* x_493; 
if (lean::is_exclusive(x_477)) {
 lean::cnstr_release(x_477, 0);
 x_488 = x_477;
} else {
 lean::dec(x_477);
 x_488 = lean::box(0);
}
x_489 = lean::cnstr_get(x_476, 1);
if (lean::is_exclusive(x_476)) {
 lean::cnstr_release(x_476, 0);
 x_491 = x_476;
} else {
 lean::inc(x_489);
 lean::dec(x_476);
 x_491 = lean::box(0);
}
if (lean::is_scalar(x_488)) {
 x_492 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_492 = x_488;
}
lean::cnstr_set(x_492, 0, x_472);
if (lean::is_scalar(x_491)) {
 x_493 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_493 = x_491;
}
lean::cnstr_set(x_493, 0, x_492);
lean::cnstr_set(x_493, 1, x_489);
x_3 = x_493;
goto lbl_4;
}
}
}
}
}
}
case 8:
{
obj* x_494; obj* x_496; uint16 x_498; obj* x_499; obj* x_500; obj* x_502; obj* x_503; 
x_494 = lean::cnstr_get(x_0, 0);
lean::inc(x_494);
x_496 = lean::cnstr_get(x_0, 1);
lean::inc(x_496);
x_498 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
x_502 = l_lean_ir_cpp_emit__var(x_494, x_1, x_2);
x_503 = lean::cnstr_get(x_502, 0);
lean::inc(x_503);
if (lean::obj_tag(x_503) == 0)
{
obj* x_505; obj* x_508; obj* x_510; obj* x_511; 
x_505 = lean::cnstr_get(x_502, 1);
lean::inc(x_505);
lean::dec(x_502);
x_508 = lean::cnstr_get(x_503, 0);
if (lean::is_exclusive(x_503)) {
 x_510 = x_503;
} else {
 lean::inc(x_508);
 lean::dec(x_503);
 x_510 = lean::box(0);
}
if (lean::is_scalar(x_510)) {
 x_511 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_511 = x_510;
}
lean::cnstr_set(x_511, 0, x_508);
x_499 = x_511;
x_500 = x_505;
goto lbl_501;
}
else
{
obj* x_513; obj* x_516; obj* x_517; obj* x_518; obj* x_520; 
lean::dec(x_503);
x_513 = lean::cnstr_get(x_502, 1);
lean::inc(x_513);
lean::dec(x_502);
x_516 = l_lean_ir_cpp_emit__instr___closed__3;
x_517 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_516, x_1, x_513);
x_518 = lean::cnstr_get(x_517, 0);
lean::inc(x_518);
x_520 = lean::cnstr_get(x_517, 1);
lean::inc(x_520);
lean::dec(x_517);
x_499 = x_518;
x_500 = x_520;
goto lbl_501;
}
lbl_501:
{
if (lean::obj_tag(x_499) == 0)
{
obj* x_524; obj* x_526; obj* x_527; obj* x_528; 
lean::dec(x_496);
x_524 = lean::cnstr_get(x_499, 0);
if (lean::is_exclusive(x_499)) {
 x_526 = x_499;
} else {
 lean::inc(x_524);
 lean::dec(x_499);
 x_526 = lean::box(0);
}
if (lean::is_scalar(x_526)) {
 x_527 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_527 = x_526;
}
lean::cnstr_set(x_527, 0, x_524);
x_528 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_528, 0, x_527);
lean::cnstr_set(x_528, 1, x_500);
x_3 = x_528;
goto lbl_4;
}
else
{
obj* x_530; obj* x_531; obj* x_532; 
lean::dec(x_499);
x_530 = l_prod_has__repr___rarg___closed__1;
x_531 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_530, x_1, x_500);
x_532 = lean::cnstr_get(x_531, 0);
lean::inc(x_532);
if (lean::obj_tag(x_532) == 0)
{
obj* x_535; obj* x_537; obj* x_538; obj* x_540; obj* x_541; obj* x_542; 
lean::dec(x_496);
x_535 = lean::cnstr_get(x_531, 1);
if (lean::is_exclusive(x_531)) {
 lean::cnstr_release(x_531, 0);
 x_537 = x_531;
} else {
 lean::inc(x_535);
 lean::dec(x_531);
 x_537 = lean::box(0);
}
x_538 = lean::cnstr_get(x_532, 0);
if (lean::is_exclusive(x_532)) {
 x_540 = x_532;
} else {
 lean::inc(x_538);
 lean::dec(x_532);
 x_540 = lean::box(0);
}
if (lean::is_scalar(x_540)) {
 x_541 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_541 = x_540;
}
lean::cnstr_set(x_541, 0, x_538);
if (lean::is_scalar(x_537)) {
 x_542 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_542 = x_537;
}
lean::cnstr_set(x_542, 0, x_541);
lean::cnstr_set(x_542, 1, x_535);
x_3 = x_542;
goto lbl_4;
}
else
{
obj* x_544; obj* x_547; obj* x_548; 
lean::dec(x_532);
x_544 = lean::cnstr_get(x_531, 1);
lean::inc(x_544);
lean::dec(x_531);
x_547 = l_lean_ir_cpp_emit__var(x_496, x_1, x_544);
x_548 = lean::cnstr_get(x_547, 0);
lean::inc(x_548);
if (lean::obj_tag(x_548) == 0)
{
obj* x_550; obj* x_552; obj* x_553; obj* x_555; obj* x_556; obj* x_557; 
x_550 = lean::cnstr_get(x_547, 1);
if (lean::is_exclusive(x_547)) {
 lean::cnstr_release(x_547, 0);
 x_552 = x_547;
} else {
 lean::inc(x_550);
 lean::dec(x_547);
 x_552 = lean::box(0);
}
x_553 = lean::cnstr_get(x_548, 0);
if (lean::is_exclusive(x_548)) {
 x_555 = x_548;
} else {
 lean::inc(x_553);
 lean::dec(x_548);
 x_555 = lean::box(0);
}
if (lean::is_scalar(x_555)) {
 x_556 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_556 = x_555;
}
lean::cnstr_set(x_556, 0, x_553);
if (lean::is_scalar(x_552)) {
 x_557 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_557 = x_552;
}
lean::cnstr_set(x_557, 0, x_556);
lean::cnstr_set(x_557, 1, x_550);
x_3 = x_557;
goto lbl_4;
}
else
{
obj* x_559; obj* x_562; obj* x_563; obj* x_564; 
lean::dec(x_548);
x_559 = lean::cnstr_get(x_547, 1);
lean::inc(x_559);
lean::dec(x_547);
x_562 = l_list_repr__aux___main___rarg___closed__1;
x_563 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_562, x_1, x_559);
x_564 = lean::cnstr_get(x_563, 0);
lean::inc(x_564);
if (lean::obj_tag(x_564) == 0)
{
obj* x_566; obj* x_568; obj* x_569; obj* x_571; obj* x_572; obj* x_573; 
x_566 = lean::cnstr_get(x_563, 1);
if (lean::is_exclusive(x_563)) {
 lean::cnstr_release(x_563, 0);
 x_568 = x_563;
} else {
 lean::inc(x_566);
 lean::dec(x_563);
 x_568 = lean::box(0);
}
x_569 = lean::cnstr_get(x_564, 0);
if (lean::is_exclusive(x_564)) {
 x_571 = x_564;
} else {
 lean::inc(x_569);
 lean::dec(x_564);
 x_571 = lean::box(0);
}
if (lean::is_scalar(x_571)) {
 x_572 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_572 = x_571;
}
lean::cnstr_set(x_572, 0, x_569);
if (lean::is_scalar(x_568)) {
 x_573 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_573 = x_568;
}
lean::cnstr_set(x_573, 0, x_572);
lean::cnstr_set(x_573, 1, x_566);
x_3 = x_573;
goto lbl_4;
}
else
{
obj* x_575; obj* x_578; obj* x_579; 
lean::dec(x_564);
x_575 = lean::cnstr_get(x_563, 1);
lean::inc(x_575);
lean::dec(x_563);
x_578 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_498, x_1, x_575);
x_579 = lean::cnstr_get(x_578, 0);
lean::inc(x_579);
if (lean::obj_tag(x_579) == 0)
{
obj* x_581; obj* x_583; obj* x_584; obj* x_586; obj* x_587; obj* x_588; 
x_581 = lean::cnstr_get(x_578, 1);
if (lean::is_exclusive(x_578)) {
 lean::cnstr_release(x_578, 0);
 x_583 = x_578;
} else {
 lean::inc(x_581);
 lean::dec(x_578);
 x_583 = lean::box(0);
}
x_584 = lean::cnstr_get(x_579, 0);
if (lean::is_exclusive(x_579)) {
 x_586 = x_579;
} else {
 lean::inc(x_584);
 lean::dec(x_579);
 x_586 = lean::box(0);
}
if (lean::is_scalar(x_586)) {
 x_587 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_587 = x_586;
}
lean::cnstr_set(x_587, 0, x_584);
if (lean::is_scalar(x_583)) {
 x_588 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_588 = x_583;
}
lean::cnstr_set(x_588, 0, x_587);
lean::cnstr_set(x_588, 1, x_581);
x_3 = x_588;
goto lbl_4;
}
else
{
obj* x_589; obj* x_592; obj* x_595; obj* x_596; obj* x_597; 
x_589 = lean::cnstr_get(x_578, 1);
lean::inc(x_589);
lean::dec(x_578);
x_592 = lean::cnstr_get(x_579, 0);
lean::inc(x_592);
lean::dec(x_579);
x_595 = l_option_has__repr___rarg___closed__3;
x_596 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_595, x_1, x_589);
x_597 = lean::cnstr_get(x_596, 0);
lean::inc(x_597);
if (lean::obj_tag(x_597) == 0)
{
obj* x_600; obj* x_602; obj* x_603; obj* x_605; obj* x_606; obj* x_607; 
lean::dec(x_592);
x_600 = lean::cnstr_get(x_596, 1);
if (lean::is_exclusive(x_596)) {
 lean::cnstr_release(x_596, 0);
 x_602 = x_596;
} else {
 lean::inc(x_600);
 lean::dec(x_596);
 x_602 = lean::box(0);
}
x_603 = lean::cnstr_get(x_597, 0);
if (lean::is_exclusive(x_597)) {
 x_605 = x_597;
} else {
 lean::inc(x_603);
 lean::dec(x_597);
 x_605 = lean::box(0);
}
if (lean::is_scalar(x_605)) {
 x_606 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_606 = x_605;
}
lean::cnstr_set(x_606, 0, x_603);
if (lean::is_scalar(x_602)) {
 x_607 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_607 = x_602;
}
lean::cnstr_set(x_607, 0, x_606);
lean::cnstr_set(x_607, 1, x_600);
x_3 = x_607;
goto lbl_4;
}
else
{
obj* x_608; obj* x_609; obj* x_611; obj* x_612; obj* x_613; 
if (lean::is_exclusive(x_597)) {
 lean::cnstr_release(x_597, 0);
 x_608 = x_597;
} else {
 lean::dec(x_597);
 x_608 = lean::box(0);
}
x_609 = lean::cnstr_get(x_596, 1);
if (lean::is_exclusive(x_596)) {
 lean::cnstr_release(x_596, 0);
 x_611 = x_596;
} else {
 lean::inc(x_609);
 lean::dec(x_596);
 x_611 = lean::box(0);
}
if (lean::is_scalar(x_608)) {
 x_612 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_612 = x_608;
}
lean::cnstr_set(x_612, 0, x_592);
if (lean::is_scalar(x_611)) {
 x_613 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_613 = x_611;
}
lean::cnstr_set(x_613, 0, x_612);
lean::cnstr_set(x_613, 1, x_609);
x_3 = x_613;
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
obj* x_614; usize x_616; obj* x_617; obj* x_619; obj* x_620; obj* x_622; obj* x_623; obj* x_624; 
x_614 = lean::cnstr_get(x_0, 0);
lean::inc(x_614);
x_616 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
x_617 = lean::cnstr_get(x_0, 1);
lean::inc(x_617);
x_622 = l_lean_ir_cpp_emit__instr___closed__4;
x_623 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_622, x_1, x_2);
x_624 = lean::cnstr_get(x_623, 0);
lean::inc(x_624);
if (lean::obj_tag(x_624) == 0)
{
obj* x_628; obj* x_630; obj* x_631; obj* x_633; obj* x_634; obj* x_635; 
lean::dec(x_617);
lean::dec(x_614);
x_628 = lean::cnstr_get(x_623, 1);
if (lean::is_exclusive(x_623)) {
 lean::cnstr_release(x_623, 0);
 x_630 = x_623;
} else {
 lean::inc(x_628);
 lean::dec(x_623);
 x_630 = lean::box(0);
}
x_631 = lean::cnstr_get(x_624, 0);
if (lean::is_exclusive(x_624)) {
 x_633 = x_624;
} else {
 lean::inc(x_631);
 lean::dec(x_624);
 x_633 = lean::box(0);
}
if (lean::is_scalar(x_633)) {
 x_634 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_634 = x_633;
}
lean::cnstr_set(x_634, 0, x_631);
if (lean::is_scalar(x_630)) {
 x_635 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_635 = x_630;
}
lean::cnstr_set(x_635, 0, x_634);
lean::cnstr_set(x_635, 1, x_628);
x_3 = x_635;
goto lbl_4;
}
else
{
obj* x_637; obj* x_640; obj* x_641; obj* x_642; 
lean::dec(x_624);
x_637 = lean::cnstr_get(x_623, 1);
lean::inc(x_637);
lean::dec(x_623);
x_640 = l_prod_has__repr___rarg___closed__1;
x_641 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_640, x_1, x_637);
x_642 = lean::cnstr_get(x_641, 0);
lean::inc(x_642);
if (lean::obj_tag(x_642) == 0)
{
obj* x_646; obj* x_648; obj* x_649; obj* x_651; obj* x_652; obj* x_653; 
lean::dec(x_617);
lean::dec(x_614);
x_646 = lean::cnstr_get(x_641, 1);
if (lean::is_exclusive(x_641)) {
 lean::cnstr_release(x_641, 0);
 x_648 = x_641;
} else {
 lean::inc(x_646);
 lean::dec(x_641);
 x_648 = lean::box(0);
}
x_649 = lean::cnstr_get(x_642, 0);
if (lean::is_exclusive(x_642)) {
 x_651 = x_642;
} else {
 lean::inc(x_649);
 lean::dec(x_642);
 x_651 = lean::box(0);
}
if (lean::is_scalar(x_651)) {
 x_652 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_652 = x_651;
}
lean::cnstr_set(x_652, 0, x_649);
if (lean::is_scalar(x_648)) {
 x_653 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_653 = x_648;
}
lean::cnstr_set(x_653, 0, x_652);
lean::cnstr_set(x_653, 1, x_646);
x_3 = x_653;
goto lbl_4;
}
else
{
obj* x_655; obj* x_658; obj* x_659; 
lean::dec(x_642);
x_655 = lean::cnstr_get(x_641, 1);
lean::inc(x_655);
lean::dec(x_641);
x_658 = l_lean_ir_cpp_emit__var(x_614, x_1, x_655);
x_659 = lean::cnstr_get(x_658, 0);
lean::inc(x_659);
if (lean::obj_tag(x_659) == 0)
{
obj* x_661; obj* x_664; obj* x_666; obj* x_667; 
x_661 = lean::cnstr_get(x_658, 1);
lean::inc(x_661);
lean::dec(x_658);
x_664 = lean::cnstr_get(x_659, 0);
if (lean::is_exclusive(x_659)) {
 x_666 = x_659;
} else {
 lean::inc(x_664);
 lean::dec(x_659);
 x_666 = lean::box(0);
}
if (lean::is_scalar(x_666)) {
 x_667 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_667 = x_666;
}
lean::cnstr_set(x_667, 0, x_664);
x_619 = x_667;
x_620 = x_661;
goto lbl_621;
}
else
{
obj* x_669; obj* x_672; obj* x_673; obj* x_674; 
lean::dec(x_659);
x_669 = lean::cnstr_get(x_658, 1);
lean::inc(x_669);
lean::dec(x_658);
x_672 = l_list_repr__aux___main___rarg___closed__1;
x_673 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_672, x_1, x_669);
x_674 = lean::cnstr_get(x_673, 0);
lean::inc(x_674);
if (lean::obj_tag(x_674) == 0)
{
obj* x_676; obj* x_679; obj* x_681; obj* x_682; 
x_676 = lean::cnstr_get(x_673, 1);
lean::inc(x_676);
lean::dec(x_673);
x_679 = lean::cnstr_get(x_674, 0);
if (lean::is_exclusive(x_674)) {
 x_681 = x_674;
} else {
 lean::inc(x_679);
 lean::dec(x_674);
 x_681 = lean::box(0);
}
if (lean::is_scalar(x_681)) {
 x_682 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_682 = x_681;
}
lean::cnstr_set(x_682, 0, x_679);
x_619 = x_682;
x_620 = x_676;
goto lbl_621;
}
else
{
obj* x_684; obj* x_687; obj* x_688; obj* x_690; 
lean::dec(x_674);
x_684 = lean::cnstr_get(x_673, 1);
lean::inc(x_684);
lean::dec(x_673);
x_687 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(x_616, x_1, x_684);
x_688 = lean::cnstr_get(x_687, 0);
lean::inc(x_688);
x_690 = lean::cnstr_get(x_687, 1);
lean::inc(x_690);
lean::dec(x_687);
x_619 = x_688;
x_620 = x_690;
goto lbl_621;
}
}
}
}
lbl_621:
{
if (lean::obj_tag(x_619) == 0)
{
obj* x_694; obj* x_696; obj* x_697; obj* x_698; 
lean::dec(x_617);
x_694 = lean::cnstr_get(x_619, 0);
if (lean::is_exclusive(x_619)) {
 x_696 = x_619;
} else {
 lean::inc(x_694);
 lean::dec(x_619);
 x_696 = lean::box(0);
}
if (lean::is_scalar(x_696)) {
 x_697 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_697 = x_696;
}
lean::cnstr_set(x_697, 0, x_694);
x_698 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_698, 0, x_697);
lean::cnstr_set(x_698, 1, x_620);
x_3 = x_698;
goto lbl_4;
}
else
{
obj* x_700; obj* x_701; obj* x_702; 
lean::dec(x_619);
x_700 = l_list_repr__aux___main___rarg___closed__1;
x_701 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_700, x_1, x_620);
x_702 = lean::cnstr_get(x_701, 0);
lean::inc(x_702);
if (lean::obj_tag(x_702) == 0)
{
obj* x_705; obj* x_707; obj* x_708; obj* x_710; obj* x_711; obj* x_712; 
lean::dec(x_617);
x_705 = lean::cnstr_get(x_701, 1);
if (lean::is_exclusive(x_701)) {
 lean::cnstr_release(x_701, 0);
 x_707 = x_701;
} else {
 lean::inc(x_705);
 lean::dec(x_701);
 x_707 = lean::box(0);
}
x_708 = lean::cnstr_get(x_702, 0);
if (lean::is_exclusive(x_702)) {
 x_710 = x_702;
} else {
 lean::inc(x_708);
 lean::dec(x_702);
 x_710 = lean::box(0);
}
if (lean::is_scalar(x_710)) {
 x_711 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_711 = x_710;
}
lean::cnstr_set(x_711, 0, x_708);
if (lean::is_scalar(x_707)) {
 x_712 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_712 = x_707;
}
lean::cnstr_set(x_712, 0, x_711);
lean::cnstr_set(x_712, 1, x_705);
x_3 = x_712;
goto lbl_4;
}
else
{
obj* x_714; obj* x_717; obj* x_718; 
lean::dec(x_702);
x_714 = lean::cnstr_get(x_701, 1);
lean::inc(x_714);
lean::dec(x_701);
x_717 = l_lean_ir_cpp_emit__var(x_617, x_1, x_714);
x_718 = lean::cnstr_get(x_717, 0);
lean::inc(x_718);
if (lean::obj_tag(x_718) == 0)
{
obj* x_720; obj* x_722; obj* x_723; obj* x_725; obj* x_726; obj* x_727; 
x_720 = lean::cnstr_get(x_717, 1);
if (lean::is_exclusive(x_717)) {
 lean::cnstr_release(x_717, 0);
 x_722 = x_717;
} else {
 lean::inc(x_720);
 lean::dec(x_717);
 x_722 = lean::box(0);
}
x_723 = lean::cnstr_get(x_718, 0);
if (lean::is_exclusive(x_718)) {
 x_725 = x_718;
} else {
 lean::inc(x_723);
 lean::dec(x_718);
 x_725 = lean::box(0);
}
if (lean::is_scalar(x_725)) {
 x_726 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_726 = x_725;
}
lean::cnstr_set(x_726, 0, x_723);
if (lean::is_scalar(x_722)) {
 x_727 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_727 = x_722;
}
lean::cnstr_set(x_727, 0, x_726);
lean::cnstr_set(x_727, 1, x_720);
x_3 = x_727;
goto lbl_4;
}
else
{
obj* x_728; obj* x_731; obj* x_734; obj* x_735; obj* x_736; 
x_728 = lean::cnstr_get(x_717, 1);
lean::inc(x_728);
lean::dec(x_717);
x_731 = lean::cnstr_get(x_718, 0);
lean::inc(x_731);
lean::dec(x_718);
x_734 = l_option_has__repr___rarg___closed__3;
x_735 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_734, x_1, x_728);
x_736 = lean::cnstr_get(x_735, 0);
lean::inc(x_736);
if (lean::obj_tag(x_736) == 0)
{
obj* x_739; obj* x_741; obj* x_742; obj* x_744; obj* x_745; obj* x_746; 
lean::dec(x_731);
x_739 = lean::cnstr_get(x_735, 1);
if (lean::is_exclusive(x_735)) {
 lean::cnstr_release(x_735, 0);
 x_741 = x_735;
} else {
 lean::inc(x_739);
 lean::dec(x_735);
 x_741 = lean::box(0);
}
x_742 = lean::cnstr_get(x_736, 0);
if (lean::is_exclusive(x_736)) {
 x_744 = x_736;
} else {
 lean::inc(x_742);
 lean::dec(x_736);
 x_744 = lean::box(0);
}
if (lean::is_scalar(x_744)) {
 x_745 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_745 = x_744;
}
lean::cnstr_set(x_745, 0, x_742);
if (lean::is_scalar(x_741)) {
 x_746 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_746 = x_741;
}
lean::cnstr_set(x_746, 0, x_745);
lean::cnstr_set(x_746, 1, x_739);
x_3 = x_746;
goto lbl_4;
}
else
{
obj* x_747; obj* x_748; obj* x_750; obj* x_751; obj* x_752; 
if (lean::is_exclusive(x_736)) {
 lean::cnstr_release(x_736, 0);
 x_747 = x_736;
} else {
 lean::dec(x_736);
 x_747 = lean::box(0);
}
x_748 = lean::cnstr_get(x_735, 1);
if (lean::is_exclusive(x_735)) {
 lean::cnstr_release(x_735, 0);
 x_750 = x_735;
} else {
 lean::inc(x_748);
 lean::dec(x_735);
 x_750 = lean::box(0);
}
if (lean::is_scalar(x_747)) {
 x_751 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_751 = x_747;
}
lean::cnstr_set(x_751, 0, x_731);
if (lean::is_scalar(x_750)) {
 x_752 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_752 = x_750;
}
lean::cnstr_set(x_752, 0, x_751);
lean::cnstr_set(x_752, 1, x_748);
x_3 = x_752;
goto lbl_4;
}
}
}
}
}
}
case 10:
{
obj* x_753; uint8 x_755; obj* x_756; usize x_758; obj* x_759; obj* x_760; obj* x_762; obj* x_763; 
x_753 = lean::cnstr_get(x_0, 0);
lean::inc(x_753);
x_755 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_756 = lean::cnstr_get(x_0, 1);
lean::inc(x_756);
x_758 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
x_762 = l_lean_ir_cpp_emit__var(x_753, x_1, x_2);
x_763 = lean::cnstr_get(x_762, 0);
lean::inc(x_763);
if (lean::obj_tag(x_763) == 0)
{
obj* x_765; obj* x_768; obj* x_770; obj* x_771; 
x_765 = lean::cnstr_get(x_762, 1);
lean::inc(x_765);
lean::dec(x_762);
x_768 = lean::cnstr_get(x_763, 0);
if (lean::is_exclusive(x_763)) {
 x_770 = x_763;
} else {
 lean::inc(x_768);
 lean::dec(x_763);
 x_770 = lean::box(0);
}
if (lean::is_scalar(x_770)) {
 x_771 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_771 = x_770;
}
lean::cnstr_set(x_771, 0, x_768);
x_759 = x_771;
x_760 = x_765;
goto lbl_761;
}
else
{
obj* x_773; obj* x_776; obj* x_777; obj* x_778; 
lean::dec(x_763);
x_773 = lean::cnstr_get(x_762, 1);
lean::inc(x_773);
lean::dec(x_762);
x_776 = l_lean_ir_cpp_emit__instr___closed__5;
x_777 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_776, x_1, x_773);
x_778 = lean::cnstr_get(x_777, 0);
lean::inc(x_778);
if (lean::obj_tag(x_778) == 0)
{
obj* x_780; obj* x_783; obj* x_785; obj* x_786; 
x_780 = lean::cnstr_get(x_777, 1);
lean::inc(x_780);
lean::dec(x_777);
x_783 = lean::cnstr_get(x_778, 0);
if (lean::is_exclusive(x_778)) {
 x_785 = x_778;
} else {
 lean::inc(x_783);
 lean::dec(x_778);
 x_785 = lean::box(0);
}
if (lean::is_scalar(x_785)) {
 x_786 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_786 = x_785;
}
lean::cnstr_set(x_786, 0, x_783);
x_759 = x_786;
x_760 = x_780;
goto lbl_761;
}
else
{
obj* x_788; obj* x_792; obj* x_793; obj* x_795; 
lean::dec(x_778);
x_788 = lean::cnstr_get(x_777, 1);
lean::inc(x_788);
lean::dec(x_777);
lean::inc(x_1);
x_792 = l_lean_ir_cpp_emit__template__param(x_755, x_1, x_788);
x_793 = lean::cnstr_get(x_792, 0);
lean::inc(x_793);
x_795 = lean::cnstr_get(x_792, 1);
lean::inc(x_795);
lean::dec(x_792);
x_759 = x_793;
x_760 = x_795;
goto lbl_761;
}
}
lbl_761:
{
if (lean::obj_tag(x_759) == 0)
{
obj* x_799; obj* x_801; obj* x_802; obj* x_803; 
lean::dec(x_756);
x_799 = lean::cnstr_get(x_759, 0);
if (lean::is_exclusive(x_759)) {
 x_801 = x_759;
} else {
 lean::inc(x_799);
 lean::dec(x_759);
 x_801 = lean::box(0);
}
if (lean::is_scalar(x_801)) {
 x_802 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_802 = x_801;
}
lean::cnstr_set(x_802, 0, x_799);
x_803 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_803, 0, x_802);
lean::cnstr_set(x_803, 1, x_760);
x_3 = x_803;
goto lbl_4;
}
else
{
obj* x_805; obj* x_806; obj* x_807; 
lean::dec(x_759);
x_805 = l_prod_has__repr___rarg___closed__1;
x_806 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_805, x_1, x_760);
x_807 = lean::cnstr_get(x_806, 0);
lean::inc(x_807);
if (lean::obj_tag(x_807) == 0)
{
obj* x_810; obj* x_812; obj* x_813; obj* x_815; obj* x_816; obj* x_817; 
lean::dec(x_756);
x_810 = lean::cnstr_get(x_806, 1);
if (lean::is_exclusive(x_806)) {
 lean::cnstr_release(x_806, 0);
 x_812 = x_806;
} else {
 lean::inc(x_810);
 lean::dec(x_806);
 x_812 = lean::box(0);
}
x_813 = lean::cnstr_get(x_807, 0);
if (lean::is_exclusive(x_807)) {
 x_815 = x_807;
} else {
 lean::inc(x_813);
 lean::dec(x_807);
 x_815 = lean::box(0);
}
if (lean::is_scalar(x_815)) {
 x_816 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_816 = x_815;
}
lean::cnstr_set(x_816, 0, x_813);
if (lean::is_scalar(x_812)) {
 x_817 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_817 = x_812;
}
lean::cnstr_set(x_817, 0, x_816);
lean::cnstr_set(x_817, 1, x_810);
x_3 = x_817;
goto lbl_4;
}
else
{
obj* x_819; obj* x_822; obj* x_823; 
lean::dec(x_807);
x_819 = lean::cnstr_get(x_806, 1);
lean::inc(x_819);
lean::dec(x_806);
x_822 = l_lean_ir_cpp_emit__var(x_756, x_1, x_819);
x_823 = lean::cnstr_get(x_822, 0);
lean::inc(x_823);
if (lean::obj_tag(x_823) == 0)
{
obj* x_825; obj* x_827; obj* x_828; obj* x_830; obj* x_831; obj* x_832; 
x_825 = lean::cnstr_get(x_822, 1);
if (lean::is_exclusive(x_822)) {
 lean::cnstr_release(x_822, 0);
 x_827 = x_822;
} else {
 lean::inc(x_825);
 lean::dec(x_822);
 x_827 = lean::box(0);
}
x_828 = lean::cnstr_get(x_823, 0);
if (lean::is_exclusive(x_823)) {
 x_830 = x_823;
} else {
 lean::inc(x_828);
 lean::dec(x_823);
 x_830 = lean::box(0);
}
if (lean::is_scalar(x_830)) {
 x_831 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_831 = x_830;
}
lean::cnstr_set(x_831, 0, x_828);
if (lean::is_scalar(x_827)) {
 x_832 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_832 = x_827;
}
lean::cnstr_set(x_832, 0, x_831);
lean::cnstr_set(x_832, 1, x_825);
x_3 = x_832;
goto lbl_4;
}
else
{
obj* x_834; obj* x_837; obj* x_838; obj* x_839; 
lean::dec(x_823);
x_834 = lean::cnstr_get(x_822, 1);
lean::inc(x_834);
lean::dec(x_822);
x_837 = l_list_repr__aux___main___rarg___closed__1;
x_838 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_837, x_1, x_834);
x_839 = lean::cnstr_get(x_838, 0);
lean::inc(x_839);
if (lean::obj_tag(x_839) == 0)
{
obj* x_841; obj* x_843; obj* x_844; obj* x_846; obj* x_847; obj* x_848; 
x_841 = lean::cnstr_get(x_838, 1);
if (lean::is_exclusive(x_838)) {
 lean::cnstr_release(x_838, 0);
 x_843 = x_838;
} else {
 lean::inc(x_841);
 lean::dec(x_838);
 x_843 = lean::box(0);
}
x_844 = lean::cnstr_get(x_839, 0);
if (lean::is_exclusive(x_839)) {
 x_846 = x_839;
} else {
 lean::inc(x_844);
 lean::dec(x_839);
 x_846 = lean::box(0);
}
if (lean::is_scalar(x_846)) {
 x_847 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_847 = x_846;
}
lean::cnstr_set(x_847, 0, x_844);
if (lean::is_scalar(x_843)) {
 x_848 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_848 = x_843;
}
lean::cnstr_set(x_848, 0, x_847);
lean::cnstr_set(x_848, 1, x_841);
x_3 = x_848;
goto lbl_4;
}
else
{
obj* x_850; obj* x_853; obj* x_854; 
lean::dec(x_839);
x_850 = lean::cnstr_get(x_838, 1);
lean::inc(x_850);
lean::dec(x_838);
x_853 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(x_758, x_1, x_850);
x_854 = lean::cnstr_get(x_853, 0);
lean::inc(x_854);
if (lean::obj_tag(x_854) == 0)
{
obj* x_856; obj* x_858; obj* x_859; obj* x_861; obj* x_862; obj* x_863; 
x_856 = lean::cnstr_get(x_853, 1);
if (lean::is_exclusive(x_853)) {
 lean::cnstr_release(x_853, 0);
 x_858 = x_853;
} else {
 lean::inc(x_856);
 lean::dec(x_853);
 x_858 = lean::box(0);
}
x_859 = lean::cnstr_get(x_854, 0);
if (lean::is_exclusive(x_854)) {
 x_861 = x_854;
} else {
 lean::inc(x_859);
 lean::dec(x_854);
 x_861 = lean::box(0);
}
if (lean::is_scalar(x_861)) {
 x_862 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_862 = x_861;
}
lean::cnstr_set(x_862, 0, x_859);
if (lean::is_scalar(x_858)) {
 x_863 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_863 = x_858;
}
lean::cnstr_set(x_863, 0, x_862);
lean::cnstr_set(x_863, 1, x_856);
x_3 = x_863;
goto lbl_4;
}
else
{
obj* x_864; obj* x_867; obj* x_870; obj* x_871; obj* x_872; 
x_864 = lean::cnstr_get(x_853, 1);
lean::inc(x_864);
lean::dec(x_853);
x_867 = lean::cnstr_get(x_854, 0);
lean::inc(x_867);
lean::dec(x_854);
x_870 = l_option_has__repr___rarg___closed__3;
x_871 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_870, x_1, x_864);
x_872 = lean::cnstr_get(x_871, 0);
lean::inc(x_872);
if (lean::obj_tag(x_872) == 0)
{
obj* x_875; obj* x_877; obj* x_878; obj* x_880; obj* x_881; obj* x_882; 
lean::dec(x_867);
x_875 = lean::cnstr_get(x_871, 1);
if (lean::is_exclusive(x_871)) {
 lean::cnstr_release(x_871, 0);
 x_877 = x_871;
} else {
 lean::inc(x_875);
 lean::dec(x_871);
 x_877 = lean::box(0);
}
x_878 = lean::cnstr_get(x_872, 0);
if (lean::is_exclusive(x_872)) {
 x_880 = x_872;
} else {
 lean::inc(x_878);
 lean::dec(x_872);
 x_880 = lean::box(0);
}
if (lean::is_scalar(x_880)) {
 x_881 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_881 = x_880;
}
lean::cnstr_set(x_881, 0, x_878);
if (lean::is_scalar(x_877)) {
 x_882 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_882 = x_877;
}
lean::cnstr_set(x_882, 0, x_881);
lean::cnstr_set(x_882, 1, x_875);
x_3 = x_882;
goto lbl_4;
}
else
{
obj* x_883; obj* x_884; obj* x_886; obj* x_887; obj* x_888; 
if (lean::is_exclusive(x_872)) {
 lean::cnstr_release(x_872, 0);
 x_883 = x_872;
} else {
 lean::dec(x_872);
 x_883 = lean::box(0);
}
x_884 = lean::cnstr_get(x_871, 1);
if (lean::is_exclusive(x_871)) {
 lean::cnstr_release(x_871, 0);
 x_886 = x_871;
} else {
 lean::inc(x_884);
 lean::dec(x_871);
 x_886 = lean::box(0);
}
if (lean::is_scalar(x_883)) {
 x_887 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_887 = x_883;
}
lean::cnstr_set(x_887, 0, x_867);
if (lean::is_scalar(x_886)) {
 x_888 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_888 = x_886;
}
lean::cnstr_set(x_888, 0, x_887);
lean::cnstr_set(x_888, 1, x_884);
x_3 = x_888;
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
obj* x_889; obj* x_891; obj* x_893; obj* x_896; 
x_889 = lean::cnstr_get(x_0, 0);
lean::inc(x_889);
x_891 = lean::cnstr_get(x_0, 1);
lean::inc(x_891);
x_893 = lean::cnstr_get(x_0, 2);
lean::inc(x_893);
lean::inc(x_1);
x_896 = l_lean_ir_cpp_emit__closure(x_889, x_891, x_893, x_1, x_2);
x_3 = x_896;
goto lbl_4;
}
case 12:
{
obj* x_897; obj* x_899; obj* x_902; 
x_897 = lean::cnstr_get(x_0, 0);
lean::inc(x_897);
x_899 = lean::cnstr_get(x_0, 1);
lean::inc(x_899);
lean::inc(x_1);
x_902 = l_lean_ir_cpp_emit__apply(x_897, x_899, x_1, x_2);
x_3 = x_902;
goto lbl_4;
}
case 13:
{
obj* x_903; obj* x_905; obj* x_907; obj* x_909; obj* x_910; obj* x_912; obj* x_913; 
x_903 = lean::cnstr_get(x_0, 0);
lean::inc(x_903);
x_905 = lean::cnstr_get(x_0, 1);
lean::inc(x_905);
x_907 = lean::cnstr_get(x_0, 2);
lean::inc(x_907);
x_912 = l_lean_ir_cpp_emit__var(x_903, x_1, x_2);
x_913 = lean::cnstr_get(x_912, 0);
lean::inc(x_913);
if (lean::obj_tag(x_913) == 0)
{
obj* x_915; obj* x_918; obj* x_920; obj* x_921; 
x_915 = lean::cnstr_get(x_912, 1);
lean::inc(x_915);
lean::dec(x_912);
x_918 = lean::cnstr_get(x_913, 0);
if (lean::is_exclusive(x_913)) {
 x_920 = x_913;
} else {
 lean::inc(x_918);
 lean::dec(x_913);
 x_920 = lean::box(0);
}
if (lean::is_scalar(x_920)) {
 x_921 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_921 = x_920;
}
lean::cnstr_set(x_921, 0, x_918);
x_909 = x_921;
x_910 = x_915;
goto lbl_911;
}
else
{
obj* x_923; obj* x_926; obj* x_927; obj* x_928; obj* x_930; 
lean::dec(x_913);
x_923 = lean::cnstr_get(x_912, 1);
lean::inc(x_923);
lean::dec(x_912);
x_926 = l_lean_ir_cpp_emit__instr___closed__6;
x_927 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_926, x_1, x_923);
x_928 = lean::cnstr_get(x_927, 0);
lean::inc(x_928);
x_930 = lean::cnstr_get(x_927, 1);
lean::inc(x_930);
lean::dec(x_927);
x_909 = x_928;
x_910 = x_930;
goto lbl_911;
}
lbl_911:
{
if (lean::obj_tag(x_909) == 0)
{
obj* x_935; obj* x_937; obj* x_938; obj* x_939; 
lean::dec(x_907);
lean::dec(x_905);
x_935 = lean::cnstr_get(x_909, 0);
if (lean::is_exclusive(x_909)) {
 x_937 = x_909;
} else {
 lean::inc(x_935);
 lean::dec(x_909);
 x_937 = lean::box(0);
}
if (lean::is_scalar(x_937)) {
 x_938 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_938 = x_937;
}
lean::cnstr_set(x_938, 0, x_935);
x_939 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_939, 0, x_938);
lean::cnstr_set(x_939, 1, x_910);
x_3 = x_939;
goto lbl_4;
}
else
{
obj* x_941; obj* x_942; obj* x_943; 
lean::dec(x_909);
x_941 = l_prod_has__repr___rarg___closed__1;
x_942 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_941, x_1, x_910);
x_943 = lean::cnstr_get(x_942, 0);
lean::inc(x_943);
if (lean::obj_tag(x_943) == 0)
{
obj* x_947; obj* x_949; obj* x_950; obj* x_952; obj* x_953; obj* x_954; 
lean::dec(x_907);
lean::dec(x_905);
x_947 = lean::cnstr_get(x_942, 1);
if (lean::is_exclusive(x_942)) {
 lean::cnstr_release(x_942, 0);
 x_949 = x_942;
} else {
 lean::inc(x_947);
 lean::dec(x_942);
 x_949 = lean::box(0);
}
x_950 = lean::cnstr_get(x_943, 0);
if (lean::is_exclusive(x_943)) {
 x_952 = x_943;
} else {
 lean::inc(x_950);
 lean::dec(x_943);
 x_952 = lean::box(0);
}
if (lean::is_scalar(x_952)) {
 x_953 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_953 = x_952;
}
lean::cnstr_set(x_953, 0, x_950);
if (lean::is_scalar(x_949)) {
 x_954 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_954 = x_949;
}
lean::cnstr_set(x_954, 0, x_953);
lean::cnstr_set(x_954, 1, x_947);
x_3 = x_954;
goto lbl_4;
}
else
{
obj* x_956; obj* x_959; obj* x_960; 
lean::dec(x_943);
x_956 = lean::cnstr_get(x_942, 1);
lean::inc(x_956);
lean::dec(x_942);
x_959 = l_lean_ir_cpp_emit__var(x_905, x_1, x_956);
x_960 = lean::cnstr_get(x_959, 0);
lean::inc(x_960);
if (lean::obj_tag(x_960) == 0)
{
obj* x_963; obj* x_965; obj* x_966; obj* x_968; obj* x_969; obj* x_970; 
lean::dec(x_907);
x_963 = lean::cnstr_get(x_959, 1);
if (lean::is_exclusive(x_959)) {
 lean::cnstr_release(x_959, 0);
 x_965 = x_959;
} else {
 lean::inc(x_963);
 lean::dec(x_959);
 x_965 = lean::box(0);
}
x_966 = lean::cnstr_get(x_960, 0);
if (lean::is_exclusive(x_960)) {
 x_968 = x_960;
} else {
 lean::inc(x_966);
 lean::dec(x_960);
 x_968 = lean::box(0);
}
if (lean::is_scalar(x_968)) {
 x_969 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_969 = x_968;
}
lean::cnstr_set(x_969, 0, x_966);
if (lean::is_scalar(x_965)) {
 x_970 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_970 = x_965;
}
lean::cnstr_set(x_970, 0, x_969);
lean::cnstr_set(x_970, 1, x_963);
x_3 = x_970;
goto lbl_4;
}
else
{
obj* x_972; obj* x_975; obj* x_976; obj* x_977; 
lean::dec(x_960);
x_972 = lean::cnstr_get(x_959, 1);
lean::inc(x_972);
lean::dec(x_959);
x_975 = l_list_repr__aux___main___rarg___closed__1;
x_976 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_975, x_1, x_972);
x_977 = lean::cnstr_get(x_976, 0);
lean::inc(x_977);
if (lean::obj_tag(x_977) == 0)
{
obj* x_980; obj* x_982; obj* x_983; obj* x_985; obj* x_986; obj* x_987; 
lean::dec(x_907);
x_980 = lean::cnstr_get(x_976, 1);
if (lean::is_exclusive(x_976)) {
 lean::cnstr_release(x_976, 0);
 x_982 = x_976;
} else {
 lean::inc(x_980);
 lean::dec(x_976);
 x_982 = lean::box(0);
}
x_983 = lean::cnstr_get(x_977, 0);
if (lean::is_exclusive(x_977)) {
 x_985 = x_977;
} else {
 lean::inc(x_983);
 lean::dec(x_977);
 x_985 = lean::box(0);
}
if (lean::is_scalar(x_985)) {
 x_986 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_986 = x_985;
}
lean::cnstr_set(x_986, 0, x_983);
if (lean::is_scalar(x_982)) {
 x_987 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_987 = x_982;
}
lean::cnstr_set(x_987, 0, x_986);
lean::cnstr_set(x_987, 1, x_980);
x_3 = x_987;
goto lbl_4;
}
else
{
obj* x_989; obj* x_992; obj* x_993; 
lean::dec(x_977);
x_989 = lean::cnstr_get(x_976, 1);
lean::inc(x_989);
lean::dec(x_976);
x_992 = l_lean_ir_cpp_emit__var(x_907, x_1, x_989);
x_993 = lean::cnstr_get(x_992, 0);
lean::inc(x_993);
if (lean::obj_tag(x_993) == 0)
{
obj* x_995; obj* x_997; obj* x_998; obj* x_1000; obj* x_1001; obj* x_1002; 
x_995 = lean::cnstr_get(x_992, 1);
if (lean::is_exclusive(x_992)) {
 lean::cnstr_release(x_992, 0);
 x_997 = x_992;
} else {
 lean::inc(x_995);
 lean::dec(x_992);
 x_997 = lean::box(0);
}
x_998 = lean::cnstr_get(x_993, 0);
if (lean::is_exclusive(x_993)) {
 x_1000 = x_993;
} else {
 lean::inc(x_998);
 lean::dec(x_993);
 x_1000 = lean::box(0);
}
if (lean::is_scalar(x_1000)) {
 x_1001 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1001 = x_1000;
}
lean::cnstr_set(x_1001, 0, x_998);
if (lean::is_scalar(x_997)) {
 x_1002 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1002 = x_997;
}
lean::cnstr_set(x_1002, 0, x_1001);
lean::cnstr_set(x_1002, 1, x_995);
x_3 = x_1002;
goto lbl_4;
}
else
{
obj* x_1003; obj* x_1006; obj* x_1009; obj* x_1010; obj* x_1011; 
x_1003 = lean::cnstr_get(x_992, 1);
lean::inc(x_1003);
lean::dec(x_992);
x_1006 = lean::cnstr_get(x_993, 0);
lean::inc(x_1006);
lean::dec(x_993);
x_1009 = l_option_has__repr___rarg___closed__3;
x_1010 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1009, x_1, x_1003);
x_1011 = lean::cnstr_get(x_1010, 0);
lean::inc(x_1011);
if (lean::obj_tag(x_1011) == 0)
{
obj* x_1014; obj* x_1016; obj* x_1017; obj* x_1019; obj* x_1020; obj* x_1021; 
lean::dec(x_1006);
x_1014 = lean::cnstr_get(x_1010, 1);
if (lean::is_exclusive(x_1010)) {
 lean::cnstr_release(x_1010, 0);
 x_1016 = x_1010;
} else {
 lean::inc(x_1014);
 lean::dec(x_1010);
 x_1016 = lean::box(0);
}
x_1017 = lean::cnstr_get(x_1011, 0);
if (lean::is_exclusive(x_1011)) {
 x_1019 = x_1011;
} else {
 lean::inc(x_1017);
 lean::dec(x_1011);
 x_1019 = lean::box(0);
}
if (lean::is_scalar(x_1019)) {
 x_1020 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1020 = x_1019;
}
lean::cnstr_set(x_1020, 0, x_1017);
if (lean::is_scalar(x_1016)) {
 x_1021 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1021 = x_1016;
}
lean::cnstr_set(x_1021, 0, x_1020);
lean::cnstr_set(x_1021, 1, x_1014);
x_3 = x_1021;
goto lbl_4;
}
else
{
obj* x_1022; obj* x_1023; obj* x_1025; obj* x_1026; obj* x_1027; 
if (lean::is_exclusive(x_1011)) {
 lean::cnstr_release(x_1011, 0);
 x_1022 = x_1011;
} else {
 lean::dec(x_1011);
 x_1022 = lean::box(0);
}
x_1023 = lean::cnstr_get(x_1010, 1);
if (lean::is_exclusive(x_1010)) {
 lean::cnstr_release(x_1010, 0);
 x_1025 = x_1010;
} else {
 lean::inc(x_1023);
 lean::dec(x_1010);
 x_1025 = lean::box(0);
}
if (lean::is_scalar(x_1022)) {
 x_1026 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1026 = x_1022;
}
lean::cnstr_set(x_1026, 0, x_1006);
if (lean::is_scalar(x_1025)) {
 x_1027 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1027 = x_1025;
}
lean::cnstr_set(x_1027, 0, x_1026);
lean::cnstr_set(x_1027, 1, x_1023);
x_3 = x_1027;
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
obj* x_1028; uint8 x_1030; obj* x_1031; obj* x_1033; obj* x_1035; obj* x_1036; obj* x_1038; obj* x_1039; obj* x_1041; obj* x_1042; 
x_1028 = lean::cnstr_get(x_0, 0);
lean::inc(x_1028);
x_1030 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_1031 = lean::cnstr_get(x_0, 1);
lean::inc(x_1031);
x_1033 = lean::cnstr_get(x_0, 2);
lean::inc(x_1033);
x_1041 = l_lean_ir_cpp_emit__var(x_1028, x_1, x_2);
x_1042 = lean::cnstr_get(x_1041, 0);
lean::inc(x_1042);
if (lean::obj_tag(x_1042) == 0)
{
obj* x_1044; obj* x_1047; obj* x_1049; obj* x_1050; 
x_1044 = lean::cnstr_get(x_1041, 1);
lean::inc(x_1044);
lean::dec(x_1041);
x_1047 = lean::cnstr_get(x_1042, 0);
if (lean::is_exclusive(x_1042)) {
 x_1049 = x_1042;
} else {
 lean::inc(x_1047);
 lean::dec(x_1042);
 x_1049 = lean::box(0);
}
if (lean::is_scalar(x_1049)) {
 x_1050 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1050 = x_1049;
}
lean::cnstr_set(x_1050, 0, x_1047);
x_1038 = x_1050;
x_1039 = x_1044;
goto lbl_1040;
}
else
{
obj* x_1052; obj* x_1055; obj* x_1056; obj* x_1057; obj* x_1059; 
lean::dec(x_1042);
x_1052 = lean::cnstr_get(x_1041, 1);
lean::inc(x_1052);
lean::dec(x_1041);
x_1055 = l_lean_ir_cpp_emit__instr___closed__7;
x_1056 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1055, x_1, x_1052);
x_1057 = lean::cnstr_get(x_1056, 0);
lean::inc(x_1057);
x_1059 = lean::cnstr_get(x_1056, 1);
lean::inc(x_1059);
lean::dec(x_1056);
x_1038 = x_1057;
x_1039 = x_1059;
goto lbl_1040;
}
lbl_1037:
{
if (lean::obj_tag(x_1035) == 0)
{
obj* x_1063; obj* x_1065; obj* x_1066; obj* x_1067; 
lean::dec(x_1033);
x_1063 = lean::cnstr_get(x_1035, 0);
if (lean::is_exclusive(x_1035)) {
 x_1065 = x_1035;
} else {
 lean::inc(x_1063);
 lean::dec(x_1035);
 x_1065 = lean::box(0);
}
if (lean::is_scalar(x_1065)) {
 x_1066 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1066 = x_1065;
}
lean::cnstr_set(x_1066, 0, x_1063);
x_1067 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1067, 0, x_1066);
lean::cnstr_set(x_1067, 1, x_1036);
x_3 = x_1067;
goto lbl_4;
}
else
{
obj* x_1069; obj* x_1070; obj* x_1071; 
lean::dec(x_1035);
x_1069 = l_list_repr__aux___main___rarg___closed__1;
x_1070 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1069, x_1, x_1036);
x_1071 = lean::cnstr_get(x_1070, 0);
lean::inc(x_1071);
if (lean::obj_tag(x_1071) == 0)
{
obj* x_1074; obj* x_1076; obj* x_1077; obj* x_1079; obj* x_1080; obj* x_1081; 
lean::dec(x_1033);
x_1074 = lean::cnstr_get(x_1070, 1);
if (lean::is_exclusive(x_1070)) {
 lean::cnstr_release(x_1070, 0);
 x_1076 = x_1070;
} else {
 lean::inc(x_1074);
 lean::dec(x_1070);
 x_1076 = lean::box(0);
}
x_1077 = lean::cnstr_get(x_1071, 0);
if (lean::is_exclusive(x_1071)) {
 x_1079 = x_1071;
} else {
 lean::inc(x_1077);
 lean::dec(x_1071);
 x_1079 = lean::box(0);
}
if (lean::is_scalar(x_1079)) {
 x_1080 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1080 = x_1079;
}
lean::cnstr_set(x_1080, 0, x_1077);
if (lean::is_scalar(x_1076)) {
 x_1081 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1081 = x_1076;
}
lean::cnstr_set(x_1081, 0, x_1080);
lean::cnstr_set(x_1081, 1, x_1074);
x_3 = x_1081;
goto lbl_4;
}
else
{
obj* x_1083; obj* x_1086; obj* x_1087; 
lean::dec(x_1071);
x_1083 = lean::cnstr_get(x_1070, 1);
lean::inc(x_1083);
lean::dec(x_1070);
x_1086 = l_lean_ir_cpp_emit__var(x_1033, x_1, x_1083);
x_1087 = lean::cnstr_get(x_1086, 0);
lean::inc(x_1087);
if (lean::obj_tag(x_1087) == 0)
{
obj* x_1089; obj* x_1091; obj* x_1092; obj* x_1094; obj* x_1095; obj* x_1096; 
x_1089 = lean::cnstr_get(x_1086, 1);
if (lean::is_exclusive(x_1086)) {
 lean::cnstr_release(x_1086, 0);
 x_1091 = x_1086;
} else {
 lean::inc(x_1089);
 lean::dec(x_1086);
 x_1091 = lean::box(0);
}
x_1092 = lean::cnstr_get(x_1087, 0);
if (lean::is_exclusive(x_1087)) {
 x_1094 = x_1087;
} else {
 lean::inc(x_1092);
 lean::dec(x_1087);
 x_1094 = lean::box(0);
}
if (lean::is_scalar(x_1094)) {
 x_1095 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1095 = x_1094;
}
lean::cnstr_set(x_1095, 0, x_1092);
if (lean::is_scalar(x_1091)) {
 x_1096 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1096 = x_1091;
}
lean::cnstr_set(x_1096, 0, x_1095);
lean::cnstr_set(x_1096, 1, x_1089);
x_3 = x_1096;
goto lbl_4;
}
else
{
obj* x_1097; obj* x_1100; obj* x_1103; obj* x_1104; obj* x_1105; 
x_1097 = lean::cnstr_get(x_1086, 1);
lean::inc(x_1097);
lean::dec(x_1086);
x_1100 = lean::cnstr_get(x_1087, 0);
lean::inc(x_1100);
lean::dec(x_1087);
x_1103 = l_option_has__repr___rarg___closed__3;
x_1104 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1103, x_1, x_1097);
x_1105 = lean::cnstr_get(x_1104, 0);
lean::inc(x_1105);
if (lean::obj_tag(x_1105) == 0)
{
obj* x_1108; obj* x_1110; obj* x_1111; obj* x_1113; obj* x_1114; obj* x_1115; 
lean::dec(x_1100);
x_1108 = lean::cnstr_get(x_1104, 1);
if (lean::is_exclusive(x_1104)) {
 lean::cnstr_release(x_1104, 0);
 x_1110 = x_1104;
} else {
 lean::inc(x_1108);
 lean::dec(x_1104);
 x_1110 = lean::box(0);
}
x_1111 = lean::cnstr_get(x_1105, 0);
if (lean::is_exclusive(x_1105)) {
 x_1113 = x_1105;
} else {
 lean::inc(x_1111);
 lean::dec(x_1105);
 x_1113 = lean::box(0);
}
if (lean::is_scalar(x_1113)) {
 x_1114 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1114 = x_1113;
}
lean::cnstr_set(x_1114, 0, x_1111);
if (lean::is_scalar(x_1110)) {
 x_1115 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1115 = x_1110;
}
lean::cnstr_set(x_1115, 0, x_1114);
lean::cnstr_set(x_1115, 1, x_1108);
x_3 = x_1115;
goto lbl_4;
}
else
{
obj* x_1116; obj* x_1117; obj* x_1119; obj* x_1120; obj* x_1121; 
if (lean::is_exclusive(x_1105)) {
 lean::cnstr_release(x_1105, 0);
 x_1116 = x_1105;
} else {
 lean::dec(x_1105);
 x_1116 = lean::box(0);
}
x_1117 = lean::cnstr_get(x_1104, 1);
if (lean::is_exclusive(x_1104)) {
 lean::cnstr_release(x_1104, 0);
 x_1119 = x_1104;
} else {
 lean::inc(x_1117);
 lean::dec(x_1104);
 x_1119 = lean::box(0);
}
if (lean::is_scalar(x_1116)) {
 x_1120 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1120 = x_1116;
}
lean::cnstr_set(x_1120, 0, x_1100);
if (lean::is_scalar(x_1119)) {
 x_1121 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1121 = x_1119;
}
lean::cnstr_set(x_1121, 0, x_1120);
lean::cnstr_set(x_1121, 1, x_1117);
x_3 = x_1121;
goto lbl_4;
}
}
}
}
}
lbl_1040:
{
if (lean::obj_tag(x_1038) == 0)
{
obj* x_1124; obj* x_1126; obj* x_1127; obj* x_1128; 
lean::dec(x_1033);
lean::dec(x_1031);
x_1124 = lean::cnstr_get(x_1038, 0);
if (lean::is_exclusive(x_1038)) {
 x_1126 = x_1038;
} else {
 lean::inc(x_1124);
 lean::dec(x_1038);
 x_1126 = lean::box(0);
}
if (lean::is_scalar(x_1126)) {
 x_1127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1127 = x_1126;
}
lean::cnstr_set(x_1127, 0, x_1124);
x_1128 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1128, 0, x_1127);
lean::cnstr_set(x_1128, 1, x_1039);
x_3 = x_1128;
goto lbl_4;
}
else
{
obj* x_1130; obj* x_1131; obj* x_1132; 
lean::dec(x_1038);
x_1130 = l_prod_has__repr___rarg___closed__1;
x_1131 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1130, x_1, x_1039);
x_1132 = lean::cnstr_get(x_1131, 0);
lean::inc(x_1132);
if (lean::obj_tag(x_1132) == 0)
{
obj* x_1136; obj* x_1138; obj* x_1139; obj* x_1141; obj* x_1142; obj* x_1143; 
lean::dec(x_1033);
lean::dec(x_1031);
x_1136 = lean::cnstr_get(x_1131, 1);
if (lean::is_exclusive(x_1131)) {
 lean::cnstr_release(x_1131, 0);
 x_1138 = x_1131;
} else {
 lean::inc(x_1136);
 lean::dec(x_1131);
 x_1138 = lean::box(0);
}
x_1139 = lean::cnstr_get(x_1132, 0);
if (lean::is_exclusive(x_1132)) {
 x_1141 = x_1132;
} else {
 lean::inc(x_1139);
 lean::dec(x_1132);
 x_1141 = lean::box(0);
}
if (lean::is_scalar(x_1141)) {
 x_1142 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1142 = x_1141;
}
lean::cnstr_set(x_1142, 0, x_1139);
if (lean::is_scalar(x_1138)) {
 x_1143 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1143 = x_1138;
}
lean::cnstr_set(x_1143, 0, x_1142);
lean::cnstr_set(x_1143, 1, x_1136);
x_3 = x_1143;
goto lbl_4;
}
else
{
obj* x_1145; obj* x_1148; obj* x_1149; 
lean::dec(x_1132);
x_1145 = lean::cnstr_get(x_1131, 1);
lean::inc(x_1145);
lean::dec(x_1131);
x_1148 = l_lean_ir_cpp_emit__type__size(x_1030, x_1, x_1145);
x_1149 = lean::cnstr_get(x_1148, 0);
lean::inc(x_1149);
if (lean::obj_tag(x_1149) == 0)
{
obj* x_1152; obj* x_1155; obj* x_1157; obj* x_1158; 
lean::dec(x_1031);
x_1152 = lean::cnstr_get(x_1148, 1);
lean::inc(x_1152);
lean::dec(x_1148);
x_1155 = lean::cnstr_get(x_1149, 0);
if (lean::is_exclusive(x_1149)) {
 x_1157 = x_1149;
} else {
 lean::inc(x_1155);
 lean::dec(x_1149);
 x_1157 = lean::box(0);
}
if (lean::is_scalar(x_1157)) {
 x_1158 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1158 = x_1157;
}
lean::cnstr_set(x_1158, 0, x_1155);
x_1035 = x_1158;
x_1036 = x_1152;
goto lbl_1037;
}
else
{
obj* x_1160; obj* x_1163; obj* x_1164; obj* x_1165; 
lean::dec(x_1149);
x_1160 = lean::cnstr_get(x_1148, 1);
lean::inc(x_1160);
lean::dec(x_1148);
x_1163 = l_list_repr__aux___main___rarg___closed__1;
x_1164 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1163, x_1, x_1160);
x_1165 = lean::cnstr_get(x_1164, 0);
lean::inc(x_1165);
if (lean::obj_tag(x_1165) == 0)
{
obj* x_1168; obj* x_1171; obj* x_1173; obj* x_1174; 
lean::dec(x_1031);
x_1168 = lean::cnstr_get(x_1164, 1);
lean::inc(x_1168);
lean::dec(x_1164);
x_1171 = lean::cnstr_get(x_1165, 0);
if (lean::is_exclusive(x_1165)) {
 x_1173 = x_1165;
} else {
 lean::inc(x_1171);
 lean::dec(x_1165);
 x_1173 = lean::box(0);
}
if (lean::is_scalar(x_1173)) {
 x_1174 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1174 = x_1173;
}
lean::cnstr_set(x_1174, 0, x_1171);
x_1035 = x_1174;
x_1036 = x_1168;
goto lbl_1037;
}
else
{
obj* x_1176; obj* x_1179; obj* x_1180; obj* x_1182; 
lean::dec(x_1165);
x_1176 = lean::cnstr_get(x_1164, 1);
lean::inc(x_1176);
lean::dec(x_1164);
x_1179 = l_lean_ir_cpp_emit__var(x_1031, x_1, x_1176);
x_1180 = lean::cnstr_get(x_1179, 0);
lean::inc(x_1180);
x_1182 = lean::cnstr_get(x_1179, 1);
lean::inc(x_1182);
lean::dec(x_1179);
x_1035 = x_1180;
x_1036 = x_1182;
goto lbl_1037;
}
}
}
}
}
}
default:
{
obj* x_1185; obj* x_1187; obj* x_1189; obj* x_1191; obj* x_1192; obj* x_1194; obj* x_1196; obj* x_1198; obj* x_1200; 
x_1185 = lean::cnstr_get(x_0, 0);
lean::inc(x_1185);
x_1187 = lean::cnstr_get(x_0, 1);
lean::inc(x_1187);
x_1189 = lean::cnstr_get(x_0, 2);
lean::inc(x_1189);
x_1198 = lean::cnstr_get(x_1, 1);
lean::inc(x_1198);
x_1200 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_1198, x_1189);
if (lean::obj_tag(x_1200) == 0)
{
obj* x_1201; 
x_1201 = lean::box(0);
x_1194 = x_1201;
goto lbl_1195;
}
else
{
obj* x_1202; uint8 x_1205; obj* x_1206; obj* x_1207; uint8 x_1208; 
x_1202 = lean::cnstr_get(x_1200, 0);
lean::inc(x_1202);
lean::dec(x_1200);
x_1205 = lean::unbox(x_1202);
x_1206 = l_lean_ir_type2id___main(x_1205);
x_1207 = l_lean_ir_valid__assign__unop__types___closed__1;
x_1208 = lean::nat_dec_eq(x_1206, x_1207);
lean::dec(x_1206);
if (x_1208 == 0)
{
obj* x_1210; 
x_1210 = lean::box(0);
x_1194 = x_1210;
goto lbl_1195;
}
else
{
obj* x_1211; 
x_1211 = lean::box(0);
x_1196 = x_1211;
goto lbl_1197;
}
}
lbl_1193:
{
if (lean::obj_tag(x_1191) == 0)
{
obj* x_1213; obj* x_1215; obj* x_1216; obj* x_1217; 
lean::dec(x_1189);
x_1213 = lean::cnstr_get(x_1191, 0);
if (lean::is_exclusive(x_1191)) {
 x_1215 = x_1191;
} else {
 lean::inc(x_1213);
 lean::dec(x_1191);
 x_1215 = lean::box(0);
}
if (lean::is_scalar(x_1215)) {
 x_1216 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1216 = x_1215;
}
lean::cnstr_set(x_1216, 0, x_1213);
x_1217 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1217, 0, x_1216);
lean::cnstr_set(x_1217, 1, x_1192);
x_3 = x_1217;
goto lbl_4;
}
else
{
obj* x_1219; obj* x_1220; obj* x_1221; 
lean::dec(x_1191);
x_1219 = l_list_repr__aux___main___rarg___closed__1;
x_1220 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1219, x_1, x_1192);
x_1221 = lean::cnstr_get(x_1220, 0);
lean::inc(x_1221);
if (lean::obj_tag(x_1221) == 0)
{
obj* x_1224; obj* x_1226; obj* x_1227; obj* x_1229; obj* x_1230; obj* x_1231; 
lean::dec(x_1189);
x_1224 = lean::cnstr_get(x_1220, 1);
if (lean::is_exclusive(x_1220)) {
 lean::cnstr_release(x_1220, 0);
 x_1226 = x_1220;
} else {
 lean::inc(x_1224);
 lean::dec(x_1220);
 x_1226 = lean::box(0);
}
x_1227 = lean::cnstr_get(x_1221, 0);
if (lean::is_exclusive(x_1221)) {
 x_1229 = x_1221;
} else {
 lean::inc(x_1227);
 lean::dec(x_1221);
 x_1229 = lean::box(0);
}
if (lean::is_scalar(x_1229)) {
 x_1230 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1230 = x_1229;
}
lean::cnstr_set(x_1230, 0, x_1227);
if (lean::is_scalar(x_1226)) {
 x_1231 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1231 = x_1226;
}
lean::cnstr_set(x_1231, 0, x_1230);
lean::cnstr_set(x_1231, 1, x_1224);
x_3 = x_1231;
goto lbl_4;
}
else
{
obj* x_1233; obj* x_1236; obj* x_1237; 
lean::dec(x_1221);
x_1233 = lean::cnstr_get(x_1220, 1);
lean::inc(x_1233);
lean::dec(x_1220);
x_1236 = l_lean_ir_cpp_emit__var(x_1189, x_1, x_1233);
x_1237 = lean::cnstr_get(x_1236, 0);
lean::inc(x_1237);
if (lean::obj_tag(x_1237) == 0)
{
obj* x_1239; obj* x_1241; obj* x_1242; obj* x_1244; obj* x_1245; obj* x_1246; 
x_1239 = lean::cnstr_get(x_1236, 1);
if (lean::is_exclusive(x_1236)) {
 lean::cnstr_release(x_1236, 0);
 x_1241 = x_1236;
} else {
 lean::inc(x_1239);
 lean::dec(x_1236);
 x_1241 = lean::box(0);
}
x_1242 = lean::cnstr_get(x_1237, 0);
if (lean::is_exclusive(x_1237)) {
 x_1244 = x_1237;
} else {
 lean::inc(x_1242);
 lean::dec(x_1237);
 x_1244 = lean::box(0);
}
if (lean::is_scalar(x_1244)) {
 x_1245 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1245 = x_1244;
}
lean::cnstr_set(x_1245, 0, x_1242);
if (lean::is_scalar(x_1241)) {
 x_1246 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1246 = x_1241;
}
lean::cnstr_set(x_1246, 0, x_1245);
lean::cnstr_set(x_1246, 1, x_1239);
x_3 = x_1246;
goto lbl_4;
}
else
{
obj* x_1247; obj* x_1250; obj* x_1253; obj* x_1254; obj* x_1255; 
x_1247 = lean::cnstr_get(x_1236, 1);
lean::inc(x_1247);
lean::dec(x_1236);
x_1250 = lean::cnstr_get(x_1237, 0);
lean::inc(x_1250);
lean::dec(x_1237);
x_1253 = l_option_has__repr___rarg___closed__3;
x_1254 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1253, x_1, x_1247);
x_1255 = lean::cnstr_get(x_1254, 0);
lean::inc(x_1255);
if (lean::obj_tag(x_1255) == 0)
{
obj* x_1258; obj* x_1260; obj* x_1261; obj* x_1263; obj* x_1264; obj* x_1265; 
lean::dec(x_1250);
x_1258 = lean::cnstr_get(x_1254, 1);
if (lean::is_exclusive(x_1254)) {
 lean::cnstr_release(x_1254, 0);
 x_1260 = x_1254;
} else {
 lean::inc(x_1258);
 lean::dec(x_1254);
 x_1260 = lean::box(0);
}
x_1261 = lean::cnstr_get(x_1255, 0);
if (lean::is_exclusive(x_1255)) {
 x_1263 = x_1255;
} else {
 lean::inc(x_1261);
 lean::dec(x_1255);
 x_1263 = lean::box(0);
}
if (lean::is_scalar(x_1263)) {
 x_1264 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1264 = x_1263;
}
lean::cnstr_set(x_1264, 0, x_1261);
if (lean::is_scalar(x_1260)) {
 x_1265 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1265 = x_1260;
}
lean::cnstr_set(x_1265, 0, x_1264);
lean::cnstr_set(x_1265, 1, x_1258);
x_3 = x_1265;
goto lbl_4;
}
else
{
obj* x_1266; obj* x_1267; obj* x_1269; obj* x_1270; obj* x_1271; 
if (lean::is_exclusive(x_1255)) {
 lean::cnstr_release(x_1255, 0);
 x_1266 = x_1255;
} else {
 lean::dec(x_1255);
 x_1266 = lean::box(0);
}
x_1267 = lean::cnstr_get(x_1254, 1);
if (lean::is_exclusive(x_1254)) {
 lean::cnstr_release(x_1254, 0);
 x_1269 = x_1254;
} else {
 lean::inc(x_1267);
 lean::dec(x_1254);
 x_1269 = lean::box(0);
}
if (lean::is_scalar(x_1266)) {
 x_1270 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1270 = x_1266;
}
lean::cnstr_set(x_1270, 0, x_1250);
if (lean::is_scalar(x_1269)) {
 x_1271 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1271 = x_1269;
}
lean::cnstr_set(x_1271, 0, x_1270);
lean::cnstr_set(x_1271, 1, x_1267);
x_3 = x_1271;
goto lbl_4;
}
}
}
}
}
lbl_1195:
{
obj* x_1273; obj* x_1274; obj* x_1275; 
lean::dec(x_1194);
x_1273 = l_lean_ir_cpp_emit__instr___closed__8;
x_1274 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1273, x_1, x_2);
x_1275 = lean::cnstr_get(x_1274, 0);
lean::inc(x_1275);
if (lean::obj_tag(x_1275) == 0)
{
obj* x_1280; obj* x_1282; obj* x_1283; obj* x_1285; obj* x_1286; obj* x_1287; 
lean::dec(x_1185);
lean::dec(x_1189);
lean::dec(x_1187);
x_1280 = lean::cnstr_get(x_1274, 1);
if (lean::is_exclusive(x_1274)) {
 lean::cnstr_release(x_1274, 0);
 x_1282 = x_1274;
} else {
 lean::inc(x_1280);
 lean::dec(x_1274);
 x_1282 = lean::box(0);
}
x_1283 = lean::cnstr_get(x_1275, 0);
if (lean::is_exclusive(x_1275)) {
 x_1285 = x_1275;
} else {
 lean::inc(x_1283);
 lean::dec(x_1275);
 x_1285 = lean::box(0);
}
if (lean::is_scalar(x_1285)) {
 x_1286 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1286 = x_1285;
}
lean::cnstr_set(x_1286, 0, x_1283);
if (lean::is_scalar(x_1282)) {
 x_1287 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1287 = x_1282;
}
lean::cnstr_set(x_1287, 0, x_1286);
lean::cnstr_set(x_1287, 1, x_1280);
x_3 = x_1287;
goto lbl_4;
}
else
{
obj* x_1289; obj* x_1292; obj* x_1293; obj* x_1294; 
lean::dec(x_1275);
x_1289 = lean::cnstr_get(x_1274, 1);
lean::inc(x_1289);
lean::dec(x_1274);
x_1292 = l_prod_has__repr___rarg___closed__1;
x_1293 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1292, x_1, x_1289);
x_1294 = lean::cnstr_get(x_1293, 0);
lean::inc(x_1294);
if (lean::obj_tag(x_1294) == 0)
{
obj* x_1299; obj* x_1301; obj* x_1302; obj* x_1304; obj* x_1305; obj* x_1306; 
lean::dec(x_1185);
lean::dec(x_1189);
lean::dec(x_1187);
x_1299 = lean::cnstr_get(x_1293, 1);
if (lean::is_exclusive(x_1293)) {
 lean::cnstr_release(x_1293, 0);
 x_1301 = x_1293;
} else {
 lean::inc(x_1299);
 lean::dec(x_1293);
 x_1301 = lean::box(0);
}
x_1302 = lean::cnstr_get(x_1294, 0);
if (lean::is_exclusive(x_1294)) {
 x_1304 = x_1294;
} else {
 lean::inc(x_1302);
 lean::dec(x_1294);
 x_1304 = lean::box(0);
}
if (lean::is_scalar(x_1304)) {
 x_1305 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1305 = x_1304;
}
lean::cnstr_set(x_1305, 0, x_1302);
if (lean::is_scalar(x_1301)) {
 x_1306 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1306 = x_1301;
}
lean::cnstr_set(x_1306, 0, x_1305);
lean::cnstr_set(x_1306, 1, x_1299);
x_3 = x_1306;
goto lbl_4;
}
else
{
obj* x_1308; obj* x_1311; obj* x_1312; 
lean::dec(x_1294);
x_1308 = lean::cnstr_get(x_1293, 1);
lean::inc(x_1308);
lean::dec(x_1293);
x_1311 = l_lean_ir_cpp_emit__var(x_1185, x_1, x_1308);
x_1312 = lean::cnstr_get(x_1311, 0);
lean::inc(x_1312);
if (lean::obj_tag(x_1312) == 0)
{
obj* x_1315; obj* x_1318; obj* x_1320; obj* x_1321; 
lean::dec(x_1187);
x_1315 = lean::cnstr_get(x_1311, 1);
lean::inc(x_1315);
lean::dec(x_1311);
x_1318 = lean::cnstr_get(x_1312, 0);
if (lean::is_exclusive(x_1312)) {
 x_1320 = x_1312;
} else {
 lean::inc(x_1318);
 lean::dec(x_1312);
 x_1320 = lean::box(0);
}
if (lean::is_scalar(x_1320)) {
 x_1321 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1321 = x_1320;
}
lean::cnstr_set(x_1321, 0, x_1318);
x_1191 = x_1321;
x_1192 = x_1315;
goto lbl_1193;
}
else
{
obj* x_1323; obj* x_1326; obj* x_1327; obj* x_1328; 
lean::dec(x_1312);
x_1323 = lean::cnstr_get(x_1311, 1);
lean::inc(x_1323);
lean::dec(x_1311);
x_1326 = l_list_repr__aux___main___rarg___closed__1;
x_1327 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1326, x_1, x_1323);
x_1328 = lean::cnstr_get(x_1327, 0);
lean::inc(x_1328);
if (lean::obj_tag(x_1328) == 0)
{
obj* x_1331; obj* x_1334; obj* x_1336; obj* x_1337; 
lean::dec(x_1187);
x_1331 = lean::cnstr_get(x_1327, 1);
lean::inc(x_1331);
lean::dec(x_1327);
x_1334 = lean::cnstr_get(x_1328, 0);
if (lean::is_exclusive(x_1328)) {
 x_1336 = x_1328;
} else {
 lean::inc(x_1334);
 lean::dec(x_1328);
 x_1336 = lean::box(0);
}
if (lean::is_scalar(x_1336)) {
 x_1337 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1337 = x_1336;
}
lean::cnstr_set(x_1337, 0, x_1334);
x_1191 = x_1337;
x_1192 = x_1331;
goto lbl_1193;
}
else
{
obj* x_1339; obj* x_1342; obj* x_1343; obj* x_1345; 
lean::dec(x_1328);
x_1339 = lean::cnstr_get(x_1327, 1);
lean::inc(x_1339);
lean::dec(x_1327);
x_1342 = l_lean_ir_cpp_emit__var(x_1187, x_1, x_1339);
x_1343 = lean::cnstr_get(x_1342, 0);
lean::inc(x_1343);
x_1345 = lean::cnstr_get(x_1342, 1);
lean::inc(x_1345);
lean::dec(x_1342);
x_1191 = x_1343;
x_1192 = x_1345;
goto lbl_1193;
}
}
}
}
}
lbl_1197:
{
obj* x_1349; obj* x_1350; obj* x_1351; 
lean::dec(x_1196);
x_1349 = l_lean_ir_cpp_emit__instr___closed__9;
x_1350 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1349, x_1, x_2);
x_1351 = lean::cnstr_get(x_1350, 0);
lean::inc(x_1351);
if (lean::obj_tag(x_1351) == 0)
{
obj* x_1356; obj* x_1358; obj* x_1359; obj* x_1361; obj* x_1362; obj* x_1363; 
lean::dec(x_1185);
lean::dec(x_1189);
lean::dec(x_1187);
x_1356 = lean::cnstr_get(x_1350, 1);
if (lean::is_exclusive(x_1350)) {
 lean::cnstr_release(x_1350, 0);
 x_1358 = x_1350;
} else {
 lean::inc(x_1356);
 lean::dec(x_1350);
 x_1358 = lean::box(0);
}
x_1359 = lean::cnstr_get(x_1351, 0);
if (lean::is_exclusive(x_1351)) {
 x_1361 = x_1351;
} else {
 lean::inc(x_1359);
 lean::dec(x_1351);
 x_1361 = lean::box(0);
}
if (lean::is_scalar(x_1361)) {
 x_1362 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1362 = x_1361;
}
lean::cnstr_set(x_1362, 0, x_1359);
if (lean::is_scalar(x_1358)) {
 x_1363 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1363 = x_1358;
}
lean::cnstr_set(x_1363, 0, x_1362);
lean::cnstr_set(x_1363, 1, x_1356);
x_3 = x_1363;
goto lbl_4;
}
else
{
obj* x_1365; obj* x_1368; obj* x_1369; obj* x_1370; 
lean::dec(x_1351);
x_1365 = lean::cnstr_get(x_1350, 1);
lean::inc(x_1365);
lean::dec(x_1350);
x_1368 = l_prod_has__repr___rarg___closed__1;
x_1369 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1368, x_1, x_1365);
x_1370 = lean::cnstr_get(x_1369, 0);
lean::inc(x_1370);
if (lean::obj_tag(x_1370) == 0)
{
obj* x_1375; obj* x_1377; obj* x_1378; obj* x_1380; obj* x_1381; obj* x_1382; 
lean::dec(x_1185);
lean::dec(x_1189);
lean::dec(x_1187);
x_1375 = lean::cnstr_get(x_1369, 1);
if (lean::is_exclusive(x_1369)) {
 lean::cnstr_release(x_1369, 0);
 x_1377 = x_1369;
} else {
 lean::inc(x_1375);
 lean::dec(x_1369);
 x_1377 = lean::box(0);
}
x_1378 = lean::cnstr_get(x_1370, 0);
if (lean::is_exclusive(x_1370)) {
 x_1380 = x_1370;
} else {
 lean::inc(x_1378);
 lean::dec(x_1370);
 x_1380 = lean::box(0);
}
if (lean::is_scalar(x_1380)) {
 x_1381 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1381 = x_1380;
}
lean::cnstr_set(x_1381, 0, x_1378);
if (lean::is_scalar(x_1377)) {
 x_1382 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1382 = x_1377;
}
lean::cnstr_set(x_1382, 0, x_1381);
lean::cnstr_set(x_1382, 1, x_1375);
x_3 = x_1382;
goto lbl_4;
}
else
{
obj* x_1384; obj* x_1387; obj* x_1388; 
lean::dec(x_1370);
x_1384 = lean::cnstr_get(x_1369, 1);
lean::inc(x_1384);
lean::dec(x_1369);
x_1387 = l_lean_ir_cpp_emit__var(x_1185, x_1, x_1384);
x_1388 = lean::cnstr_get(x_1387, 0);
lean::inc(x_1388);
if (lean::obj_tag(x_1388) == 0)
{
obj* x_1391; obj* x_1394; obj* x_1396; obj* x_1397; 
lean::dec(x_1187);
x_1391 = lean::cnstr_get(x_1387, 1);
lean::inc(x_1391);
lean::dec(x_1387);
x_1394 = lean::cnstr_get(x_1388, 0);
if (lean::is_exclusive(x_1388)) {
 x_1396 = x_1388;
} else {
 lean::inc(x_1394);
 lean::dec(x_1388);
 x_1396 = lean::box(0);
}
if (lean::is_scalar(x_1396)) {
 x_1397 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1397 = x_1396;
}
lean::cnstr_set(x_1397, 0, x_1394);
x_1191 = x_1397;
x_1192 = x_1391;
goto lbl_1193;
}
else
{
obj* x_1399; obj* x_1402; obj* x_1403; obj* x_1404; 
lean::dec(x_1388);
x_1399 = lean::cnstr_get(x_1387, 1);
lean::inc(x_1399);
lean::dec(x_1387);
x_1402 = l_list_repr__aux___main___rarg___closed__1;
x_1403 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1402, x_1, x_1399);
x_1404 = lean::cnstr_get(x_1403, 0);
lean::inc(x_1404);
if (lean::obj_tag(x_1404) == 0)
{
obj* x_1407; obj* x_1410; obj* x_1412; obj* x_1413; 
lean::dec(x_1187);
x_1407 = lean::cnstr_get(x_1403, 1);
lean::inc(x_1407);
lean::dec(x_1403);
x_1410 = lean::cnstr_get(x_1404, 0);
if (lean::is_exclusive(x_1404)) {
 x_1412 = x_1404;
} else {
 lean::inc(x_1410);
 lean::dec(x_1404);
 x_1412 = lean::box(0);
}
if (lean::is_scalar(x_1412)) {
 x_1413 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1413 = x_1412;
}
lean::cnstr_set(x_1413, 0, x_1410);
x_1191 = x_1413;
x_1192 = x_1407;
goto lbl_1193;
}
else
{
obj* x_1415; obj* x_1418; obj* x_1419; obj* x_1421; 
lean::dec(x_1404);
x_1415 = lean::cnstr_get(x_1403, 1);
lean::inc(x_1415);
lean::dec(x_1403);
x_1418 = l_lean_ir_cpp_emit__var(x_1187, x_1, x_1415);
x_1419 = lean::cnstr_get(x_1418, 0);
lean::inc(x_1419);
x_1421 = lean::cnstr_get(x_1418, 1);
lean::inc(x_1421);
lean::dec(x_1418);
x_1191 = x_1419;
x_1192 = x_1421;
goto lbl_1193;
}
}
}
}
}
}
}
lbl_4:
{
obj* x_1424; 
x_1424 = lean::cnstr_get(x_3, 0);
lean::inc(x_1424);
if (lean::obj_tag(x_1424) == 0)
{
obj* x_1427; obj* x_1429; obj* x_1430; obj* x_1432; obj* x_1433; uint8 x_1434; obj* x_1435; obj* x_1436; obj* x_1437; obj* x_1438; obj* x_1439; obj* x_1440; obj* x_1441; obj* x_1442; obj* x_1443; obj* x_1444; obj* x_1445; obj* x_1446; obj* x_1447; 
lean::dec(x_1);
x_1427 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_1429 = x_3;
} else {
 lean::inc(x_1427);
 lean::dec(x_3);
 x_1429 = lean::box(0);
}
x_1430 = lean::cnstr_get(x_1424, 0);
if (lean::is_exclusive(x_1424)) {
 x_1432 = x_1424;
} else {
 lean::inc(x_1430);
 lean::dec(x_1424);
 x_1432 = lean::box(0);
}
x_1433 = l_lean_ir_instr_to__format___main(x_0);
x_1434 = 0;
x_1435 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
x_1436 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1436, 0, x_1435);
lean::cnstr_set(x_1436, 1, x_1433);
lean::cnstr_set_scalar(x_1436, sizeof(void*)*2, x_1434);
x_1437 = x_1436;
x_1438 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_1439 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1439, 0, x_1437);
lean::cnstr_set(x_1439, 1, x_1438);
lean::cnstr_set_scalar(x_1439, sizeof(void*)*2, x_1434);
x_1440 = x_1439;
x_1441 = lean::box(1);
x_1442 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1442, 0, x_1440);
lean::cnstr_set(x_1442, 1, x_1441);
lean::cnstr_set_scalar(x_1442, sizeof(void*)*2, x_1434);
x_1443 = x_1442;
x_1444 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1444, 0, x_1443);
lean::cnstr_set(x_1444, 1, x_1430);
lean::cnstr_set_scalar(x_1444, sizeof(void*)*2, x_1434);
x_1445 = x_1444;
if (lean::is_scalar(x_1432)) {
 x_1446 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1446 = x_1432;
}
lean::cnstr_set(x_1446, 0, x_1445);
if (lean::is_scalar(x_1429)) {
 x_1447 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1447 = x_1429;
}
lean::cnstr_set(x_1447, 0, x_1446);
lean::cnstr_set(x_1447, 1, x_1427);
return x_1447;
}
else
{
obj* x_1449; obj* x_1452; obj* x_1454; 
lean::dec(x_1424);
x_1449 = lean::cnstr_get(x_3, 1);
lean::inc(x_1449);
lean::dec(x_3);
x_1452 = l_lean_ir_cpp_emit__eos(x_1, x_1449);
lean::dec(x_1);
x_1454 = lean::cnstr_get(x_1452, 0);
lean::inc(x_1454);
if (lean::obj_tag(x_1454) == 0)
{
obj* x_1456; obj* x_1458; obj* x_1459; obj* x_1461; obj* x_1462; uint8 x_1463; obj* x_1464; obj* x_1465; obj* x_1466; obj* x_1467; obj* x_1468; obj* x_1469; obj* x_1470; obj* x_1471; obj* x_1472; obj* x_1473; obj* x_1474; obj* x_1475; obj* x_1476; 
x_1456 = lean::cnstr_get(x_1452, 1);
if (lean::is_exclusive(x_1452)) {
 lean::cnstr_release(x_1452, 0);
 x_1458 = x_1452;
} else {
 lean::inc(x_1456);
 lean::dec(x_1452);
 x_1458 = lean::box(0);
}
x_1459 = lean::cnstr_get(x_1454, 0);
if (lean::is_exclusive(x_1454)) {
 x_1461 = x_1454;
} else {
 lean::inc(x_1459);
 lean::dec(x_1454);
 x_1461 = lean::box(0);
}
x_1462 = l_lean_ir_instr_to__format___main(x_0);
x_1463 = 0;
x_1464 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
x_1465 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1465, 0, x_1464);
lean::cnstr_set(x_1465, 1, x_1462);
lean::cnstr_set_scalar(x_1465, sizeof(void*)*2, x_1463);
x_1466 = x_1465;
x_1467 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_1468 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1468, 0, x_1466);
lean::cnstr_set(x_1468, 1, x_1467);
lean::cnstr_set_scalar(x_1468, sizeof(void*)*2, x_1463);
x_1469 = x_1468;
x_1470 = lean::box(1);
x_1471 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1471, 0, x_1469);
lean::cnstr_set(x_1471, 1, x_1470);
lean::cnstr_set_scalar(x_1471, sizeof(void*)*2, x_1463);
x_1472 = x_1471;
x_1473 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1473, 0, x_1472);
lean::cnstr_set(x_1473, 1, x_1459);
lean::cnstr_set_scalar(x_1473, sizeof(void*)*2, x_1463);
x_1474 = x_1473;
if (lean::is_scalar(x_1461)) {
 x_1475 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1475 = x_1461;
}
lean::cnstr_set(x_1475, 0, x_1474);
if (lean::is_scalar(x_1458)) {
 x_1476 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1476 = x_1458;
}
lean::cnstr_set(x_1476, 0, x_1475);
lean::cnstr_set(x_1476, 1, x_1456);
return x_1476;
}
else
{
obj* x_1478; obj* x_1480; obj* x_1481; 
lean::dec(x_0);
x_1478 = lean::cnstr_get(x_1452, 1);
if (lean::is_exclusive(x_1452)) {
 lean::cnstr_release(x_1452, 0);
 x_1480 = x_1452;
} else {
 lean::inc(x_1478);
 lean::dec(x_1452);
 x_1480 = lean::box(0);
}
if (lean::is_scalar(x_1480)) {
 x_1481 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1481 = x_1480;
}
lean::cnstr_set(x_1481, 0, x_1454);
lean::cnstr_set(x_1481, 1, x_1478);
return x_1481;
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
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint16 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__2(x_3, x_1, x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint16 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_3, x_1, x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__block___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_cpp_emit__instr(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
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
obj* x_3; uint8 x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = l_list_empty___main___rarg(x_3);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
lean::dec(x_0);
if (x_5 == 0)
{
obj* x_17; 
x_17 = l_lean_ir_cpp_emit__block___closed__2;
lean::inc(x_2);
x_14 = x_17;
x_15 = x_2;
goto lbl_16;
}
else
{
obj* x_19; 
x_19 = l_lean_ir_match__type___closed__5;
lean::inc(x_2);
x_14 = x_19;
x_15 = x_2;
goto lbl_16;
}
lbl_16:
{
if (lean::obj_tag(x_14) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_7);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_9);
x_25 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_27 = x_14;
} else {
 lean::inc(x_25);
 lean::dec(x_14);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_15);
return x_29;
}
else
{
obj* x_31; obj* x_32; 
lean::dec(x_14);
x_31 = l_lean_ir_cpp_emit__blockid(x_7, x_1, x_15);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_9);
x_37 = lean::cnstr_get(x_31, 1);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 x_39 = x_31;
} else {
 lean::inc(x_37);
 lean::dec(x_31);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_32, 0);
if (lean::is_exclusive(x_32)) {
 x_42 = x_32;
} else {
 lean::inc(x_40);
 lean::dec(x_32);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_40);
if (lean::is_scalar(x_39)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_39;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_37);
return x_44;
}
else
{
obj* x_46; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_32);
x_46 = lean::cnstr_get(x_31, 1);
lean::inc(x_46);
lean::dec(x_31);
x_49 = l_lean_ir_cpp_emit__block___closed__1;
x_50 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_49, x_1, x_46);
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
if (lean::obj_tag(x_51) == 0)
{
obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_9);
x_56 = lean::cnstr_get(x_50, 1);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_58 = x_50;
} else {
 lean::inc(x_56);
 lean::dec(x_50);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get(x_51, 0);
if (lean::is_exclusive(x_51)) {
 x_61 = x_51;
} else {
 lean::inc(x_59);
 lean::dec(x_51);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_59);
if (lean::is_scalar(x_58)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_58;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_56);
return x_63;
}
else
{
obj* x_65; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_51);
x_65 = lean::cnstr_get(x_50, 1);
lean::inc(x_65);
lean::dec(x_50);
x_68 = l_lean_format_be___main___closed__1;
x_69 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_68, x_1, x_65);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_9);
x_75 = lean::cnstr_get(x_69, 1);
if (lean::is_exclusive(x_69)) {
 lean::cnstr_release(x_69, 0);
 x_77 = x_69;
} else {
 lean::inc(x_75);
 lean::dec(x_69);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_70, 0);
if (lean::is_exclusive(x_70)) {
 x_80 = x_70;
} else {
 lean::inc(x_78);
 lean::dec(x_70);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
if (lean::is_scalar(x_77)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_77;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_75);
return x_82;
}
else
{
obj* x_84; obj* x_88; obj* x_89; 
lean::dec(x_70);
x_84 = lean::cnstr_get(x_69, 1);
lean::inc(x_84);
lean::dec(x_69);
lean::inc(x_1);
x_88 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__block___spec__1(x_9, x_1, x_84);
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
if (lean::obj_tag(x_89) == 0)
{
obj* x_93; obj* x_95; obj* x_96; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_11);
lean::dec(x_1);
x_93 = lean::cnstr_get(x_88, 1);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 x_95 = x_88;
} else {
 lean::inc(x_93);
 lean::dec(x_88);
 x_95 = lean::box(0);
}
x_96 = lean::cnstr_get(x_89, 0);
if (lean::is_exclusive(x_89)) {
 x_98 = x_89;
} else {
 lean::inc(x_96);
 lean::dec(x_89);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
if (lean::is_scalar(x_95)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_95;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_93);
return x_100;
}
else
{
obj* x_102; obj* x_105; 
lean::dec(x_89);
x_102 = lean::cnstr_get(x_88, 1);
lean::inc(x_102);
lean::dec(x_88);
x_105 = l_lean_ir_cpp_emit__terminator(x_11, x_1, x_102);
return x_105;
}
}
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__block___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_emit__block(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_lean_ir_cpp_emit__header___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_emit__arg__list___lambda__1___boxed), 3, 0);
return x_0;
}
}
obj* l_lean_ir_cpp_emit__header(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; uint8 x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_0, 2);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_13 = lean::unbox(x_3);
x_14 = l_lean_ir_cpp_emit__type(x_13, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_20; obj* x_22; obj* x_23; 
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_22 = x_15;
} else {
 lean::inc(x_20);
 lean::dec(x_15);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
x_10 = x_23;
x_11 = x_17;
goto lbl_12;
}
else
{
obj* x_25; obj* x_28; obj* x_29; obj* x_30; obj* x_32; 
lean::dec(x_15);
x_25 = lean::cnstr_get(x_14, 1);
lean::inc(x_25);
lean::dec(x_14);
x_28 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
x_29 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_28, x_1, x_25);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_10 = x_30;
x_11 = x_32;
goto lbl_12;
}
lbl_12:
{
if (lean::obj_tag(x_10) == 0)
{
obj* x_38; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_1);
x_38 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_40 = x_10;
} else {
 lean::inc(x_38);
 lean::dec(x_10);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_38);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_11);
return x_42;
}
else
{
obj* x_45; obj* x_46; 
lean::dec(x_10);
lean::inc(x_1);
x_45 = l_lean_ir_cpp_emit__fnid(x_5, x_1, x_11);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
if (lean::obj_tag(x_46) == 0)
{
obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_7);
lean::dec(x_1);
x_50 = lean::cnstr_get(x_45, 1);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 x_52 = x_45;
} else {
 lean::inc(x_50);
 lean::dec(x_45);
 x_52 = lean::box(0);
}
x_53 = lean::cnstr_get(x_46, 0);
if (lean::is_exclusive(x_46)) {
 x_55 = x_46;
} else {
 lean::inc(x_53);
 lean::dec(x_46);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
if (lean::is_scalar(x_52)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_52;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_50);
return x_57;
}
else
{
obj* x_59; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_46);
x_59 = lean::cnstr_get(x_45, 1);
lean::inc(x_59);
lean::dec(x_45);
x_62 = l_prod_has__repr___rarg___closed__1;
x_63 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_62, x_1, x_59);
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
if (lean::obj_tag(x_64) == 0)
{
obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_7);
lean::dec(x_1);
x_68 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 x_70 = x_63;
} else {
 lean::inc(x_68);
 lean::dec(x_63);
 x_70 = lean::box(0);
}
x_71 = lean::cnstr_get(x_64, 0);
if (lean::is_exclusive(x_64)) {
 x_73 = x_64;
} else {
 lean::inc(x_71);
 lean::dec(x_64);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_71);
if (lean::is_scalar(x_70)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_70;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_68);
return x_75;
}
else
{
obj* x_77; obj* x_80; obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_64);
x_77 = lean::cnstr_get(x_63, 1);
lean::inc(x_77);
lean::dec(x_63);
x_80 = l_lean_ir_cpp_emit__header___closed__1;
x_81 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_1);
x_83 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_80, x_81, x_7, x_1, x_77);
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
if (lean::obj_tag(x_84) == 0)
{
obj* x_87; obj* x_89; obj* x_90; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_1);
x_87 = lean::cnstr_get(x_83, 1);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 x_89 = x_83;
} else {
 lean::inc(x_87);
 lean::dec(x_83);
 x_89 = lean::box(0);
}
x_90 = lean::cnstr_get(x_84, 0);
if (lean::is_exclusive(x_84)) {
 x_92 = x_84;
} else {
 lean::inc(x_90);
 lean::dec(x_84);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_90);
if (lean::is_scalar(x_89)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_89;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_87);
return x_94;
}
else
{
obj* x_95; obj* x_98; obj* x_101; obj* x_102; obj* x_104; 
x_95 = lean::cnstr_get(x_83, 1);
lean::inc(x_95);
lean::dec(x_83);
x_98 = lean::cnstr_get(x_84, 0);
lean::inc(x_98);
lean::dec(x_84);
x_101 = l_option_has__repr___rarg___closed__3;
x_102 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_101, x_1, x_95);
lean::dec(x_1);
x_104 = lean::cnstr_get(x_102, 0);
lean::inc(x_104);
if (lean::obj_tag(x_104) == 0)
{
obj* x_107; obj* x_109; obj* x_110; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_98);
x_107 = lean::cnstr_get(x_102, 1);
if (lean::is_exclusive(x_102)) {
 lean::cnstr_release(x_102, 0);
 x_109 = x_102;
} else {
 lean::inc(x_107);
 lean::dec(x_102);
 x_109 = lean::box(0);
}
x_110 = lean::cnstr_get(x_104, 0);
if (lean::is_exclusive(x_104)) {
 x_112 = x_104;
} else {
 lean::inc(x_110);
 lean::dec(x_104);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_110);
if (lean::is_scalar(x_109)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_109;
}
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_107);
return x_114;
}
else
{
obj* x_115; obj* x_116; obj* x_118; obj* x_119; obj* x_120; 
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 x_115 = x_104;
} else {
 lean::dec(x_104);
 x_115 = lean::box(0);
}
x_116 = lean::cnstr_get(x_102, 1);
if (lean::is_exclusive(x_102)) {
 lean::cnstr_release(x_102, 0);
 x_118 = x_102;
} else {
 lean::inc(x_116);
 lean::dec(x_102);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_119 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_119 = x_115;
}
lean::cnstr_set(x_119, 0, x_98);
if (lean::is_scalar(x_118)) {
 x_120 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_120 = x_118;
}
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_116);
return x_120;
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
obj* x_4; obj* x_5; 
x_4 = l_lean_ir_cpp_emit__type(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_0);
x_8 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
} else {
 lean::inc(x_8);
 lean::dec(x_4);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_13 = x_5;
} else {
 lean::inc(x_11);
 lean::dec(x_5);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
if (lean::is_scalar(x_10)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_10;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_8);
return x_15;
}
else
{
obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_5);
x_17 = lean::cnstr_get(x_4, 1);
lean::inc(x_17);
lean::dec(x_4);
x_20 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_20, x_2, x_17);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_0);
x_25 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_27 = x_21;
} else {
 lean::inc(x_25);
 lean::dec(x_21);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_30 = x_22;
} else {
 lean::inc(x_28);
 lean::dec(x_22);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
if (lean::is_scalar(x_27)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_27;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_25);
return x_32;
}
else
{
obj* x_34; obj* x_37; obj* x_38; 
lean::dec(x_22);
x_34 = lean::cnstr_get(x_21, 1);
lean::inc(x_34);
lean::dec(x_21);
x_37 = l_lean_ir_cpp_emit__var(x_0, x_2, x_34);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
x_40 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_42 = x_37;
} else {
 lean::inc(x_40);
 lean::dec(x_37);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_45 = x_38;
} else {
 lean::inc(x_43);
 lean::dec(x_38);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_43);
if (lean::is_scalar(x_42)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_42;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_40);
return x_47;
}
else
{
obj* x_49; obj* x_52; 
lean::dec(x_38);
x_49 = lean::cnstr_get(x_37, 1);
lean::inc(x_49);
lean::dec(x_37);
x_52 = l_lean_ir_cpp_emit__eos(x_2, x_49);
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
lean::dec(x_2);
return x_5;
}
}
obj* l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; obj* x_3; 
x_2 = 0;
x_3 = lean::box(x_2);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_4, 0);
x_7 = lean_name_dec_eq(x_6, x_0);
if (x_7 == 0)
{
x_1 = x_5;
goto _start;
}
else
{
uint8 x_9; obj* x_10; 
x_9 = 1;
x_10 = lean::box(x_9);
return x_10;
}
}
}
}
obj* l_rbnode_mfold___main___at_lean_ir_cpp_decl__locals___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_4);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_17; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
lean::dec(x_1);
x_16 = l_rbnode_mfold___main___at_lean_ir_cpp_decl__locals___spec__2(x_0, x_7, x_2, x_3, x_4);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_13);
x_22 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_24 = x_16;
} else {
 lean::inc(x_22);
 lean::dec(x_16);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_17, 0);
if (lean::is_exclusive(x_17)) {
 x_27 = x_17;
} else {
 lean::inc(x_25);
 lean::dec(x_17);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
if (lean::is_scalar(x_24)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_24;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_22);
return x_29;
}
else
{
obj* x_31; obj* x_34; uint8 x_35; 
lean::dec(x_17);
x_31 = lean::cnstr_get(x_16, 1);
lean::inc(x_31);
lean::dec(x_16);
x_34 = l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1(x_9, x_0);
x_35 = lean::unbox(x_34);
if (x_35 == 0)
{
uint8 x_36; obj* x_37; obj* x_38; 
x_36 = lean::unbox(x_11);
x_37 = l_lean_ir_cpp_decl__local(x_9, x_36, x_3, x_31);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_48; 
lean::dec(x_13);
x_41 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_43 = x_37;
} else {
 lean::inc(x_41);
 lean::dec(x_37);
 x_43 = lean::box(0);
}
x_44 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_46 = x_38;
} else {
 lean::inc(x_44);
 lean::dec(x_38);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_44);
if (lean::is_scalar(x_43)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_43;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_41);
return x_48;
}
else
{
obj* x_50; obj* x_53; 
lean::dec(x_38);
x_50 = lean::cnstr_get(x_37, 1);
lean::inc(x_50);
lean::dec(x_37);
x_53 = lean::box(0);
x_1 = x_13;
x_2 = x_53;
x_4 = x_50;
goto _start;
}
}
else
{
obj* x_57; 
lean::dec(x_9);
lean::dec(x_11);
x_57 = lean::box(0);
x_1 = x_13;
x_2 = x_57;
x_4 = x_31;
goto _start;
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
lean::dec(x_1);
return x_6;
}
}
obj* l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_mfold___main___at_lean_ir_cpp_decl__locals___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_rbnode_mfold___main___at_lean_ir_cpp_decl__locals___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_3);
return x_5;
}
}
obj* l_lean_ir_cpp_decl__locals___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_decl__locals(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_list_foldr___main___at_lean_ir_cpp_need__uncurry___spec__1(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_1; obj* x_2; 
x_1 = 1;
x_2 = lean::box(x_1);
return x_2;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
x_6 = l_lean_ir_type2id___main(x_5);
x_7 = l_lean_ir_valid__assign__unop__types___closed__1;
x_8 = lean::nat_dec_eq(x_6, x_7);
lean::dec(x_6);
if (x_8 == 0)
{
uint8 x_10; obj* x_11; 
x_10 = 0;
x_11 = lean::box(x_10);
return x_11;
}
else
{
x_0 = x_4;
goto _start;
}
}
}
}
obj* l_lean_ir_cpp_need__uncurry(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; 
x_1 = l_lean_ir_decl_header___main(x_0);
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_list_length__aux___main___rarg(x_2, x_4);
x_6 = l_lean_closure__max__args;
x_7 = lean::nat_dec_lt(x_6, x_5);
lean::dec(x_5);
if (x_7 == 0)
{
uint8 x_11; obj* x_12; 
lean::dec(x_1);
lean::dec(x_2);
x_11 = 0;
x_12 = lean::box(x_11);
return x_12;
}
else
{
obj* x_13; uint8 x_16; obj* x_17; obj* x_18; uint8 x_19; 
x_13 = lean::cnstr_get(x_1, 2);
lean::inc(x_13);
lean::dec(x_1);
x_16 = lean::unbox(x_13);
x_17 = l_lean_ir_type2id___main(x_16);
x_18 = l_lean_ir_valid__assign__unop__types___closed__1;
x_19 = lean::nat_dec_eq(x_17, x_18);
lean::dec(x_17);
if (x_19 == 0)
{
uint8 x_22; obj* x_23; 
lean::dec(x_2);
x_22 = 0;
x_23 = lean::box(x_22);
return x_23;
}
else
{
obj* x_24; 
x_24 = l_list_foldr___main___at_lean_ir_cpp_need__uncurry___spec__1(x_2);
lean::dec(x_2);
return x_24;
}
}
}
}
obj* l_list_foldr___main___at_lean_ir_cpp_need__uncurry___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_list_foldr___main___at_lean_ir_cpp_need__uncurry___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_ir_cpp_need__uncurry___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_ir_cpp_need__uncurry(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_ir_cpp_emit__uncurry__header___closed__1;
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
} else {
 lean::inc(x_8);
 lean::dec(x_4);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_13 = x_5;
} else {
 lean::inc(x_11);
 lean::dec(x_5);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
if (lean::is_scalar(x_10)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_10;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_8);
return x_15;
}
else
{
obj* x_17; obj* x_20; obj* x_21; obj* x_25; obj* x_26; 
lean::dec(x_5);
x_17 = lean::cnstr_get(x_4, 1);
lean::inc(x_17);
lean::dec(x_4);
x_20 = l_lean_ir_decl_header___main(x_0);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
lean::dec(x_20);
lean::inc(x_1);
x_25 = l_lean_ir_cpp_emit__fnid(x_21, x_1, x_17);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
x_29 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_31 = x_25;
} else {
 lean::inc(x_29);
 lean::dec(x_25);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_34 = x_26;
} else {
 lean::inc(x_32);
 lean::dec(x_26);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
if (lean::is_scalar(x_31)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_31;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_29);
return x_36;
}
else
{
obj* x_38; obj* x_41; obj* x_42; 
lean::dec(x_26);
x_38 = lean::cnstr_get(x_25, 1);
lean::inc(x_38);
lean::dec(x_25);
x_41 = l_lean_ir_cpp_emit__uncurry__header___closed__2;
x_42 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_41, x_1, x_38);
lean::dec(x_1);
return x_42;
}
}
}
}
obj* l_lean_ir_cpp_emit__uncurry__header___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_emit__uncurry__header(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2___rarg___boxed), 3, 0);
return x_1;
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
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = lean::apply_2(x_0, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_2);
x_9 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_11 = x_5;
} else {
 lean::inc(x_9);
 lean::dec(x_5);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_14 = x_6;
} else {
 lean::inc(x_12);
 lean::dec(x_6);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_12);
if (lean::is_scalar(x_11)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_11;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_9);
return x_16;
}
else
{
obj* x_18; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_6);
x_18 = lean::cnstr_get(x_5, 1);
lean::inc(x_18);
lean::dec(x_5);
x_21 = l_list_repr__aux___main___rarg___closed__1;
x_22 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_21, x_2, x_18);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_2);
x_26 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_release(x_22, 0);
 x_28 = x_22;
} else {
 lean::inc(x_26);
 lean::dec(x_22);
 x_28 = lean::box(0);
}
x_29 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_31 = x_23;
} else {
 lean::inc(x_29);
 lean::dec(x_23);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_28)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_28;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_26);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_23);
x_35 = lean::cnstr_get(x_22, 1);
lean::inc(x_35);
lean::dec(x_22);
x_38 = l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___closed__1;
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_38, x_2, x_35);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_2);
x_43 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 lean::cnstr_release(x_39, 0);
 x_45 = x_39;
} else {
 lean::inc(x_43);
 lean::dec(x_39);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_48 = x_40;
} else {
 lean::inc(x_46);
 lean::dec(x_40);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_46);
if (lean::is_scalar(x_45)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_45;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_43);
return x_50;
}
else
{
obj* x_52; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_40);
x_52 = lean::cnstr_get(x_39, 1);
lean::inc(x_52);
lean::dec(x_39);
x_55 = lean::mk_nat_obj(1u);
x_56 = lean::nat_add(x_1, x_55);
x_57 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_56, x_2, x_52);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
if (lean::obj_tag(x_58) == 0)
{
obj* x_61; obj* x_63; obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_2);
x_61 = lean::cnstr_get(x_57, 1);
if (lean::is_exclusive(x_57)) {
 lean::cnstr_release(x_57, 0);
 x_63 = x_57;
} else {
 lean::inc(x_61);
 lean::dec(x_57);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_58, 0);
if (lean::is_exclusive(x_58)) {
 x_66 = x_58;
} else {
 lean::inc(x_64);
 lean::dec(x_58);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_64);
if (lean::is_scalar(x_63)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_63;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_61);
return x_68;
}
else
{
obj* x_70; obj* x_73; obj* x_74; 
lean::dec(x_58);
x_70 = lean::cnstr_get(x_57, 1);
lean::inc(x_70);
lean::dec(x_57);
x_73 = l_list_repr___main___rarg___closed__3;
x_74 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_73, x_2, x_70);
lean::dec(x_2);
return x_74;
}
}
}
}
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
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_15; obj* x_17; obj* x_20; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
x_9 = l_lean_ir_decl_header___main(x_0);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_13 = l_list_length__aux___main___rarg(x_10, x_5);
lean::dec(x_10);
x_15 = lean::nat_sub(x_13, x_7);
lean::dec(x_13);
x_17 = lean::nat_sub(x_15, x_1);
lean::dec(x_1);
lean::dec(x_15);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___boxed), 4, 2);
lean::closure_set(x_20, 0, x_2);
lean::closure_set(x_20, 1, x_17);
x_1 = x_8;
x_2 = x_20;
goto _start;
}
else
{
obj* x_23; 
lean::dec(x_1);
x_23 = lean::apply_2(x_2, x_3, x_4);
return x_23;
}
}
}
obj* _init_l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2___rarg___boxed), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_3 = l_lean_ir_decl_header___main(x_0);
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_list_length__aux___main___rarg(x_4, x_7);
lean::dec(x_4);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_8, x_10);
lean::dec(x_8);
x_13 = l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1___closed__1;
x_14 = l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3(x_0, x_11, x_13, x_1, x_2);
return x_14;
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
lean::inc(x_1);
x_10 = l_lean_ir_cpp_emit__uncurry__header(x_0, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_16; obj* x_18; obj* x_19; 
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_18 = x_11;
} else {
 lean::inc(x_16);
 lean::dec(x_11);
 x_18 = lean::box(0);
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
obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_31; 
lean::dec(x_11);
x_21 = lean::cnstr_get(x_10, 1);
lean::inc(x_21);
lean::dec(x_10);
x_24 = l_lean_ir_cpp_emit__uncurry___closed__3;
x_25 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_24, x_1, x_21);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = l_lean_ir_decl_header___main(x_0);
if (lean::obj_tag(x_26) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_31);
x_33 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_35 = x_26;
} else {
 lean::inc(x_33);
 lean::dec(x_26);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
x_6 = x_36;
x_7 = x_28;
goto lbl_8;
}
else
{
obj* x_38; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_26);
x_38 = lean::cnstr_get(x_31, 0);
lean::inc(x_38);
lean::dec(x_31);
x_41 = l_lean_ir_cpp_emit__terminator___closed__1;
x_42 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_41, x_1, x_28);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; obj* x_49; obj* x_51; obj* x_52; 
lean::dec(x_38);
x_46 = lean::cnstr_get(x_42, 1);
lean::inc(x_46);
lean::dec(x_42);
x_49 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_51 = x_43;
} else {
 lean::inc(x_49);
 lean::dec(x_43);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
x_6 = x_52;
x_7 = x_46;
goto lbl_8;
}
else
{
obj* x_54; obj* x_58; obj* x_59; obj* x_61; 
lean::dec(x_43);
x_54 = lean::cnstr_get(x_42, 1);
lean::inc(x_54);
lean::dec(x_42);
lean::inc(x_1);
x_58 = l_lean_ir_cpp_emit__fnid(x_38, x_1, x_54);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
x_6 = x_59;
x_7 = x_61;
goto lbl_8;
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_65; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_1);
x_65 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_67 = x_3;
} else {
 lean::inc(x_65);
 lean::dec(x_3);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_65);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_4);
return x_69;
}
else
{
obj* x_71; obj* x_72; 
lean::dec(x_3);
x_71 = l_lean_ir_cpp_emit__eos(x_1, x_4);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_1);
x_75 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 x_77 = x_71;
} else {
 lean::inc(x_75);
 lean::dec(x_71);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_80 = x_72;
} else {
 lean::inc(x_78);
 lean::dec(x_72);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
if (lean::is_scalar(x_77)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_77;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_75);
return x_82;
}
else
{
obj* x_84; obj* x_87; obj* x_88; 
lean::dec(x_72);
x_84 = lean::cnstr_get(x_71, 1);
lean::inc(x_84);
lean::dec(x_71);
x_87 = l_lean_ir_cpp_emit__uncurry___closed__1;
x_88 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_87, x_1, x_84);
lean::dec(x_1);
return x_88;
}
}
}
lbl_8:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_90; obj* x_92; obj* x_93; 
x_90 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_92 = x_6;
} else {
 lean::inc(x_90);
 lean::dec(x_6);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_90);
x_3 = x_93;
x_4 = x_7;
goto lbl_5;
}
else
{
obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_6);
x_95 = l_prod_has__repr___rarg___closed__1;
x_96 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_95, x_1, x_7);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
if (lean::obj_tag(x_97) == 0)
{
obj* x_99; obj* x_102; obj* x_104; obj* x_105; 
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
lean::dec(x_96);
x_102 = lean::cnstr_get(x_97, 0);
if (lean::is_exclusive(x_97)) {
 x_104 = x_97;
} else {
 lean::inc(x_102);
 lean::dec(x_97);
 x_104 = lean::box(0);
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_102);
x_3 = x_105;
x_4 = x_99;
goto lbl_5;
}
else
{
obj* x_107; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_97);
x_107 = lean::cnstr_get(x_96, 1);
lean::inc(x_107);
lean::dec(x_96);
x_110 = l_lean_ir_cpp_emit__uncurry___closed__2;
x_111 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_110, x_1, x_107);
x_112 = lean::cnstr_get(x_111, 0);
lean::inc(x_112);
if (lean::obj_tag(x_112) == 0)
{
obj* x_114; obj* x_117; obj* x_119; obj* x_120; 
x_114 = lean::cnstr_get(x_111, 1);
lean::inc(x_114);
lean::dec(x_111);
x_117 = lean::cnstr_get(x_112, 0);
if (lean::is_exclusive(x_112)) {
 x_119 = x_112;
} else {
 lean::inc(x_117);
 lean::dec(x_112);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_117);
x_3 = x_120;
x_4 = x_114;
goto lbl_5;
}
else
{
obj* x_122; obj* x_126; obj* x_127; 
lean::dec(x_112);
x_122 = lean::cnstr_get(x_111, 1);
lean::inc(x_122);
lean::dec(x_111);
lean::inc(x_1);
x_126 = l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1(x_0, x_1, x_122);
x_127 = lean::cnstr_get(x_126, 0);
lean::inc(x_127);
if (lean::obj_tag(x_127) == 0)
{
obj* x_129; obj* x_132; obj* x_134; obj* x_135; 
x_129 = lean::cnstr_get(x_126, 1);
lean::inc(x_129);
lean::dec(x_126);
x_132 = lean::cnstr_get(x_127, 0);
if (lean::is_exclusive(x_127)) {
 x_134 = x_127;
} else {
 lean::inc(x_132);
 lean::dec(x_127);
 x_134 = lean::box(0);
}
if (lean::is_scalar(x_134)) {
 x_135 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_135 = x_134;
}
lean::cnstr_set(x_135, 0, x_132);
x_3 = x_135;
x_4 = x_129;
goto lbl_5;
}
else
{
obj* x_136; obj* x_139; obj* x_142; obj* x_143; obj* x_144; 
x_136 = lean::cnstr_get(x_126, 1);
lean::inc(x_136);
lean::dec(x_126);
x_139 = lean::cnstr_get(x_127, 0);
lean::inc(x_139);
lean::dec(x_127);
x_142 = l_option_has__repr___rarg___closed__3;
x_143 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_142, x_1, x_136);
x_144 = lean::cnstr_get(x_143, 0);
lean::inc(x_144);
if (lean::obj_tag(x_144) == 0)
{
obj* x_147; obj* x_150; obj* x_152; obj* x_153; 
lean::dec(x_139);
x_147 = lean::cnstr_get(x_143, 1);
lean::inc(x_147);
lean::dec(x_143);
x_150 = lean::cnstr_get(x_144, 0);
if (lean::is_exclusive(x_144)) {
 x_152 = x_144;
} else {
 lean::inc(x_150);
 lean::dec(x_144);
 x_152 = lean::box(0);
}
if (lean::is_scalar(x_152)) {
 x_153 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_153 = x_152;
}
lean::cnstr_set(x_153, 0, x_150);
x_3 = x_153;
x_4 = x_147;
goto lbl_5;
}
else
{
obj* x_154; obj* x_155; obj* x_158; 
if (lean::is_exclusive(x_144)) {
 lean::cnstr_release(x_144, 0);
 x_154 = x_144;
} else {
 lean::dec(x_144);
 x_154 = lean::box(0);
}
x_155 = lean::cnstr_get(x_143, 1);
lean::inc(x_155);
lean::dec(x_143);
if (lean::is_scalar(x_154)) {
 x_158 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_158 = x_154;
}
lean::cnstr_set(x_158, 0, x_139);
x_3 = x_158;
x_4 = x_155;
goto lbl_5;
}
}
}
}
}
}
}
}
obj* l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_reader__t_pure___at_lean_ir_cpp_emit__uncurry___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_ir_cpp_emit__uncurry___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_emit__uncurry(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__def__core___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_14; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_cpp_emit__block(x_6, x_1, x_2);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_8);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_20 = x_12;
} else {
 lean::inc(x_18);
 lean::dec(x_12);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_23 = x_14;
} else {
 lean::inc(x_21);
 lean::dec(x_14);
 x_23 = lean::box(0);
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_20)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_20;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_18);
return x_25;
}
else
{
obj* x_27; 
lean::dec(x_14);
x_27 = lean::cnstr_get(x_12, 1);
lean::inc(x_27);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_27;
goto _start;
}
}
}
}
obj* l_lean_ir_cpp_emit__def__core(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_ir_decl_header___main(x_0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_9; 
lean::dec(x_1);
lean::dec(x_0);
x_9 = l_lean_ir_match__type___closed__5;
x_4 = x_9;
x_5 = x_2;
goto lbl_6;
}
else
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; uint8 x_18; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_10, 1);
lean::inc(x_14);
x_16 = l_lean_ir_cpp_need__uncurry(x_0);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
uint8 x_20; 
x_20 = 0;
x_18 = x_20;
goto lbl_19;
}
else
{
uint8 x_21; 
x_21 = 1;
x_18 = x_21;
goto lbl_19;
}
lbl_19:
{
obj* x_22; obj* x_23; obj* x_26; obj* x_27; 
lean::inc(x_1);
x_26 = l_lean_ir_cpp_emit__header(x_10, x_1, x_2);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_30; obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_14);
x_30 = lean::cnstr_get(x_26, 1);
lean::inc(x_30);
lean::dec(x_26);
x_33 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_35 = x_27;
} else {
 lean::inc(x_33);
 lean::dec(x_27);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
x_22 = x_36;
x_23 = x_30;
goto lbl_24;
}
else
{
obj* x_38; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_27);
x_38 = lean::cnstr_get(x_26, 1);
lean::inc(x_38);
lean::dec(x_26);
x_41 = l_lean_ir_cpp_emit__case___main___closed__1;
x_42 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_41, x_1, x_38);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; obj* x_49; obj* x_51; obj* x_52; 
lean::dec(x_14);
x_46 = lean::cnstr_get(x_42, 1);
lean::inc(x_46);
lean::dec(x_42);
x_49 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_51 = x_43;
} else {
 lean::inc(x_49);
 lean::dec(x_43);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
x_22 = x_52;
x_23 = x_46;
goto lbl_24;
}
else
{
obj* x_54; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_43);
x_54 = lean::cnstr_get(x_42, 1);
lean::inc(x_54);
lean::dec(x_42);
x_57 = l_lean_format_be___main___closed__1;
x_58 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_57, x_1, x_54);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
if (lean::obj_tag(x_59) == 0)
{
obj* x_62; obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_14);
x_62 = lean::cnstr_get(x_58, 1);
lean::inc(x_62);
lean::dec(x_58);
x_65 = lean::cnstr_get(x_59, 0);
if (lean::is_exclusive(x_59)) {
 x_67 = x_59;
} else {
 lean::inc(x_65);
 lean::dec(x_59);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_65);
x_22 = x_68;
x_23 = x_62;
goto lbl_24;
}
else
{
obj* x_70; obj* x_74; obj* x_76; obj* x_78; 
lean::dec(x_59);
x_70 = lean::cnstr_get(x_58, 1);
lean::inc(x_70);
lean::dec(x_58);
lean::inc(x_1);
x_74 = l_lean_ir_cpp_decl__locals(x_14, x_1, x_70);
lean::dec(x_14);
x_76 = lean::cnstr_get(x_74, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_74, 1);
lean::inc(x_78);
lean::dec(x_74);
x_22 = x_76;
x_23 = x_78;
goto lbl_24;
}
}
}
lbl_24:
{
if (lean::obj_tag(x_22) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_12);
lean::dec(x_1);
lean::dec(x_0);
x_84 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_86 = x_22;
} else {
 lean::inc(x_84);
 lean::dec(x_22);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_84);
x_4 = x_87;
x_5 = x_23;
goto lbl_6;
}
else
{
obj* x_90; obj* x_91; 
lean::dec(x_22);
lean::inc(x_1);
x_90 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__def__core___spec__1(x_12, x_1, x_23);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
if (lean::obj_tag(x_91) == 0)
{
obj* x_95; obj* x_98; obj* x_100; obj* x_101; 
lean::dec(x_1);
lean::dec(x_0);
x_95 = lean::cnstr_get(x_90, 1);
lean::inc(x_95);
lean::dec(x_90);
x_98 = lean::cnstr_get(x_91, 0);
if (lean::is_exclusive(x_91)) {
 x_100 = x_91;
} else {
 lean::inc(x_98);
 lean::dec(x_91);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
x_4 = x_101;
x_5 = x_95;
goto lbl_6;
}
else
{
obj* x_103; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_91);
x_103 = lean::cnstr_get(x_90, 1);
lean::inc(x_103);
lean::dec(x_90);
x_106 = l_lean_ir_cpp_emit__case___main___closed__2;
x_107 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_106, x_1, x_103);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
if (lean::obj_tag(x_108) == 0)
{
obj* x_112; obj* x_115; obj* x_117; obj* x_118; 
lean::dec(x_1);
lean::dec(x_0);
x_112 = lean::cnstr_get(x_107, 1);
lean::inc(x_112);
lean::dec(x_107);
x_115 = lean::cnstr_get(x_108, 0);
if (lean::is_exclusive(x_108)) {
 x_117 = x_108;
} else {
 lean::inc(x_115);
 lean::dec(x_108);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_115);
x_4 = x_118;
x_5 = x_112;
goto lbl_6;
}
else
{
obj* x_120; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_108);
x_120 = lean::cnstr_get(x_107, 1);
lean::inc(x_120);
lean::dec(x_107);
x_123 = l_lean_format_be___main___closed__1;
x_124 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_123, x_1, x_120);
x_125 = lean::cnstr_get(x_124, 0);
lean::inc(x_125);
if (lean::obj_tag(x_125) == 0)
{
obj* x_129; obj* x_132; obj* x_134; obj* x_135; 
lean::dec(x_1);
lean::dec(x_0);
x_129 = lean::cnstr_get(x_124, 1);
lean::inc(x_129);
lean::dec(x_124);
x_132 = lean::cnstr_get(x_125, 0);
if (lean::is_exclusive(x_125)) {
 x_134 = x_125;
} else {
 lean::inc(x_132);
 lean::dec(x_125);
 x_134 = lean::box(0);
}
if (lean::is_scalar(x_134)) {
 x_135 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_135 = x_134;
}
lean::cnstr_set(x_135, 0, x_132);
x_4 = x_135;
x_5 = x_129;
goto lbl_6;
}
else
{
lean::dec(x_125);
if (x_18 == 0)
{
obj* x_139; obj* x_142; 
lean::dec(x_1);
lean::dec(x_0);
x_139 = lean::cnstr_get(x_124, 1);
lean::inc(x_139);
lean::dec(x_124);
x_142 = l_lean_ir_match__type___closed__5;
x_4 = x_142;
x_5 = x_139;
goto lbl_6;
}
else
{
obj* x_143; obj* x_146; obj* x_148; obj* x_150; 
x_143 = lean::cnstr_get(x_124, 1);
lean::inc(x_143);
lean::dec(x_124);
x_146 = l_lean_ir_cpp_emit__uncurry(x_0, x_1, x_143);
lean::dec(x_0);
x_148 = lean::cnstr_get(x_146, 0);
lean::inc(x_148);
x_150 = lean::cnstr_get(x_146, 1);
lean::inc(x_150);
lean::dec(x_146);
x_4 = x_148;
x_5 = x_150;
goto lbl_6;
}
}
}
}
}
}
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_153; obj* x_155; obj* x_156; obj* x_159; uint8 x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
x_153 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_155 = x_4;
} else {
 lean::inc(x_153);
 lean::dec(x_4);
 x_155 = lean::box(0);
}
x_156 = lean::cnstr_get(x_3, 0);
lean::inc(x_156);
lean::dec(x_3);
x_159 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_156);
x_160 = 0;
x_161 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_162 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_162, 0, x_161);
lean::cnstr_set(x_162, 1, x_159);
lean::cnstr_set_scalar(x_162, sizeof(void*)*2, x_160);
x_163 = x_162;
x_164 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_165 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_165, 0, x_163);
lean::cnstr_set(x_165, 1, x_164);
lean::cnstr_set_scalar(x_165, sizeof(void*)*2, x_160);
x_166 = x_165;
x_167 = lean::box(1);
x_168 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_168, 0, x_166);
lean::cnstr_set(x_168, 1, x_167);
lean::cnstr_set_scalar(x_168, sizeof(void*)*2, x_160);
x_169 = x_168;
x_170 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_170, 0, x_169);
lean::cnstr_set(x_170, 1, x_153);
lean::cnstr_set_scalar(x_170, sizeof(void*)*2, x_160);
x_171 = x_170;
if (lean::is_scalar(x_155)) {
 x_172 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_172 = x_155;
}
lean::cnstr_set(x_172, 0, x_171);
x_173 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_173, 0, x_172);
lean::cnstr_set(x_173, 1, x_5);
return x_173;
}
else
{
obj* x_175; 
lean::dec(x_3);
x_175 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_175, 0, x_4);
lean::cnstr_set(x_175, 1, x_5);
return x_175;
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
if (lean::is_exclusive(x_9)) {
 x_14 = x_9;
} else {
 lean::inc(x_12);
 lean::dec(x_9);
 x_14 = lean::box(0);
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
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_4; obj* x_5; 
x_3 = 0;
x_4 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
lean::cnstr_set_scalar(x_4, sizeof(void*)*4, x_3);
x_5 = x_4;
return x_5;
}
else
{
uint8 x_6; 
x_6 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; 
x_7 = lean::cnstr_get(x_0, 0);
x_9 = lean::cnstr_get(x_0, 1);
x_11 = lean::cnstr_get(x_0, 2);
x_13 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_15 = x_0;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_0);
 x_15 = lean::box(0);
}
x_16 = l_lean_name_quick__lt___main(x_1, x_9);
x_17 = lean::unbox(x_16);
if (x_17 == 0)
{
obj* x_18; uint8 x_19; 
x_18 = l_lean_name_quick__lt___main(x_9, x_1);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_11);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_7);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_2);
lean::cnstr_set(x_22, 3, x_13);
lean::cnstr_set_scalar(x_22, sizeof(void*)*4, x_6);
x_23 = x_22;
return x_23;
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_13, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_25 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_25 = x_15;
}
lean::cnstr_set(x_25, 0, x_7);
lean::cnstr_set(x_25, 1, x_9);
lean::cnstr_set(x_25, 2, x_11);
lean::cnstr_set(x_25, 3, x_24);
lean::cnstr_set_scalar(x_25, sizeof(void*)*4, x_6);
x_26 = x_25;
return x_26;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_7, x_1, x_2);
if (lean::is_scalar(x_15)) {
 x_28 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_28 = x_15;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_11);
lean::cnstr_set(x_28, 3, x_13);
lean::cnstr_set_scalar(x_28, sizeof(void*)*4, x_6);
x_29 = x_28;
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; uint8 x_40; 
x_30 = lean::cnstr_get(x_0, 0);
x_32 = lean::cnstr_get(x_0, 1);
x_34 = lean::cnstr_get(x_0, 2);
x_36 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_38 = x_0;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_0);
 x_38 = lean::box(0);
}
x_39 = l_lean_name_quick__lt___main(x_1, x_32);
x_40 = lean::unbox(x_39);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = l_lean_name_quick__lt___main(x_32, x_1);
x_42 = lean::unbox(x_41);
if (x_42 == 0)
{
obj* x_45; obj* x_46; 
lean::dec(x_34);
lean::dec(x_32);
if (lean::is_scalar(x_38)) {
 x_45 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_45 = x_38;
}
lean::cnstr_set(x_45, 0, x_30);
lean::cnstr_set(x_45, 1, x_1);
lean::cnstr_set(x_45, 2, x_2);
lean::cnstr_set(x_45, 3, x_36);
lean::cnstr_set_scalar(x_45, sizeof(void*)*4, x_6);
x_46 = x_45;
return x_46;
}
else
{
uint8 x_47; 
x_47 = l_rbnode_is__red___main___rarg(x_36);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_49 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_49 = x_38;
}
lean::cnstr_set(x_49, 0, x_30);
lean::cnstr_set(x_49, 1, x_32);
lean::cnstr_set(x_49, 2, x_34);
lean::cnstr_set(x_49, 3, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*4, x_6);
x_50 = x_49;
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_51 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_52 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_52 = x_38;
}
lean::cnstr_set(x_52, 0, x_30);
lean::cnstr_set(x_52, 1, x_32);
lean::cnstr_set(x_52, 2, x_34);
lean::cnstr_set(x_52, 3, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*4, x_6);
x_53 = x_52;
x_54 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_36, x_1, x_2);
x_55 = l_rbnode_balance2___main___rarg(x_53, x_54);
return x_55;
}
}
}
else
{
uint8 x_56; 
x_56 = l_rbnode_is__red___main___rarg(x_30);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; 
x_57 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_36);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_6);
x_59 = x_58;
return x_59;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_60 = lean::box(0);
if (lean::is_scalar(x_38)) {
 x_61 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_61 = x_38;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_32);
lean::cnstr_set(x_61, 2, x_34);
lean::cnstr_set(x_61, 3, x_36);
lean::cnstr_set_scalar(x_61, sizeof(void*)*4, x_6);
x_62 = x_61;
x_63 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_30, x_1, x_2);
x_64 = l_rbnode_balance1___main___rarg(x_62, x_63);
return x_64;
}
}
}
}
}
}
obj* l_rbnode_insert___at_lean_ir_cpp_collect__used___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
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
return x_0;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::box(0);
x_11 = l_rbnode_insert___at_lean_ir_cpp_collect__used___spec__2(x_0, x_7, x_10);
x_0 = x_11;
x_1 = x_4;
goto _start;
}
case 11:
{
obj* x_13; obj* x_16; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_2, 1);
lean::inc(x_16);
lean::dec(x_2);
x_19 = lean::box(0);
x_20 = l_rbnode_insert___at_lean_ir_cpp_collect__used___spec__2(x_0, x_16, x_19);
x_0 = x_20;
x_1 = x_13;
goto _start;
}
default:
{
obj* x_23; 
lean::dec(x_2);
x_23 = lean::cnstr_get(x_1, 1);
lean::inc(x_23);
lean::dec(x_1);
x_1 = x_23;
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
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_7; obj* x_10; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
x_10 = l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__4(x_0, x_7);
x_0 = x_10;
x_1 = x_4;
goto _start;
}
}
}
obj* l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__6(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_1 = x_5;
goto _start;
}
else
{
obj* x_9; obj* x_12; obj* x_15; 
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::dec(x_2);
x_15 = l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__5(x_0, x_12);
x_0 = x_15;
x_1 = x_9;
goto _start;
}
}
}
}
obj* l_lean_ir_cpp_collect__used(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_ir_mk__fnid__set;
x_2 = l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__6(x_1, x_0);
return x_2;
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_18; obj* x_19; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 3);
lean::inc(x_13);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_0);
x_18 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1(x_0, x_9, x_2, x_3, x_4);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
x_25 = lean::cnstr_get(x_18, 1);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 x_27 = x_18;
} else {
 lean::inc(x_25);
 lean::dec(x_18);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_30 = x_19;
} else {
 lean::inc(x_28);
 lean::dec(x_19);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
if (lean::is_scalar(x_27)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_27;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_25);
return x_32;
}
else
{
obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_45; 
lean::dec(x_19);
x_34 = lean::cnstr_get(x_18, 1);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_set(x_18, 1, lean::box(0));
 x_36 = x_18;
} else {
 lean::inc(x_34);
 lean::dec(x_18);
 x_36 = lean::box(0);
}
x_40 = lean::cnstr_get(x_0, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_40, 3);
lean::inc(x_42);
lean::inc(x_11);
x_45 = lean::apply_1(x_42, x_11);
if (lean::obj_tag(x_45) == 0)
{
obj* x_48; 
lean::dec(x_11);
lean::dec(x_40);
x_48 = l_lean_ir_match__type___closed__5;
x_37 = x_48;
x_38 = x_34;
goto lbl_39;
}
else
{
obj* x_49; obj* x_52; obj* x_55; 
x_49 = lean::cnstr_get(x_45, 0);
lean::inc(x_49);
lean::dec(x_45);
x_52 = lean::cnstr_get(x_40, 4);
lean::inc(x_52);
lean::dec(x_40);
x_55 = lean::apply_1(x_52, x_11);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_57; uint8 x_58; obj* x_60; 
x_56 = l_lean_ir_decl_header___main(x_49);
x_57 = l_lean_ir_cpp_need__uncurry(x_49);
x_58 = lean::unbox(x_57);
lean::inc(x_3);
x_60 = l_lean_ir_cpp_emit__header(x_56, x_3, x_34);
if (x_58 == 0)
{
obj* x_62; 
lean::dec(x_49);
x_62 = lean::cnstr_get(x_60, 0);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_67; obj* x_69; obj* x_70; 
x_64 = lean::cnstr_get(x_60, 1);
lean::inc(x_64);
lean::dec(x_60);
x_67 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_69 = x_62;
} else {
 lean::inc(x_67);
 lean::dec(x_62);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_67);
x_37 = x_70;
x_38 = x_64;
goto lbl_39;
}
else
{
obj* x_72; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_62);
x_72 = lean::cnstr_get(x_60, 1);
lean::inc(x_72);
lean::dec(x_60);
x_75 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
x_76 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_75, x_3, x_72);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
if (lean::obj_tag(x_77) == 0)
{
obj* x_79; obj* x_82; obj* x_84; obj* x_85; 
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
x_82 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_84 = x_77;
} else {
 lean::inc(x_82);
 lean::dec(x_77);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_82);
x_37 = x_85;
x_38 = x_79;
goto lbl_39;
}
else
{
obj* x_87; obj* x_90; 
lean::dec(x_77);
x_87 = lean::cnstr_get(x_76, 1);
lean::inc(x_87);
lean::dec(x_76);
x_90 = l_lean_ir_match__type___closed__5;
x_37 = x_90;
x_38 = x_87;
goto lbl_39;
}
}
}
else
{
obj* x_91; 
x_91 = lean::cnstr_get(x_60, 0);
lean::inc(x_91);
if (lean::obj_tag(x_91) == 0)
{
obj* x_94; obj* x_97; obj* x_99; obj* x_100; 
lean::dec(x_49);
x_94 = lean::cnstr_get(x_60, 1);
lean::inc(x_94);
lean::dec(x_60);
x_97 = lean::cnstr_get(x_91, 0);
if (lean::is_exclusive(x_91)) {
 x_99 = x_91;
} else {
 lean::inc(x_97);
 lean::dec(x_91);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_97);
x_37 = x_100;
x_38 = x_94;
goto lbl_39;
}
else
{
obj* x_102; obj* x_105; obj* x_106; obj* x_107; 
lean::dec(x_91);
x_102 = lean::cnstr_get(x_60, 1);
lean::inc(x_102);
lean::dec(x_60);
x_105 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
x_106 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_105, x_3, x_102);
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
if (lean::obj_tag(x_107) == 0)
{
obj* x_110; obj* x_113; obj* x_115; obj* x_116; 
lean::dec(x_49);
x_110 = lean::cnstr_get(x_106, 1);
lean::inc(x_110);
lean::dec(x_106);
x_113 = lean::cnstr_get(x_107, 0);
if (lean::is_exclusive(x_107)) {
 x_115 = x_107;
} else {
 lean::inc(x_113);
 lean::dec(x_107);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_113);
x_37 = x_116;
x_38 = x_110;
goto lbl_39;
}
else
{
obj* x_118; obj* x_122; obj* x_124; 
lean::dec(x_107);
x_118 = lean::cnstr_get(x_106, 1);
lean::inc(x_118);
lean::dec(x_106);
lean::inc(x_3);
x_122 = l_lean_ir_cpp_emit__uncurry__header(x_49, x_3, x_118);
lean::dec(x_49);
x_124 = lean::cnstr_get(x_122, 0);
lean::inc(x_124);
if (lean::obj_tag(x_124) == 0)
{
obj* x_126; obj* x_129; obj* x_131; obj* x_132; 
x_126 = lean::cnstr_get(x_122, 1);
lean::inc(x_126);
lean::dec(x_122);
x_129 = lean::cnstr_get(x_124, 0);
if (lean::is_exclusive(x_124)) {
 x_131 = x_124;
} else {
 lean::inc(x_129);
 lean::dec(x_124);
 x_131 = lean::box(0);
}
if (lean::is_scalar(x_131)) {
 x_132 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_132 = x_131;
}
lean::cnstr_set(x_132, 0, x_129);
x_37 = x_132;
x_38 = x_126;
goto lbl_39;
}
else
{
obj* x_134; obj* x_137; obj* x_138; obj* x_140; 
lean::dec(x_124);
x_134 = lean::cnstr_get(x_122, 1);
lean::inc(x_134);
lean::dec(x_122);
x_137 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_105, x_3, x_134);
x_138 = lean::cnstr_get(x_137, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_137, 1);
lean::inc(x_140);
lean::dec(x_137);
x_37 = x_138;
x_38 = x_140;
goto lbl_39;
}
}
}
}
}
else
{
obj* x_144; obj* x_145; obj* x_146; 
lean::dec(x_55);
x_144 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2;
x_145 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_144, x_3, x_34);
x_146 = lean::cnstr_get(x_145, 0);
lean::inc(x_146);
if (lean::obj_tag(x_146) == 0)
{
obj* x_149; obj* x_152; obj* x_154; obj* x_155; 
lean::dec(x_49);
x_149 = lean::cnstr_get(x_145, 1);
lean::inc(x_149);
lean::dec(x_145);
x_152 = lean::cnstr_get(x_146, 0);
if (lean::is_exclusive(x_146)) {
 x_154 = x_146;
} else {
 lean::inc(x_152);
 lean::dec(x_146);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_152);
x_37 = x_155;
x_38 = x_149;
goto lbl_39;
}
else
{
obj* x_157; obj* x_160; obj* x_161; uint8 x_162; obj* x_164; 
lean::dec(x_146);
x_157 = lean::cnstr_get(x_145, 1);
lean::inc(x_157);
lean::dec(x_145);
x_160 = l_lean_ir_decl_header___main(x_49);
x_161 = l_lean_ir_cpp_need__uncurry(x_49);
x_162 = lean::unbox(x_161);
lean::inc(x_3);
x_164 = l_lean_ir_cpp_emit__header(x_160, x_3, x_157);
if (x_162 == 0)
{
obj* x_166; 
lean::dec(x_49);
x_166 = lean::cnstr_get(x_164, 0);
lean::inc(x_166);
if (lean::obj_tag(x_166) == 0)
{
obj* x_168; obj* x_171; obj* x_173; obj* x_174; 
x_168 = lean::cnstr_get(x_164, 1);
lean::inc(x_168);
lean::dec(x_164);
x_171 = lean::cnstr_get(x_166, 0);
if (lean::is_exclusive(x_166)) {
 x_173 = x_166;
} else {
 lean::inc(x_171);
 lean::dec(x_166);
 x_173 = lean::box(0);
}
if (lean::is_scalar(x_173)) {
 x_174 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_174 = x_173;
}
lean::cnstr_set(x_174, 0, x_171);
x_37 = x_174;
x_38 = x_168;
goto lbl_39;
}
else
{
obj* x_176; obj* x_179; obj* x_180; obj* x_181; 
lean::dec(x_166);
x_176 = lean::cnstr_get(x_164, 1);
lean::inc(x_176);
lean::dec(x_164);
x_179 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
x_180 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_179, x_3, x_176);
x_181 = lean::cnstr_get(x_180, 0);
lean::inc(x_181);
if (lean::obj_tag(x_181) == 0)
{
obj* x_183; obj* x_186; obj* x_188; obj* x_189; 
x_183 = lean::cnstr_get(x_180, 1);
lean::inc(x_183);
lean::dec(x_180);
x_186 = lean::cnstr_get(x_181, 0);
if (lean::is_exclusive(x_181)) {
 x_188 = x_181;
} else {
 lean::inc(x_186);
 lean::dec(x_181);
 x_188 = lean::box(0);
}
if (lean::is_scalar(x_188)) {
 x_189 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_189 = x_188;
}
lean::cnstr_set(x_189, 0, x_186);
x_37 = x_189;
x_38 = x_183;
goto lbl_39;
}
else
{
obj* x_191; obj* x_194; 
lean::dec(x_181);
x_191 = lean::cnstr_get(x_180, 1);
lean::inc(x_191);
lean::dec(x_180);
x_194 = l_lean_ir_match__type___closed__5;
x_37 = x_194;
x_38 = x_191;
goto lbl_39;
}
}
}
else
{
obj* x_195; 
x_195 = lean::cnstr_get(x_164, 0);
lean::inc(x_195);
if (lean::obj_tag(x_195) == 0)
{
obj* x_198; obj* x_201; obj* x_203; obj* x_204; 
lean::dec(x_49);
x_198 = lean::cnstr_get(x_164, 1);
lean::inc(x_198);
lean::dec(x_164);
x_201 = lean::cnstr_get(x_195, 0);
if (lean::is_exclusive(x_195)) {
 x_203 = x_195;
} else {
 lean::inc(x_201);
 lean::dec(x_195);
 x_203 = lean::box(0);
}
if (lean::is_scalar(x_203)) {
 x_204 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_204 = x_203;
}
lean::cnstr_set(x_204, 0, x_201);
x_37 = x_204;
x_38 = x_198;
goto lbl_39;
}
else
{
obj* x_206; obj* x_209; obj* x_210; obj* x_211; 
lean::dec(x_195);
x_206 = lean::cnstr_get(x_164, 1);
lean::inc(x_206);
lean::dec(x_164);
x_209 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
x_210 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_209, x_3, x_206);
x_211 = lean::cnstr_get(x_210, 0);
lean::inc(x_211);
if (lean::obj_tag(x_211) == 0)
{
obj* x_214; obj* x_217; obj* x_219; obj* x_220; 
lean::dec(x_49);
x_214 = lean::cnstr_get(x_210, 1);
lean::inc(x_214);
lean::dec(x_210);
x_217 = lean::cnstr_get(x_211, 0);
if (lean::is_exclusive(x_211)) {
 x_219 = x_211;
} else {
 lean::inc(x_217);
 lean::dec(x_211);
 x_219 = lean::box(0);
}
if (lean::is_scalar(x_219)) {
 x_220 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_220 = x_219;
}
lean::cnstr_set(x_220, 0, x_217);
x_37 = x_220;
x_38 = x_214;
goto lbl_39;
}
else
{
obj* x_222; obj* x_226; obj* x_228; 
lean::dec(x_211);
x_222 = lean::cnstr_get(x_210, 1);
lean::inc(x_222);
lean::dec(x_210);
lean::inc(x_3);
x_226 = l_lean_ir_cpp_emit__uncurry__header(x_49, x_3, x_222);
lean::dec(x_49);
x_228 = lean::cnstr_get(x_226, 0);
lean::inc(x_228);
if (lean::obj_tag(x_228) == 0)
{
obj* x_230; obj* x_233; obj* x_235; obj* x_236; 
x_230 = lean::cnstr_get(x_226, 1);
lean::inc(x_230);
lean::dec(x_226);
x_233 = lean::cnstr_get(x_228, 0);
if (lean::is_exclusive(x_228)) {
 x_235 = x_228;
} else {
 lean::inc(x_233);
 lean::dec(x_228);
 x_235 = lean::box(0);
}
if (lean::is_scalar(x_235)) {
 x_236 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_236 = x_235;
}
lean::cnstr_set(x_236, 0, x_233);
x_37 = x_236;
x_38 = x_230;
goto lbl_39;
}
else
{
obj* x_238; obj* x_241; obj* x_242; obj* x_244; 
lean::dec(x_228);
x_238 = lean::cnstr_get(x_226, 1);
lean::inc(x_238);
lean::dec(x_226);
x_241 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_209, x_3, x_238);
x_242 = lean::cnstr_get(x_241, 0);
lean::inc(x_242);
x_244 = lean::cnstr_get(x_241, 1);
lean::inc(x_244);
lean::dec(x_241);
x_37 = x_242;
x_38 = x_244;
goto lbl_39;
}
}
}
}
}
}
}
lbl_39:
{
if (lean::obj_tag(x_37) == 0)
{
obj* x_250; obj* x_252; obj* x_253; obj* x_254; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_250 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_252 = x_37;
} else {
 lean::inc(x_250);
 lean::dec(x_37);
 x_252 = lean::box(0);
}
if (lean::is_scalar(x_252)) {
 x_253 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_253 = x_252;
}
lean::cnstr_set(x_253, 0, x_250);
if (lean::is_scalar(x_36)) {
 x_254 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_254 = x_36;
}
lean::cnstr_set(x_254, 0, x_253);
lean::cnstr_set(x_254, 1, x_38);
return x_254;
}
else
{
obj* x_257; 
lean::dec(x_37);
lean::dec(x_36);
x_257 = lean::box(0);
x_1 = x_13;
x_2 = x_257;
x_4 = x_38;
goto _start;
}
}
}
}
}
}
obj* l_lean_ir_cpp_emit__used__headers(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; 
x_3 = l_lean_ir_mk__fnid__set;
x_4 = l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__6(x_3, x_0);
x_5 = lean::box(0);
lean::inc(x_1);
x_7 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1(x_1, x_4, x_5, x_1, x_2);
return x_7;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__global__var__decls___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::cnstr_get(x_0, 0);
x_7 = lean::cnstr_get(x_0, 1);
x_8 = l_lean_ir_decl_header___main(x_6);
x_9 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*3);
if (x_9 == 0)
{
lean::dec(x_8);
x_0 = x_7;
goto _start;
}
else
{
obj* x_12; uint8 x_14; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_8, 2);
lean::inc(x_12);
x_14 = lean::unbox(x_12);
x_15 = l_lean_ir_cpp_emit__type(x_14, x_1, x_2);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_8);
lean::dec(x_1);
x_20 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_22 = x_15;
} else {
 lean::inc(x_20);
 lean::dec(x_15);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_25 = x_16;
} else {
 lean::inc(x_23);
 lean::dec(x_16);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_23);
if (lean::is_scalar(x_22)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_22;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_20);
return x_27;
}
else
{
obj* x_29; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_16);
x_29 = lean::cnstr_get(x_15, 1);
lean::inc(x_29);
lean::dec(x_15);
x_32 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
x_33 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_32, x_1, x_29);
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
if (lean::obj_tag(x_34) == 0)
{
obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_8);
lean::dec(x_1);
x_38 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_40 = x_33;
} else {
 lean::inc(x_38);
 lean::dec(x_33);
 x_40 = lean::box(0);
}
x_41 = lean::cnstr_get(x_34, 0);
if (lean::is_exclusive(x_34)) {
 x_43 = x_34;
} else {
 lean::inc(x_41);
 lean::dec(x_34);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_41);
if (lean::is_scalar(x_40)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_40;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_38);
return x_45;
}
else
{
obj* x_47; obj* x_50; obj* x_54; obj* x_55; 
lean::dec(x_34);
x_47 = lean::cnstr_get(x_33, 1);
lean::inc(x_47);
lean::dec(x_33);
x_50 = lean::cnstr_get(x_8, 0);
lean::inc(x_50);
lean::dec(x_8);
lean::inc(x_1);
x_54 = l_lean_ir_cpp_emit__global(x_50, x_1, x_47);
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
if (lean::obj_tag(x_55) == 0)
{
obj* x_58; obj* x_60; obj* x_61; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_1);
x_58 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_release(x_54, 0);
 x_60 = x_54;
} else {
 lean::inc(x_58);
 lean::dec(x_54);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 x_63 = x_55;
} else {
 lean::inc(x_61);
 lean::dec(x_55);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_61);
if (lean::is_scalar(x_60)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_60;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_58);
return x_65;
}
else
{
obj* x_67; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_55);
x_67 = lean::cnstr_get(x_54, 1);
lean::inc(x_67);
lean::dec(x_54);
x_70 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
x_71 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_70, x_1, x_67);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_1);
x_75 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 x_77 = x_71;
} else {
 lean::inc(x_75);
 lean::dec(x_71);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_72, 0);
if (lean::is_exclusive(x_72)) {
 x_80 = x_72;
} else {
 lean::inc(x_78);
 lean::dec(x_72);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
if (lean::is_scalar(x_77)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_77;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_75);
return x_82;
}
else
{
obj* x_84; 
lean::dec(x_72);
x_84 = lean::cnstr_get(x_71, 1);
lean::inc(x_84);
lean::dec(x_71);
x_0 = x_7;
x_2 = x_84;
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
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__global__var__decls___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__global__var__decls___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_ir_cpp_emit__global__var__decls___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_emit__global__var__decls(x_0, x_1, x_2);
lean::dec(x_0);
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
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_match__type___closed__5;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
x_7 = l_lean_ir_cpp_initialize__prefix;
x_8 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_7, x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_13 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
if (lean::is_scalar(x_13)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_13;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_11);
return x_18;
}
else
{
obj* x_20; obj* x_23; obj* x_24; 
lean::dec(x_9);
x_20 = lean::cnstr_get(x_8, 1);
lean::inc(x_20);
lean::dec(x_8);
x_23 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_5, x_1, x_20);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
x_26 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_28 = x_23;
} else {
 lean::inc(x_26);
 lean::dec(x_23);
 x_28 = lean::box(0);
}
x_29 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_31 = x_24;
} else {
 lean::inc(x_29);
 lean::dec(x_24);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_28)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_28;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_26);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_24);
x_35 = lean::cnstr_get(x_23, 1);
lean::inc(x_35);
lean::dec(x_23);
x_38 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_38, x_1, x_35);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
x_42 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 lean::cnstr_release(x_39, 0);
 x_44 = x_39;
} else {
 lean::inc(x_42);
 lean::dec(x_39);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_47 = x_40;
} else {
 lean::inc(x_45);
 lean::dec(x_40);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
if (lean::is_scalar(x_44)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_44;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_42);
return x_49;
}
else
{
obj* x_51; 
lean::dec(x_40);
x_51 = lean::cnstr_get(x_39, 1);
lean::inc(x_51);
lean::dec(x_39);
x_0 = x_6;
x_2 = x_51;
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
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::cnstr_get(x_0, 0);
x_7 = lean::cnstr_get(x_0, 1);
x_8 = l_lean_ir_decl_header___main(x_6);
x_9 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*3);
if (x_9 == 0)
{
lean::dec(x_8);
x_0 = x_7;
goto _start;
}
else
{
obj* x_12; obj* x_17; obj* x_18; 
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
lean::dec(x_8);
lean::inc(x_1);
lean::inc(x_12);
x_17 = l_lean_ir_cpp_emit__global(x_12, x_1, x_2);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_12);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_24 = x_17;
} else {
 lean::inc(x_22);
 lean::dec(x_17);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_18, 0);
if (lean::is_exclusive(x_18)) {
 x_27 = x_18;
} else {
 lean::inc(x_25);
 lean::dec(x_18);
 x_27 = lean::box(0);
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_25);
if (lean::is_scalar(x_24)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_24;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_22);
return x_29;
}
else
{
obj* x_31; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_18);
x_31 = lean::cnstr_get(x_17, 1);
lean::inc(x_31);
lean::dec(x_17);
x_34 = l_lean_ir_cpp_emit__infix___closed__1;
x_35 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_34, x_1, x_31);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_12);
lean::dec(x_1);
x_40 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 x_42 = x_35;
} else {
 lean::inc(x_40);
 lean::dec(x_35);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_36, 0);
if (lean::is_exclusive(x_36)) {
 x_45 = x_36;
} else {
 lean::inc(x_43);
 lean::dec(x_36);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_43);
if (lean::is_scalar(x_42)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_42;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_40);
return x_47;
}
else
{
obj* x_49; obj* x_53; obj* x_54; 
lean::dec(x_36);
x_49 = lean::cnstr_get(x_35, 1);
lean::inc(x_49);
lean::dec(x_35);
lean::inc(x_1);
x_53 = l_lean_ir_cpp_emit__fnid(x_12, x_1, x_49);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_1);
x_57 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 x_59 = x_53;
} else {
 lean::inc(x_57);
 lean::dec(x_53);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_54, 0);
if (lean::is_exclusive(x_54)) {
 x_62 = x_54;
} else {
 lean::inc(x_60);
 lean::dec(x_54);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_60);
if (lean::is_scalar(x_59)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_59;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_57);
return x_64;
}
else
{
obj* x_66; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_54);
x_66 = lean::cnstr_get(x_53, 1);
lean::inc(x_66);
lean::dec(x_53);
x_69 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
x_70 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_69, x_1, x_66);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
obj* x_74; obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_1);
x_74 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 x_76 = x_70;
} else {
 lean::inc(x_74);
 lean::dec(x_70);
 x_76 = lean::box(0);
}
x_77 = lean::cnstr_get(x_71, 0);
if (lean::is_exclusive(x_71)) {
 x_79 = x_71;
} else {
 lean::inc(x_77);
 lean::dec(x_71);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
if (lean::is_scalar(x_76)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_76;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_74);
return x_81;
}
else
{
obj* x_83; 
lean::dec(x_71);
x_83 = lean::cnstr_get(x_70, 1);
lean::inc(x_83);
lean::dec(x_70);
x_0 = x_7;
x_2 = x_83;
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
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_ir_cpp_emit__initialize__proc___closed__1;
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
} else {
 lean::inc(x_8);
 lean::dec(x_4);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_13 = x_5;
} else {
 lean::inc(x_11);
 lean::dec(x_5);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
if (lean::is_scalar(x_10)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_10;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_8);
return x_15;
}
else
{
obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_5);
x_17 = lean::cnstr_get(x_4, 1);
lean::inc(x_17);
lean::dec(x_4);
x_20 = l_lean_ir_cpp_initialize__prefix;
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_20, x_1, x_17);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_1);
x_25 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_27 = x_21;
} else {
 lean::inc(x_25);
 lean::dec(x_21);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_30 = x_22;
} else {
 lean::inc(x_28);
 lean::dec(x_22);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
if (lean::is_scalar(x_27)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_27;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_25);
return x_32;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_41; obj* x_43; 
lean::dec(x_22);
x_34 = lean::cnstr_get(x_21, 1);
lean::inc(x_34);
lean::dec(x_21);
x_37 = lean::cnstr_get(x_1, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
x_41 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_39, x_1, x_34);
lean::dec(x_39);
x_43 = lean::cnstr_get(x_41, 0);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_1);
lean::dec(x_37);
x_47 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_49 = x_41;
} else {
 lean::inc(x_47);
 lean::dec(x_41);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_52 = x_43;
} else {
 lean::inc(x_50);
 lean::dec(x_43);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
if (lean::is_scalar(x_49)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_49;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_47);
return x_54;
}
else
{
obj* x_56; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_43);
x_56 = lean::cnstr_get(x_41, 1);
lean::inc(x_56);
lean::dec(x_41);
x_59 = l_lean_ir_cpp_emit__initialize__proc___closed__2;
x_60 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_59, x_1, x_56);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
if (lean::obj_tag(x_61) == 0)
{
obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_1);
lean::dec(x_37);
x_65 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_67 = x_60;
} else {
 lean::inc(x_65);
 lean::dec(x_60);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_70 = x_61;
} else {
 lean::inc(x_68);
 lean::dec(x_61);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_68);
if (lean::is_scalar(x_67)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_67;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_65);
return x_72;
}
else
{
obj* x_74; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_61);
x_74 = lean::cnstr_get(x_60, 1);
lean::inc(x_74);
lean::dec(x_60);
x_77 = l_lean_ir_cpp_emit__initialize__proc___closed__3;
x_78 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_77, x_1, x_74);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
if (lean::obj_tag(x_79) == 0)
{
obj* x_83; obj* x_85; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_1);
lean::dec(x_37);
x_83 = lean::cnstr_get(x_78, 1);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 x_85 = x_78;
} else {
 lean::inc(x_83);
 lean::dec(x_78);
 x_85 = lean::box(0);
}
x_86 = lean::cnstr_get(x_79, 0);
if (lean::is_exclusive(x_79)) {
 x_88 = x_79;
} else {
 lean::inc(x_86);
 lean::dec(x_79);
 x_88 = lean::box(0);
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_86);
if (lean::is_scalar(x_85)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_85;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_83);
return x_90;
}
else
{
obj* x_92; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_79);
x_92 = lean::cnstr_get(x_78, 1);
lean::inc(x_92);
lean::dec(x_78);
x_95 = l_lean_ir_cpp_emit__initialize__proc___closed__4;
x_96 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_95, x_1, x_92);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
if (lean::obj_tag(x_97) == 0)
{
obj* x_101; obj* x_103; obj* x_104; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_1);
lean::dec(x_37);
x_101 = lean::cnstr_get(x_96, 1);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_103 = x_96;
} else {
 lean::inc(x_101);
 lean::dec(x_96);
 x_103 = lean::box(0);
}
x_104 = lean::cnstr_get(x_97, 0);
if (lean::is_exclusive(x_97)) {
 x_106 = x_97;
} else {
 lean::inc(x_104);
 lean::dec(x_97);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_104);
if (lean::is_scalar(x_103)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_103;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_101);
return x_108;
}
else
{
obj* x_110; obj* x_113; obj* x_116; obj* x_118; 
lean::dec(x_97);
x_110 = lean::cnstr_get(x_96, 1);
lean::inc(x_110);
lean::dec(x_96);
x_113 = lean::cnstr_get(x_37, 1);
lean::inc(x_113);
lean::dec(x_37);
x_116 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1(x_113, x_1, x_110);
lean::dec(x_113);
x_118 = lean::cnstr_get(x_116, 0);
lean::inc(x_118);
if (lean::obj_tag(x_118) == 0)
{
obj* x_121; obj* x_123; obj* x_124; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_1);
x_121 = lean::cnstr_get(x_116, 1);
if (lean::is_exclusive(x_116)) {
 lean::cnstr_release(x_116, 0);
 x_123 = x_116;
} else {
 lean::inc(x_121);
 lean::dec(x_116);
 x_123 = lean::box(0);
}
x_124 = lean::cnstr_get(x_118, 0);
if (lean::is_exclusive(x_118)) {
 x_126 = x_118;
} else {
 lean::inc(x_124);
 lean::dec(x_118);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_124);
if (lean::is_scalar(x_123)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_123;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_121);
return x_128;
}
else
{
obj* x_130; obj* x_134; obj* x_135; 
lean::dec(x_118);
x_130 = lean::cnstr_get(x_116, 1);
lean::inc(x_130);
lean::dec(x_116);
lean::inc(x_1);
x_134 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__2(x_0, x_1, x_130);
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
if (lean::obj_tag(x_135) == 0)
{
obj* x_138; obj* x_140; obj* x_141; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_1);
x_138 = lean::cnstr_get(x_134, 1);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 x_140 = x_134;
} else {
 lean::inc(x_138);
 lean::dec(x_134);
 x_140 = lean::box(0);
}
x_141 = lean::cnstr_get(x_135, 0);
if (lean::is_exclusive(x_135)) {
 x_143 = x_135;
} else {
 lean::inc(x_141);
 lean::dec(x_135);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_141);
if (lean::is_scalar(x_140)) {
 x_145 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_145 = x_140;
}
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_138);
return x_145;
}
else
{
obj* x_147; obj* x_150; obj* x_151; 
lean::dec(x_135);
x_147 = lean::cnstr_get(x_134, 1);
lean::inc(x_147);
lean::dec(x_134);
x_150 = l_lean_ir_cpp_emit__uncurry___closed__1;
x_151 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_150, x_1, x_147);
lean::dec(x_1);
return x_151;
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
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_ir_cpp_emit__initialize__proc___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_emit__initialize__proc(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_match__type___closed__5;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_0, 0);
x_6 = lean::cnstr_get(x_0, 1);
x_7 = l_lean_ir_cpp_finalize__prefix;
x_8 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_7, x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_13 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_16 = x_9;
} else {
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
if (lean::is_scalar(x_13)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_13;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_11);
return x_18;
}
else
{
obj* x_20; obj* x_23; obj* x_24; 
lean::dec(x_9);
x_20 = lean::cnstr_get(x_8, 1);
lean::inc(x_20);
lean::dec(x_8);
x_23 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_5, x_1, x_20);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
x_26 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_28 = x_23;
} else {
 lean::inc(x_26);
 lean::dec(x_23);
 x_28 = lean::box(0);
}
x_29 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_31 = x_24;
} else {
 lean::inc(x_29);
 lean::dec(x_24);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_28)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_28;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_26);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_24);
x_35 = lean::cnstr_get(x_23, 1);
lean::inc(x_35);
lean::dec(x_23);
x_38 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_38, x_1, x_35);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
x_42 = lean::cnstr_get(x_39, 1);
if (lean::is_exclusive(x_39)) {
 lean::cnstr_release(x_39, 0);
 x_44 = x_39;
} else {
 lean::inc(x_42);
 lean::dec(x_39);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_47 = x_40;
} else {
 lean::inc(x_45);
 lean::dec(x_40);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
if (lean::is_scalar(x_44)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_44;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_42);
return x_49;
}
else
{
obj* x_51; 
lean::dec(x_40);
x_51 = lean::cnstr_get(x_39, 1);
lean::inc(x_51);
lean::dec(x_39);
x_0 = x_6;
x_2 = x_51;
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
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; uint8 x_14; 
x_6 = lean::cnstr_get(x_0, 0);
x_7 = lean::cnstr_get(x_0, 1);
x_11 = l_lean_ir_decl_header___main(x_6);
x_14 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*3);
if (x_14 == 0)
{
if (x_14 == 0)
{
obj* x_16; 
lean::dec(x_11);
x_16 = l_lean_ir_match__type___closed__5;
x_8 = x_16;
x_9 = x_2;
goto lbl_10;
}
else
{
obj* x_17; 
x_17 = lean::box(0);
x_12 = x_17;
goto lbl_13;
}
}
else
{
obj* x_18; uint8 x_20; obj* x_21; obj* x_22; uint8 x_23; 
x_18 = lean::cnstr_get(x_11, 2);
lean::inc(x_18);
x_20 = lean::unbox(x_18);
x_21 = l_lean_ir_type2id___main(x_20);
x_22 = l_lean_ir_valid__assign__unop__types___closed__1;
x_23 = lean::nat_dec_eq(x_21, x_22);
lean::dec(x_21);
if (x_23 == 0)
{
obj* x_26; 
lean::dec(x_11);
x_26 = l_lean_ir_match__type___closed__5;
x_8 = x_26;
x_9 = x_2;
goto lbl_10;
}
else
{
if (x_14 == 0)
{
obj* x_28; 
lean::dec(x_11);
x_28 = l_lean_ir_match__type___closed__5;
x_8 = x_28;
x_9 = x_2;
goto lbl_10;
}
else
{
obj* x_29; 
x_29 = lean::box(0);
x_12 = x_29;
goto lbl_13;
}
}
}
lbl_10:
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
x_31 = lean::cnstr_get(x_8, 0);
if (lean::is_exclusive(x_8)) {
 x_33 = x_8;
} else {
 lean::inc(x_31);
 lean::dec(x_8);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_31);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_9);
return x_35;
}
else
{
lean::dec(x_8);
x_0 = x_7;
x_2 = x_9;
goto _start;
}
}
lbl_13:
{
obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_12);
x_39 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__1;
x_40 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_39, x_1, x_2);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_44; obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_11);
x_44 = lean::cnstr_get(x_40, 1);
lean::inc(x_44);
lean::dec(x_40);
x_47 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_49 = x_41;
} else {
 lean::inc(x_47);
 lean::dec(x_41);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_47);
x_8 = x_50;
x_9 = x_44;
goto lbl_10;
}
else
{
obj* x_52; obj* x_55; obj* x_60; obj* x_61; 
lean::dec(x_41);
x_52 = lean::cnstr_get(x_40, 1);
lean::inc(x_52);
lean::dec(x_40);
x_55 = lean::cnstr_get(x_11, 0);
lean::inc(x_55);
lean::dec(x_11);
lean::inc(x_1);
lean::inc(x_55);
x_60 = l_lean_ir_cpp_emit__global(x_55, x_1, x_52);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
if (lean::obj_tag(x_61) == 0)
{
obj* x_64; obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_55);
x_64 = lean::cnstr_get(x_60, 1);
lean::inc(x_64);
lean::dec(x_60);
x_67 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_69 = x_61;
} else {
 lean::inc(x_67);
 lean::dec(x_61);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_67);
x_8 = x_70;
x_9 = x_64;
goto lbl_10;
}
else
{
obj* x_72; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_61);
x_72 = lean::cnstr_get(x_60, 1);
lean::inc(x_72);
lean::dec(x_60);
x_75 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__2;
x_76 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_75, x_1, x_72);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
if (lean::obj_tag(x_77) == 0)
{
obj* x_80; obj* x_83; obj* x_85; obj* x_86; 
lean::dec(x_55);
x_80 = lean::cnstr_get(x_76, 1);
lean::inc(x_80);
lean::dec(x_76);
x_83 = lean::cnstr_get(x_77, 0);
if (lean::is_exclusive(x_77)) {
 x_85 = x_77;
} else {
 lean::inc(x_83);
 lean::dec(x_77);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_83);
x_8 = x_86;
x_9 = x_80;
goto lbl_10;
}
else
{
obj* x_88; obj* x_92; obj* x_93; 
lean::dec(x_77);
x_88 = lean::cnstr_get(x_76, 1);
lean::inc(x_88);
lean::dec(x_76);
lean::inc(x_1);
x_92 = l_lean_ir_cpp_emit__global(x_55, x_1, x_88);
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
if (lean::obj_tag(x_93) == 0)
{
obj* x_95; obj* x_98; obj* x_100; obj* x_101; 
x_95 = lean::cnstr_get(x_92, 1);
lean::inc(x_95);
lean::dec(x_92);
x_98 = lean::cnstr_get(x_93, 0);
if (lean::is_exclusive(x_93)) {
 x_100 = x_93;
} else {
 lean::inc(x_98);
 lean::dec(x_93);
 x_100 = lean::box(0);
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
x_8 = x_101;
x_9 = x_95;
goto lbl_10;
}
else
{
obj* x_103; obj* x_106; obj* x_107; obj* x_108; obj* x_110; 
lean::dec(x_93);
x_103 = lean::cnstr_get(x_92, 1);
lean::inc(x_103);
lean::dec(x_92);
x_106 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__3;
x_107 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_106, x_1, x_103);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_107, 1);
lean::inc(x_110);
lean::dec(x_107);
x_8 = x_108;
x_9 = x_110;
goto lbl_10;
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
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_ir_cpp_emit__initialize__proc___closed__1;
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_10 = x_4;
} else {
 lean::inc(x_8);
 lean::dec(x_4);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_13 = x_5;
} else {
 lean::inc(x_11);
 lean::dec(x_5);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_11);
if (lean::is_scalar(x_10)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_10;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_8);
return x_15;
}
else
{
obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_5);
x_17 = lean::cnstr_get(x_4, 1);
lean::inc(x_17);
lean::dec(x_4);
x_20 = l_lean_ir_cpp_finalize__prefix;
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_20, x_1, x_17);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_1);
x_25 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_27 = x_21;
} else {
 lean::inc(x_25);
 lean::dec(x_21);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 x_30 = x_22;
} else {
 lean::inc(x_28);
 lean::dec(x_22);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
if (lean::is_scalar(x_27)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_27;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_25);
return x_32;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_41; obj* x_43; 
lean::dec(x_22);
x_34 = lean::cnstr_get(x_21, 1);
lean::inc(x_34);
lean::dec(x_21);
x_37 = lean::cnstr_get(x_1, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_37, 0);
lean::inc(x_39);
x_41 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_39, x_1, x_34);
lean::dec(x_39);
x_43 = lean::cnstr_get(x_41, 0);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_1);
lean::dec(x_37);
x_47 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_49 = x_41;
} else {
 lean::inc(x_47);
 lean::dec(x_41);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_52 = x_43;
} else {
 lean::inc(x_50);
 lean::dec(x_43);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
if (lean::is_scalar(x_49)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_49;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_47);
return x_54;
}
else
{
obj* x_56; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_43);
x_56 = lean::cnstr_get(x_41, 1);
lean::inc(x_56);
lean::dec(x_41);
x_59 = l_lean_ir_cpp_emit__initialize__proc___closed__2;
x_60 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_59, x_1, x_56);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
if (lean::obj_tag(x_61) == 0)
{
obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_1);
lean::dec(x_37);
x_65 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_67 = x_60;
} else {
 lean::inc(x_65);
 lean::dec(x_60);
 x_67 = lean::box(0);
}
x_68 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_70 = x_61;
} else {
 lean::inc(x_68);
 lean::dec(x_61);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_68);
if (lean::is_scalar(x_67)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_67;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_65);
return x_72;
}
else
{
obj* x_74; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_61);
x_74 = lean::cnstr_get(x_60, 1);
lean::inc(x_74);
lean::dec(x_60);
x_77 = l_lean_ir_cpp_emit__finalize__proc___closed__1;
x_78 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_77, x_1, x_74);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
if (lean::obj_tag(x_79) == 0)
{
obj* x_83; obj* x_85; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_1);
lean::dec(x_37);
x_83 = lean::cnstr_get(x_78, 1);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 x_85 = x_78;
} else {
 lean::inc(x_83);
 lean::dec(x_78);
 x_85 = lean::box(0);
}
x_86 = lean::cnstr_get(x_79, 0);
if (lean::is_exclusive(x_79)) {
 x_88 = x_79;
} else {
 lean::inc(x_86);
 lean::dec(x_79);
 x_88 = lean::box(0);
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_86);
if (lean::is_scalar(x_85)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_85;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_83);
return x_90;
}
else
{
obj* x_92; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_79);
x_92 = lean::cnstr_get(x_78, 1);
lean::inc(x_92);
lean::dec(x_78);
x_95 = l_lean_ir_cpp_emit__finalize__proc___closed__2;
x_96 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_95, x_1, x_92);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
if (lean::obj_tag(x_97) == 0)
{
obj* x_101; obj* x_103; obj* x_104; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_1);
lean::dec(x_37);
x_101 = lean::cnstr_get(x_96, 1);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_103 = x_96;
} else {
 lean::inc(x_101);
 lean::dec(x_96);
 x_103 = lean::box(0);
}
x_104 = lean::cnstr_get(x_97, 0);
if (lean::is_exclusive(x_97)) {
 x_106 = x_97;
} else {
 lean::inc(x_104);
 lean::dec(x_97);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_104);
if (lean::is_scalar(x_103)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_103;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_101);
return x_108;
}
else
{
obj* x_110; obj* x_113; obj* x_116; obj* x_118; 
lean::dec(x_97);
x_110 = lean::cnstr_get(x_96, 1);
lean::inc(x_110);
lean::dec(x_96);
x_113 = lean::cnstr_get(x_37, 1);
lean::inc(x_113);
lean::dec(x_37);
x_116 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__1(x_113, x_1, x_110);
lean::dec(x_113);
x_118 = lean::cnstr_get(x_116, 0);
lean::inc(x_118);
if (lean::obj_tag(x_118) == 0)
{
obj* x_121; obj* x_123; obj* x_124; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_1);
x_121 = lean::cnstr_get(x_116, 1);
if (lean::is_exclusive(x_116)) {
 lean::cnstr_release(x_116, 0);
 x_123 = x_116;
} else {
 lean::inc(x_121);
 lean::dec(x_116);
 x_123 = lean::box(0);
}
x_124 = lean::cnstr_get(x_118, 0);
if (lean::is_exclusive(x_118)) {
 x_126 = x_118;
} else {
 lean::inc(x_124);
 lean::dec(x_118);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_124);
if (lean::is_scalar(x_123)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_123;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_121);
return x_128;
}
else
{
obj* x_130; obj* x_134; obj* x_135; 
lean::dec(x_118);
x_130 = lean::cnstr_get(x_116, 1);
lean::inc(x_130);
lean::dec(x_116);
lean::inc(x_1);
x_134 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2(x_0, x_1, x_130);
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
if (lean::obj_tag(x_135) == 0)
{
obj* x_138; obj* x_140; obj* x_141; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_1);
x_138 = lean::cnstr_get(x_134, 1);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 x_140 = x_134;
} else {
 lean::inc(x_138);
 lean::dec(x_134);
 x_140 = lean::box(0);
}
x_141 = lean::cnstr_get(x_135, 0);
if (lean::is_exclusive(x_135)) {
 x_143 = x_135;
} else {
 lean::inc(x_141);
 lean::dec(x_135);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_141);
if (lean::is_scalar(x_140)) {
 x_145 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_145 = x_140;
}
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_138);
return x_145;
}
else
{
obj* x_147; obj* x_150; obj* x_151; 
lean::dec(x_135);
x_147 = lean::cnstr_get(x_134, 1);
lean::inc(x_147);
lean::dec(x_134);
x_150 = l_lean_ir_cpp_emit__uncurry___closed__1;
x_151 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_150, x_1, x_147);
lean::dec(x_1);
return x_151;
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
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_ir_cpp_emit__finalize__proc___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_emit__finalize__proc(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
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
obj* x_8; obj* x_9; 
lean::dec(x_0);
lean::dec(x_2);
x_8 = l_lean_ir_match__type___closed__5;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_1);
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_16; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
lean::dec(x_4);
x_13 = lean::cnstr_get(x_2, 3);
lean::inc(x_13);
lean::inc(x_10);
x_16 = lean::apply_1(x_13, x_10);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
lean::dec(x_2);
x_19 = l_lean_ir_id_to__string___main(x_10);
x_20 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
x_21 = 0;
x_22 = l_lean_ir_cpp_emit__main__proc___closed__1;
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_21);
x_24 = x_23;
x_25 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_21);
x_27 = x_26;
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_1);
return x_29;
}
else
{
obj* x_30; obj* x_33; obj* x_35; obj* x_37; obj* x_38; uint8 x_40; obj* x_42; uint8 x_45; obj* x_46; obj* x_47; uint8 x_48; obj* x_50; uint8 x_53; 
x_30 = lean::cnstr_get(x_16, 0);
lean::inc(x_30);
lean::dec(x_16);
x_33 = l_lean_ir_decl_header___main(x_30);
lean::dec(x_30);
x_35 = lean::cnstr_get(x_33, 1);
lean::inc(x_35);
x_37 = lean::mk_nat_obj(0u);
x_38 = l_list_length__aux___main___rarg(x_35, x_37);
lean::dec(x_35);
x_40 = lean::nat_dec_eq(x_38, x_37);
lean::dec(x_38);
x_42 = lean::cnstr_get(x_33, 2);
lean::inc(x_42);
lean::dec(x_33);
x_45 = lean::unbox(x_42);
x_46 = l_lean_ir_type2id___main(x_45);
x_47 = l_lean_ir_valid__assign__unop__types___closed__4;
x_48 = lean::nat_dec_eq(x_46, x_47);
lean::dec(x_46);
x_50 = lean::cnstr_get(x_2, 0);
lean::inc(x_50);
lean::dec(x_2);
if (x_48 == 0)
{
uint8 x_55; 
x_55 = 0;
x_53 = x_55;
goto lbl_54;
}
else
{
uint8 x_56; 
x_56 = 1;
x_53 = x_56;
goto lbl_54;
}
lbl_54:
{
obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_63; obj* x_64; 
if (x_40 == 0)
{
obj* x_67; obj* x_68; uint8 x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::inc(x_10);
x_67 = l_lean_ir_id_to__string___main(x_10);
x_68 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_68, 0, x_67);
x_69 = 0;
x_70 = l_lean_ir_cpp_emit__main__proc___closed__5;
x_71 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_68);
lean::cnstr_set_scalar(x_71, sizeof(void*)*2, x_69);
x_72 = x_71;
x_73 = l_lean_ir_cpp_emit__main__proc___closed__6;
x_74 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_73);
lean::cnstr_set_scalar(x_74, sizeof(void*)*2, x_69);
x_75 = x_74;
x_76 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
x_63 = x_76;
x_64 = x_1;
goto lbl_65;
}
else
{
if (x_53 == 0)
{
obj* x_78; obj* x_79; uint8 x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
lean::inc(x_10);
x_78 = l_lean_ir_id_to__string___main(x_10);
x_79 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_79, 0, x_78);
x_80 = 0;
x_81 = l_lean_ir_cpp_emit__main__proc___closed__5;
x_82 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_79);
lean::cnstr_set_scalar(x_82, sizeof(void*)*2, x_80);
x_83 = x_82;
x_84 = l_lean_ir_cpp_emit__main__proc___closed__7;
x_85 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_85, 0, x_83);
lean::cnstr_set(x_85, 1, x_84);
lean::cnstr_set_scalar(x_85, sizeof(void*)*2, x_80);
x_86 = x_85;
x_87 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
x_63 = x_87;
x_64 = x_1;
goto lbl_65;
}
else
{
obj* x_88; 
x_88 = l_lean_ir_match__type___closed__5;
x_63 = x_88;
x_64 = x_1;
goto lbl_65;
}
}
lbl_59:
{
if (lean::obj_tag(x_57) == 0)
{
obj* x_91; obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_0);
lean::dec(x_50);
x_91 = lean::cnstr_get(x_57, 0);
if (lean::is_exclusive(x_57)) {
 x_93 = x_57;
} else {
 lean::inc(x_91);
 lean::dec(x_57);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_91);
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_58);
return x_95;
}
else
{
obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_57);
x_97 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
x_98 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_97, x_0, x_58);
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
if (lean::obj_tag(x_99) == 0)
{
obj* x_103; obj* x_105; obj* x_106; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_0);
lean::dec(x_50);
x_103 = lean::cnstr_get(x_98, 1);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 x_105 = x_98;
} else {
 lean::inc(x_103);
 lean::dec(x_98);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_99, 0);
if (lean::is_exclusive(x_99)) {
 x_108 = x_99;
} else {
 lean::inc(x_106);
 lean::dec(x_99);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_106);
if (lean::is_scalar(x_105)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_105;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_103);
return x_110;
}
else
{
obj* x_112; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_99);
x_112 = lean::cnstr_get(x_98, 1);
lean::inc(x_112);
lean::dec(x_98);
x_115 = l_lean_ir_cpp_finalize__prefix;
x_116 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_115, x_0, x_112);
x_117 = lean::cnstr_get(x_116, 0);
lean::inc(x_117);
if (lean::obj_tag(x_117) == 0)
{
obj* x_121; obj* x_123; obj* x_124; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_0);
lean::dec(x_50);
x_121 = lean::cnstr_get(x_116, 1);
if (lean::is_exclusive(x_116)) {
 lean::cnstr_release(x_116, 0);
 x_123 = x_116;
} else {
 lean::inc(x_121);
 lean::dec(x_116);
 x_123 = lean::box(0);
}
x_124 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_126 = x_117;
} else {
 lean::inc(x_124);
 lean::dec(x_117);
 x_126 = lean::box(0);
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_124);
if (lean::is_scalar(x_123)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_123;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_121);
return x_128;
}
else
{
obj* x_130; obj* x_133; obj* x_135; 
lean::dec(x_117);
x_130 = lean::cnstr_get(x_116, 1);
lean::inc(x_130);
lean::dec(x_116);
x_133 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_50, x_0, x_130);
lean::dec(x_50);
x_135 = lean::cnstr_get(x_133, 0);
lean::inc(x_135);
if (lean::obj_tag(x_135) == 0)
{
obj* x_138; obj* x_140; obj* x_141; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_0);
x_138 = lean::cnstr_get(x_133, 1);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 x_140 = x_133;
} else {
 lean::inc(x_138);
 lean::dec(x_133);
 x_140 = lean::box(0);
}
x_141 = lean::cnstr_get(x_135, 0);
if (lean::is_exclusive(x_135)) {
 x_143 = x_135;
} else {
 lean::inc(x_141);
 lean::dec(x_135);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_141);
if (lean::is_scalar(x_140)) {
 x_145 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_145 = x_140;
}
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_138);
return x_145;
}
else
{
obj* x_147; obj* x_150; obj* x_151; 
lean::dec(x_135);
x_147 = lean::cnstr_get(x_133, 1);
lean::inc(x_147);
lean::dec(x_133);
x_150 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_97, x_0, x_147);
x_151 = lean::cnstr_get(x_150, 0);
lean::inc(x_151);
if (lean::obj_tag(x_151) == 0)
{
obj* x_154; obj* x_156; obj* x_157; obj* x_159; obj* x_160; obj* x_161; 
lean::dec(x_0);
x_154 = lean::cnstr_get(x_150, 1);
if (lean::is_exclusive(x_150)) {
 lean::cnstr_release(x_150, 0);
 x_156 = x_150;
} else {
 lean::inc(x_154);
 lean::dec(x_150);
 x_156 = lean::box(0);
}
x_157 = lean::cnstr_get(x_151, 0);
if (lean::is_exclusive(x_151)) {
 x_159 = x_151;
} else {
 lean::inc(x_157);
 lean::dec(x_151);
 x_159 = lean::box(0);
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_157);
if (lean::is_scalar(x_156)) {
 x_161 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_161 = x_156;
}
lean::cnstr_set(x_161, 0, x_160);
lean::cnstr_set(x_161, 1, x_154);
return x_161;
}
else
{
obj* x_163; obj* x_166; obj* x_167; 
lean::dec(x_151);
x_163 = lean::cnstr_get(x_150, 1);
lean::inc(x_163);
lean::dec(x_150);
x_166 = l_lean_ir_cpp_emit__main__proc___closed__2;
x_167 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_166, x_0, x_163);
lean::dec(x_0);
return x_167;
}
}
}
}
}
}
lbl_62:
{
if (lean::obj_tag(x_60) == 0)
{
obj* x_170; obj* x_172; obj* x_173; 
lean::dec(x_10);
x_170 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_172 = x_60;
} else {
 lean::inc(x_170);
 lean::dec(x_60);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_170);
x_57 = x_173;
x_58 = x_61;
goto lbl_59;
}
else
{
obj* x_175; obj* x_176; 
lean::dec(x_60);
x_175 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_50, x_0, x_61);
x_176 = lean::cnstr_get(x_175, 0);
lean::inc(x_176);
if (lean::obj_tag(x_176) == 0)
{
obj* x_179; obj* x_182; obj* x_184; obj* x_185; 
lean::dec(x_10);
x_179 = lean::cnstr_get(x_175, 1);
lean::inc(x_179);
lean::dec(x_175);
x_182 = lean::cnstr_get(x_176, 0);
if (lean::is_exclusive(x_176)) {
 x_184 = x_176;
} else {
 lean::inc(x_182);
 lean::dec(x_176);
 x_184 = lean::box(0);
}
if (lean::is_scalar(x_184)) {
 x_185 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_185 = x_184;
}
lean::cnstr_set(x_185, 0, x_182);
x_57 = x_185;
x_58 = x_179;
goto lbl_59;
}
else
{
obj* x_187; obj* x_190; obj* x_191; obj* x_192; 
lean::dec(x_176);
x_187 = lean::cnstr_get(x_175, 1);
lean::inc(x_187);
lean::dec(x_175);
x_190 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
x_191 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_190, x_0, x_187);
x_192 = lean::cnstr_get(x_191, 0);
lean::inc(x_192);
if (lean::obj_tag(x_192) == 0)
{
obj* x_195; obj* x_198; obj* x_200; obj* x_201; 
lean::dec(x_10);
x_195 = lean::cnstr_get(x_191, 1);
lean::inc(x_195);
lean::dec(x_191);
x_198 = lean::cnstr_get(x_192, 0);
if (lean::is_exclusive(x_192)) {
 x_200 = x_192;
} else {
 lean::inc(x_198);
 lean::dec(x_192);
 x_200 = lean::box(0);
}
if (lean::is_scalar(x_200)) {
 x_201 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_201 = x_200;
}
lean::cnstr_set(x_201, 0, x_198);
x_57 = x_201;
x_58 = x_195;
goto lbl_59;
}
else
{
obj* x_203; obj* x_206; obj* x_207; obj* x_208; 
lean::dec(x_192);
x_203 = lean::cnstr_get(x_191, 1);
lean::inc(x_203);
lean::dec(x_191);
x_206 = l_lean_ir_cpp_emit__main__proc___closed__3;
x_207 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_206, x_0, x_203);
x_208 = lean::cnstr_get(x_207, 0);
lean::inc(x_208);
if (lean::obj_tag(x_208) == 0)
{
obj* x_211; obj* x_214; obj* x_216; obj* x_217; 
lean::dec(x_10);
x_211 = lean::cnstr_get(x_207, 1);
lean::inc(x_211);
lean::dec(x_207);
x_214 = lean::cnstr_get(x_208, 0);
if (lean::is_exclusive(x_208)) {
 x_216 = x_208;
} else {
 lean::inc(x_214);
 lean::dec(x_208);
 x_216 = lean::box(0);
}
if (lean::is_scalar(x_216)) {
 x_217 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_217 = x_216;
}
lean::cnstr_set(x_217, 0, x_214);
x_57 = x_217;
x_58 = x_211;
goto lbl_59;
}
else
{
obj* x_219; obj* x_223; obj* x_224; obj* x_226; 
lean::dec(x_208);
x_219 = lean::cnstr_get(x_207, 1);
lean::inc(x_219);
lean::dec(x_207);
lean::inc(x_0);
x_223 = l_lean_ir_cpp_emit__fnid(x_10, x_0, x_219);
x_224 = lean::cnstr_get(x_223, 0);
lean::inc(x_224);
x_226 = lean::cnstr_get(x_223, 1);
lean::inc(x_226);
lean::dec(x_223);
x_57 = x_224;
x_58 = x_226;
goto lbl_59;
}
}
}
}
}
lbl_65:
{
if (lean::obj_tag(x_63) == 0)
{
obj* x_229; obj* x_231; obj* x_232; 
x_229 = lean::cnstr_get(x_63, 0);
if (lean::is_exclusive(x_63)) {
 x_231 = x_63;
} else {
 lean::inc(x_229);
 lean::dec(x_63);
 x_231 = lean::box(0);
}
if (lean::is_scalar(x_231)) {
 x_232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_232 = x_231;
}
lean::cnstr_set(x_232, 0, x_229);
x_60 = x_232;
x_61 = x_64;
goto lbl_62;
}
else
{
obj* x_234; obj* x_235; obj* x_236; 
lean::dec(x_63);
x_234 = l_lean_ir_cpp_emit__main__proc___closed__4;
x_235 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_234, x_0, x_64);
x_236 = lean::cnstr_get(x_235, 0);
lean::inc(x_236);
if (lean::obj_tag(x_236) == 0)
{
obj* x_238; obj* x_241; obj* x_243; obj* x_244; 
x_238 = lean::cnstr_get(x_235, 1);
lean::inc(x_238);
lean::dec(x_235);
x_241 = lean::cnstr_get(x_236, 0);
if (lean::is_exclusive(x_236)) {
 x_243 = x_236;
} else {
 lean::inc(x_241);
 lean::dec(x_236);
 x_243 = lean::box(0);
}
if (lean::is_scalar(x_243)) {
 x_244 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_244 = x_243;
}
lean::cnstr_set(x_244, 0, x_241);
x_60 = x_244;
x_61 = x_238;
goto lbl_62;
}
else
{
obj* x_246; obj* x_249; obj* x_250; obj* x_251; obj* x_253; 
lean::dec(x_236);
x_246 = lean::cnstr_get(x_235, 1);
lean::inc(x_246);
lean::dec(x_235);
x_249 = l_lean_ir_cpp_initialize__prefix;
x_250 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_249, x_0, x_246);
x_251 = lean::cnstr_get(x_250, 0);
lean::inc(x_251);
x_253 = lean::cnstr_get(x_250, 1);
lean::inc(x_253);
lean::dec(x_250);
x_60 = x_251;
x_61 = x_253;
goto lbl_62;
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
obj* x_4; obj* x_5; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_cpp_emit__def(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::inc(x_17);
 lean::dec(x_12);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get(x_13, 0);
if (lean::is_exclusive(x_13)) {
 x_22 = x_13;
} else {
 lean::inc(x_20);
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_13);
x_26 = lean::cnstr_get(x_12, 1);
lean::inc(x_26);
lean::dec(x_12);
x_0 = x_8;
x_2 = x_26;
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_15; obj* x_16; 
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
x_4 = l_lean_ir_cpp_file__header(x_2);
lean::dec(x_2);
x_6 = l_lean_format_be___main___closed__1;
x_7 = lean::string_append(x_4, x_6);
x_8 = l_lean_ir_mk__context;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
lean::inc(x_0);
x_15 = l_lean_ir_cpp_emit__used__headers(x_0, x_9, x_7);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_18; obj* x_21; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
x_21 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_23 = x_16;
} else {
 lean::inc(x_21);
 lean::dec(x_16);
 x_23 = lean::box(0);
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
obj* x_26; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_16);
x_26 = lean::cnstr_get(x_15, 1);
lean::inc(x_26);
lean::dec(x_15);
x_29 = l_lean_ir_extract__cpp___closed__1;
x_30 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_29, x_9, x_26);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; obj* x_36; obj* x_38; obj* x_39; 
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
x_36 = lean::cnstr_get(x_31, 0);
if (lean::is_exclusive(x_31)) {
 x_38 = x_31;
} else {
 lean::inc(x_36);
 lean::dec(x_31);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
x_10 = x_39;
x_11 = x_33;
goto lbl_12;
}
else
{
obj* x_41; obj* x_44; obj* x_45; obj* x_46; obj* x_48; 
lean::dec(x_31);
x_41 = lean::cnstr_get(x_30, 1);
lean::inc(x_41);
lean::dec(x_30);
x_44 = l_lean_ir_extract__cpp___closed__2;
x_45 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_44, x_9, x_41);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
x_10 = x_46;
x_11 = x_48;
goto lbl_12;
}
}
lbl_12:
{
if (lean::obj_tag(x_10) == 0)
{
obj* x_54; obj* x_56; obj* x_57; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_11);
x_54 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_56 = x_10;
} else {
 lean::inc(x_54);
 lean::dec(x_10);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_54);
return x_57;
}
else
{
obj* x_60; obj* x_61; 
lean::dec(x_10);
lean::inc(x_9);
x_60 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__global__var__decls___spec__1(x_0, x_9, x_11);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
if (lean::obj_tag(x_61) == 0)
{
obj* x_66; obj* x_68; obj* x_69; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_60);
x_66 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_68 = x_61;
} else {
 lean::inc(x_66);
 lean::dec(x_61);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_66);
return x_69;
}
else
{
obj* x_71; obj* x_75; obj* x_76; 
lean::dec(x_61);
x_71 = lean::cnstr_get(x_60, 1);
lean::inc(x_71);
lean::dec(x_60);
lean::inc(x_9);
x_75 = l_lean_ir_cpp_emit__initialize__proc(x_0, x_9, x_71);
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
if (lean::obj_tag(x_76) == 0)
{
obj* x_81; obj* x_83; obj* x_84; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_75);
x_81 = lean::cnstr_get(x_76, 0);
if (lean::is_exclusive(x_76)) {
 x_83 = x_76;
} else {
 lean::inc(x_81);
 lean::dec(x_76);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_81);
return x_84;
}
else
{
obj* x_86; obj* x_90; obj* x_91; 
lean::dec(x_76);
x_86 = lean::cnstr_get(x_75, 1);
lean::inc(x_86);
lean::dec(x_75);
lean::inc(x_9);
x_90 = l_lean_ir_cpp_emit__finalize__proc(x_0, x_9, x_86);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
if (lean::obj_tag(x_91) == 0)
{
obj* x_96; obj* x_98; obj* x_99; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_90);
x_96 = lean::cnstr_get(x_91, 0);
if (lean::is_exclusive(x_91)) {
 x_98 = x_91;
} else {
 lean::inc(x_96);
 lean::dec(x_91);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
return x_99;
}
else
{
obj* x_101; obj* x_105; obj* x_106; 
lean::dec(x_91);
x_101 = lean::cnstr_get(x_90, 1);
lean::inc(x_101);
lean::dec(x_90);
lean::inc(x_9);
x_105 = l_list_mmap_x_27___main___at_lean_ir_extract__cpp___spec__1(x_0, x_9, x_101);
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
if (lean::obj_tag(x_106) == 0)
{
obj* x_110; obj* x_112; obj* x_113; 
lean::dec(x_9);
lean::dec(x_105);
x_110 = lean::cnstr_get(x_106, 0);
if (lean::is_exclusive(x_106)) {
 x_112 = x_106;
} else {
 lean::inc(x_110);
 lean::dec(x_106);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_110);
return x_113;
}
else
{
obj* x_115; obj* x_118; obj* x_119; 
lean::dec(x_106);
x_115 = lean::cnstr_get(x_105, 1);
lean::inc(x_115);
lean::dec(x_105);
x_118 = l_lean_ir_cpp_emit__main__proc(x_9, x_115);
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
if (lean::obj_tag(x_119) == 0)
{
obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_118);
x_122 = lean::cnstr_get(x_119, 0);
if (lean::is_exclusive(x_119)) {
 x_124 = x_119;
} else {
 lean::inc(x_122);
 lean::dec(x_119);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_122);
return x_125;
}
else
{
obj* x_126; obj* x_127; obj* x_130; 
if (lean::is_exclusive(x_119)) {
 lean::cnstr_release(x_119, 0);
 x_126 = x_119;
} else {
 lean::dec(x_119);
 x_126 = lean::box(0);
}
x_127 = lean::cnstr_get(x_118, 1);
lean::inc(x_127);
lean::dec(x_118);
if (lean::is_scalar(x_126)) {
 x_130 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_130 = x_126;
}
lean::cnstr_set(x_130, 0, x_127);
return x_130;
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
lean::mark_persistent(l_lean_ir_cpp_initialize__prefix);
 l_lean_ir_cpp_finalize__prefix = _init_l_lean_ir_cpp_finalize__prefix();
lean::mark_persistent(l_lean_ir_cpp_finalize__prefix);
 l_lean_ir_cpp_file__header___closed__1 = _init_l_lean_ir_cpp_file__header___closed__1();
lean::mark_persistent(l_lean_ir_cpp_file__header___closed__1);
 l_lean_ir_cpp_file__header___closed__2 = _init_l_lean_ir_cpp_file__header___closed__2();
lean::mark_persistent(l_lean_ir_cpp_file__header___closed__2);
 l_lean_ir_cpp_file__header___closed__3 = _init_l_lean_ir_cpp_file__header___closed__3();
lean::mark_persistent(l_lean_ir_cpp_file__header___closed__3);
 l_lean_ir_cpp_file__header___closed__4 = _init_l_lean_ir_cpp_file__header___closed__4();
lean::mark_persistent(l_lean_ir_cpp_file__header___closed__4);
 l_lean_ir_cpp_extract__m_monad = _init_l_lean_ir_cpp_extract__m_monad();
lean::mark_persistent(l_lean_ir_cpp_extract__m_monad);
 l_lean_ir_cpp_extract__m_monad__except = _init_l_lean_ir_cpp_extract__m_monad__except();
lean::mark_persistent(l_lean_ir_cpp_extract__m_monad__except);
 l_lean_ir_cpp_extract__m_monad__state = _init_l_lean_ir_cpp_extract__m_monad__state();
lean::mark_persistent(l_lean_ir_cpp_extract__m_monad__state);
 l_lean_ir_cpp_extract__m_monad__reader = _init_l_lean_ir_cpp_extract__m_monad__reader();
lean::mark_persistent(l_lean_ir_cpp_extract__m_monad__reader);
 l_lean_ir_cpp_extract__m_monad__run = _init_l_lean_ir_cpp_extract__m_monad__run();
lean::mark_persistent(l_lean_ir_cpp_extract__m_monad__run);
 l_lean_ir_cpp_extract__m = _init_l_lean_ir_cpp_extract__m();
lean::mark_persistent(l_lean_ir_cpp_extract__m);
 l_lean_ir_cpp_emit__blockid___closed__1 = _init_l_lean_ir_cpp_emit__blockid___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__blockid___closed__1);
 l_lean_ir_cpp_fid2cpp___closed__1 = _init_l_lean_ir_cpp_fid2cpp___closed__1();
lean::mark_persistent(l_lean_ir_cpp_fid2cpp___closed__1);
 l_lean_ir_cpp_is__const___closed__1 = _init_l_lean_ir_cpp_is__const___closed__1();
lean::mark_persistent(l_lean_ir_cpp_is__const___closed__1);
 l_lean_ir_cpp_global2cpp___closed__1 = _init_l_lean_ir_cpp_global2cpp___closed__1();
lean::mark_persistent(l_lean_ir_cpp_global2cpp___closed__1);
 l_lean_ir_cpp_type2cpp___main___closed__1 = _init_l_lean_ir_cpp_type2cpp___main___closed__1();
lean::mark_persistent(l_lean_ir_cpp_type2cpp___main___closed__1);
 l_lean_ir_cpp_type2cpp___main___closed__2 = _init_l_lean_ir_cpp_type2cpp___main___closed__2();
lean::mark_persistent(l_lean_ir_cpp_type2cpp___main___closed__2);
 l_lean_ir_cpp_type2cpp___main___closed__3 = _init_l_lean_ir_cpp_type2cpp___main___closed__3();
lean::mark_persistent(l_lean_ir_cpp_type2cpp___main___closed__3);
 l_lean_ir_cpp_type2cpp___main___closed__4 = _init_l_lean_ir_cpp_type2cpp___main___closed__4();
lean::mark_persistent(l_lean_ir_cpp_type2cpp___main___closed__4);
 l_lean_ir_cpp_type2cpp___main___closed__5 = _init_l_lean_ir_cpp_type2cpp___main___closed__5();
lean::mark_persistent(l_lean_ir_cpp_type2cpp___main___closed__5);
 l_lean_ir_cpp_type2cpp___main___closed__6 = _init_l_lean_ir_cpp_type2cpp___main___closed__6();
lean::mark_persistent(l_lean_ir_cpp_type2cpp___main___closed__6);
 l_lean_ir_cpp_type2cpp___main___closed__7 = _init_l_lean_ir_cpp_type2cpp___main___closed__7();
lean::mark_persistent(l_lean_ir_cpp_type2cpp___main___closed__7);
 l_lean_ir_cpp_type2cpp___main___closed__8 = _init_l_lean_ir_cpp_type2cpp___main___closed__8();
lean::mark_persistent(l_lean_ir_cpp_type2cpp___main___closed__8);
 l_lean_ir_cpp_type2cpp___main___closed__9 = _init_l_lean_ir_cpp_type2cpp___main___closed__9();
lean::mark_persistent(l_lean_ir_cpp_type2cpp___main___closed__9);
 l_lean_ir_cpp_type2cpp___main___closed__10 = _init_l_lean_ir_cpp_type2cpp___main___closed__10();
lean::mark_persistent(l_lean_ir_cpp_type2cpp___main___closed__10);
 l_lean_ir_cpp_type2cpp___main___closed__11 = _init_l_lean_ir_cpp_type2cpp___main___closed__11();
lean::mark_persistent(l_lean_ir_cpp_type2cpp___main___closed__11);
 l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1 = _init_l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1);
 l_lean_ir_cpp_emit__template__params___closed__1 = _init_l_lean_ir_cpp_emit__template__params___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__template__params___closed__1);
 l_lean_ir_cpp_emit__template__params___closed__2 = _init_l_lean_ir_cpp_emit__template__params___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__template__params___closed__2);
 l_lean_ir_cpp_emit__template__params___closed__3 = _init_l_lean_ir_cpp_emit__template__params___closed__3();
lean::mark_persistent(l_lean_ir_cpp_emit__template__params___closed__3);
 l_lean_ir_cpp_emit__template__params___closed__4 = _init_l_lean_ir_cpp_emit__template__params___closed__4();
lean::mark_persistent(l_lean_ir_cpp_emit__template__params___closed__4);
 l_lean_ir_cpp_emit__eos___closed__1 = _init_l_lean_ir_cpp_emit__eos___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__eos___closed__1);
 l_lean_ir_cpp_emit__cases___main___closed__1 = _init_l_lean_ir_cpp_emit__cases___main___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__cases___main___closed__1);
 l_lean_ir_cpp_emit__cases___main___closed__2 = _init_l_lean_ir_cpp_emit__cases___main___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__cases___main___closed__2);
 l_lean_ir_cpp_emit__cases___main___closed__3 = _init_l_lean_ir_cpp_emit__cases___main___closed__3();
lean::mark_persistent(l_lean_ir_cpp_emit__cases___main___closed__3);
 l_lean_ir_cpp_emit__cases___main___closed__4 = _init_l_lean_ir_cpp_emit__cases___main___closed__4();
lean::mark_persistent(l_lean_ir_cpp_emit__cases___main___closed__4);
 l_lean_ir_cpp_emit__case___main___closed__1 = _init_l_lean_ir_cpp_emit__case___main___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__case___main___closed__1);
 l_lean_ir_cpp_emit__case___main___closed__2 = _init_l_lean_ir_cpp_emit__case___main___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__case___main___closed__2);
 l_lean_ir_cpp_emit__case___main___closed__3 = _init_l_lean_ir_cpp_emit__case___main___closed__3();
lean::mark_persistent(l_lean_ir_cpp_emit__case___main___closed__3);
 l_lean_ir_cpp_emit__case___main___closed__4 = _init_l_lean_ir_cpp_emit__case___main___closed__4();
lean::mark_persistent(l_lean_ir_cpp_emit__case___main___closed__4);
 l_lean_ir_cpp_emit__case___main___closed__5 = _init_l_lean_ir_cpp_emit__case___main___closed__5();
lean::mark_persistent(l_lean_ir_cpp_emit__case___main___closed__5);
 l_lean_ir_cpp_emit__case___main___closed__6 = _init_l_lean_ir_cpp_emit__case___main___closed__6();
lean::mark_persistent(l_lean_ir_cpp_emit__case___main___closed__6);
 l_lean_ir_cpp_emit__case___main___closed__7 = _init_l_lean_ir_cpp_emit__case___main___closed__7();
lean::mark_persistent(l_lean_ir_cpp_emit__case___main___closed__7);
 l_lean_ir_cpp_emit__case___main___closed__8 = _init_l_lean_ir_cpp_emit__case___main___closed__8();
lean::mark_persistent(l_lean_ir_cpp_emit__case___main___closed__8);
 l_lean_ir_cpp_emit__case___main___closed__9 = _init_l_lean_ir_cpp_emit__case___main___closed__9();
lean::mark_persistent(l_lean_ir_cpp_emit__case___main___closed__9);
 l_lean_ir_cpp_emit__terminator___closed__1 = _init_l_lean_ir_cpp_emit__terminator___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__terminator___closed__1);
 l_lean_ir_cpp_emit__type__size___closed__1 = _init_l_lean_ir_cpp_emit__type__size___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__type__size___closed__1);
 l_lean_ir_cpp_emit__infix___closed__1 = _init_l_lean_ir_cpp_emit__infix___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__infix___closed__1);
 l_lean_ir_cpp_emit__assign__binop___closed__1 = _init_l_lean_ir_cpp_emit__assign__binop___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__1);
 l_lean_ir_cpp_emit__assign__binop___closed__2 = _init_l_lean_ir_cpp_emit__assign__binop___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__2);
 l_lean_ir_cpp_emit__assign__binop___closed__3 = _init_l_lean_ir_cpp_emit__assign__binop___closed__3();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__3);
 l_lean_ir_cpp_emit__assign__binop___closed__4 = _init_l_lean_ir_cpp_emit__assign__binop___closed__4();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__4);
 l_lean_ir_cpp_emit__assign__binop___closed__5 = _init_l_lean_ir_cpp_emit__assign__binop___closed__5();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__5);
 l_lean_ir_cpp_emit__assign__binop___closed__6 = _init_l_lean_ir_cpp_emit__assign__binop___closed__6();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__6);
 l_lean_ir_cpp_emit__assign__binop___closed__7 = _init_l_lean_ir_cpp_emit__assign__binop___closed__7();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__7);
 l_lean_ir_cpp_emit__assign__binop___closed__8 = _init_l_lean_ir_cpp_emit__assign__binop___closed__8();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__8);
 l_lean_ir_cpp_emit__assign__binop___closed__9 = _init_l_lean_ir_cpp_emit__assign__binop___closed__9();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__9);
 l_lean_ir_cpp_emit__assign__binop___closed__10 = _init_l_lean_ir_cpp_emit__assign__binop___closed__10();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__10);
 l_lean_ir_cpp_emit__assign__binop___closed__11 = _init_l_lean_ir_cpp_emit__assign__binop___closed__11();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__11);
 l_lean_ir_cpp_emit__assign__binop___closed__12 = _init_l_lean_ir_cpp_emit__assign__binop___closed__12();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__12);
 l_lean_ir_cpp_emit__assign__binop___closed__13 = _init_l_lean_ir_cpp_emit__assign__binop___closed__13();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__13);
 l_lean_ir_cpp_emit__assign__binop___closed__14 = _init_l_lean_ir_cpp_emit__assign__binop___closed__14();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__14);
 l_lean_ir_cpp_emit__assign__binop___closed__15 = _init_l_lean_ir_cpp_emit__assign__binop___closed__15();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__15);
 l_lean_ir_cpp_emit__assign__binop___closed__16 = _init_l_lean_ir_cpp_emit__assign__binop___closed__16();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__16);
 l_lean_ir_cpp_emit__assign__binop___closed__17 = _init_l_lean_ir_cpp_emit__assign__binop___closed__17();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__17);
 l_lean_ir_cpp_emit__assign__binop___closed__18 = _init_l_lean_ir_cpp_emit__assign__binop___closed__18();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__18);
 l_lean_ir_cpp_emit__assign__binop___closed__19 = _init_l_lean_ir_cpp_emit__assign__binop___closed__19();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__19);
 l_lean_ir_cpp_emit__assign__binop___closed__20 = _init_l_lean_ir_cpp_emit__assign__binop___closed__20();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__20);
 l_lean_ir_cpp_emit__assign__binop___closed__21 = _init_l_lean_ir_cpp_emit__assign__binop___closed__21();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__21);
 l_lean_ir_cpp_emit__assign__binop___closed__22 = _init_l_lean_ir_cpp_emit__assign__binop___closed__22();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__22);
 l_lean_ir_cpp_emit__assign__binop___closed__23 = _init_l_lean_ir_cpp_emit__assign__binop___closed__23();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__23);
 l_lean_ir_cpp_emit__assign__binop___closed__24 = _init_l_lean_ir_cpp_emit__assign__binop___closed__24();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__24);
 l_lean_ir_cpp_emit__assign__binop___closed__25 = _init_l_lean_ir_cpp_emit__assign__binop___closed__25();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__25);
 l_lean_ir_cpp_emit__assign__binop___closed__26 = _init_l_lean_ir_cpp_emit__assign__binop___closed__26();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__26);
 l_lean_ir_cpp_emit__assign__binop___closed__27 = _init_l_lean_ir_cpp_emit__assign__binop___closed__27();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__27);
 l_lean_ir_cpp_emit__assign__binop___closed__28 = _init_l_lean_ir_cpp_emit__assign__binop___closed__28();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__28);
 l_lean_ir_cpp_emit__assign__binop___closed__29 = _init_l_lean_ir_cpp_emit__assign__binop___closed__29();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__29);
 l_lean_ir_cpp_emit__assign__binop___closed__30 = _init_l_lean_ir_cpp_emit__assign__binop___closed__30();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__30);
 l_lean_ir_cpp_emit__assign__binop___closed__31 = _init_l_lean_ir_cpp_emit__assign__binop___closed__31();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__31);
 l_lean_ir_cpp_emit__assign__binop___closed__32 = _init_l_lean_ir_cpp_emit__assign__binop___closed__32();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__32);
 l_lean_ir_cpp_emit__assign__binop___closed__33 = _init_l_lean_ir_cpp_emit__assign__binop___closed__33();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__33);
 l_lean_ir_cpp_emit__assign__binop___closed__34 = _init_l_lean_ir_cpp_emit__assign__binop___closed__34();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__34);
 l_lean_ir_cpp_emit__assign__binop___closed__35 = _init_l_lean_ir_cpp_emit__assign__binop___closed__35();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__35);
 l_lean_ir_cpp_emit__assign__binop___closed__36 = _init_l_lean_ir_cpp_emit__assign__binop___closed__36();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__36);
 l_lean_ir_cpp_emit__assign__binop___closed__37 = _init_l_lean_ir_cpp_emit__assign__binop___closed__37();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__37);
 l_lean_ir_cpp_emit__assign__binop___closed__38 = _init_l_lean_ir_cpp_emit__assign__binop___closed__38();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__38);
 l_lean_ir_cpp_emit__assign__binop___closed__39 = _init_l_lean_ir_cpp_emit__assign__binop___closed__39();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__39);
 l_lean_ir_cpp_emit__assign__binop___closed__40 = _init_l_lean_ir_cpp_emit__assign__binop___closed__40();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__40);
 l_lean_ir_cpp_emit__assign__binop___closed__41 = _init_l_lean_ir_cpp_emit__assign__binop___closed__41();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__binop___closed__41);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__1 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__1();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__1);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__2 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__2();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__2);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__3 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__3();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__3);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__4 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__4();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__4);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__5 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__5();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__5);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__6 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__6();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__6);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__7 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__7();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__7);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__8 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__8();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__8);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__9 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__9();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__9);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__10 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__10();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__10);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__11 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__11();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__11);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__12 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__12();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__12);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__13 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__13();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__13);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__14 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__14();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__14);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__15 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__15();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__15);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__16 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__16();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__16);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__17 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__17();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__17);
 l_lean_ir_cpp_assign__unop2cpp___main___closed__18 = _init_l_lean_ir_cpp_assign__unop2cpp___main___closed__18();
lean::mark_persistent(l_lean_ir_cpp_assign__unop2cpp___main___closed__18);
 l_lean_ir_cpp_emit__num__suffix___main___closed__1 = _init_l_lean_ir_cpp_emit__num__suffix___main___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__num__suffix___main___closed__1);
 l_lean_ir_cpp_emit__num__suffix___main___closed__2 = _init_l_lean_ir_cpp_emit__num__suffix___main___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__num__suffix___main___closed__2);
 l_lean_ir_cpp_emit__num__suffix___main___closed__3 = _init_l_lean_ir_cpp_emit__num__suffix___main___closed__3();
lean::mark_persistent(l_lean_ir_cpp_emit__num__suffix___main___closed__3);
 l_lean_ir_cpp_emit__assign__lit___closed__1 = _init_l_lean_ir_cpp_emit__assign__lit___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__lit___closed__1);
 l_lean_ir_cpp_emit__assign__lit___closed__2 = _init_l_lean_ir_cpp_emit__assign__lit___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__lit___closed__2);
 l_lean_ir_cpp_emit__assign__lit___closed__3 = _init_l_lean_ir_cpp_emit__assign__lit___closed__3();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__lit___closed__3);
 l_lean_ir_cpp_emit__assign__lit___closed__4 = _init_l_lean_ir_cpp_emit__assign__lit___closed__4();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__lit___closed__4);
 l_lean_ir_cpp_emit__assign__lit___closed__5 = _init_l_lean_ir_cpp_emit__assign__lit___closed__5();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__lit___closed__5);
 l_lean_ir_cpp_emit__assign__lit___closed__6 = _init_l_lean_ir_cpp_emit__assign__lit___closed__6();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__lit___closed__6);
 l_lean_ir_cpp_emit__assign__lit___closed__7 = _init_l_lean_ir_cpp_emit__assign__lit___closed__7();
lean::mark_persistent(l_lean_ir_cpp_emit__assign__lit___closed__7);
 l_lean_ir_cpp_unop2cpp___main___closed__1 = _init_l_lean_ir_cpp_unop2cpp___main___closed__1();
lean::mark_persistent(l_lean_ir_cpp_unop2cpp___main___closed__1);
 l_lean_ir_cpp_unop2cpp___main___closed__2 = _init_l_lean_ir_cpp_unop2cpp___main___closed__2();
lean::mark_persistent(l_lean_ir_cpp_unop2cpp___main___closed__2);
 l_lean_ir_cpp_unop2cpp___main___closed__3 = _init_l_lean_ir_cpp_unop2cpp___main___closed__3();
lean::mark_persistent(l_lean_ir_cpp_unop2cpp___main___closed__3);
 l_lean_ir_cpp_unop2cpp___main___closed__4 = _init_l_lean_ir_cpp_unop2cpp___main___closed__4();
lean::mark_persistent(l_lean_ir_cpp_unop2cpp___main___closed__4);
 l_lean_ir_cpp_unop2cpp___main___closed__5 = _init_l_lean_ir_cpp_unop2cpp___main___closed__5();
lean::mark_persistent(l_lean_ir_cpp_unop2cpp___main___closed__5);
 l_lean_ir_cpp_unop2cpp___main___closed__6 = _init_l_lean_ir_cpp_unop2cpp___main___closed__6();
lean::mark_persistent(l_lean_ir_cpp_unop2cpp___main___closed__6);
 l_lean_ir_cpp_unop2cpp___main___closed__7 = _init_l_lean_ir_cpp_unop2cpp___main___closed__7();
lean::mark_persistent(l_lean_ir_cpp_unop2cpp___main___closed__7);
 l_lean_ir_cpp_unop2cpp___main___closed__8 = _init_l_lean_ir_cpp_unop2cpp___main___closed__8();
lean::mark_persistent(l_lean_ir_cpp_unop2cpp___main___closed__8);
 l_lean_ir_cpp_unop2cpp___main___closed__9 = _init_l_lean_ir_cpp_unop2cpp___main___closed__9();
lean::mark_persistent(l_lean_ir_cpp_unop2cpp___main___closed__9);
 l_lean_ir_cpp_emit__apply___closed__1 = _init_l_lean_ir_cpp_emit__apply___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__apply___closed__1);
 l_lean_ir_cpp_emit__apply___closed__2 = _init_l_lean_ir_cpp_emit__apply___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__apply___closed__2);
 l_lean_ir_cpp_emit__apply___closed__3 = _init_l_lean_ir_cpp_emit__apply___closed__3();
lean::mark_persistent(l_lean_ir_cpp_emit__apply___closed__3);
 l_lean_ir_cpp_emit__apply___closed__4 = _init_l_lean_ir_cpp_emit__apply___closed__4();
lean::mark_persistent(l_lean_ir_cpp_emit__apply___closed__4);
 l_lean_ir_cpp_emit__apply___closed__5 = _init_l_lean_ir_cpp_emit__apply___closed__5();
lean::mark_persistent(l_lean_ir_cpp_emit__apply___closed__5);
 l_lean_ir_cpp_emit__apply___closed__6 = _init_l_lean_ir_cpp_emit__apply___closed__6();
lean::mark_persistent(l_lean_ir_cpp_emit__apply___closed__6);
 l_lean_ir_cpp_emit__apply___closed__7 = _init_l_lean_ir_cpp_emit__apply___closed__7();
lean::mark_persistent(l_lean_ir_cpp_emit__apply___closed__7);
 l_lean_ir_cpp_emit__apply___closed__8 = _init_l_lean_ir_cpp_emit__apply___closed__8();
lean::mark_persistent(l_lean_ir_cpp_emit__apply___closed__8);
 l_lean_ir_cpp_emit__apply___closed__9 = _init_l_lean_ir_cpp_emit__apply___closed__9();
lean::mark_persistent(l_lean_ir_cpp_emit__apply___closed__9);
 l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___closed__1 = _init_l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___closed__1();
lean::mark_persistent(l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___closed__1);
 l_lean_ir_cpp_emit__closure___closed__1 = _init_l_lean_ir_cpp_emit__closure___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__closure___closed__1);
 l_lean_ir_cpp_emit__closure___closed__2 = _init_l_lean_ir_cpp_emit__closure___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__closure___closed__2);
 l_lean_ir_cpp_emit__closure___closed__3 = _init_l_lean_ir_cpp_emit__closure___closed__3();
lean::mark_persistent(l_lean_ir_cpp_emit__closure___closed__3);
 l_lean_ir_cpp_emit__closure___closed__4 = _init_l_lean_ir_cpp_emit__closure___closed__4();
lean::mark_persistent(l_lean_ir_cpp_emit__closure___closed__4);
 l_lean_ir_cpp_emit__instr___closed__1 = _init_l_lean_ir_cpp_emit__instr___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__instr___closed__1);
 l_lean_ir_cpp_emit__instr___closed__2 = _init_l_lean_ir_cpp_emit__instr___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__instr___closed__2);
 l_lean_ir_cpp_emit__instr___closed__3 = _init_l_lean_ir_cpp_emit__instr___closed__3();
lean::mark_persistent(l_lean_ir_cpp_emit__instr___closed__3);
 l_lean_ir_cpp_emit__instr___closed__4 = _init_l_lean_ir_cpp_emit__instr___closed__4();
lean::mark_persistent(l_lean_ir_cpp_emit__instr___closed__4);
 l_lean_ir_cpp_emit__instr___closed__5 = _init_l_lean_ir_cpp_emit__instr___closed__5();
lean::mark_persistent(l_lean_ir_cpp_emit__instr___closed__5);
 l_lean_ir_cpp_emit__instr___closed__6 = _init_l_lean_ir_cpp_emit__instr___closed__6();
lean::mark_persistent(l_lean_ir_cpp_emit__instr___closed__6);
 l_lean_ir_cpp_emit__instr___closed__7 = _init_l_lean_ir_cpp_emit__instr___closed__7();
lean::mark_persistent(l_lean_ir_cpp_emit__instr___closed__7);
 l_lean_ir_cpp_emit__instr___closed__8 = _init_l_lean_ir_cpp_emit__instr___closed__8();
lean::mark_persistent(l_lean_ir_cpp_emit__instr___closed__8);
 l_lean_ir_cpp_emit__instr___closed__9 = _init_l_lean_ir_cpp_emit__instr___closed__9();
lean::mark_persistent(l_lean_ir_cpp_emit__instr___closed__9);
 l_lean_ir_cpp_emit__block___closed__1 = _init_l_lean_ir_cpp_emit__block___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__block___closed__1);
 l_lean_ir_cpp_emit__block___closed__2 = _init_l_lean_ir_cpp_emit__block___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__block___closed__2);
 l_lean_ir_cpp_emit__header___closed__1 = _init_l_lean_ir_cpp_emit__header___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__header___closed__1);
 l_lean_ir_cpp_emit__uncurry__header___closed__1 = _init_l_lean_ir_cpp_emit__uncurry__header___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__uncurry__header___closed__1);
 l_lean_ir_cpp_emit__uncurry__header___closed__2 = _init_l_lean_ir_cpp_emit__uncurry__header___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__uncurry__header___closed__2);
 l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___closed__1 = _init_l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___closed__1();
lean::mark_persistent(l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___closed__1);
 l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1___closed__1 = _init_l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1___closed__1();
lean::mark_persistent(l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1___closed__1);
 l_lean_ir_cpp_emit__uncurry___closed__1 = _init_l_lean_ir_cpp_emit__uncurry___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__uncurry___closed__1);
 l_lean_ir_cpp_emit__uncurry___closed__2 = _init_l_lean_ir_cpp_emit__uncurry___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__uncurry___closed__2);
 l_lean_ir_cpp_emit__uncurry___closed__3 = _init_l_lean_ir_cpp_emit__uncurry___closed__3();
lean::mark_persistent(l_lean_ir_cpp_emit__uncurry___closed__3);
 l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1 = _init_l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1();
lean::mark_persistent(l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1);
 l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2 = _init_l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2();
lean::mark_persistent(l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2);
 l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1 = _init_l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1);
 l_lean_ir_cpp_emit__initialize__proc___closed__1 = _init_l_lean_ir_cpp_emit__initialize__proc___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__initialize__proc___closed__1);
 l_lean_ir_cpp_emit__initialize__proc___closed__2 = _init_l_lean_ir_cpp_emit__initialize__proc___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__initialize__proc___closed__2);
 l_lean_ir_cpp_emit__initialize__proc___closed__3 = _init_l_lean_ir_cpp_emit__initialize__proc___closed__3();
lean::mark_persistent(l_lean_ir_cpp_emit__initialize__proc___closed__3);
 l_lean_ir_cpp_emit__initialize__proc___closed__4 = _init_l_lean_ir_cpp_emit__initialize__proc___closed__4();
lean::mark_persistent(l_lean_ir_cpp_emit__initialize__proc___closed__4);
 l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__1 = _init_l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__1();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__1);
 l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__2 = _init_l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__2();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__2);
 l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__3 = _init_l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__3();
lean::mark_persistent(l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__3);
 l_lean_ir_cpp_emit__finalize__proc___closed__1 = _init_l_lean_ir_cpp_emit__finalize__proc___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__finalize__proc___closed__1);
 l_lean_ir_cpp_emit__finalize__proc___closed__2 = _init_l_lean_ir_cpp_emit__finalize__proc___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__finalize__proc___closed__2);
 l_lean_ir_cpp_emit__main__proc___closed__1 = _init_l_lean_ir_cpp_emit__main__proc___closed__1();
lean::mark_persistent(l_lean_ir_cpp_emit__main__proc___closed__1);
 l_lean_ir_cpp_emit__main__proc___closed__2 = _init_l_lean_ir_cpp_emit__main__proc___closed__2();
lean::mark_persistent(l_lean_ir_cpp_emit__main__proc___closed__2);
 l_lean_ir_cpp_emit__main__proc___closed__3 = _init_l_lean_ir_cpp_emit__main__proc___closed__3();
lean::mark_persistent(l_lean_ir_cpp_emit__main__proc___closed__3);
 l_lean_ir_cpp_emit__main__proc___closed__4 = _init_l_lean_ir_cpp_emit__main__proc___closed__4();
lean::mark_persistent(l_lean_ir_cpp_emit__main__proc___closed__4);
 l_lean_ir_cpp_emit__main__proc___closed__5 = _init_l_lean_ir_cpp_emit__main__proc___closed__5();
lean::mark_persistent(l_lean_ir_cpp_emit__main__proc___closed__5);
 l_lean_ir_cpp_emit__main__proc___closed__6 = _init_l_lean_ir_cpp_emit__main__proc___closed__6();
lean::mark_persistent(l_lean_ir_cpp_emit__main__proc___closed__6);
 l_lean_ir_cpp_emit__main__proc___closed__7 = _init_l_lean_ir_cpp_emit__main__proc___closed__7();
lean::mark_persistent(l_lean_ir_cpp_emit__main__proc___closed__7);
 l_lean_ir_extract__cpp___closed__1 = _init_l_lean_ir_extract__cpp___closed__1();
lean::mark_persistent(l_lean_ir_extract__cpp___closed__1);
 l_lean_ir_extract__cpp___closed__2 = _init_l_lean_ir_extract__cpp___closed__2();
lean::mark_persistent(l_lean_ir_extract__cpp___closed__2);
}
