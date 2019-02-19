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
obj* l_except__t_monad__run___rarg(obj*, obj*, obj*);
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
extern obj* l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
namespace lean {
obj* uint16_to_nat(uint16);
}
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
namespace lean {
obj* nat_add(obj*, obj*);
}
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
namespace lean {
obj* string_append(obj*, obj*);
}
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
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
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
obj* l_lean_ir_cpp_type2cpp___main___closed__8;
obj* l_lean_ir_cpp_emit__terminator___closed__1;
obj* l___private_init_lean_name__mangling_4__name_mangle__aux___main(obj*, obj*);
obj* l_lean_ir_cpp_file__header___closed__3;
obj* l_lean_ir_cpp_emit__logical__arith___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_ir_cpp_extract__m_monad__state;
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
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
extern obj* l_int_repr___main___closed__2;
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
namespace lean {
obj* nat_sub(obj*, obj*);
}
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
namespace lean {
obj* usize_to_nat(usize);
}
obj* l_lean_ir_cpp_emit__apply___closed__3;
namespace lean {
uint8 int_dec_lt(obj*, obj*);
}
obj* l_lean_ir_cpp_emit__assign__binop___closed__32;
obj* l_lean_ir_cpp_emit__assign__binop___closed__22;
extern obj* l_lean_closure__max__args;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
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
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = l_lean_ir_cpp_file__header___closed__1;
x_2 = lean::string_append(x_1, x_0);
x_3 = l_lean_ir_cpp_file__header___closed__2;
x_4 = lean::string_append(x_2, x_3);
x_5 = lean::string_append(x_4, x_1);
x_6 = lean::string_append(x_5, x_0);
lean::dec(x_0);
x_8 = l_lean_ir_cpp_file__header___closed__3;
x_9 = lean::string_append(x_6, x_8);
x_10 = l_lean_ir_cpp_file__header___closed__4;
x_11 = lean::string_append(x_9, x_10);
return x_11;
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
obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
lean::dec(x_2);
x_5 = lean::apply_1(x_0, x_1);
x_6 = lean::string_append(x_3, x_5);
lean::dec(x_5);
x_8 = l_lean_ir_match__type___closed__5;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_6);
return x_9;
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
obj* x_4; obj* x_6; obj* x_7; 
lean::dec(x_1);
x_4 = lean::string_append(x_2, x_0);
lean::dec(x_0);
x_6 = l_lean_ir_match__type___closed__5;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
return x_7;
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
obj* l_lean_ir_cpp_paren___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_3 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
} else {
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
} else {
 lean::dec(x_6);
 x_15 = lean::box(0);
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
obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
} else {
 lean::dec(x_6);
 x_18 = lean::box(0);
}
lean::inc(x_1);
x_20 = lean::apply_2(x_0, x_1, x_8);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_27; obj* x_30; obj* x_31; 
lean::dec(x_1);
x_27 = lean::cnstr_get(x_21, 0);
lean::inc(x_27);
lean::dec(x_21);
if (lean::is_scalar(x_18)) {
 x_30 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_30 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_30, 0, x_27);
if (lean::is_scalar(x_10)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_10;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_23);
return x_31;
}
else
{
obj* x_32; obj* x_35; obj* x_36; obj* x_37; obj* x_39; 
x_32 = lean::cnstr_get(x_21, 0);
lean::inc(x_32);
lean::dec(x_21);
x_35 = l_option_has__repr___rarg___closed__3;
x_36 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_35, x_1, x_23);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
if (lean::obj_tag(x_37) == 0)
{
obj* x_43; obj* x_46; obj* x_47; 
lean::dec(x_32);
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
if (lean::is_scalar(x_10)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_10;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_39);
return x_47;
}
else
{
obj* x_49; obj* x_50; 
lean::dec(x_37);
if (lean::is_scalar(x_18)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_18;
}
lean::cnstr_set(x_49, 0, x_32);
if (lean::is_scalar(x_10)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_10;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_39);
return x_50;
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
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
} else {
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
} else {
 lean::dec(x_6);
 x_15 = lean::box(0);
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
obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
} else {
 lean::dec(x_6);
 x_18 = lean::box(0);
}
x_19 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_2, x_8);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_29; obj* x_32; obj* x_33; 
lean::dec(x_1);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
lean::dec(x_22);
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_10)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_10;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_24);
return x_33;
}
else
{
obj* x_37; 
lean::dec(x_10);
lean::dec(x_22);
lean::dec(x_18);
x_37 = lean::apply_2(x_1, x_2, x_24);
return x_37;
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
return x_5;
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
return x_5;
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
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
lean::inc(x_1);
x_4 = l_lean_ir_cpp_fid2cpp(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
} else {
 lean::dec(x_4);
 x_9 = lean::box(0);
}
if (lean::obj_tag(x_5) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_13 = x_5;
} else {
 lean::dec(x_5);
 x_13 = lean::box(0);
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
obj* x_10; obj* x_11; 
x_10 = l_lean_ir_cpp_is__const___closed__1;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_15; uint8 x_16; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_lean_ir_decl_header___main(x_12);
x_16 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*3);
lean::dec(x_15);
x_18 = lean::box(x_16);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
return x_20;
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
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_8 = x_3;
} else {
 lean::dec(x_3);
 x_8 = lean::box(0);
}
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_11 = x_4;
} else {
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
obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_16 = x_4;
} else {
 lean::dec(x_4);
 x_16 = lean::box(0);
}
x_17 = l_lean_ir_cpp_global2cpp___closed__1;
x_18 = lean::string_append(x_17, x_14);
lean::dec(x_14);
if (lean::is_scalar(x_16)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_16;
}
lean::cnstr_set(x_20, 0, x_18);
if (lean::is_scalar(x_8)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_8;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_6);
return x_21;
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
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
} else {
 lean::dec(x_4);
 x_9 = lean::box(0);
}
if (lean::obj_tag(x_5) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_13 = x_5;
} else {
 lean::dec(x_5);
 x_13 = lean::box(0);
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
obj* x_8; obj* x_9; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_8 = l_lean_ir_match__type___closed__5;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
return x_9;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::dec(x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; 
lean::dec(x_1);
x_16 = lean::apply_3(x_0, x_10, x_3, x_4);
return x_16;
}
else
{
obj* x_19; obj* x_20; obj* x_22; obj* x_24; 
lean::inc(x_3);
lean::inc(x_0);
x_19 = lean::apply_3(x_0, x_10, x_3, x_4);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 lean::cnstr_release(x_19, 1);
 x_24 = x_19;
} else {
 lean::dec(x_19);
 x_24 = lean::box(0);
}
if (lean::obj_tag(x_20) == 0)
{
obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
x_29 = lean::cnstr_get(x_20, 0);
lean::inc(x_29);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 x_31 = x_20;
} else {
 lean::dec(x_20);
 x_31 = lean::box(0);
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
obj* x_34; obj* x_37; obj* x_38; obj* x_40; 
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 x_34 = x_20;
} else {
 lean::dec(x_20);
 x_34 = lean::box(0);
}
lean::inc(x_3);
lean::inc(x_1);
x_37 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1, x_3, x_22);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_47; obj* x_50; obj* x_51; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
x_47 = lean::cnstr_get(x_38, 0);
lean::inc(x_47);
lean::dec(x_38);
if (lean::is_scalar(x_34)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_34;
 lean::cnstr_set_tag(x_34, 0);
}
lean::cnstr_set(x_50, 0, x_47);
if (lean::is_scalar(x_24)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_24;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_40);
return x_51;
}
else
{
obj* x_53; obj* x_55; obj* x_56; obj* x_58; 
lean::dec(x_38);
x_53 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_3);
x_55 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_53, x_3, x_40);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_65; obj* x_68; obj* x_69; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_12);
x_65 = lean::cnstr_get(x_56, 0);
lean::inc(x_65);
lean::dec(x_56);
if (lean::is_scalar(x_34)) {
 x_68 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_68 = x_34;
 lean::cnstr_set_tag(x_34, 0);
}
lean::cnstr_set(x_68, 0, x_65);
if (lean::is_scalar(x_24)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_24;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_58);
return x_69;
}
else
{
lean::dec(x_24);
lean::dec(x_56);
lean::dec(x_34);
x_2 = x_12;
x_4 = x_58;
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
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_3 = l_lean_ir_cpp_emit__template__params___closed__1;
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
} else {
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
} else {
 lean::dec(x_6);
 x_15 = lean::box(0);
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
obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_25; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
} else {
 lean::dec(x_6);
 x_18 = lean::box(0);
}
x_19 = l_lean_ir_cpp_emit__template__params___closed__2;
x_20 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_1);
x_22 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_19, x_20, x_0, x_1, x_8);
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
if (lean::is_scalar(x_10)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_10;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_25);
return x_33;
}
else
{
obj* x_37; obj* x_38; 
lean::dec(x_10);
lean::dec(x_23);
lean::dec(x_18);
x_37 = l_lean_ir_cpp_emit__template__params___closed__4;
x_38 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_37, x_1, x_25);
return x_38;
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
uint8 x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_3 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit__type(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
} else {
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
} else {
 lean::dec(x_6);
 x_15 = lean::box(0);
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
obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
} else {
 lean::dec(x_6);
 x_18 = lean::box(0);
}
x_19 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_1);
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_1, x_8);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_29; obj* x_32; obj* x_33; 
lean::dec(x_1);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
lean::dec(x_22);
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_10)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_10;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_24);
return x_33;
}
else
{
obj* x_37; obj* x_40; 
lean::dec(x_10);
lean::dec(x_22);
lean::dec(x_18);
x_37 = lean::cnstr_get(x_0, 0);
lean::inc(x_37);
lean::dec(x_0);
x_40 = l_lean_ir_cpp_emit__var(x_37, x_1, x_24);
return x_40;
}
}
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
obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_2 = l_lean_ir_cpp_emit__eos___closed__1;
lean::inc(x_0);
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_2, x_0, x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 x_9 = x_4;
} else {
 lean::dec(x_4);
 x_9 = lean::box(0);
}
if (lean::obj_tag(x_5) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_0);
x_11 = lean::cnstr_get(x_5, 0);
lean::inc(x_11);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_13 = x_5;
} else {
 lean::dec(x_5);
 x_13 = lean::box(0);
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
obj* x_18; obj* x_19; 
lean::dec(x_5);
lean::dec(x_9);
x_18 = l_lean_format_be___main___closed__1;
x_19 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_18, x_0, x_7);
return x_19;
}
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_4 = l_nat_repr(x_0);
x_5 = lean::string_append(x_2, x_4);
lean::dec(x_4);
x_7 = l_lean_ir_match__type___closed__5;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
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
obj* x_6; obj* x_7; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = l_lean_ir_cpp_emit__cases___main___closed__1;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
return x_7;
}
else
{
obj* x_8; obj* x_10; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_21; 
lean::dec(x_1);
x_14 = l_lean_ir_cpp_emit__cases___main___closed__2;
lean::inc(x_2);
x_16 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_14, x_2, x_3);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 x_21 = x_16;
} else {
 lean::dec(x_16);
 x_21 = lean::box(0);
}
if (lean::obj_tag(x_17) == 0)
{
obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_8);
lean::dec(x_2);
x_24 = lean::cnstr_get(x_17, 0);
lean::inc(x_24);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_26 = x_17;
} else {
 lean::dec(x_17);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
if (lean::is_scalar(x_21)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_21;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_19);
return x_28;
}
else
{
obj* x_29; obj* x_31; obj* x_32; obj* x_34; 
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_29 = x_17;
} else {
 lean::dec(x_17);
 x_29 = lean::box(0);
}
lean::inc(x_2);
x_31 = l_lean_ir_cpp_emit__blockid(x_8, x_2, x_19);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
if (lean::obj_tag(x_32) == 0)
{
obj* x_38; obj* x_41; obj* x_42; 
lean::dec(x_2);
x_38 = lean::cnstr_get(x_32, 0);
lean::inc(x_38);
lean::dec(x_32);
if (lean::is_scalar(x_29)) {
 x_41 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_41 = x_29;
 lean::cnstr_set_tag(x_29, 0);
}
lean::cnstr_set(x_41, 0, x_38);
if (lean::is_scalar(x_21)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_21;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_34);
return x_42;
}
else
{
obj* x_46; 
lean::dec(x_32);
lean::dec(x_21);
lean::dec(x_29);
x_46 = l_lean_ir_cpp_emit__eos(x_2, x_34);
return x_46;
}
}
}
else
{
obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_54; 
x_47 = l_lean_ir_cpp_emit__cases___main___closed__3;
lean::inc(x_2);
x_49 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_47, x_2, x_3);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_54 = x_49;
} else {
 lean::dec(x_49);
 x_54 = lean::box(0);
}
if (lean::obj_tag(x_50) == 0)
{
obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_2);
x_59 = lean::cnstr_get(x_50, 0);
lean::inc(x_59);
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_61 = x_50;
} else {
 lean::dec(x_50);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_59);
if (lean::is_scalar(x_54)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_54;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_52);
return x_63;
}
else
{
obj* x_64; obj* x_67; obj* x_68; obj* x_70; 
if (lean::is_exclusive(x_50)) {
 lean::cnstr_release(x_50, 0);
 x_64 = x_50;
} else {
 lean::dec(x_50);
 x_64 = lean::box(0);
}
lean::inc(x_2);
lean::inc(x_1);
x_67 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_1, x_2, x_52);
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
if (lean::obj_tag(x_68) == 0)
{
obj* x_77; obj* x_80; obj* x_81; 
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_2);
x_77 = lean::cnstr_get(x_68, 0);
lean::inc(x_77);
lean::dec(x_68);
if (lean::is_scalar(x_64)) {
 x_80 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_80 = x_64;
 lean::cnstr_set_tag(x_64, 0);
}
lean::cnstr_set(x_80, 0, x_77);
if (lean::is_scalar(x_54)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_54;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_70);
return x_81;
}
else
{
obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_91; 
lean::dec(x_68);
x_83 = lean::mk_nat_obj(1u);
x_84 = lean::nat_add(x_1, x_83);
lean::dec(x_1);
x_86 = l_lean_ir_cpp_emit__cases___main___closed__4;
lean::inc(x_2);
x_88 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_86, x_2, x_70);
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_88, 1);
lean::inc(x_91);
lean::dec(x_88);
if (lean::obj_tag(x_89) == 0)
{
obj* x_98; obj* x_101; obj* x_102; 
lean::dec(x_10);
lean::dec(x_8);
lean::dec(x_2);
lean::dec(x_84);
x_98 = lean::cnstr_get(x_89, 0);
lean::inc(x_98);
lean::dec(x_89);
if (lean::is_scalar(x_64)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_64;
 lean::cnstr_set_tag(x_64, 0);
}
lean::cnstr_set(x_101, 0, x_98);
if (lean::is_scalar(x_54)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_54;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_91);
return x_102;
}
else
{
obj* x_105; obj* x_106; obj* x_108; 
lean::dec(x_89);
lean::inc(x_2);
x_105 = l_lean_ir_cpp_emit__blockid(x_8, x_2, x_91);
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_105, 1);
lean::inc(x_108);
lean::dec(x_105);
if (lean::obj_tag(x_106) == 0)
{
obj* x_114; obj* x_117; obj* x_118; 
lean::dec(x_10);
lean::dec(x_2);
lean::dec(x_84);
x_114 = lean::cnstr_get(x_106, 0);
lean::inc(x_114);
lean::dec(x_106);
if (lean::is_scalar(x_64)) {
 x_117 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_117 = x_64;
 lean::cnstr_set_tag(x_64, 0);
}
lean::cnstr_set(x_117, 0, x_114);
if (lean::is_scalar(x_54)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_54;
}
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_108);
return x_118;
}
else
{
obj* x_121; obj* x_122; obj* x_124; 
lean::dec(x_106);
lean::inc(x_2);
x_121 = l_lean_ir_cpp_emit__eos(x_2, x_108);
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_121, 1);
lean::inc(x_124);
lean::dec(x_121);
if (lean::obj_tag(x_122) == 0)
{
obj* x_130; obj* x_133; obj* x_134; 
lean::dec(x_10);
lean::dec(x_2);
lean::dec(x_84);
x_130 = lean::cnstr_get(x_122, 0);
lean::inc(x_130);
lean::dec(x_122);
if (lean::is_scalar(x_64)) {
 x_133 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_133 = x_64;
 lean::cnstr_set_tag(x_64, 0);
}
lean::cnstr_set(x_133, 0, x_130);
if (lean::is_scalar(x_54)) {
 x_134 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_134 = x_54;
}
lean::cnstr_set(x_134, 0, x_133);
lean::cnstr_set(x_134, 1, x_124);
return x_134;
}
else
{
lean::dec(x_54);
lean::dec(x_64);
lean::dec(x_122);
x_0 = x_10;
x_1 = x_84;
x_3 = x_124;
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
obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_23; 
lean::dec(x_1);
lean::dec(x_0);
x_16 = l_lean_ir_cpp_emit__case___main___closed__4;
lean::inc(x_2);
x_18 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_16, x_2, x_3);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 x_23 = x_18;
} else {
 lean::dec(x_18);
 x_23 = lean::box(0);
}
if (lean::obj_tag(x_19) == 0)
{
obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_10);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_19, 0);
lean::inc(x_26);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 x_28 = x_19;
} else {
 lean::dec(x_19);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_26);
if (lean::is_scalar(x_23)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_23;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_21);
return x_30;
}
else
{
obj* x_31; obj* x_33; obj* x_34; obj* x_36; 
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 x_31 = x_19;
} else {
 lean::dec(x_19);
 x_31 = lean::box(0);
}
lean::inc(x_2);
x_33 = l_lean_ir_cpp_emit__blockid(x_10, x_2, x_21);
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
if (lean::obj_tag(x_34) == 0)
{
obj* x_40; obj* x_43; obj* x_44; 
lean::dec(x_2);
x_40 = lean::cnstr_get(x_34, 0);
lean::inc(x_40);
lean::dec(x_34);
if (lean::is_scalar(x_31)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_31;
 lean::cnstr_set_tag(x_31, 0);
}
lean::cnstr_set(x_43, 0, x_40);
if (lean::is_scalar(x_23)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_23;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_36);
return x_44;
}
else
{
obj* x_48; 
lean::dec(x_31);
lean::dec(x_23);
lean::dec(x_34);
x_48 = l_lean_ir_cpp_emit__eos(x_2, x_36);
return x_48;
}
}
}
else
{
obj* x_49; obj* x_51; 
x_49 = lean::cnstr_get(x_12, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_12, 1);
lean::inc(x_51);
lean::dec(x_12);
if (lean::obj_tag(x_51) == 0)
{
obj* x_55; obj* x_56; obj* x_58; obj* x_61; 
lean::dec(x_1);
x_58 = lean::cnstr_get(x_2, 1);
lean::inc(x_58);
lean::inc(x_0);
x_61 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_58, x_0);
if (lean::obj_tag(x_61) == 0)
{
obj* x_65; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_49);
x_65 = l_lean_ir_cpp_emit__case___main___closed__5;
x_55 = x_65;
x_56 = x_3;
goto lbl_57;
}
else
{
obj* x_66; uint8 x_69; 
x_66 = lean::cnstr_get(x_61, 0);
lean::inc(x_66);
lean::dec(x_61);
x_69 = lean::unbox(x_66);
lean::dec(x_66);
switch (x_69) {
case 0:
{
obj* x_71; obj* x_73; obj* x_74; obj* x_76; 
x_71 = l_lean_ir_cpp_emit__case___main___closed__6;
lean::inc(x_2);
x_73 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_71, x_2, x_3);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_82; obj* x_84; obj* x_85; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_49);
x_82 = lean::cnstr_get(x_74, 0);
lean::inc(x_82);
if (lean::is_exclusive(x_74)) {
 lean::cnstr_release(x_74, 0);
 x_84 = x_74;
} else {
 lean::dec(x_74);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_82);
x_55 = x_85;
x_56 = x_76;
goto lbl_57;
}
else
{
obj* x_86; obj* x_88; obj* x_89; obj* x_91; 
if (lean::is_exclusive(x_74)) {
 lean::cnstr_release(x_74, 0);
 x_86 = x_74;
} else {
 lean::dec(x_74);
 x_86 = lean::box(0);
}
lean::inc(x_2);
x_88 = l_lean_ir_cpp_emit__var(x_0, x_2, x_76);
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_88, 1);
lean::inc(x_91);
lean::dec(x_88);
if (lean::obj_tag(x_89) == 0)
{
obj* x_96; obj* x_99; 
lean::dec(x_10);
lean::dec(x_49);
x_96 = lean::cnstr_get(x_89, 0);
lean::inc(x_96);
lean::dec(x_89);
if (lean::is_scalar(x_86)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_86;
 lean::cnstr_set_tag(x_86, 0);
}
lean::cnstr_set(x_99, 0, x_96);
x_55 = x_99;
x_56 = x_91;
goto lbl_57;
}
else
{
obj* x_101; obj* x_103; obj* x_104; obj* x_106; 
lean::dec(x_89);
x_101 = l_lean_ir_cpp_emit__case___main___closed__7;
lean::inc(x_2);
x_103 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_101, x_2, x_91);
x_104 = lean::cnstr_get(x_103, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_103, 1);
lean::inc(x_106);
lean::dec(x_103);
if (lean::obj_tag(x_104) == 0)
{
obj* x_111; obj* x_114; 
lean::dec(x_10);
lean::dec(x_49);
x_111 = lean::cnstr_get(x_104, 0);
lean::inc(x_111);
lean::dec(x_104);
if (lean::is_scalar(x_86)) {
 x_114 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_114 = x_86;
 lean::cnstr_set_tag(x_86, 0);
}
lean::cnstr_set(x_114, 0, x_111);
x_55 = x_114;
x_56 = x_106;
goto lbl_57;
}
else
{
obj* x_117; obj* x_118; obj* x_120; 
lean::dec(x_104);
lean::inc(x_2);
x_117 = l_lean_ir_cpp_emit__blockid(x_49, x_2, x_106);
x_118 = lean::cnstr_get(x_117, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_117, 1);
lean::inc(x_120);
lean::dec(x_117);
if (lean::obj_tag(x_118) == 0)
{
obj* x_124; obj* x_127; 
lean::dec(x_10);
x_124 = lean::cnstr_get(x_118, 0);
lean::inc(x_124);
lean::dec(x_118);
if (lean::is_scalar(x_86)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_86;
 lean::cnstr_set_tag(x_86, 0);
}
lean::cnstr_set(x_127, 0, x_124);
x_55 = x_127;
x_56 = x_120;
goto lbl_57;
}
else
{
obj* x_129; obj* x_131; obj* x_132; obj* x_134; 
lean::dec(x_118);
x_129 = l_lean_ir_cpp_emit__case___main___closed__8;
lean::inc(x_2);
x_131 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_129, x_2, x_120);
x_132 = lean::cnstr_get(x_131, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_131, 1);
lean::inc(x_134);
lean::dec(x_131);
if (lean::obj_tag(x_132) == 0)
{
obj* x_138; obj* x_141; 
lean::dec(x_10);
x_138 = lean::cnstr_get(x_132, 0);
lean::inc(x_138);
lean::dec(x_132);
if (lean::is_scalar(x_86)) {
 x_141 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_141 = x_86;
 lean::cnstr_set_tag(x_86, 0);
}
lean::cnstr_set(x_141, 0, x_138);
x_55 = x_141;
x_56 = x_134;
goto lbl_57;
}
else
{
obj* x_145; obj* x_146; obj* x_148; 
lean::dec(x_132);
lean::dec(x_86);
lean::inc(x_2);
x_145 = l_lean_ir_cpp_emit__blockid(x_10, x_2, x_134);
x_146 = lean::cnstr_get(x_145, 0);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_145, 1);
lean::inc(x_148);
lean::dec(x_145);
x_55 = x_146;
x_56 = x_148;
goto lbl_57;
}
}
}
}
}
}
case 3:
{
obj* x_151; obj* x_153; obj* x_154; obj* x_156; 
x_151 = l_lean_ir_cpp_emit__case___main___closed__6;
lean::inc(x_2);
x_153 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_151, x_2, x_3);
x_154 = lean::cnstr_get(x_153, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_153, 1);
lean::inc(x_156);
lean::dec(x_153);
if (lean::obj_tag(x_154) == 0)
{
obj* x_162; obj* x_164; obj* x_165; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_49);
x_162 = lean::cnstr_get(x_154, 0);
lean::inc(x_162);
if (lean::is_exclusive(x_154)) {
 lean::cnstr_release(x_154, 0);
 x_164 = x_154;
} else {
 lean::dec(x_154);
 x_164 = lean::box(0);
}
if (lean::is_scalar(x_164)) {
 x_165 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_165 = x_164;
}
lean::cnstr_set(x_165, 0, x_162);
x_55 = x_165;
x_56 = x_156;
goto lbl_57;
}
else
{
obj* x_166; obj* x_168; obj* x_169; obj* x_171; 
if (lean::is_exclusive(x_154)) {
 lean::cnstr_release(x_154, 0);
 x_166 = x_154;
} else {
 lean::dec(x_154);
 x_166 = lean::box(0);
}
lean::inc(x_2);
x_168 = l_lean_ir_cpp_emit__var(x_0, x_2, x_156);
x_169 = lean::cnstr_get(x_168, 0);
lean::inc(x_169);
x_171 = lean::cnstr_get(x_168, 1);
lean::inc(x_171);
lean::dec(x_168);
if (lean::obj_tag(x_169) == 0)
{
obj* x_176; obj* x_179; 
lean::dec(x_10);
lean::dec(x_49);
x_176 = lean::cnstr_get(x_169, 0);
lean::inc(x_176);
lean::dec(x_169);
if (lean::is_scalar(x_166)) {
 x_179 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_179 = x_166;
 lean::cnstr_set_tag(x_166, 0);
}
lean::cnstr_set(x_179, 0, x_176);
x_55 = x_179;
x_56 = x_171;
goto lbl_57;
}
else
{
obj* x_181; obj* x_183; obj* x_184; obj* x_186; 
lean::dec(x_169);
x_181 = l_lean_ir_cpp_emit__case___main___closed__9;
lean::inc(x_2);
x_183 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_181, x_2, x_171);
x_184 = lean::cnstr_get(x_183, 0);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_183, 1);
lean::inc(x_186);
lean::dec(x_183);
if (lean::obj_tag(x_184) == 0)
{
obj* x_191; obj* x_194; 
lean::dec(x_10);
lean::dec(x_49);
x_191 = lean::cnstr_get(x_184, 0);
lean::inc(x_191);
lean::dec(x_184);
if (lean::is_scalar(x_166)) {
 x_194 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_194 = x_166;
 lean::cnstr_set_tag(x_166, 0);
}
lean::cnstr_set(x_194, 0, x_191);
x_55 = x_194;
x_56 = x_186;
goto lbl_57;
}
else
{
obj* x_197; obj* x_198; obj* x_200; 
lean::dec(x_184);
lean::inc(x_2);
x_197 = l_lean_ir_cpp_emit__blockid(x_10, x_2, x_186);
x_198 = lean::cnstr_get(x_197, 0);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_197, 1);
lean::inc(x_200);
lean::dec(x_197);
if (lean::obj_tag(x_198) == 0)
{
obj* x_204; obj* x_207; 
lean::dec(x_49);
x_204 = lean::cnstr_get(x_198, 0);
lean::inc(x_204);
lean::dec(x_198);
if (lean::is_scalar(x_166)) {
 x_207 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_207 = x_166;
 lean::cnstr_set_tag(x_166, 0);
}
lean::cnstr_set(x_207, 0, x_204);
x_55 = x_207;
x_56 = x_200;
goto lbl_57;
}
else
{
obj* x_209; obj* x_211; obj* x_212; obj* x_214; 
lean::dec(x_198);
x_209 = l_lean_ir_cpp_emit__case___main___closed__8;
lean::inc(x_2);
x_211 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_209, x_2, x_200);
x_212 = lean::cnstr_get(x_211, 0);
lean::inc(x_212);
x_214 = lean::cnstr_get(x_211, 1);
lean::inc(x_214);
lean::dec(x_211);
if (lean::obj_tag(x_212) == 0)
{
obj* x_218; obj* x_221; 
lean::dec(x_49);
x_218 = lean::cnstr_get(x_212, 0);
lean::inc(x_218);
lean::dec(x_212);
if (lean::is_scalar(x_166)) {
 x_221 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_221 = x_166;
 lean::cnstr_set_tag(x_166, 0);
}
lean::cnstr_set(x_221, 0, x_218);
x_55 = x_221;
x_56 = x_214;
goto lbl_57;
}
else
{
obj* x_225; obj* x_226; obj* x_228; 
lean::dec(x_166);
lean::dec(x_212);
lean::inc(x_2);
x_225 = l_lean_ir_cpp_emit__blockid(x_49, x_2, x_214);
x_226 = lean::cnstr_get(x_225, 0);
lean::inc(x_226);
x_228 = lean::cnstr_get(x_225, 1);
lean::inc(x_228);
lean::dec(x_225);
x_55 = x_226;
x_56 = x_228;
goto lbl_57;
}
}
}
}
}
}
default:
{
obj* x_234; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_49);
x_234 = l_lean_ir_cpp_emit__case___main___closed__5;
x_55 = x_234;
x_56 = x_3;
goto lbl_57;
}
}
}
lbl_57:
{
if (lean::obj_tag(x_55) == 0)
{
obj* x_236; obj* x_238; obj* x_239; obj* x_240; 
lean::dec(x_2);
x_236 = lean::cnstr_get(x_55, 0);
lean::inc(x_236);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_238 = x_55;
} else {
 lean::dec(x_55);
 x_238 = lean::box(0);
}
if (lean::is_scalar(x_238)) {
 x_239 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_239 = x_238;
}
lean::cnstr_set(x_239, 0, x_236);
x_240 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_240, 0, x_239);
lean::cnstr_set(x_240, 1, x_56);
return x_240;
}
else
{
obj* x_242; 
lean::dec(x_55);
x_242 = l_lean_ir_cpp_emit__eos(x_2, x_56);
return x_242;
}
}
}
else
{
obj* x_246; 
lean::dec(x_10);
lean::dec(x_49);
lean::dec(x_51);
x_246 = lean::box(0);
x_7 = x_246;
goto lbl_8;
}
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_249; obj* x_251; obj* x_252; obj* x_253; 
lean::dec(x_1);
lean::dec(x_2);
x_249 = lean::cnstr_get(x_4, 0);
lean::inc(x_249);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_251 = x_4;
} else {
 lean::dec(x_4);
 x_251 = lean::box(0);
}
if (lean::is_scalar(x_251)) {
 x_252 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_252 = x_251;
}
lean::cnstr_set(x_252, 0, x_249);
x_253 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_253, 0, x_252);
lean::cnstr_set(x_253, 1, x_5);
return x_253;
}
else
{
obj* x_254; obj* x_255; obj* x_257; obj* x_258; obj* x_260; obj* x_262; 
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_254 = x_4;
} else {
 lean::dec(x_4);
 x_254 = lean::box(0);
}
x_255 = l_lean_ir_cpp_emit__case___main___closed__1;
lean::inc(x_2);
x_257 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_255, x_2, x_5);
x_258 = lean::cnstr_get(x_257, 0);
lean::inc(x_258);
x_260 = lean::cnstr_get(x_257, 1);
lean::inc(x_260);
if (lean::is_exclusive(x_257)) {
 lean::cnstr_release(x_257, 0);
 lean::cnstr_release(x_257, 1);
 x_262 = x_257;
} else {
 lean::dec(x_257);
 x_262 = lean::box(0);
}
if (lean::obj_tag(x_258) == 0)
{
obj* x_265; obj* x_268; obj* x_269; 
lean::dec(x_1);
lean::dec(x_2);
x_265 = lean::cnstr_get(x_258, 0);
lean::inc(x_265);
lean::dec(x_258);
if (lean::is_scalar(x_254)) {
 x_268 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_268 = x_254;
 lean::cnstr_set_tag(x_254, 0);
}
lean::cnstr_set(x_268, 0, x_265);
if (lean::is_scalar(x_262)) {
 x_269 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_269 = x_262;
}
lean::cnstr_set(x_269, 0, x_268);
lean::cnstr_set(x_269, 1, x_260);
return x_269;
}
else
{
obj* x_271; obj* x_273; obj* x_274; obj* x_276; 
lean::dec(x_258);
x_271 = l_lean_format_be___main___closed__1;
lean::inc(x_2);
x_273 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_271, x_2, x_260);
x_274 = lean::cnstr_get(x_273, 0);
lean::inc(x_274);
x_276 = lean::cnstr_get(x_273, 1);
lean::inc(x_276);
lean::dec(x_273);
if (lean::obj_tag(x_274) == 0)
{
obj* x_281; obj* x_284; obj* x_285; 
lean::dec(x_1);
lean::dec(x_2);
x_281 = lean::cnstr_get(x_274, 0);
lean::inc(x_281);
lean::dec(x_274);
if (lean::is_scalar(x_254)) {
 x_284 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_284 = x_254;
 lean::cnstr_set_tag(x_254, 0);
}
lean::cnstr_set(x_284, 0, x_281);
if (lean::is_scalar(x_262)) {
 x_285 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_285 = x_262;
}
lean::cnstr_set(x_285, 0, x_284);
lean::cnstr_set(x_285, 1, x_276);
return x_285;
}
else
{
obj* x_287; obj* x_289; obj* x_290; obj* x_292; 
lean::dec(x_274);
x_287 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_289 = l_lean_ir_cpp_emit__cases___main(x_1, x_287, x_2, x_276);
x_290 = lean::cnstr_get(x_289, 0);
lean::inc(x_290);
x_292 = lean::cnstr_get(x_289, 1);
lean::inc(x_292);
lean::dec(x_289);
if (lean::obj_tag(x_290) == 0)
{
obj* x_296; obj* x_299; obj* x_300; 
lean::dec(x_2);
x_296 = lean::cnstr_get(x_290, 0);
lean::inc(x_296);
lean::dec(x_290);
if (lean::is_scalar(x_254)) {
 x_299 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_299 = x_254;
 lean::cnstr_set_tag(x_254, 0);
}
lean::cnstr_set(x_299, 0, x_296);
if (lean::is_scalar(x_262)) {
 x_300 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_300 = x_262;
}
lean::cnstr_set(x_300, 0, x_299);
lean::cnstr_set(x_300, 1, x_292);
return x_300;
}
else
{
obj* x_302; obj* x_304; obj* x_305; obj* x_307; 
lean::dec(x_290);
x_302 = l_lean_ir_cpp_emit__case___main___closed__2;
lean::inc(x_2);
x_304 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_302, x_2, x_292);
x_305 = lean::cnstr_get(x_304, 0);
lean::inc(x_305);
x_307 = lean::cnstr_get(x_304, 1);
lean::inc(x_307);
lean::dec(x_304);
if (lean::obj_tag(x_305) == 0)
{
obj* x_311; obj* x_314; obj* x_315; 
lean::dec(x_2);
x_311 = lean::cnstr_get(x_305, 0);
lean::inc(x_311);
lean::dec(x_305);
if (lean::is_scalar(x_254)) {
 x_314 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_314 = x_254;
 lean::cnstr_set_tag(x_254, 0);
}
lean::cnstr_set(x_314, 0, x_311);
if (lean::is_scalar(x_262)) {
 x_315 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_315 = x_262;
}
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_307);
return x_315;
}
else
{
obj* x_319; 
lean::dec(x_305);
lean::dec(x_262);
lean::dec(x_254);
x_319 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_271, x_2, x_307);
return x_319;
}
}
}
}
}
}
lbl_8:
{
obj* x_321; obj* x_323; obj* x_324; obj* x_326; obj* x_328; 
lean::dec(x_7);
x_321 = l_lean_ir_cpp_emit__case___main___closed__3;
lean::inc(x_2);
x_323 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_321, x_2, x_3);
x_324 = lean::cnstr_get(x_323, 0);
lean::inc(x_324);
x_326 = lean::cnstr_get(x_323, 1);
lean::inc(x_326);
if (lean::is_exclusive(x_323)) {
 lean::cnstr_release(x_323, 0);
 lean::cnstr_release(x_323, 1);
 x_328 = x_323;
} else {
 lean::dec(x_323);
 x_328 = lean::box(0);
}
if (lean::obj_tag(x_324) == 0)
{
obj* x_332; obj* x_334; obj* x_335; obj* x_336; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_332 = lean::cnstr_get(x_324, 0);
lean::inc(x_332);
if (lean::is_exclusive(x_324)) {
 lean::cnstr_release(x_324, 0);
 x_334 = x_324;
} else {
 lean::dec(x_324);
 x_334 = lean::box(0);
}
if (lean::is_scalar(x_334)) {
 x_335 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_335 = x_334;
}
lean::cnstr_set(x_335, 0, x_332);
if (lean::is_scalar(x_328)) {
 x_336 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_336 = x_328;
}
lean::cnstr_set(x_336, 0, x_335);
lean::cnstr_set(x_336, 1, x_326);
return x_336;
}
else
{
obj* x_338; obj* x_339; obj* x_341; obj* x_342; obj* x_344; 
lean::dec(x_328);
if (lean::is_exclusive(x_324)) {
 lean::cnstr_release(x_324, 0);
 x_338 = x_324;
} else {
 lean::dec(x_324);
 x_338 = lean::box(0);
}
x_339 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
x_341 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_339, x_2, x_326);
x_342 = lean::cnstr_get(x_341, 0);
lean::inc(x_342);
x_344 = lean::cnstr_get(x_341, 1);
lean::inc(x_344);
lean::dec(x_341);
if (lean::obj_tag(x_342) == 0)
{
obj* x_348; obj* x_351; 
lean::dec(x_0);
x_348 = lean::cnstr_get(x_342, 0);
lean::inc(x_348);
lean::dec(x_342);
if (lean::is_scalar(x_338)) {
 x_351 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_351 = x_338;
 lean::cnstr_set_tag(x_338, 0);
}
lean::cnstr_set(x_351, 0, x_348);
x_4 = x_351;
x_5 = x_344;
goto lbl_6;
}
else
{
obj* x_354; obj* x_355; obj* x_357; 
lean::dec(x_342);
lean::inc(x_2);
x_354 = l_lean_ir_cpp_emit__var(x_0, x_2, x_344);
x_355 = lean::cnstr_get(x_354, 0);
lean::inc(x_355);
x_357 = lean::cnstr_get(x_354, 1);
lean::inc(x_357);
lean::dec(x_354);
if (lean::obj_tag(x_355) == 0)
{
obj* x_360; obj* x_363; 
x_360 = lean::cnstr_get(x_355, 0);
lean::inc(x_360);
lean::dec(x_355);
if (lean::is_scalar(x_338)) {
 x_363 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_363 = x_338;
 lean::cnstr_set_tag(x_338, 0);
}
lean::cnstr_set(x_363, 0, x_360);
x_4 = x_363;
x_5 = x_357;
goto lbl_6;
}
else
{
obj* x_364; obj* x_367; obj* x_369; obj* x_370; obj* x_372; 
x_364 = lean::cnstr_get(x_355, 0);
lean::inc(x_364);
lean::dec(x_355);
x_367 = l_option_has__repr___rarg___closed__3;
lean::inc(x_2);
x_369 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_367, x_2, x_357);
x_370 = lean::cnstr_get(x_369, 0);
lean::inc(x_370);
x_372 = lean::cnstr_get(x_369, 1);
lean::inc(x_372);
lean::dec(x_369);
if (lean::obj_tag(x_370) == 0)
{
obj* x_376; obj* x_379; 
lean::dec(x_364);
x_376 = lean::cnstr_get(x_370, 0);
lean::inc(x_376);
lean::dec(x_370);
if (lean::is_scalar(x_338)) {
 x_379 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_379 = x_338;
 lean::cnstr_set_tag(x_338, 0);
}
lean::cnstr_set(x_379, 0, x_376);
x_4 = x_379;
x_5 = x_372;
goto lbl_6;
}
else
{
obj* x_381; 
lean::dec(x_370);
if (lean::is_scalar(x_338)) {
 x_381 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_381 = x_338;
}
lean::cnstr_set(x_381, 0, x_364);
x_4 = x_381;
x_5 = x_372;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = l_lean_ir_cpp_emit__terminator___closed__1;
lean::inc(x_1);
x_10 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_8, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_6);
lean::dec(x_1);
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_20 = x_11;
} else {
 lean::dec(x_11);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
x_3 = x_21;
x_4 = x_13;
goto lbl_5;
}
else
{
obj* x_22; obj* x_24; obj* x_25; obj* x_27; 
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_22 = x_11;
} else {
 lean::dec(x_11);
 x_22 = lean::box(0);
}
lean::inc(x_1);
x_24 = l_lean_ir_cpp_emit__var(x_6, x_1, x_13);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_31; obj* x_34; 
lean::dec(x_1);
x_31 = lean::cnstr_get(x_25, 0);
lean::inc(x_31);
lean::dec(x_25);
if (lean::is_scalar(x_22)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_22;
 lean::cnstr_set_tag(x_22, 0);
}
lean::cnstr_set(x_34, 0, x_31);
x_3 = x_34;
x_4 = x_27;
goto lbl_5;
}
else
{
obj* x_37; obj* x_38; obj* x_40; 
lean::dec(x_22);
lean::dec(x_25);
x_37 = l_lean_ir_cpp_emit__eos(x_1, x_27);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
x_3 = x_38;
x_4 = x_40;
goto lbl_5;
}
}
}
case 1:
{
obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_50; 
x_43 = lean::cnstr_get(x_0, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_0, 1);
lean::inc(x_45);
x_47 = l_lean_ir_cpp_emit__case___main(x_43, x_45, x_1, x_2);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
lean::dec(x_47);
x_3 = x_48;
x_4 = x_50;
goto lbl_5;
}
default:
{
obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_60; 
x_53 = lean::cnstr_get(x_0, 0);
lean::inc(x_53);
x_55 = l_lean_ir_cpp_emit__case___main___closed__4;
lean::inc(x_1);
x_57 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_55, x_1, x_2);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_65; obj* x_67; obj* x_68; 
lean::dec(x_1);
lean::dec(x_53);
x_65 = lean::cnstr_get(x_58, 0);
lean::inc(x_65);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 x_67 = x_58;
} else {
 lean::dec(x_58);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_65);
x_3 = x_68;
x_4 = x_60;
goto lbl_5;
}
else
{
obj* x_69; obj* x_71; obj* x_72; obj* x_74; 
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 x_69 = x_58;
} else {
 lean::dec(x_58);
 x_69 = lean::box(0);
}
lean::inc(x_1);
x_71 = l_lean_ir_cpp_emit__blockid(x_53, x_1, x_60);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
lean::dec(x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_78; obj* x_81; 
lean::dec(x_1);
x_78 = lean::cnstr_get(x_72, 0);
lean::inc(x_78);
lean::dec(x_72);
if (lean::is_scalar(x_69)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_69;
 lean::cnstr_set_tag(x_69, 0);
}
lean::cnstr_set(x_81, 0, x_78);
x_3 = x_81;
x_4 = x_74;
goto lbl_5;
}
else
{
obj* x_84; obj* x_85; obj* x_87; 
lean::dec(x_72);
lean::dec(x_69);
x_84 = l_lean_ir_cpp_emit__eos(x_1, x_74);
x_85 = lean::cnstr_get(x_84, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_84, 1);
lean::inc(x_87);
lean::dec(x_84);
x_3 = x_85;
x_4 = x_87;
goto lbl_5;
}
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_90; obj* x_92; obj* x_93; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_90 = lean::cnstr_get(x_3, 0);
lean::inc(x_90);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_92 = x_3;
} else {
 lean::dec(x_3);
 x_92 = lean::box(0);
}
x_93 = l_lean_ir_terminator_to__format___main(x_0);
x_94 = 0;
x_95 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
x_96 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_93);
lean::cnstr_set_scalar(x_96, sizeof(void*)*2, x_94);
x_97 = x_96;
x_98 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_99 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_99, 0, x_97);
lean::cnstr_set(x_99, 1, x_98);
lean::cnstr_set_scalar(x_99, sizeof(void*)*2, x_94);
x_100 = x_99;
x_101 = lean::box(1);
x_102 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_102, 0, x_100);
lean::cnstr_set(x_102, 1, x_101);
lean::cnstr_set_scalar(x_102, sizeof(void*)*2, x_94);
x_103 = x_102;
x_104 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_90);
lean::cnstr_set_scalar(x_104, sizeof(void*)*2, x_94);
x_105 = x_104;
if (lean::is_scalar(x_92)) {
 x_106 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_106 = x_92;
}
lean::cnstr_set(x_106, 0, x_105);
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_4);
return x_107;
}
else
{
obj* x_109; 
lean::dec(x_0);
x_109 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_109, 0, x_3);
lean::cnstr_set(x_109, 1, x_4);
return x_109;
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
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_3 = l_lean_ir_cpp_emit__type__size___closed__1;
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
} else {
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_14 = x_6;
} else {
 lean::dec(x_6);
 x_14 = lean::box(0);
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
obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_17 = x_6;
} else {
 lean::dec(x_6);
 x_17 = lean::box(0);
}
x_18 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_20 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_18, x_1, x_8);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_27; obj* x_30; obj* x_31; 
lean::dec(x_1);
x_27 = lean::cnstr_get(x_21, 0);
lean::inc(x_27);
lean::dec(x_21);
if (lean::is_scalar(x_17)) {
 x_30 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_30 = x_17;
 lean::cnstr_set_tag(x_17, 0);
}
lean::cnstr_set(x_30, 0, x_27);
if (lean::is_scalar(x_10)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_10;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_23);
return x_31;
}
else
{
obj* x_34; obj* x_35; obj* x_37; 
lean::dec(x_21);
lean::inc(x_1);
x_34 = l_lean_ir_cpp_emit__type(x_0, x_1, x_23);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
if (lean::obj_tag(x_35) == 0)
{
obj* x_41; obj* x_44; obj* x_45; 
lean::dec(x_1);
x_41 = lean::cnstr_get(x_35, 0);
lean::inc(x_41);
lean::dec(x_35);
if (lean::is_scalar(x_17)) {
 x_44 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_44 = x_17;
 lean::cnstr_set_tag(x_17, 0);
}
lean::cnstr_set(x_44, 0, x_41);
if (lean::is_scalar(x_10)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_10;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_37);
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_50; obj* x_51; obj* x_53; 
x_46 = lean::cnstr_get(x_35, 0);
lean::inc(x_46);
lean::dec(x_35);
x_49 = l_option_has__repr___rarg___closed__3;
x_50 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_49, x_1, x_37);
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_50, 1);
lean::inc(x_53);
lean::dec(x_50);
if (lean::obj_tag(x_51) == 0)
{
obj* x_57; obj* x_60; obj* x_61; 
lean::dec(x_46);
x_57 = lean::cnstr_get(x_51, 0);
lean::inc(x_57);
lean::dec(x_51);
if (lean::is_scalar(x_17)) {
 x_60 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_60 = x_17;
 lean::cnstr_set_tag(x_17, 0);
}
lean::cnstr_set(x_60, 0, x_57);
if (lean::is_scalar(x_10)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_10;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_53);
return x_61;
}
else
{
obj* x_63; obj* x_64; 
lean::dec(x_51);
if (lean::is_scalar(x_17)) {
 x_63 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_63 = x_17;
}
lean::cnstr_set(x_63, 0, x_46);
if (lean::is_scalar(x_10)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_10;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_53);
return x_64;
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
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
} else {
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
} else {
 lean::dec(x_6);
 x_15 = lean::box(0);
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
obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
} else {
 lean::dec(x_6);
 x_18 = lean::box(0);
}
x_19 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_2, x_8);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_29; obj* x_32; obj* x_33; 
lean::dec(x_1);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
lean::dec(x_22);
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_10)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_10;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_24);
return x_33;
}
else
{
obj* x_36; obj* x_37; obj* x_39; 
lean::dec(x_22);
lean::inc(x_2);
x_36 = l_lean_ir_cpp_emit__var(x_1, x_2, x_24);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
if (lean::obj_tag(x_37) == 0)
{
obj* x_43; obj* x_46; obj* x_47; 
lean::dec(x_2);
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
if (lean::is_scalar(x_10)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_10;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_39);
return x_47;
}
else
{
obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_55; 
x_48 = lean::cnstr_get(x_37, 0);
lean::inc(x_48);
lean::dec(x_37);
x_51 = l_option_has__repr___rarg___closed__3;
x_52 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_51, x_2, x_39);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
if (lean::obj_tag(x_53) == 0)
{
obj* x_59; obj* x_62; obj* x_63; 
lean::dec(x_48);
x_59 = lean::cnstr_get(x_53, 0);
lean::inc(x_59);
lean::dec(x_53);
if (lean::is_scalar(x_18)) {
 x_62 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_62 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_62, 0, x_59);
if (lean::is_scalar(x_10)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_10;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_55);
return x_63;
}
else
{
obj* x_65; obj* x_66; 
lean::dec(x_53);
if (lean::is_scalar(x_18)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_18;
}
lean::cnstr_set(x_65, 0, x_48);
if (lean::is_scalar(x_10)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_10;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_55);
return x_66;
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
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_18 = x_11;
} else {
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
obj* x_21; obj* x_23; obj* x_24; obj* x_26; 
lean::dec(x_11);
x_21 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_4);
x_23 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_21, x_4, x_13);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
x_6 = x_24;
x_7 = x_26;
goto lbl_8;
}
lbl_8:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_33 = lean::cnstr_get(x_6, 0);
lean::inc(x_33);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_35 = x_6;
} else {
 lean::dec(x_6);
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
lean::cnstr_set(x_37, 1, x_7);
return x_37;
}
else
{
obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_45; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_38 = x_6;
} else {
 lean::dec(x_6);
 x_38 = lean::box(0);
}
lean::inc(x_4);
x_40 = l_lean_ir_cpp_emit__var(x_1, x_4, x_7);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 lean::cnstr_release(x_40, 1);
 x_45 = x_40;
} else {
 lean::dec(x_40);
 x_45 = lean::box(0);
}
if (lean::obj_tag(x_41) == 0)
{
obj* x_49; obj* x_52; obj* x_53; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_49 = lean::cnstr_get(x_41, 0);
lean::inc(x_49);
lean::dec(x_41);
if (lean::is_scalar(x_38)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_38;
 lean::cnstr_set_tag(x_38, 0);
}
lean::cnstr_set(x_52, 0, x_49);
if (lean::is_scalar(x_45)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_45;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_43);
return x_53;
}
else
{
obj* x_55; obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_41);
x_55 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_4);
x_57 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_55, x_4, x_43);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_66; obj* x_69; obj* x_70; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_66 = lean::cnstr_get(x_58, 0);
lean::inc(x_66);
lean::dec(x_58);
if (lean::is_scalar(x_38)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_38;
 lean::cnstr_set_tag(x_38, 0);
}
lean::cnstr_set(x_69, 0, x_66);
if (lean::is_scalar(x_45)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_45;
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
x_73 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_4, x_60);
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
if (lean::is_scalar(x_38)) {
 x_84 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_84 = x_38;
 lean::cnstr_set_tag(x_38, 0);
}
lean::cnstr_set(x_84, 0, x_81);
if (lean::is_scalar(x_45)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_45;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_76);
return x_85;
}
else
{
obj* x_88; obj* x_89; obj* x_91; 
lean::dec(x_74);
lean::inc(x_4);
x_88 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_55, x_4, x_76);
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_88, 1);
lean::inc(x_91);
lean::dec(x_88);
if (lean::obj_tag(x_89) == 0)
{
obj* x_96; obj* x_99; obj* x_100; 
lean::dec(x_4);
lean::dec(x_2);
x_96 = lean::cnstr_get(x_89, 0);
lean::inc(x_96);
lean::dec(x_89);
if (lean::is_scalar(x_38)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_38;
 lean::cnstr_set_tag(x_38, 0);
}
lean::cnstr_set(x_99, 0, x_96);
if (lean::is_scalar(x_45)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_45;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_91);
return x_100;
}
else
{
obj* x_104; 
lean::dec(x_45);
lean::dec(x_38);
lean::dec(x_89);
x_104 = l_lean_ir_cpp_emit__var(x_2, x_4, x_91);
return x_104;
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
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_19 = x_11;
} else {
 lean::dec(x_11);
 x_19 = lean::box(0);
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
obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_27; 
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_21 = x_11;
} else {
 lean::dec(x_11);
 x_21 = lean::box(0);
}
x_22 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_4);
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_4, x_13);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_31; obj* x_34; 
lean::dec(x_3);
x_31 = lean::cnstr_get(x_25, 0);
lean::inc(x_31);
lean::dec(x_25);
if (lean::is_scalar(x_21)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_21;
 lean::cnstr_set_tag(x_21, 0);
}
lean::cnstr_set(x_34, 0, x_31);
x_6 = x_34;
x_7 = x_27;
goto lbl_8;
}
else
{
obj* x_38; obj* x_39; obj* x_41; 
lean::dec(x_21);
lean::dec(x_25);
lean::inc(x_4);
x_38 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_4, x_27);
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
obj* x_47; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
x_47 = lean::cnstr_get(x_6, 0);
lean::inc(x_47);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_49 = x_6;
} else {
 lean::dec(x_6);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_47);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_7);
return x_51;
}
else
{
obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_60; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_52 = x_6;
} else {
 lean::dec(x_6);
 x_52 = lean::box(0);
}
x_53 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_4);
x_55 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_53, x_4, x_7);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 lean::cnstr_release(x_55, 1);
 x_60 = x_55;
} else {
 lean::dec(x_55);
 x_60 = lean::box(0);
}
if (lean::obj_tag(x_56) == 0)
{
obj* x_64; obj* x_67; obj* x_68; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
x_64 = lean::cnstr_get(x_56, 0);
lean::inc(x_64);
lean::dec(x_56);
if (lean::is_scalar(x_52)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_52;
 lean::cnstr_set_tag(x_52, 0);
}
lean::cnstr_set(x_67, 0, x_64);
if (lean::is_scalar(x_60)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_60;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_58);
return x_68;
}
else
{
obj* x_71; obj* x_72; obj* x_74; 
lean::dec(x_56);
lean::inc(x_4);
x_71 = l_lean_ir_cpp_emit__var(x_1, x_4, x_58);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
lean::dec(x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_79; obj* x_82; obj* x_83; 
lean::dec(x_4);
lean::dec(x_2);
x_79 = lean::cnstr_get(x_72, 0);
lean::inc(x_79);
lean::dec(x_72);
if (lean::is_scalar(x_52)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_52;
 lean::cnstr_set_tag(x_52, 0);
}
lean::cnstr_set(x_82, 0, x_79);
if (lean::is_scalar(x_60)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_60;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_74);
return x_83;
}
else
{
obj* x_85; obj* x_87; obj* x_88; obj* x_90; 
lean::dec(x_72);
x_85 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_4);
x_87 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_85, x_4, x_74);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_87, 1);
lean::inc(x_90);
lean::dec(x_87);
if (lean::obj_tag(x_88) == 0)
{
obj* x_95; obj* x_98; obj* x_99; 
lean::dec(x_4);
lean::dec(x_2);
x_95 = lean::cnstr_get(x_88, 0);
lean::inc(x_95);
lean::dec(x_88);
if (lean::is_scalar(x_52)) {
 x_98 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_98 = x_52;
 lean::cnstr_set_tag(x_52, 0);
}
lean::cnstr_set(x_98, 0, x_95);
if (lean::is_scalar(x_60)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_60;
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_90);
return x_99;
}
else
{
obj* x_102; obj* x_103; obj* x_105; 
lean::dec(x_88);
lean::inc(x_4);
x_102 = l_lean_ir_cpp_emit__var(x_2, x_4, x_90);
x_103 = lean::cnstr_get(x_102, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_102, 1);
lean::inc(x_105);
lean::dec(x_102);
if (lean::obj_tag(x_103) == 0)
{
obj* x_109; obj* x_112; obj* x_113; 
lean::dec(x_4);
x_109 = lean::cnstr_get(x_103, 0);
lean::inc(x_109);
lean::dec(x_103);
if (lean::is_scalar(x_52)) {
 x_112 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_112 = x_52;
 lean::cnstr_set_tag(x_52, 0);
}
lean::cnstr_set(x_112, 0, x_109);
if (lean::is_scalar(x_60)) {
 x_113 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_113 = x_60;
}
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_105);
return x_113;
}
else
{
obj* x_114; obj* x_117; obj* x_118; obj* x_119; obj* x_121; 
x_114 = lean::cnstr_get(x_103, 0);
lean::inc(x_114);
lean::dec(x_103);
x_117 = l_option_has__repr___rarg___closed__3;
x_118 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_117, x_4, x_105);
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_118, 1);
lean::inc(x_121);
lean::dec(x_118);
if (lean::obj_tag(x_119) == 0)
{
obj* x_125; obj* x_128; obj* x_129; 
lean::dec(x_114);
x_125 = lean::cnstr_get(x_119, 0);
lean::inc(x_125);
lean::dec(x_119);
if (lean::is_scalar(x_52)) {
 x_128 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_128 = x_52;
 lean::cnstr_set_tag(x_52, 0);
}
lean::cnstr_set(x_128, 0, x_125);
if (lean::is_scalar(x_60)) {
 x_129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_129 = x_60;
}
lean::cnstr_set(x_129, 0, x_128);
lean::cnstr_set(x_129, 1, x_121);
return x_129;
}
else
{
obj* x_131; obj* x_132; 
lean::dec(x_119);
if (lean::is_scalar(x_52)) {
 x_131 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_131 = x_52;
}
lean::cnstr_set(x_131, 0, x_114);
if (lean::is_scalar(x_60)) {
 x_132 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_132 = x_60;
}
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_121);
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
obj* l_lean_ir_cpp_emit__arith(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
switch (x_0) {
case 11:
{
obj* x_9; 
lean::dec(x_4);
x_9 = l_lean_ir_cpp_emit__big__binop(x_1, x_2, x_3, x_5, x_6, x_7);
return x_9;
}
default:
{
obj* x_11; 
lean::dec(x_5);
x_11 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_4, x_6, x_7);
return x_11;
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
case 11:
{
obj* x_14; 
lean::dec(x_5);
lean::dec(x_4);
x_14 = l_lean_ir_cpp_emit__big__binop(x_1, x_2, x_3, x_6, x_7, x_8);
return x_14;
}
default:
{
obj* x_17; 
lean::dec(x_4);
lean::dec(x_6);
x_17 = l_lean_ir_cpp_emit__infix(x_1, x_2, x_3, x_5, x_7, x_8);
return x_17;
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
obj* x_12; obj* x_13; obj* x_14; 
x_12 = l_lean_ir_cpp_emit__assign__binop___closed__2;
x_13 = l_lean_ir_cpp_emit__assign__binop___closed__3;
x_14 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_12, x_13, x_5, x_6);
return x_14;
}
case 1:
{
obj* x_15; obj* x_16; obj* x_17; 
x_15 = l_int_repr___main___closed__2;
x_16 = l_lean_ir_cpp_emit__assign__binop___closed__4;
x_17 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_15, x_16, x_5, x_6);
return x_17;
}
case 2:
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = l_lean_ir_cpp_emit__assign__binop___closed__5;
x_19 = l_lean_ir_cpp_emit__assign__binop___closed__6;
x_20 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_18, x_19, x_5, x_6);
return x_20;
}
case 3:
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = l_lean_ir_cpp_emit__assign__binop___closed__7;
x_22 = l_lean_ir_cpp_emit__assign__binop___closed__8;
x_23 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_21, x_22, x_5, x_6);
return x_23;
}
case 4:
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = l_lean_ir_cpp_emit__assign__binop___closed__9;
x_25 = l_lean_ir_cpp_emit__assign__binop___closed__10;
x_26 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_24, x_25, x_5, x_6);
return x_26;
}
case 5:
{
obj* x_27; obj* x_28; 
x_27 = l_lean_ir_cpp_emit__assign__binop___closed__11;
x_28 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_27, x_5, x_6);
return x_28;
}
case 6:
{
obj* x_29; obj* x_30; 
x_29 = l_lean_ir_cpp_emit__assign__binop___closed__12;
x_30 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_29, x_5, x_6);
return x_30;
}
case 7:
{
obj* x_31; obj* x_32; 
x_31 = l_lean_ir_cpp_emit__assign__binop___closed__13;
x_32 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_31, x_5, x_6);
return x_32;
}
case 8:
{
obj* x_33; obj* x_34; 
x_33 = l_lean_ir_cpp_emit__assign__binop___closed__14;
x_34 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_33, x_5, x_6);
return x_34;
}
case 9:
{
obj* x_35; obj* x_36; 
x_35 = l_lean_ir_cpp_emit__assign__binop___closed__15;
x_36 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_35, x_5, x_6);
return x_36;
}
case 10:
{
obj* x_37; obj* x_38; 
x_37 = l_lean_ir_cpp_emit__assign__binop___closed__16;
x_38 = l_lean_ir_cpp_emit__infix(x_0, x_3, x_4, x_37, x_5, x_6);
return x_38;
}
case 11:
{
obj* x_39; obj* x_40; 
x_39 = l_lean_ir_cpp_emit__assign__binop___closed__17;
x_40 = l_lean_ir_cpp_emit__infix(x_0, x_3, x_4, x_39, x_5, x_6);
return x_40;
}
case 12:
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_41 = l_lean_ir_cpp_emit__assign__binop___closed__18;
x_42 = l_lean_ir_cpp_emit__assign__binop___closed__19;
x_43 = l_lean_ir_cpp_emit__assign__binop___closed__20;
x_44 = l_lean_ir_cpp_emit__logical__arith(x_1, x_0, x_3, x_4, x_41, x_42, x_43, x_5, x_6);
return x_44;
}
case 13:
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_45 = l_lean_ir_cpp_emit__assign__binop___closed__21;
x_46 = l_lean_ir_cpp_emit__assign__binop___closed__22;
x_47 = l_lean_ir_cpp_emit__assign__binop___closed__23;
x_48 = l_lean_ir_cpp_emit__logical__arith(x_1, x_0, x_3, x_4, x_45, x_46, x_47, x_5, x_6);
return x_48;
}
case 14:
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_49 = l_lean_ir_cpp_emit__assign__binop___closed__24;
x_50 = l_lean_ir_cpp_emit__assign__binop___closed__25;
x_51 = l_lean_ir_cpp_emit__assign__binop___closed__26;
x_52 = l_lean_ir_cpp_emit__logical__arith(x_1, x_0, x_3, x_4, x_49, x_50, x_51, x_5, x_6);
return x_52;
}
case 15:
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = l_lean_ir_cpp_emit__assign__binop___closed__27;
x_54 = l_lean_ir_cpp_emit__assign__binop___closed__28;
x_55 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_53, x_54, x_5, x_6);
return x_55;
}
case 16:
{
obj* x_56; obj* x_57; obj* x_58; 
x_56 = l_lean_ir_cpp_emit__template__params___closed__1;
x_57 = l_lean_ir_cpp_emit__assign__binop___closed__29;
x_58 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_56, x_57, x_5, x_6);
return x_58;
}
case 17:
{
obj* x_59; obj* x_60; obj* x_61; 
x_59 = l_lean_ir_cpp_emit__assign__binop___closed__30;
x_60 = l_lean_ir_cpp_emit__assign__binop___closed__31;
x_61 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_59, x_60, x_5, x_6);
return x_61;
}
case 18:
{
obj* x_62; obj* x_63; obj* x_64; 
x_62 = l_lean_ir_cpp_emit__assign__binop___closed__24;
x_63 = l_lean_ir_cpp_emit__assign__binop___closed__32;
x_64 = l_lean_ir_cpp_emit__arith(x_1, x_0, x_3, x_4, x_62, x_63, x_5, x_6);
return x_64;
}
case 19:
{
obj* x_65; obj* x_66; 
x_65 = l_lean_ir_cpp_emit__assign__binop___closed__33;
x_66 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_65, x_5, x_6);
return x_66;
}
case 20:
{
obj* x_67; obj* x_68; 
x_67 = l_lean_ir_cpp_emit__assign__binop___closed__34;
x_68 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_67, x_5, x_6);
return x_68;
}
case 21:
{
obj* x_69; obj* x_70; 
x_69 = l_lean_ir_cpp_emit__assign__binop___closed__35;
x_70 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_69, x_5, x_6);
return x_70;
}
case 22:
{
obj* x_71; obj* x_72; 
x_71 = l_lean_ir_cpp_emit__assign__binop___closed__36;
x_72 = l_lean_ir_cpp_emit__big__binop(x_0, x_3, x_4, x_71, x_5, x_6);
return x_72;
}
case 23:
{
switch (x_1) {
case 11:
{
obj* x_74; obj* x_75; obj* x_77; 
lean::inc(x_5);
x_74 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
lean::dec(x_74);
if (lean::obj_tag(x_75) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
x_80 = lean::cnstr_get(x_75, 0);
lean::inc(x_80);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 x_82 = x_75;
} else {
 lean::dec(x_75);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_80);
x_9 = x_83;
x_10 = x_77;
goto lbl_11;
}
else
{
obj* x_85; obj* x_87; obj* x_88; obj* x_90; 
lean::dec(x_75);
x_85 = l_lean_ir_cpp_emit__assign__binop___closed__37;
lean::inc(x_5);
x_87 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_85, x_5, x_77);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_87, 1);
lean::inc(x_90);
lean::dec(x_87);
x_9 = x_88;
x_10 = x_90;
goto lbl_11;
}
}
default:
{
obj* x_93; 
x_93 = lean::box(0);
x_7 = x_93;
goto lbl_8;
}
}
}
case 24:
{
obj* x_95; obj* x_96; obj* x_98; obj* x_100; 
lean::inc(x_5);
x_95 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_95, 1);
lean::inc(x_98);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 lean::cnstr_release(x_95, 1);
 x_100 = x_95;
} else {
 lean::dec(x_95);
 x_100 = lean::box(0);
}
if (lean::obj_tag(x_96) == 0)
{
obj* x_104; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_104 = lean::cnstr_get(x_96, 0);
lean::inc(x_104);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_106 = x_96;
} else {
 lean::dec(x_96);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_104);
if (lean::is_scalar(x_100)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_100;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_98);
return x_108;
}
else
{
obj* x_109; obj* x_110; obj* x_112; obj* x_113; obj* x_115; 
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_109 = x_96;
} else {
 lean::dec(x_96);
 x_109 = lean::box(0);
}
x_110 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_5);
x_112 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_110, x_5, x_98);
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_112, 1);
lean::inc(x_115);
lean::dec(x_112);
if (lean::obj_tag(x_113) == 0)
{
obj* x_121; obj* x_124; obj* x_125; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_121 = lean::cnstr_get(x_113, 0);
lean::inc(x_121);
lean::dec(x_113);
if (lean::is_scalar(x_109)) {
 x_124 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_124 = x_109;
 lean::cnstr_set_tag(x_109, 0);
}
lean::cnstr_set(x_124, 0, x_121);
if (lean::is_scalar(x_100)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_100;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_115);
return x_125;
}
else
{
obj* x_129; obj* x_132; 
lean::dec(x_109);
lean::dec(x_113);
lean::dec(x_100);
x_129 = lean::cnstr_get(x_5, 1);
lean::inc(x_129);
lean::inc(x_4);
x_132 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_129, x_4);
if (lean::obj_tag(x_132) == 0)
{
obj* x_133; obj* x_135; obj* x_136; obj* x_138; 
x_133 = l_lean_ir_cpp_emit__assign__binop___closed__38;
lean::inc(x_5);
x_135 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_133, x_5, x_115);
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_135, 1);
lean::inc(x_138);
lean::dec(x_135);
x_9 = x_136;
x_10 = x_138;
goto lbl_11;
}
else
{
obj* x_141; uint8 x_144; obj* x_146; obj* x_147; uint8 x_148; 
x_141 = lean::cnstr_get(x_132, 0);
lean::inc(x_141);
lean::dec(x_132);
x_144 = lean::unbox(x_141);
lean::dec(x_141);
x_146 = l_lean_ir_type2id___main(x_144);
x_147 = l_lean_ir_valid__assign__unop__types___closed__1;
x_148 = lean::nat_dec_eq(x_146, x_147);
lean::dec(x_146);
if (x_148 == 0)
{
obj* x_150; obj* x_152; obj* x_153; obj* x_155; 
x_150 = l_lean_ir_cpp_emit__assign__binop___closed__38;
lean::inc(x_5);
x_152 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_150, x_5, x_115);
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_152, 1);
lean::inc(x_155);
lean::dec(x_152);
x_9 = x_153;
x_10 = x_155;
goto lbl_11;
}
else
{
obj* x_158; obj* x_160; obj* x_161; obj* x_163; 
x_158 = l_lean_ir_cpp_emit__assign__binop___closed__39;
lean::inc(x_5);
x_160 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_158, x_5, x_115);
x_161 = lean::cnstr_get(x_160, 0);
lean::inc(x_161);
x_163 = lean::cnstr_get(x_160, 1);
lean::inc(x_163);
lean::dec(x_160);
x_9 = x_161;
x_10 = x_163;
goto lbl_11;
}
}
}
}
}
case 25:
{
obj* x_167; obj* x_168; obj* x_170; 
lean::inc(x_5);
x_167 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_168 = lean::cnstr_get(x_167, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_167, 1);
lean::inc(x_170);
lean::dec(x_167);
if (lean::obj_tag(x_168) == 0)
{
obj* x_173; obj* x_175; obj* x_176; 
x_173 = lean::cnstr_get(x_168, 0);
lean::inc(x_173);
if (lean::is_exclusive(x_168)) {
 lean::cnstr_release(x_168, 0);
 x_175 = x_168;
} else {
 lean::dec(x_168);
 x_175 = lean::box(0);
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_173);
x_9 = x_176;
x_10 = x_170;
goto lbl_11;
}
else
{
obj* x_178; obj* x_180; obj* x_181; obj* x_183; 
lean::dec(x_168);
x_178 = l_lean_ir_cpp_emit__assign__binop___closed__40;
lean::inc(x_5);
x_180 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_178, x_5, x_170);
x_181 = lean::cnstr_get(x_180, 0);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_180, 1);
lean::inc(x_183);
lean::dec(x_180);
x_9 = x_181;
x_10 = x_183;
goto lbl_11;
}
}
default:
{
obj* x_187; obj* x_188; obj* x_190; 
lean::inc(x_5);
x_187 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
x_190 = lean::cnstr_get(x_187, 1);
lean::inc(x_190);
lean::dec(x_187);
if (lean::obj_tag(x_188) == 0)
{
obj* x_193; obj* x_195; obj* x_196; 
x_193 = lean::cnstr_get(x_188, 0);
lean::inc(x_193);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 x_195 = x_188;
} else {
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
obj* x_198; obj* x_200; obj* x_201; obj* x_203; 
lean::dec(x_188);
x_198 = l_lean_ir_cpp_emit__assign__binop___closed__41;
lean::inc(x_5);
x_200 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_198, x_5, x_190);
x_201 = lean::cnstr_get(x_200, 0);
lean::inc(x_201);
x_203 = lean::cnstr_get(x_200, 1);
lean::inc(x_203);
lean::dec(x_200);
x_9 = x_201;
x_10 = x_203;
goto lbl_11;
}
}
}
lbl_8:
{
obj* x_207; obj* x_208; obj* x_211; obj* x_212; obj* x_214; 
lean::dec(x_7);
lean::inc(x_5);
x_211 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_212 = lean::cnstr_get(x_211, 0);
lean::inc(x_212);
x_214 = lean::cnstr_get(x_211, 1);
lean::inc(x_214);
lean::dec(x_211);
if (lean::obj_tag(x_212) == 0)
{
obj* x_217; obj* x_219; obj* x_220; 
x_217 = lean::cnstr_get(x_212, 0);
lean::inc(x_217);
if (lean::is_exclusive(x_212)) {
 lean::cnstr_release(x_212, 0);
 x_219 = x_212;
} else {
 lean::dec(x_212);
 x_219 = lean::box(0);
}
if (lean::is_scalar(x_219)) {
 x_220 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_220 = x_219;
}
lean::cnstr_set(x_220, 0, x_217);
x_207 = x_220;
x_208 = x_214;
goto lbl_209;
}
else
{
obj* x_221; obj* x_222; obj* x_224; obj* x_225; obj* x_227; 
if (lean::is_exclusive(x_212)) {
 lean::cnstr_release(x_212, 0);
 x_221 = x_212;
} else {
 lean::dec(x_212);
 x_221 = lean::box(0);
}
x_222 = l_lean_ir_cpp_emit__assign__binop___closed__1;
lean::inc(x_5);
x_224 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_222, x_5, x_214);
x_225 = lean::cnstr_get(x_224, 0);
lean::inc(x_225);
x_227 = lean::cnstr_get(x_224, 1);
lean::inc(x_227);
lean::dec(x_224);
if (lean::obj_tag(x_225) == 0)
{
obj* x_230; obj* x_233; 
x_230 = lean::cnstr_get(x_225, 0);
lean::inc(x_230);
lean::dec(x_225);
if (lean::is_scalar(x_221)) {
 x_233 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_233 = x_221;
 lean::cnstr_set_tag(x_221, 0);
}
lean::cnstr_set(x_233, 0, x_230);
x_207 = x_233;
x_208 = x_227;
goto lbl_209;
}
else
{
obj* x_237; obj* x_238; obj* x_240; 
lean::dec(x_225);
lean::dec(x_221);
lean::inc(x_5);
x_237 = l_lean_ir_cpp_emit__template__param(x_1, x_5, x_227);
x_238 = lean::cnstr_get(x_237, 0);
lean::inc(x_238);
x_240 = lean::cnstr_get(x_237, 1);
lean::inc(x_240);
lean::dec(x_237);
x_207 = x_238;
x_208 = x_240;
goto lbl_209;
}
}
lbl_209:
{
if (lean::obj_tag(x_207) == 0)
{
obj* x_246; obj* x_248; obj* x_249; obj* x_250; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_246 = lean::cnstr_get(x_207, 0);
lean::inc(x_246);
if (lean::is_exclusive(x_207)) {
 lean::cnstr_release(x_207, 0);
 x_248 = x_207;
} else {
 lean::dec(x_207);
 x_248 = lean::box(0);
}
if (lean::is_scalar(x_248)) {
 x_249 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_249 = x_248;
}
lean::cnstr_set(x_249, 0, x_246);
x_250 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_250, 0, x_249);
lean::cnstr_set(x_250, 1, x_208);
return x_250;
}
else
{
obj* x_251; obj* x_252; obj* x_254; obj* x_255; obj* x_257; obj* x_259; 
if (lean::is_exclusive(x_207)) {
 lean::cnstr_release(x_207, 0);
 x_251 = x_207;
} else {
 lean::dec(x_207);
 x_251 = lean::box(0);
}
x_252 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_5);
x_254 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_252, x_5, x_208);
x_255 = lean::cnstr_get(x_254, 0);
lean::inc(x_255);
x_257 = lean::cnstr_get(x_254, 1);
lean::inc(x_257);
if (lean::is_exclusive(x_254)) {
 lean::cnstr_release(x_254, 0);
 lean::cnstr_release(x_254, 1);
 x_259 = x_254;
} else {
 lean::dec(x_254);
 x_259 = lean::box(0);
}
if (lean::obj_tag(x_255) == 0)
{
obj* x_263; obj* x_266; obj* x_267; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_263 = lean::cnstr_get(x_255, 0);
lean::inc(x_263);
lean::dec(x_255);
if (lean::is_scalar(x_251)) {
 x_266 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_266 = x_251;
 lean::cnstr_set_tag(x_251, 0);
}
lean::cnstr_set(x_266, 0, x_263);
if (lean::is_scalar(x_259)) {
 x_267 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_267 = x_259;
}
lean::cnstr_set(x_267, 0, x_266);
lean::cnstr_set(x_267, 1, x_257);
return x_267;
}
else
{
obj* x_270; obj* x_271; obj* x_273; 
lean::dec(x_255);
lean::inc(x_5);
x_270 = l_lean_ir_cpp_emit__var(x_3, x_5, x_257);
x_271 = lean::cnstr_get(x_270, 0);
lean::inc(x_271);
x_273 = lean::cnstr_get(x_270, 1);
lean::inc(x_273);
lean::dec(x_270);
if (lean::obj_tag(x_271) == 0)
{
obj* x_278; obj* x_281; obj* x_282; 
lean::dec(x_5);
lean::dec(x_4);
x_278 = lean::cnstr_get(x_271, 0);
lean::inc(x_278);
lean::dec(x_271);
if (lean::is_scalar(x_251)) {
 x_281 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_281 = x_251;
 lean::cnstr_set_tag(x_251, 0);
}
lean::cnstr_set(x_281, 0, x_278);
if (lean::is_scalar(x_259)) {
 x_282 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_282 = x_259;
}
lean::cnstr_set(x_282, 0, x_281);
lean::cnstr_set(x_282, 1, x_273);
return x_282;
}
else
{
obj* x_284; obj* x_286; obj* x_287; obj* x_289; 
lean::dec(x_271);
x_284 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_5);
x_286 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_284, x_5, x_273);
x_287 = lean::cnstr_get(x_286, 0);
lean::inc(x_287);
x_289 = lean::cnstr_get(x_286, 1);
lean::inc(x_289);
lean::dec(x_286);
if (lean::obj_tag(x_287) == 0)
{
obj* x_294; obj* x_297; obj* x_298; 
lean::dec(x_5);
lean::dec(x_4);
x_294 = lean::cnstr_get(x_287, 0);
lean::inc(x_294);
lean::dec(x_287);
if (lean::is_scalar(x_251)) {
 x_297 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_297 = x_251;
 lean::cnstr_set_tag(x_251, 0);
}
lean::cnstr_set(x_297, 0, x_294);
if (lean::is_scalar(x_259)) {
 x_298 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_298 = x_259;
}
lean::cnstr_set(x_298, 0, x_297);
lean::cnstr_set(x_298, 1, x_289);
return x_298;
}
else
{
obj* x_301; obj* x_302; obj* x_304; 
lean::dec(x_287);
lean::inc(x_5);
x_301 = l_lean_ir_cpp_emit__var(x_4, x_5, x_289);
x_302 = lean::cnstr_get(x_301, 0);
lean::inc(x_302);
x_304 = lean::cnstr_get(x_301, 1);
lean::inc(x_304);
lean::dec(x_301);
if (lean::obj_tag(x_302) == 0)
{
obj* x_308; obj* x_311; obj* x_312; 
lean::dec(x_5);
x_308 = lean::cnstr_get(x_302, 0);
lean::inc(x_308);
lean::dec(x_302);
if (lean::is_scalar(x_251)) {
 x_311 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_311 = x_251;
 lean::cnstr_set_tag(x_251, 0);
}
lean::cnstr_set(x_311, 0, x_308);
if (lean::is_scalar(x_259)) {
 x_312 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_312 = x_259;
}
lean::cnstr_set(x_312, 0, x_311);
lean::cnstr_set(x_312, 1, x_304);
return x_312;
}
else
{
obj* x_313; obj* x_316; obj* x_317; obj* x_318; obj* x_320; 
x_313 = lean::cnstr_get(x_302, 0);
lean::inc(x_313);
lean::dec(x_302);
x_316 = l_option_has__repr___rarg___closed__3;
x_317 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_316, x_5, x_304);
x_318 = lean::cnstr_get(x_317, 0);
lean::inc(x_318);
x_320 = lean::cnstr_get(x_317, 1);
lean::inc(x_320);
lean::dec(x_317);
if (lean::obj_tag(x_318) == 0)
{
obj* x_324; obj* x_327; obj* x_328; 
lean::dec(x_313);
x_324 = lean::cnstr_get(x_318, 0);
lean::inc(x_324);
lean::dec(x_318);
if (lean::is_scalar(x_251)) {
 x_327 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_327 = x_251;
 lean::cnstr_set_tag(x_251, 0);
}
lean::cnstr_set(x_327, 0, x_324);
if (lean::is_scalar(x_259)) {
 x_328 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_328 = x_259;
}
lean::cnstr_set(x_328, 0, x_327);
lean::cnstr_set(x_328, 1, x_320);
return x_328;
}
else
{
obj* x_330; obj* x_331; 
lean::dec(x_318);
if (lean::is_scalar(x_251)) {
 x_330 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_330 = x_251;
}
lean::cnstr_set(x_330, 0, x_313);
if (lean::is_scalar(x_259)) {
 x_331 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_331 = x_259;
}
lean::cnstr_set(x_331, 0, x_330);
lean::cnstr_set(x_331, 1, x_320);
return x_331;
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
obj* x_335; obj* x_337; obj* x_338; obj* x_339; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_335 = lean::cnstr_get(x_9, 0);
lean::inc(x_335);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_337 = x_9;
} else {
 lean::dec(x_9);
 x_337 = lean::box(0);
}
if (lean::is_scalar(x_337)) {
 x_338 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_338 = x_337;
}
lean::cnstr_set(x_338, 0, x_335);
x_339 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_339, 0, x_338);
lean::cnstr_set(x_339, 1, x_10);
return x_339;
}
else
{
obj* x_340; obj* x_341; obj* x_343; obj* x_344; obj* x_346; obj* x_348; 
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_340 = x_9;
} else {
 lean::dec(x_9);
 x_340 = lean::box(0);
}
x_341 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_5);
x_343 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_341, x_5, x_10);
x_344 = lean::cnstr_get(x_343, 0);
lean::inc(x_344);
x_346 = lean::cnstr_get(x_343, 1);
lean::inc(x_346);
if (lean::is_exclusive(x_343)) {
 lean::cnstr_release(x_343, 0);
 lean::cnstr_release(x_343, 1);
 x_348 = x_343;
} else {
 lean::dec(x_343);
 x_348 = lean::box(0);
}
if (lean::obj_tag(x_344) == 0)
{
obj* x_352; obj* x_355; obj* x_356; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_352 = lean::cnstr_get(x_344, 0);
lean::inc(x_352);
lean::dec(x_344);
if (lean::is_scalar(x_340)) {
 x_355 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_355 = x_340;
 lean::cnstr_set_tag(x_340, 0);
}
lean::cnstr_set(x_355, 0, x_352);
if (lean::is_scalar(x_348)) {
 x_356 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_356 = x_348;
}
lean::cnstr_set(x_356, 0, x_355);
lean::cnstr_set(x_356, 1, x_346);
return x_356;
}
else
{
obj* x_359; obj* x_360; obj* x_362; 
lean::dec(x_344);
lean::inc(x_5);
x_359 = l_lean_ir_cpp_emit__var(x_3, x_5, x_346);
x_360 = lean::cnstr_get(x_359, 0);
lean::inc(x_360);
x_362 = lean::cnstr_get(x_359, 1);
lean::inc(x_362);
lean::dec(x_359);
if (lean::obj_tag(x_360) == 0)
{
obj* x_367; obj* x_370; obj* x_371; 
lean::dec(x_5);
lean::dec(x_4);
x_367 = lean::cnstr_get(x_360, 0);
lean::inc(x_367);
lean::dec(x_360);
if (lean::is_scalar(x_340)) {
 x_370 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_370 = x_340;
 lean::cnstr_set_tag(x_340, 0);
}
lean::cnstr_set(x_370, 0, x_367);
if (lean::is_scalar(x_348)) {
 x_371 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_371 = x_348;
}
lean::cnstr_set(x_371, 0, x_370);
lean::cnstr_set(x_371, 1, x_362);
return x_371;
}
else
{
obj* x_373; obj* x_375; obj* x_376; obj* x_378; 
lean::dec(x_360);
x_373 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_5);
x_375 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_373, x_5, x_362);
x_376 = lean::cnstr_get(x_375, 0);
lean::inc(x_376);
x_378 = lean::cnstr_get(x_375, 1);
lean::inc(x_378);
lean::dec(x_375);
if (lean::obj_tag(x_376) == 0)
{
obj* x_383; obj* x_386; obj* x_387; 
lean::dec(x_5);
lean::dec(x_4);
x_383 = lean::cnstr_get(x_376, 0);
lean::inc(x_383);
lean::dec(x_376);
if (lean::is_scalar(x_340)) {
 x_386 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_386 = x_340;
 lean::cnstr_set_tag(x_340, 0);
}
lean::cnstr_set(x_386, 0, x_383);
if (lean::is_scalar(x_348)) {
 x_387 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_387 = x_348;
}
lean::cnstr_set(x_387, 0, x_386);
lean::cnstr_set(x_387, 1, x_378);
return x_387;
}
else
{
obj* x_390; obj* x_391; obj* x_393; 
lean::dec(x_376);
lean::inc(x_5);
x_390 = l_lean_ir_cpp_emit__var(x_4, x_5, x_378);
x_391 = lean::cnstr_get(x_390, 0);
lean::inc(x_391);
x_393 = lean::cnstr_get(x_390, 1);
lean::inc(x_393);
lean::dec(x_390);
if (lean::obj_tag(x_391) == 0)
{
obj* x_397; obj* x_400; obj* x_401; 
lean::dec(x_5);
x_397 = lean::cnstr_get(x_391, 0);
lean::inc(x_397);
lean::dec(x_391);
if (lean::is_scalar(x_340)) {
 x_400 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_400 = x_340;
 lean::cnstr_set_tag(x_340, 0);
}
lean::cnstr_set(x_400, 0, x_397);
if (lean::is_scalar(x_348)) {
 x_401 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_401 = x_348;
}
lean::cnstr_set(x_401, 0, x_400);
lean::cnstr_set(x_401, 1, x_393);
return x_401;
}
else
{
obj* x_402; obj* x_405; obj* x_406; obj* x_407; obj* x_409; 
x_402 = lean::cnstr_get(x_391, 0);
lean::inc(x_402);
lean::dec(x_391);
x_405 = l_option_has__repr___rarg___closed__3;
x_406 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_405, x_5, x_393);
x_407 = lean::cnstr_get(x_406, 0);
lean::inc(x_407);
x_409 = lean::cnstr_get(x_406, 1);
lean::inc(x_409);
lean::dec(x_406);
if (lean::obj_tag(x_407) == 0)
{
obj* x_413; obj* x_416; obj* x_417; 
lean::dec(x_402);
x_413 = lean::cnstr_get(x_407, 0);
lean::inc(x_413);
lean::dec(x_407);
if (lean::is_scalar(x_340)) {
 x_416 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_416 = x_340;
 lean::cnstr_set_tag(x_340, 0);
}
lean::cnstr_set(x_416, 0, x_413);
if (lean::is_scalar(x_348)) {
 x_417 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_417 = x_348;
}
lean::cnstr_set(x_417, 0, x_416);
lean::cnstr_set(x_417, 1, x_409);
return x_417;
}
else
{
obj* x_419; obj* x_420; 
lean::dec(x_407);
if (lean::is_scalar(x_340)) {
 x_419 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_419 = x_340;
}
lean::cnstr_set(x_419, 0, x_402);
if (lean::is_scalar(x_348)) {
 x_420 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_420 = x_348;
}
lean::cnstr_set(x_420, 0, x_419);
lean::cnstr_set(x_420, 1, x_409);
return x_420;
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
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_17 = x_10;
} else {
 lean::dec(x_10);
 x_17 = lean::box(0);
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
obj* x_20; obj* x_22; obj* x_23; obj* x_25; 
lean::dec(x_10);
x_20 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
x_22 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_20, x_3, x_12);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
x_5 = x_23;
x_6 = x_25;
goto lbl_7;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_31 = lean::cnstr_get(x_5, 0);
lean::inc(x_31);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_33 = x_5;
} else {
 lean::dec(x_5);
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
lean::cnstr_set(x_35, 1, x_6);
return x_35;
}
else
{
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_43; 
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_36 = x_5;
} else {
 lean::dec(x_5);
 x_36 = lean::box(0);
}
lean::inc(x_3);
x_38 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1, x_3, x_6);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 x_43 = x_38;
} else {
 lean::dec(x_38);
 x_43 = lean::box(0);
}
if (lean::obj_tag(x_39) == 0)
{
obj* x_46; obj* x_49; obj* x_50; 
lean::dec(x_3);
lean::dec(x_2);
x_46 = lean::cnstr_get(x_39, 0);
lean::inc(x_46);
lean::dec(x_39);
if (lean::is_scalar(x_36)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_36;
 lean::cnstr_set_tag(x_36, 0);
}
lean::cnstr_set(x_49, 0, x_46);
if (lean::is_scalar(x_43)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_43;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_41);
return x_50;
}
else
{
obj* x_52; obj* x_54; obj* x_55; obj* x_57; 
lean::dec(x_39);
x_52 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
x_54 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_52, x_3, x_41);
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
if (lean::obj_tag(x_55) == 0)
{
obj* x_62; obj* x_65; obj* x_66; 
lean::dec(x_3);
lean::dec(x_2);
x_62 = lean::cnstr_get(x_55, 0);
lean::inc(x_62);
lean::dec(x_55);
if (lean::is_scalar(x_36)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_36;
 lean::cnstr_set_tag(x_36, 0);
}
lean::cnstr_set(x_65, 0, x_62);
if (lean::is_scalar(x_43)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_43;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_57);
return x_66;
}
else
{
obj* x_69; obj* x_70; obj* x_72; 
lean::dec(x_55);
lean::inc(x_3);
x_69 = l_lean_ir_cpp_emit__var(x_2, x_3, x_57);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
lean::dec(x_69);
if (lean::obj_tag(x_70) == 0)
{
obj* x_76; obj* x_79; obj* x_80; 
lean::dec(x_3);
x_76 = lean::cnstr_get(x_70, 0);
lean::inc(x_76);
lean::dec(x_70);
if (lean::is_scalar(x_36)) {
 x_79 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_79 = x_36;
 lean::cnstr_set_tag(x_36, 0);
}
lean::cnstr_set(x_79, 0, x_76);
if (lean::is_scalar(x_43)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_43;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_72);
return x_80;
}
else
{
obj* x_81; obj* x_84; obj* x_85; obj* x_86; obj* x_88; 
x_81 = lean::cnstr_get(x_70, 0);
lean::inc(x_81);
lean::dec(x_70);
x_84 = l_option_has__repr___rarg___closed__3;
x_85 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_84, x_3, x_72);
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_85, 1);
lean::inc(x_88);
lean::dec(x_85);
if (lean::obj_tag(x_86) == 0)
{
obj* x_92; obj* x_95; obj* x_96; 
lean::dec(x_81);
x_92 = lean::cnstr_get(x_86, 0);
lean::inc(x_92);
lean::dec(x_86);
if (lean::is_scalar(x_36)) {
 x_95 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_95 = x_36;
 lean::cnstr_set_tag(x_36, 0);
}
lean::cnstr_set(x_95, 0, x_92);
if (lean::is_scalar(x_43)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_43;
}
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_88);
return x_96;
}
else
{
obj* x_98; obj* x_99; 
lean::dec(x_86);
if (lean::is_scalar(x_36)) {
 x_98 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_98 = x_36;
}
lean::cnstr_set(x_98, 0, x_81);
if (lean::is_scalar(x_43)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_43;
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_88);
return x_99;
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
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::dec(x_12);
 x_19 = lean::box(0);
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
obj* x_22; obj* x_24; obj* x_25; obj* x_27; 
lean::dec(x_12);
x_22 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_4);
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_4, x_14);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_7 = x_25;
x_8 = x_27;
goto lbl_9;
}
lbl_9:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
x_33 = lean::cnstr_get(x_7, 0);
lean::inc(x_33);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_35 = x_7;
} else {
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
obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_45; 
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_38 = x_7;
} else {
 lean::dec(x_7);
 x_38 = lean::box(0);
}
lean::inc(x_4);
x_40 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_6, x_4, x_8);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 lean::cnstr_release(x_40, 1);
 x_45 = x_40;
} else {
 lean::dec(x_40);
 x_45 = lean::box(0);
}
if (lean::obj_tag(x_41) == 0)
{
obj* x_48; obj* x_51; obj* x_52; 
lean::dec(x_4);
lean::dec(x_3);
x_48 = lean::cnstr_get(x_41, 0);
lean::inc(x_48);
lean::dec(x_41);
if (lean::is_scalar(x_38)) {
 x_51 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_51 = x_38;
 lean::cnstr_set_tag(x_38, 0);
}
lean::cnstr_set(x_51, 0, x_48);
if (lean::is_scalar(x_45)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_45;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_43);
return x_52;
}
else
{
obj* x_54; obj* x_56; obj* x_57; obj* x_59; 
lean::dec(x_41);
x_54 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_4);
x_56 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_54, x_4, x_43);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
if (lean::obj_tag(x_57) == 0)
{
obj* x_64; obj* x_67; obj* x_68; 
lean::dec(x_4);
lean::dec(x_3);
x_64 = lean::cnstr_get(x_57, 0);
lean::inc(x_64);
lean::dec(x_57);
if (lean::is_scalar(x_38)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_38;
 lean::cnstr_set_tag(x_38, 0);
}
lean::cnstr_set(x_67, 0, x_64);
if (lean::is_scalar(x_45)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_45;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_59);
return x_68;
}
else
{
obj* x_71; obj* x_72; obj* x_74; 
lean::dec(x_57);
lean::inc(x_4);
x_71 = l_lean_ir_cpp_emit__var(x_3, x_4, x_59);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
lean::dec(x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_78; obj* x_81; obj* x_82; 
lean::dec(x_4);
x_78 = lean::cnstr_get(x_72, 0);
lean::inc(x_78);
lean::dec(x_72);
if (lean::is_scalar(x_38)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_38;
 lean::cnstr_set_tag(x_38, 0);
}
lean::cnstr_set(x_81, 0, x_78);
if (lean::is_scalar(x_45)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_45;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_74);
return x_82;
}
else
{
obj* x_83; obj* x_86; obj* x_87; obj* x_88; obj* x_90; 
x_83 = lean::cnstr_get(x_72, 0);
lean::inc(x_83);
lean::dec(x_72);
x_86 = l_option_has__repr___rarg___closed__3;
x_87 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_86, x_4, x_74);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_87, 1);
lean::inc(x_90);
lean::dec(x_87);
if (lean::obj_tag(x_88) == 0)
{
obj* x_94; obj* x_97; obj* x_98; 
lean::dec(x_83);
x_94 = lean::cnstr_get(x_88, 0);
lean::inc(x_94);
lean::dec(x_88);
if (lean::is_scalar(x_38)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_38;
 lean::cnstr_set_tag(x_38, 0);
}
lean::cnstr_set(x_97, 0, x_94);
if (lean::is_scalar(x_45)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_45;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_90);
return x_98;
}
else
{
obj* x_100; obj* x_101; 
lean::dec(x_88);
if (lean::is_scalar(x_38)) {
 x_100 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_100 = x_38;
}
lean::cnstr_set(x_100, 0, x_83);
if (lean::is_scalar(x_45)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_45;
}
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_90);
return x_101;
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
obj* x_10; obj* x_11; 
lean::dec(x_1);
x_10 = l_lean_ir_match__type___closed__5;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_2);
return x_11;
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
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_4 = l_int_repr___main(x_0);
x_5 = lean::string_append(x_2, x_4);
lean::dec(x_4);
x_7 = l_lean_ir_match__type___closed__5;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
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
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
} else {
 lean::dec(x_8);
 x_13 = lean::box(0);
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_3);
x_15 = lean::cnstr_get(x_9, 0);
lean::inc(x_15);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_17 = x_9;
} else {
 lean::dec(x_9);
 x_17 = lean::box(0);
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
obj* x_22; obj* x_23; 
lean::dec(x_9);
lean::dec(x_13);
x_22 = l_lean_ir_cpp_emit__assign__lit___closed__1;
x_23 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_3, x_11);
return x_23;
}
}
else
{
obj* x_25; obj* x_26; obj* x_28; obj* x_30; 
lean::inc(x_3);
x_25 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 x_30 = x_25;
} else {
 lean::dec(x_25);
 x_30 = lean::box(0);
}
if (lean::obj_tag(x_26) == 0)
{
obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_3);
x_32 = lean::cnstr_get(x_26, 0);
lean::inc(x_32);
if (lean::is_exclusive(x_26)) {
 lean::cnstr_release(x_26, 0);
 x_34 = x_26;
} else {
 lean::dec(x_26);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
if (lean::is_scalar(x_30)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_30;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_28);
return x_36;
}
else
{
obj* x_39; obj* x_40; 
lean::dec(x_30);
lean::dec(x_26);
x_39 = l_lean_ir_cpp_emit__assign__lit___closed__2;
x_40 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_39, x_3, x_28);
return x_40;
}
}
}
case 1:
{
obj* x_41; obj* x_45; obj* x_46; obj* x_48; obj* x_50; 
x_41 = lean::cnstr_get(x_2, 0);
lean::inc(x_41);
lean::dec(x_2);
lean::inc(x_3);
x_45 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_50 = x_45;
} else {
 lean::dec(x_45);
 x_50 = lean::box(0);
}
if (lean::obj_tag(x_46) == 0)
{
obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_3);
lean::dec(x_41);
x_53 = lean::cnstr_get(x_46, 0);
lean::inc(x_53);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_55 = x_46;
} else {
 lean::dec(x_46);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
if (lean::is_scalar(x_50)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_50;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_48);
return x_57;
}
else
{
obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_64; 
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_58 = x_46;
} else {
 lean::dec(x_46);
 x_58 = lean::box(0);
}
x_59 = l_lean_ir_cpp_emit__assign__lit___closed__3;
lean::inc(x_3);
x_61 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_59, x_3, x_48);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
if (lean::obj_tag(x_62) == 0)
{
obj* x_69; obj* x_72; obj* x_73; 
lean::dec(x_3);
lean::dec(x_41);
x_69 = lean::cnstr_get(x_62, 0);
lean::inc(x_69);
lean::dec(x_62);
if (lean::is_scalar(x_58)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_58;
 lean::cnstr_set_tag(x_58, 0);
}
lean::cnstr_set(x_72, 0, x_69);
if (lean::is_scalar(x_50)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_50;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_64);
return x_73;
}
else
{
obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_81; 
lean::dec(x_62);
x_75 = l_string_quote(x_41);
x_76 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
x_78 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_76, x_3, x_64);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
lean::dec(x_78);
if (lean::obj_tag(x_79) == 0)
{
obj* x_86; obj* x_89; obj* x_90; 
lean::dec(x_3);
lean::dec(x_75);
x_86 = lean::cnstr_get(x_79, 0);
lean::inc(x_86);
lean::dec(x_79);
if (lean::is_scalar(x_58)) {
 x_89 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_89 = x_58;
 lean::cnstr_set_tag(x_58, 0);
}
lean::cnstr_set(x_89, 0, x_86);
if (lean::is_scalar(x_50)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_50;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_81);
return x_90;
}
else
{
obj* x_93; obj* x_94; obj* x_96; 
lean::dec(x_79);
lean::inc(x_3);
x_93 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_75, x_3, x_81);
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_93, 1);
lean::inc(x_96);
lean::dec(x_93);
if (lean::obj_tag(x_94) == 0)
{
obj* x_100; obj* x_103; obj* x_104; 
lean::dec(x_3);
x_100 = lean::cnstr_get(x_94, 0);
lean::inc(x_100);
lean::dec(x_94);
if (lean::is_scalar(x_58)) {
 x_103 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_103 = x_58;
 lean::cnstr_set_tag(x_58, 0);
}
lean::cnstr_set(x_103, 0, x_100);
if (lean::is_scalar(x_50)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_50;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_96);
return x_104;
}
else
{
obj* x_105; obj* x_108; obj* x_109; obj* x_110; obj* x_112; 
x_105 = lean::cnstr_get(x_94, 0);
lean::inc(x_105);
lean::dec(x_94);
x_108 = l_option_has__repr___rarg___closed__3;
x_109 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_108, x_3, x_96);
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_109, 1);
lean::inc(x_112);
lean::dec(x_109);
if (lean::obj_tag(x_110) == 0)
{
obj* x_116; obj* x_119; obj* x_120; 
lean::dec(x_105);
x_116 = lean::cnstr_get(x_110, 0);
lean::inc(x_116);
lean::dec(x_110);
if (lean::is_scalar(x_58)) {
 x_119 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_119 = x_58;
 lean::cnstr_set_tag(x_58, 0);
}
lean::cnstr_set(x_119, 0, x_116);
if (lean::is_scalar(x_50)) {
 x_120 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_120 = x_50;
}
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_112);
return x_120;
}
else
{
obj* x_122; obj* x_123; 
lean::dec(x_110);
if (lean::is_scalar(x_58)) {
 x_122 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_122 = x_58;
}
lean::cnstr_set(x_122, 0, x_105);
if (lean::is_scalar(x_50)) {
 x_123 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_123 = x_50;
}
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_112);
return x_123;
}
}
}
}
}
}
case 2:
{
obj* x_124; obj* x_127; 
x_124 = lean::cnstr_get(x_2, 0);
lean::inc(x_124);
lean::dec(x_2);
switch (x_1) {
case 11:
{
obj* x_129; uint8 x_130; obj* x_131; obj* x_132; obj* x_135; obj* x_136; obj* x_138; 
x_129 = l_lean_ir_cpp_emit__assign__lit___closed__4;
x_130 = lean::int_dec_lt(x_124, x_129);
lean::inc(x_3);
x_135 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_135, 1);
lean::inc(x_138);
lean::dec(x_135);
if (lean::obj_tag(x_136) == 0)
{
obj* x_141; obj* x_143; obj* x_144; 
x_141 = lean::cnstr_get(x_136, 0);
lean::inc(x_141);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 x_143 = x_136;
} else {
 lean::dec(x_136);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_141);
x_131 = x_144;
x_132 = x_138;
goto lbl_133;
}
else
{
obj* x_146; obj* x_148; obj* x_149; obj* x_151; 
lean::dec(x_136);
x_146 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
x_148 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_146, x_3, x_138);
x_149 = lean::cnstr_get(x_148, 0);
lean::inc(x_149);
x_151 = lean::cnstr_get(x_148, 1);
lean::inc(x_151);
lean::dec(x_148);
x_131 = x_149;
x_132 = x_151;
goto lbl_133;
}
lbl_133:
{
if (lean::obj_tag(x_131) == 0)
{
obj* x_156; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_124);
lean::dec(x_3);
x_156 = lean::cnstr_get(x_131, 0);
lean::inc(x_156);
if (lean::is_exclusive(x_131)) {
 lean::cnstr_release(x_131, 0);
 x_158 = x_131;
} else {
 lean::dec(x_131);
 x_158 = lean::box(0);
}
if (lean::is_scalar(x_158)) {
 x_159 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_159 = x_158;
}
lean::cnstr_set(x_159, 0, x_156);
x_160 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_160, 0, x_159);
lean::cnstr_set(x_160, 1, x_132);
return x_160;
}
else
{
obj* x_161; 
if (lean::is_exclusive(x_131)) {
 lean::cnstr_release(x_131, 0);
 x_161 = x_131;
} else {
 lean::dec(x_131);
 x_161 = lean::box(0);
}
if (x_130 == 0)
{
obj* x_162; obj* x_164; obj* x_165; obj* x_167; obj* x_169; 
x_162 = l_lean_ir_cpp_emit__assign__lit___closed__5;
lean::inc(x_3);
x_164 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_162, x_3, x_132);
x_165 = lean::cnstr_get(x_164, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_164, 1);
lean::inc(x_167);
if (lean::is_exclusive(x_164)) {
 lean::cnstr_release(x_164, 0);
 lean::cnstr_release(x_164, 1);
 x_169 = x_164;
} else {
 lean::dec(x_164);
 x_169 = lean::box(0);
}
if (lean::obj_tag(x_165) == 0)
{
obj* x_172; obj* x_175; obj* x_176; 
lean::dec(x_124);
lean::dec(x_3);
x_172 = lean::cnstr_get(x_165, 0);
lean::inc(x_172);
lean::dec(x_165);
if (lean::is_scalar(x_161)) {
 x_175 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_175 = x_161;
 lean::cnstr_set_tag(x_161, 0);
}
lean::cnstr_set(x_175, 0, x_172);
if (lean::is_scalar(x_169)) {
 x_176 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_176 = x_169;
}
lean::cnstr_set(x_176, 0, x_175);
lean::cnstr_set(x_176, 1, x_167);
return x_176;
}
else
{
obj* x_179; obj* x_180; obj* x_182; 
lean::dec(x_165);
lean::inc(x_3);
x_179 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_124, x_3, x_167);
x_180 = lean::cnstr_get(x_179, 0);
lean::inc(x_180);
x_182 = lean::cnstr_get(x_179, 1);
lean::inc(x_182);
lean::dec(x_179);
if (lean::obj_tag(x_180) == 0)
{
obj* x_186; obj* x_189; obj* x_190; 
lean::dec(x_3);
x_186 = lean::cnstr_get(x_180, 0);
lean::inc(x_186);
lean::dec(x_180);
if (lean::is_scalar(x_161)) {
 x_189 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_189 = x_161;
 lean::cnstr_set_tag(x_161, 0);
}
lean::cnstr_set(x_189, 0, x_186);
if (lean::is_scalar(x_169)) {
 x_190 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_190 = x_169;
}
lean::cnstr_set(x_190, 0, x_189);
lean::cnstr_set(x_190, 1, x_182);
return x_190;
}
else
{
obj* x_194; obj* x_195; 
lean::dec(x_161);
lean::dec(x_180);
lean::dec(x_169);
x_194 = l_lean_ir_cpp_emit__assign__lit___closed__6;
x_195 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_194, x_3, x_182);
return x_195;
}
}
}
else
{
obj* x_196; obj* x_198; obj* x_199; obj* x_201; obj* x_203; 
x_196 = l_lean_ir_cpp_emit__assign__lit___closed__7;
lean::inc(x_3);
x_198 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_196, x_3, x_132);
x_199 = lean::cnstr_get(x_198, 0);
lean::inc(x_199);
x_201 = lean::cnstr_get(x_198, 1);
lean::inc(x_201);
if (lean::is_exclusive(x_198)) {
 lean::cnstr_release(x_198, 0);
 lean::cnstr_release(x_198, 1);
 x_203 = x_198;
} else {
 lean::dec(x_198);
 x_203 = lean::box(0);
}
if (lean::obj_tag(x_199) == 0)
{
obj* x_206; obj* x_209; obj* x_210; 
lean::dec(x_124);
lean::dec(x_3);
x_206 = lean::cnstr_get(x_199, 0);
lean::inc(x_206);
lean::dec(x_199);
if (lean::is_scalar(x_161)) {
 x_209 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_209 = x_161;
 lean::cnstr_set_tag(x_161, 0);
}
lean::cnstr_set(x_209, 0, x_206);
if (lean::is_scalar(x_203)) {
 x_210 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_210 = x_203;
}
lean::cnstr_set(x_210, 0, x_209);
lean::cnstr_set(x_210, 1, x_201);
return x_210;
}
else
{
obj* x_212; obj* x_214; obj* x_215; obj* x_217; 
lean::dec(x_199);
x_212 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
x_214 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_212, x_3, x_201);
x_215 = lean::cnstr_get(x_214, 0);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_214, 1);
lean::inc(x_217);
lean::dec(x_214);
if (lean::obj_tag(x_215) == 0)
{
obj* x_222; obj* x_225; obj* x_226; 
lean::dec(x_124);
lean::dec(x_3);
x_222 = lean::cnstr_get(x_215, 0);
lean::inc(x_222);
lean::dec(x_215);
if (lean::is_scalar(x_161)) {
 x_225 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_225 = x_161;
 lean::cnstr_set_tag(x_161, 0);
}
lean::cnstr_set(x_225, 0, x_222);
if (lean::is_scalar(x_203)) {
 x_226 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_226 = x_203;
}
lean::cnstr_set(x_226, 0, x_225);
lean::cnstr_set(x_226, 1, x_217);
return x_226;
}
else
{
obj* x_229; obj* x_230; obj* x_232; 
lean::dec(x_215);
lean::inc(x_3);
x_229 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_124, x_3, x_217);
x_230 = lean::cnstr_get(x_229, 0);
lean::inc(x_230);
x_232 = lean::cnstr_get(x_229, 1);
lean::inc(x_232);
lean::dec(x_229);
if (lean::obj_tag(x_230) == 0)
{
obj* x_236; obj* x_239; obj* x_240; 
lean::dec(x_3);
x_236 = lean::cnstr_get(x_230, 0);
lean::inc(x_236);
lean::dec(x_230);
if (lean::is_scalar(x_161)) {
 x_239 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_239 = x_161;
 lean::cnstr_set_tag(x_161, 0);
}
lean::cnstr_set(x_239, 0, x_236);
if (lean::is_scalar(x_203)) {
 x_240 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_240 = x_203;
}
lean::cnstr_set(x_240, 0, x_239);
lean::cnstr_set(x_240, 1, x_232);
return x_240;
}
else
{
obj* x_242; obj* x_244; obj* x_245; obj* x_247; 
lean::dec(x_230);
x_242 = l_lean_ir_cpp_emit__num__suffix___main___closed__1;
lean::inc(x_3);
x_244 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_242, x_3, x_232);
x_245 = lean::cnstr_get(x_244, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_244, 1);
lean::inc(x_247);
lean::dec(x_244);
if (lean::obj_tag(x_245) == 0)
{
obj* x_251; obj* x_254; obj* x_255; 
lean::dec(x_3);
x_251 = lean::cnstr_get(x_245, 0);
lean::inc(x_251);
lean::dec(x_245);
if (lean::is_scalar(x_161)) {
 x_254 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_254 = x_161;
 lean::cnstr_set_tag(x_161, 0);
}
lean::cnstr_set(x_254, 0, x_251);
if (lean::is_scalar(x_203)) {
 x_255 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_255 = x_203;
}
lean::cnstr_set(x_255, 0, x_254);
lean::cnstr_set(x_255, 1, x_247);
return x_255;
}
else
{
obj* x_256; obj* x_259; obj* x_260; obj* x_261; obj* x_263; 
x_256 = lean::cnstr_get(x_245, 0);
lean::inc(x_256);
lean::dec(x_245);
x_259 = l_option_has__repr___rarg___closed__3;
x_260 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_259, x_3, x_247);
x_261 = lean::cnstr_get(x_260, 0);
lean::inc(x_261);
x_263 = lean::cnstr_get(x_260, 1);
lean::inc(x_263);
lean::dec(x_260);
if (lean::obj_tag(x_261) == 0)
{
obj* x_267; obj* x_270; obj* x_271; 
lean::dec(x_256);
x_267 = lean::cnstr_get(x_261, 0);
lean::inc(x_267);
lean::dec(x_261);
if (lean::is_scalar(x_161)) {
 x_270 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_270 = x_161;
 lean::cnstr_set_tag(x_161, 0);
}
lean::cnstr_set(x_270, 0, x_267);
if (lean::is_scalar(x_203)) {
 x_271 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_271 = x_203;
}
lean::cnstr_set(x_271, 0, x_270);
lean::cnstr_set(x_271, 1, x_263);
return x_271;
}
else
{
obj* x_273; obj* x_274; 
lean::dec(x_261);
if (lean::is_scalar(x_161)) {
 x_273 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_273 = x_161;
}
lean::cnstr_set(x_273, 0, x_256);
if (lean::is_scalar(x_203)) {
 x_274 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_274 = x_203;
}
lean::cnstr_set(x_274, 0, x_273);
lean::cnstr_set(x_274, 1, x_263);
return x_274;
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
obj* x_275; 
x_275 = lean::box(0);
x_127 = x_275;
goto lbl_128;
}
}
lbl_128:
{
obj* x_278; obj* x_279; obj* x_281; obj* x_283; 
lean::dec(x_127);
lean::inc(x_3);
x_278 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_279 = lean::cnstr_get(x_278, 0);
lean::inc(x_279);
x_281 = lean::cnstr_get(x_278, 1);
lean::inc(x_281);
if (lean::is_exclusive(x_278)) {
 lean::cnstr_release(x_278, 0);
 lean::cnstr_release(x_278, 1);
 x_283 = x_278;
} else {
 lean::dec(x_278);
 x_283 = lean::box(0);
}
if (lean::obj_tag(x_279) == 0)
{
obj* x_286; obj* x_288; obj* x_289; obj* x_290; 
lean::dec(x_124);
lean::dec(x_3);
x_286 = lean::cnstr_get(x_279, 0);
lean::inc(x_286);
if (lean::is_exclusive(x_279)) {
 lean::cnstr_release(x_279, 0);
 x_288 = x_279;
} else {
 lean::dec(x_279);
 x_288 = lean::box(0);
}
if (lean::is_scalar(x_288)) {
 x_289 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_289 = x_288;
}
lean::cnstr_set(x_289, 0, x_286);
if (lean::is_scalar(x_283)) {
 x_290 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_290 = x_283;
}
lean::cnstr_set(x_290, 0, x_289);
lean::cnstr_set(x_290, 1, x_281);
return x_290;
}
else
{
obj* x_291; obj* x_292; obj* x_294; obj* x_295; obj* x_297; 
if (lean::is_exclusive(x_279)) {
 lean::cnstr_release(x_279, 0);
 x_291 = x_279;
} else {
 lean::dec(x_279);
 x_291 = lean::box(0);
}
x_292 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
x_294 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_292, x_3, x_281);
x_295 = lean::cnstr_get(x_294, 0);
lean::inc(x_295);
x_297 = lean::cnstr_get(x_294, 1);
lean::inc(x_297);
lean::dec(x_294);
if (lean::obj_tag(x_295) == 0)
{
obj* x_302; obj* x_305; obj* x_306; 
lean::dec(x_124);
lean::dec(x_3);
x_302 = lean::cnstr_get(x_295, 0);
lean::inc(x_302);
lean::dec(x_295);
if (lean::is_scalar(x_291)) {
 x_305 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_305 = x_291;
 lean::cnstr_set_tag(x_291, 0);
}
lean::cnstr_set(x_305, 0, x_302);
if (lean::is_scalar(x_283)) {
 x_306 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_306 = x_283;
}
lean::cnstr_set(x_306, 0, x_305);
lean::cnstr_set(x_306, 1, x_297);
return x_306;
}
else
{
obj* x_309; obj* x_310; obj* x_312; 
lean::dec(x_295);
lean::inc(x_3);
x_309 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_124, x_3, x_297);
x_310 = lean::cnstr_get(x_309, 0);
lean::inc(x_310);
x_312 = lean::cnstr_get(x_309, 1);
lean::inc(x_312);
lean::dec(x_309);
if (lean::obj_tag(x_310) == 0)
{
obj* x_316; obj* x_319; obj* x_320; 
lean::dec(x_3);
x_316 = lean::cnstr_get(x_310, 0);
lean::inc(x_316);
lean::dec(x_310);
if (lean::is_scalar(x_291)) {
 x_319 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_319 = x_291;
 lean::cnstr_set_tag(x_291, 0);
}
lean::cnstr_set(x_319, 0, x_316);
if (lean::is_scalar(x_283)) {
 x_320 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_320 = x_283;
}
lean::cnstr_set(x_320, 0, x_319);
lean::cnstr_set(x_320, 1, x_312);
return x_320;
}
else
{
obj* x_324; 
lean::dec(x_310);
lean::dec(x_283);
lean::dec(x_291);
x_324 = l_lean_ir_cpp_emit__num__suffix___main(x_1, x_3, x_312);
return x_324;
}
}
}
}
}
default:
{
obj* x_325; obj* x_329; obj* x_330; obj* x_332; obj* x_334; 
x_325 = lean::cnstr_get(x_2, 0);
lean::inc(x_325);
lean::dec(x_2);
lean::inc(x_3);
x_329 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_330 = lean::cnstr_get(x_329, 0);
lean::inc(x_330);
x_332 = lean::cnstr_get(x_329, 1);
lean::inc(x_332);
if (lean::is_exclusive(x_329)) {
 lean::cnstr_release(x_329, 0);
 lean::cnstr_release(x_329, 1);
 x_334 = x_329;
} else {
 lean::dec(x_329);
 x_334 = lean::box(0);
}
if (lean::obj_tag(x_330) == 0)
{
obj* x_337; obj* x_339; obj* x_340; obj* x_341; 
lean::dec(x_325);
lean::dec(x_3);
x_337 = lean::cnstr_get(x_330, 0);
lean::inc(x_337);
if (lean::is_exclusive(x_330)) {
 lean::cnstr_release(x_330, 0);
 x_339 = x_330;
} else {
 lean::dec(x_330);
 x_339 = lean::box(0);
}
if (lean::is_scalar(x_339)) {
 x_340 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_340 = x_339;
}
lean::cnstr_set(x_340, 0, x_337);
if (lean::is_scalar(x_334)) {
 x_341 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_341 = x_334;
}
lean::cnstr_set(x_341, 0, x_340);
lean::cnstr_set(x_341, 1, x_332);
return x_341;
}
else
{
obj* x_342; obj* x_343; obj* x_345; obj* x_346; obj* x_348; 
if (lean::is_exclusive(x_330)) {
 lean::cnstr_release(x_330, 0);
 x_342 = x_330;
} else {
 lean::dec(x_330);
 x_342 = lean::box(0);
}
x_343 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
x_345 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_343, x_3, x_332);
x_346 = lean::cnstr_get(x_345, 0);
lean::inc(x_346);
x_348 = lean::cnstr_get(x_345, 1);
lean::inc(x_348);
lean::dec(x_345);
if (lean::obj_tag(x_346) == 0)
{
obj* x_353; obj* x_356; obj* x_357; 
lean::dec(x_325);
lean::dec(x_3);
x_353 = lean::cnstr_get(x_346, 0);
lean::inc(x_353);
lean::dec(x_346);
if (lean::is_scalar(x_342)) {
 x_356 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_356 = x_342;
 lean::cnstr_set_tag(x_342, 0);
}
lean::cnstr_set(x_356, 0, x_353);
if (lean::is_scalar(x_334)) {
 x_357 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_357 = x_334;
}
lean::cnstr_set(x_357, 0, x_356);
lean::cnstr_set(x_357, 1, x_348);
return x_357;
}
else
{
obj* x_361; 
lean::dec(x_334);
lean::dec(x_346);
lean::dec(x_342);
x_361 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_325, x_3, x_348);
return x_361;
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
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_4 = l_lean_ir_cpp_unop2cpp___main(x_0);
lean::inc(x_2);
x_6 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_4, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
} else {
 lean::dec(x_6);
 x_11 = lean::box(0);
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_1);
lean::dec(x_2);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_16 = x_7;
} else {
 lean::dec(x_7);
 x_16 = lean::box(0);
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
obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_25; 
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_19 = x_7;
} else {
 lean::dec(x_7);
 x_19 = lean::box(0);
}
x_20 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
x_22 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_20, x_2, x_9);
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
if (lean::is_scalar(x_19)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_19;
 lean::cnstr_set_tag(x_19, 0);
}
lean::cnstr_set(x_33, 0, x_30);
if (lean::is_scalar(x_11)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_11;
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
if (lean::is_scalar(x_19)) {
 x_47 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_47 = x_19;
 lean::cnstr_set_tag(x_19, 0);
}
lean::cnstr_set(x_47, 0, x_44);
if (lean::is_scalar(x_11)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_11;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_40);
return x_48;
}
else
{
obj* x_49; obj* x_52; obj* x_53; obj* x_54; obj* x_56; 
x_49 = lean::cnstr_get(x_38, 0);
lean::inc(x_49);
lean::dec(x_38);
x_52 = l_option_has__repr___rarg___closed__3;
x_53 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_52, x_2, x_40);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
lean::dec(x_53);
if (lean::obj_tag(x_54) == 0)
{
obj* x_60; obj* x_63; obj* x_64; 
lean::dec(x_49);
x_60 = lean::cnstr_get(x_54, 0);
lean::inc(x_60);
lean::dec(x_54);
if (lean::is_scalar(x_19)) {
 x_63 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_63 = x_19;
 lean::cnstr_set_tag(x_19, 0);
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
if (lean::is_scalar(x_19)) {
 x_66 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_66 = x_19;
}
lean::cnstr_set(x_66, 0, x_49);
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
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; uint8 x_16; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
x_12 = lean::mk_nat_obj(0u);
lean::inc(x_10);
x_14 = l_list_length__aux___main___rarg(x_10, x_12);
x_15 = l_lean_closure__max__args;
x_16 = lean::nat_dec_lt(x_15, x_14);
if (x_16 == 0)
{
obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_26; 
lean::dec(x_10);
lean::dec(x_8);
lean::inc(x_2);
x_23 = l_lean_ir_cpp_emit__var(x_0, x_2, x_3);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_29; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_24, 0);
lean::inc(x_29);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_31 = x_24;
} else {
 lean::dec(x_24);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
x_19 = x_32;
x_20 = x_26;
goto lbl_21;
}
else
{
obj* x_34; obj* x_36; obj* x_37; obj* x_39; 
lean::dec(x_24);
x_34 = l_lean_ir_cpp_emit__apply___closed__3;
lean::inc(x_2);
x_36 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_34, x_2, x_26);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_19 = x_37;
x_20 = x_39;
goto lbl_21;
}
lbl_21:
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_1);
lean::dec(x_14);
lean::dec(x_2);
x_45 = lean::cnstr_get(x_19, 0);
lean::inc(x_45);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 x_47 = x_19;
} else {
 lean::dec(x_19);
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
lean::cnstr_set(x_49, 1, x_20);
return x_49;
}
else
{
obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_57; 
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 x_50 = x_19;
} else {
 lean::dec(x_19);
 x_50 = lean::box(0);
}
lean::inc(x_2);
x_52 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_14, x_2, x_20);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 x_57 = x_52;
} else {
 lean::dec(x_52);
 x_57 = lean::box(0);
}
if (lean::obj_tag(x_53) == 0)
{
obj* x_60; obj* x_63; obj* x_64; 
lean::dec(x_1);
lean::dec(x_2);
x_60 = lean::cnstr_get(x_53, 0);
lean::inc(x_60);
lean::dec(x_53);
if (lean::is_scalar(x_50)) {
 x_63 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_63 = x_50;
 lean::cnstr_set_tag(x_50, 0);
}
lean::cnstr_set(x_63, 0, x_60);
if (lean::is_scalar(x_57)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_57;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_55);
return x_64;
}
else
{
obj* x_66; obj* x_68; obj* x_69; obj* x_71; 
lean::dec(x_53);
x_66 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
x_68 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_66, x_2, x_55);
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_68, 1);
lean::inc(x_71);
lean::dec(x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_76; obj* x_79; obj* x_80; 
lean::dec(x_1);
lean::dec(x_2);
x_76 = lean::cnstr_get(x_69, 0);
lean::inc(x_76);
lean::dec(x_69);
if (lean::is_scalar(x_50)) {
 x_79 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_79 = x_50;
 lean::cnstr_set_tag(x_50, 0);
}
lean::cnstr_set(x_79, 0, x_76);
if (lean::is_scalar(x_57)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_57;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_71);
return x_80;
}
else
{
obj* x_82; obj* x_83; obj* x_85; obj* x_86; obj* x_88; 
lean::dec(x_69);
x_82 = l_lean_ir_cpp_emit__apply___closed__2;
x_83 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_2);
x_85 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_82, x_83, x_1, x_2, x_71);
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_85, 1);
lean::inc(x_88);
lean::dec(x_85);
if (lean::obj_tag(x_86) == 0)
{
obj* x_92; obj* x_95; obj* x_96; 
lean::dec(x_2);
x_92 = lean::cnstr_get(x_86, 0);
lean::inc(x_92);
lean::dec(x_86);
if (lean::is_scalar(x_50)) {
 x_95 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_95 = x_50;
 lean::cnstr_set_tag(x_50, 0);
}
lean::cnstr_set(x_95, 0, x_92);
if (lean::is_scalar(x_57)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_57;
}
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_88);
return x_96;
}
else
{
obj* x_97; obj* x_100; obj* x_101; obj* x_102; obj* x_104; 
x_97 = lean::cnstr_get(x_86, 0);
lean::inc(x_97);
lean::dec(x_86);
x_100 = l_option_has__repr___rarg___closed__3;
x_101 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_100, x_2, x_88);
x_102 = lean::cnstr_get(x_101, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_101, 1);
lean::inc(x_104);
lean::dec(x_101);
if (lean::obj_tag(x_102) == 0)
{
obj* x_108; obj* x_111; obj* x_112; 
lean::dec(x_97);
x_108 = lean::cnstr_get(x_102, 0);
lean::inc(x_108);
lean::dec(x_102);
if (lean::is_scalar(x_50)) {
 x_111 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_111 = x_50;
 lean::cnstr_set_tag(x_50, 0);
}
lean::cnstr_set(x_111, 0, x_108);
if (lean::is_scalar(x_57)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_57;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_104);
return x_112;
}
else
{
obj* x_114; obj* x_115; 
lean::dec(x_102);
if (lean::is_scalar(x_50)) {
 x_114 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_114 = x_50;
}
lean::cnstr_set(x_114, 0, x_97);
if (lean::is_scalar(x_57)) {
 x_115 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_115 = x_57;
}
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_104);
return x_115;
}
}
}
}
}
}
}
else
{
obj* x_117; obj* x_118; obj* x_120; obj* x_121; obj* x_123; obj* x_124; obj* x_126; obj* x_127; obj* x_129; obj* x_131; obj* x_132; obj* x_134; 
lean::dec(x_1);
x_129 = l_lean_ir_cpp_emit__apply___closed__8;
lean::inc(x_2);
x_131 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_129, x_2, x_3);
x_132 = lean::cnstr_get(x_131, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_131, 1);
lean::inc(x_134);
lean::dec(x_131);
if (lean::obj_tag(x_132) == 0)
{
obj* x_137; obj* x_139; obj* x_140; 
x_137 = lean::cnstr_get(x_132, 0);
lean::inc(x_137);
if (lean::is_exclusive(x_132)) {
 lean::cnstr_release(x_132, 0);
 x_139 = x_132;
} else {
 lean::dec(x_132);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_137);
x_126 = x_140;
x_127 = x_134;
goto lbl_128;
}
else
{
obj* x_141; obj* x_144; obj* x_145; obj* x_147; 
if (lean::is_exclusive(x_132)) {
 lean::cnstr_release(x_132, 0);
 x_141 = x_132;
} else {
 lean::dec(x_132);
 x_141 = lean::box(0);
}
lean::inc(x_2);
lean::inc(x_14);
x_144 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_14, x_2, x_134);
x_145 = lean::cnstr_get(x_144, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_144, 1);
lean::inc(x_147);
lean::dec(x_144);
if (lean::obj_tag(x_145) == 0)
{
obj* x_150; obj* x_153; 
x_150 = lean::cnstr_get(x_145, 0);
lean::inc(x_150);
lean::dec(x_145);
if (lean::is_scalar(x_141)) {
 x_153 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_153 = x_141;
 lean::cnstr_set_tag(x_141, 0);
}
lean::cnstr_set(x_153, 0, x_150);
x_126 = x_153;
x_127 = x_147;
goto lbl_128;
}
else
{
obj* x_156; obj* x_158; obj* x_159; obj* x_161; 
lean::dec(x_141);
lean::dec(x_145);
x_156 = l_lean_ir_cpp_emit__apply___closed__9;
lean::inc(x_2);
x_158 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_156, x_2, x_147);
x_159 = lean::cnstr_get(x_158, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_158, 1);
lean::inc(x_161);
lean::dec(x_158);
x_126 = x_159;
x_127 = x_161;
goto lbl_128;
}
}
lbl_119:
{
if (lean::obj_tag(x_117) == 0)
{
obj* x_165; obj* x_167; obj* x_168; obj* x_169; 
lean::dec(x_2);
x_165 = lean::cnstr_get(x_117, 0);
lean::inc(x_165);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 x_167 = x_117;
} else {
 lean::dec(x_117);
 x_167 = lean::box(0);
}
if (lean::is_scalar(x_167)) {
 x_168 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_168 = x_167;
}
lean::cnstr_set(x_168, 0, x_165);
x_169 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_169, 0, x_168);
lean::cnstr_set(x_169, 1, x_118);
return x_169;
}
else
{
obj* x_171; obj* x_172; 
lean::dec(x_117);
x_171 = l_lean_ir_cpp_emit__apply___closed__4;
x_172 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_171, x_2, x_118);
return x_172;
}
}
lbl_122:
{
if (lean::obj_tag(x_120) == 0)
{
obj* x_173; obj* x_175; obj* x_176; 
x_173 = lean::cnstr_get(x_120, 0);
lean::inc(x_173);
if (lean::is_exclusive(x_120)) {
 lean::cnstr_release(x_120, 0);
 x_175 = x_120;
} else {
 lean::dec(x_120);
 x_175 = lean::box(0);
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_173);
x_117 = x_176;
x_118 = x_121;
goto lbl_119;
}
else
{
obj* x_177; obj* x_178; obj* x_180; obj* x_181; obj* x_183; 
if (lean::is_exclusive(x_120)) {
 lean::cnstr_release(x_120, 0);
 x_177 = x_120;
} else {
 lean::dec(x_120);
 x_177 = lean::box(0);
}
x_178 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
x_180 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_178, x_2, x_121);
x_181 = lean::cnstr_get(x_180, 0);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_180, 1);
lean::inc(x_183);
lean::dec(x_180);
if (lean::obj_tag(x_181) == 0)
{
obj* x_186; obj* x_189; 
x_186 = lean::cnstr_get(x_181, 0);
lean::inc(x_186);
lean::dec(x_181);
if (lean::is_scalar(x_177)) {
 x_189 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_189 = x_177;
 lean::cnstr_set_tag(x_177, 0);
}
lean::cnstr_set(x_189, 0, x_186);
x_117 = x_189;
x_118 = x_183;
goto lbl_119;
}
else
{
obj* x_191; obj* x_193; obj* x_194; obj* x_196; 
lean::dec(x_181);
x_191 = l_lean_ir_cpp_emit__apply___closed__5;
lean::inc(x_2);
x_193 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_191, x_2, x_183);
x_194 = lean::cnstr_get(x_193, 0);
lean::inc(x_194);
x_196 = lean::cnstr_get(x_193, 1);
lean::inc(x_196);
lean::dec(x_193);
if (lean::obj_tag(x_194) == 0)
{
obj* x_199; obj* x_202; 
x_199 = lean::cnstr_get(x_194, 0);
lean::inc(x_199);
lean::dec(x_194);
if (lean::is_scalar(x_177)) {
 x_202 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_202 = x_177;
 lean::cnstr_set_tag(x_177, 0);
}
lean::cnstr_set(x_202, 0, x_199);
x_117 = x_202;
x_118 = x_196;
goto lbl_119;
}
else
{
obj* x_203; obj* x_206; obj* x_208; obj* x_209; obj* x_211; 
x_203 = lean::cnstr_get(x_194, 0);
lean::inc(x_203);
lean::dec(x_194);
x_206 = l_option_has__repr___rarg___closed__3;
lean::inc(x_2);
x_208 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_206, x_2, x_196);
x_209 = lean::cnstr_get(x_208, 0);
lean::inc(x_209);
x_211 = lean::cnstr_get(x_208, 1);
lean::inc(x_211);
lean::dec(x_208);
if (lean::obj_tag(x_209) == 0)
{
obj* x_215; obj* x_218; 
lean::dec(x_203);
x_215 = lean::cnstr_get(x_209, 0);
lean::inc(x_215);
lean::dec(x_209);
if (lean::is_scalar(x_177)) {
 x_218 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_218 = x_177;
 lean::cnstr_set_tag(x_177, 0);
}
lean::cnstr_set(x_218, 0, x_215);
x_117 = x_218;
x_118 = x_211;
goto lbl_119;
}
else
{
obj* x_220; 
lean::dec(x_209);
if (lean::is_scalar(x_177)) {
 x_220 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_220 = x_177;
}
lean::cnstr_set(x_220, 0, x_203);
x_117 = x_220;
x_118 = x_211;
goto lbl_119;
}
}
}
}
}
lbl_125:
{
if (lean::obj_tag(x_123) == 0)
{
obj* x_223; obj* x_225; obj* x_226; 
lean::dec(x_8);
lean::dec(x_14);
x_223 = lean::cnstr_get(x_123, 0);
lean::inc(x_223);
if (lean::is_exclusive(x_123)) {
 lean::cnstr_release(x_123, 0);
 x_225 = x_123;
} else {
 lean::dec(x_123);
 x_225 = lean::box(0);
}
if (lean::is_scalar(x_225)) {
 x_226 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_226 = x_225;
}
lean::cnstr_set(x_226, 0, x_223);
x_117 = x_226;
x_118 = x_124;
goto lbl_119;
}
else
{
obj* x_227; obj* x_228; obj* x_230; obj* x_231; obj* x_233; 
if (lean::is_exclusive(x_123)) {
 lean::cnstr_release(x_123, 0);
 x_227 = x_123;
} else {
 lean::dec(x_123);
 x_227 = lean::box(0);
}
x_228 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
x_230 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_228, x_2, x_124);
x_231 = lean::cnstr_get(x_230, 0);
lean::inc(x_231);
x_233 = lean::cnstr_get(x_230, 1);
lean::inc(x_233);
lean::dec(x_230);
if (lean::obj_tag(x_231) == 0)
{
obj* x_238; obj* x_241; 
lean::dec(x_8);
lean::dec(x_14);
x_238 = lean::cnstr_get(x_231, 0);
lean::inc(x_238);
lean::dec(x_231);
if (lean::is_scalar(x_227)) {
 x_241 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_241 = x_227;
 lean::cnstr_set_tag(x_227, 0);
}
lean::cnstr_set(x_241, 0, x_238);
x_117 = x_241;
x_118 = x_233;
goto lbl_119;
}
else
{
obj* x_244; obj* x_245; obj* x_247; 
lean::dec(x_231);
lean::inc(x_2);
x_244 = l_lean_ir_cpp_emit__var(x_8, x_2, x_233);
x_245 = lean::cnstr_get(x_244, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get(x_244, 1);
lean::inc(x_247);
lean::dec(x_244);
if (lean::obj_tag(x_245) == 0)
{
obj* x_251; obj* x_254; 
lean::dec(x_14);
x_251 = lean::cnstr_get(x_245, 0);
lean::inc(x_251);
lean::dec(x_245);
if (lean::is_scalar(x_227)) {
 x_254 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_254 = x_227;
 lean::cnstr_set_tag(x_227, 0);
}
lean::cnstr_set(x_254, 0, x_251);
x_120 = x_254;
x_121 = x_247;
goto lbl_122;
}
else
{
obj* x_256; obj* x_258; obj* x_259; obj* x_261; 
lean::dec(x_245);
x_256 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
x_258 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_256, x_2, x_247);
x_259 = lean::cnstr_get(x_258, 0);
lean::inc(x_259);
x_261 = lean::cnstr_get(x_258, 1);
lean::inc(x_261);
lean::dec(x_258);
if (lean::obj_tag(x_259) == 0)
{
obj* x_265; obj* x_268; 
lean::dec(x_14);
x_265 = lean::cnstr_get(x_259, 0);
lean::inc(x_265);
lean::dec(x_259);
if (lean::is_scalar(x_227)) {
 x_268 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_268 = x_227;
 lean::cnstr_set_tag(x_227, 0);
}
lean::cnstr_set(x_268, 0, x_265);
x_120 = x_268;
x_121 = x_261;
goto lbl_122;
}
else
{
obj* x_272; obj* x_273; obj* x_275; 
lean::dec(x_259);
lean::dec(x_227);
lean::inc(x_2);
x_272 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_14, x_2, x_261);
x_273 = lean::cnstr_get(x_272, 0);
lean::inc(x_273);
x_275 = lean::cnstr_get(x_272, 1);
lean::inc(x_275);
lean::dec(x_272);
x_120 = x_273;
x_121 = x_275;
goto lbl_122;
}
}
}
}
}
lbl_128:
{
if (lean::obj_tag(x_126) == 0)
{
obj* x_280; obj* x_282; obj* x_283; 
lean::dec(x_10);
lean::dec(x_0);
x_280 = lean::cnstr_get(x_126, 0);
lean::inc(x_280);
if (lean::is_exclusive(x_126)) {
 lean::cnstr_release(x_126, 0);
 x_282 = x_126;
} else {
 lean::dec(x_126);
 x_282 = lean::box(0);
}
if (lean::is_scalar(x_282)) {
 x_283 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_283 = x_282;
}
lean::cnstr_set(x_283, 0, x_280);
x_123 = x_283;
x_124 = x_127;
goto lbl_125;
}
else
{
obj* x_284; obj* x_285; obj* x_286; obj* x_288; obj* x_289; obj* x_291; 
if (lean::is_exclusive(x_126)) {
 lean::cnstr_release(x_126, 0);
 x_284 = x_126;
} else {
 lean::dec(x_126);
 x_284 = lean::box(0);
}
x_285 = l_lean_ir_cpp_emit__apply___closed__2;
x_286 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_2);
x_288 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_285, x_286, x_10, x_2, x_127);
x_289 = lean::cnstr_get(x_288, 0);
lean::inc(x_289);
x_291 = lean::cnstr_get(x_288, 1);
lean::inc(x_291);
lean::dec(x_288);
if (lean::obj_tag(x_289) == 0)
{
obj* x_295; obj* x_298; 
lean::dec(x_0);
x_295 = lean::cnstr_get(x_289, 0);
lean::inc(x_295);
lean::dec(x_289);
if (lean::is_scalar(x_284)) {
 x_298 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_298 = x_284;
 lean::cnstr_set_tag(x_284, 0);
}
lean::cnstr_set(x_298, 0, x_295);
x_123 = x_298;
x_124 = x_291;
goto lbl_125;
}
else
{
obj* x_300; obj* x_302; obj* x_303; obj* x_305; 
lean::dec(x_289);
x_300 = l_lean_ir_cpp_emit__apply___closed__6;
lean::inc(x_2);
x_302 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_300, x_2, x_291);
x_303 = lean::cnstr_get(x_302, 0);
lean::inc(x_303);
x_305 = lean::cnstr_get(x_302, 1);
lean::inc(x_305);
lean::dec(x_302);
if (lean::obj_tag(x_303) == 0)
{
obj* x_309; obj* x_312; 
lean::dec(x_0);
x_309 = lean::cnstr_get(x_303, 0);
lean::inc(x_309);
lean::dec(x_303);
if (lean::is_scalar(x_284)) {
 x_312 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_312 = x_284;
 lean::cnstr_set_tag(x_284, 0);
}
lean::cnstr_set(x_312, 0, x_309);
x_123 = x_312;
x_124 = x_305;
goto lbl_125;
}
else
{
obj* x_315; obj* x_316; obj* x_318; 
lean::dec(x_303);
lean::inc(x_2);
x_315 = l_lean_ir_cpp_emit__var(x_0, x_2, x_305);
x_316 = lean::cnstr_get(x_315, 0);
lean::inc(x_316);
x_318 = lean::cnstr_get(x_315, 1);
lean::inc(x_318);
lean::dec(x_315);
if (lean::obj_tag(x_316) == 0)
{
obj* x_321; obj* x_324; 
x_321 = lean::cnstr_get(x_316, 0);
lean::inc(x_321);
lean::dec(x_316);
if (lean::is_scalar(x_284)) {
 x_324 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_324 = x_284;
 lean::cnstr_set_tag(x_284, 0);
}
lean::cnstr_set(x_324, 0, x_321);
x_123 = x_324;
x_124 = x_318;
goto lbl_125;
}
else
{
obj* x_327; obj* x_329; obj* x_330; obj* x_332; 
lean::dec(x_284);
lean::dec(x_316);
x_327 = l_lean_ir_cpp_emit__apply___closed__7;
lean::inc(x_2);
x_329 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_327, x_2, x_318);
x_330 = lean::cnstr_get(x_329, 0);
lean::inc(x_330);
x_332 = lean::cnstr_get(x_329, 1);
lean::inc(x_332);
lean::dec(x_329);
x_123 = x_330;
x_124 = x_332;
goto lbl_125;
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
obj* x_7; obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_1);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_27; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_1, x_14);
x_22 = l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___closed__1;
lean::inc(x_3);
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_3, x_4);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_9);
lean::dec(x_1);
x_32 = lean::cnstr_get(x_25, 0);
lean::inc(x_32);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_34 = x_25;
} else {
 lean::dec(x_25);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_32);
x_16 = x_35;
x_17 = x_27;
goto lbl_18;
}
else
{
obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_42; 
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_36 = x_25;
} else {
 lean::dec(x_25);
 x_36 = lean::box(0);
}
x_37 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_37, x_3, x_27);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
if (lean::obj_tag(x_40) == 0)
{
obj* x_47; obj* x_50; 
lean::dec(x_9);
lean::dec(x_1);
x_47 = lean::cnstr_get(x_40, 0);
lean::inc(x_47);
lean::dec(x_40);
if (lean::is_scalar(x_36)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_36;
 lean::cnstr_set_tag(x_36, 0);
}
lean::cnstr_set(x_50, 0, x_47);
x_16 = x_50;
x_17 = x_42;
goto lbl_18;
}
else
{
obj* x_54; obj* x_55; obj* x_57; 
lean::dec(x_40);
lean::inc(x_3);
lean::inc(x_0);
x_54 = l_lean_ir_cpp_emit__var(x_0, x_3, x_42);
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
if (lean::obj_tag(x_55) == 0)
{
obj* x_61; obj* x_64; 
lean::dec(x_1);
x_61 = lean::cnstr_get(x_55, 0);
lean::inc(x_61);
lean::dec(x_55);
if (lean::is_scalar(x_36)) {
 x_64 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_64 = x_36;
 lean::cnstr_set_tag(x_36, 0);
}
lean::cnstr_set(x_64, 0, x_61);
x_19 = x_64;
x_20 = x_57;
goto lbl_21;
}
else
{
obj* x_66; obj* x_68; obj* x_69; obj* x_71; 
lean::dec(x_55);
x_66 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_3);
x_68 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_66, x_3, x_57);
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_68, 1);
lean::inc(x_71);
lean::dec(x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_75; obj* x_78; 
lean::dec(x_1);
x_75 = lean::cnstr_get(x_69, 0);
lean::inc(x_75);
lean::dec(x_69);
if (lean::is_scalar(x_36)) {
 x_78 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_78 = x_36;
 lean::cnstr_set_tag(x_36, 0);
}
lean::cnstr_set(x_78, 0, x_75);
x_19 = x_78;
x_20 = x_71;
goto lbl_21;
}
else
{
obj* x_82; obj* x_83; obj* x_85; 
lean::dec(x_69);
lean::dec(x_36);
lean::inc(x_3);
x_82 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_1, x_3, x_71);
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
x_19 = x_83;
x_20 = x_85;
goto lbl_21;
}
}
}
}
lbl_18:
{
if (lean::obj_tag(x_16) == 0)
{
obj* x_92; obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_92 = lean::cnstr_get(x_16, 0);
lean::inc(x_92);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_94 = x_16;
} else {
 lean::dec(x_16);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_92);
x_96 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_17);
return x_96;
}
else
{
lean::dec(x_16);
x_1 = x_15;
x_2 = x_11;
x_4 = x_17;
goto _start;
}
}
lbl_21:
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_9);
x_100 = lean::cnstr_get(x_19, 0);
lean::inc(x_100);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 x_102 = x_19;
} else {
 lean::dec(x_19);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_100);
x_16 = x_103;
x_17 = x_20;
goto lbl_18;
}
else
{
obj* x_104; obj* x_105; obj* x_107; obj* x_108; obj* x_110; 
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 x_104 = x_19;
} else {
 lean::dec(x_19);
 x_104 = lean::box(0);
}
x_105 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_3);
x_107 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_105, x_3, x_20);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_107, 1);
lean::inc(x_110);
lean::dec(x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_114; obj* x_117; 
lean::dec(x_9);
x_114 = lean::cnstr_get(x_108, 0);
lean::inc(x_114);
lean::dec(x_108);
if (lean::is_scalar(x_104)) {
 x_117 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_117 = x_104;
 lean::cnstr_set_tag(x_104, 0);
}
lean::cnstr_set(x_117, 0, x_114);
x_16 = x_117;
x_17 = x_110;
goto lbl_18;
}
else
{
obj* x_120; obj* x_121; obj* x_123; 
lean::dec(x_108);
lean::inc(x_3);
x_120 = l_lean_ir_cpp_emit__var(x_9, x_3, x_110);
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
if (lean::is_scalar(x_104)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_104;
 lean::cnstr_set_tag(x_104, 0);
}
lean::cnstr_set(x_129, 0, x_126);
x_16 = x_129;
x_17 = x_123;
goto lbl_18;
}
else
{
obj* x_130; obj* x_133; obj* x_135; obj* x_136; obj* x_138; 
x_130 = lean::cnstr_get(x_121, 0);
lean::inc(x_130);
lean::dec(x_121);
x_133 = l_option_has__repr___rarg___closed__3;
lean::inc(x_3);
x_135 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_133, x_3, x_123);
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_135, 1);
lean::inc(x_138);
lean::dec(x_135);
if (lean::obj_tag(x_136) == 0)
{
obj* x_142; obj* x_145; 
lean::dec(x_130);
x_142 = lean::cnstr_get(x_136, 0);
lean::inc(x_142);
lean::dec(x_136);
if (lean::is_scalar(x_104)) {
 x_145 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_145 = x_104;
 lean::cnstr_set_tag(x_104, 0);
}
lean::cnstr_set(x_145, 0, x_142);
x_16 = x_145;
x_17 = x_138;
goto lbl_18;
}
else
{
obj* x_147; 
lean::dec(x_136);
if (lean::is_scalar(x_104)) {
 x_147 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_147 = x_104;
}
lean::cnstr_set(x_147, 0, x_130);
x_16 = x_147;
x_17 = x_138;
goto lbl_18;
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
obj* x_18; obj* x_23; obj* x_24; obj* x_26; obj* x_28; 
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
lean::dec(x_11);
lean::inc(x_3);
lean::inc(x_0);
x_23 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 lean::cnstr_release(x_23, 1);
 x_28 = x_23;
} else {
 lean::dec(x_23);
 x_28 = lean::box(0);
}
if (lean::obj_tag(x_24) == 0)
{
obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_2);
x_34 = lean::cnstr_get(x_24, 0);
lean::inc(x_34);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_36 = x_24;
} else {
 lean::dec(x_24);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
if (lean::is_scalar(x_28)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_28;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_26);
return x_38;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; 
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_39 = x_24;
} else {
 lean::dec(x_24);
 x_39 = lean::box(0);
}
x_43 = l_lean_ir_cpp_emit__closure___closed__2;
lean::inc(x_3);
x_45 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_43, x_3, x_26);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_50 = x_45;
} else {
 lean::dec(x_45);
 x_50 = lean::box(0);
}
if (lean::obj_tag(x_46) == 0)
{
obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_2);
lean::dec(x_28);
lean::dec(x_39);
x_58 = lean::cnstr_get(x_46, 0);
lean::inc(x_58);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_60 = x_46;
} else {
 lean::dec(x_46);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_58);
if (lean::is_scalar(x_50)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_50;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_48);
return x_62;
}
else
{
obj* x_63; obj* x_65; obj* x_66; obj* x_68; 
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_63 = x_46;
} else {
 lean::dec(x_46);
 x_63 = lean::box(0);
}
lean::inc(x_3);
x_65 = l_lean_ir_cpp_fid2cpp(x_1, x_3, x_48);
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_65, 1);
lean::inc(x_68);
lean::dec(x_65);
if (lean::obj_tag(x_66) == 0)
{
obj* x_77; obj* x_80; obj* x_81; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_2);
lean::dec(x_28);
lean::dec(x_39);
x_77 = lean::cnstr_get(x_66, 0);
lean::inc(x_77);
lean::dec(x_66);
if (lean::is_scalar(x_63)) {
 x_80 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_80 = x_63;
 lean::cnstr_set_tag(x_63, 0);
}
lean::cnstr_set(x_80, 0, x_77);
if (lean::is_scalar(x_50)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_50;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_68);
return x_81;
}
else
{
obj* x_83; obj* x_85; obj* x_86; obj* x_87; obj* x_90; obj* x_91; obj* x_92; uint8 x_93; obj* x_95; obj* x_96; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_50);
x_83 = lean::cnstr_get(x_66, 0);
lean::inc(x_83);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_85 = x_66;
} else {
 lean::dec(x_66);
 x_85 = lean::box(0);
}
x_86 = l_lean_ir_decl_header___main(x_18);
x_87 = lean::cnstr_get(x_86, 1);
lean::inc(x_87);
lean::dec(x_86);
x_90 = lean::mk_nat_obj(0u);
x_91 = l_list_length__aux___main___rarg(x_87, x_90);
x_92 = l_lean_closure__max__args;
x_93 = lean::nat_dec_lt(x_92, x_91);
lean::inc(x_2);
x_95 = l_list_length__aux___main___rarg(x_2, x_90);
x_96 = l_lean_ir_cpp_emit__closure___closed__3;
lean::inc(x_3);
x_98 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_96, x_3, x_68);
if (x_93 == 0)
{
obj* x_102; obj* x_104; 
x_102 = lean::cnstr_get(x_98, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_98, 1);
lean::inc(x_104);
lean::dec(x_98);
if (lean::obj_tag(x_102) == 0)
{
obj* x_108; obj* x_111; 
lean::dec(x_83);
x_108 = lean::cnstr_get(x_102, 0);
lean::inc(x_108);
lean::dec(x_102);
if (lean::is_scalar(x_85)) {
 x_111 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_111 = x_85;
 lean::cnstr_set_tag(x_85, 0);
}
lean::cnstr_set(x_111, 0, x_108);
x_99 = x_111;
x_100 = x_104;
goto lbl_101;
}
else
{
obj* x_115; obj* x_116; obj* x_118; 
lean::dec(x_85);
lean::dec(x_102);
lean::inc(x_3);
x_115 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_83, x_3, x_104);
x_116 = lean::cnstr_get(x_115, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_115, 1);
lean::inc(x_118);
lean::dec(x_115);
x_99 = x_116;
x_100 = x_118;
goto lbl_101;
}
}
else
{
obj* x_121; obj* x_123; 
x_121 = lean::cnstr_get(x_98, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_98, 1);
lean::inc(x_123);
lean::dec(x_98);
if (lean::obj_tag(x_121) == 0)
{
obj* x_127; obj* x_130; 
lean::dec(x_83);
x_127 = lean::cnstr_get(x_121, 0);
lean::inc(x_127);
lean::dec(x_121);
if (lean::is_scalar(x_85)) {
 x_130 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_130 = x_85;
 lean::cnstr_set_tag(x_85, 0);
}
lean::cnstr_set(x_130, 0, x_127);
x_99 = x_130;
x_100 = x_123;
goto lbl_101;
}
else
{
obj* x_133; obj* x_134; obj* x_137; obj* x_138; obj* x_140; 
lean::dec(x_85);
lean::dec(x_121);
x_133 = l_lean_ir_cpp_emit__closure___closed__4;
x_134 = lean::string_append(x_133, x_83);
lean::dec(x_83);
lean::inc(x_3);
x_137 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_134, x_3, x_123);
x_138 = lean::cnstr_get(x_137, 0);
lean::inc(x_138);
x_140 = lean::cnstr_get(x_137, 1);
lean::inc(x_140);
lean::dec(x_137);
x_99 = x_138;
x_100 = x_140;
goto lbl_101;
}
}
lbl_101:
{
if (lean::obj_tag(x_99) == 0)
{
obj* x_145; obj* x_148; 
lean::dec(x_95);
lean::dec(x_91);
x_145 = lean::cnstr_get(x_99, 0);
lean::inc(x_145);
lean::dec(x_99);
if (lean::is_scalar(x_63)) {
 x_148 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_148 = x_63;
 lean::cnstr_set_tag(x_63, 0);
}
lean::cnstr_set(x_148, 0, x_145);
x_40 = x_148;
x_41 = x_100;
goto lbl_42;
}
else
{
obj* x_150; obj* x_152; obj* x_153; obj* x_155; 
lean::dec(x_99);
x_150 = l_option_has__repr___rarg___closed__3;
lean::inc(x_3);
x_152 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_150, x_3, x_100);
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_152, 1);
lean::inc(x_155);
lean::dec(x_152);
if (lean::obj_tag(x_153) == 0)
{
obj* x_160; obj* x_163; 
lean::dec(x_95);
lean::dec(x_91);
x_160 = lean::cnstr_get(x_153, 0);
lean::inc(x_160);
lean::dec(x_153);
if (lean::is_scalar(x_63)) {
 x_163 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_163 = x_63;
 lean::cnstr_set_tag(x_63, 0);
}
lean::cnstr_set(x_163, 0, x_160);
x_40 = x_163;
x_41 = x_155;
goto lbl_42;
}
else
{
obj* x_165; obj* x_167; obj* x_168; obj* x_170; 
lean::dec(x_153);
x_165 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_3);
x_167 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_165, x_3, x_155);
x_168 = lean::cnstr_get(x_167, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_167, 1);
lean::inc(x_170);
lean::dec(x_167);
if (lean::obj_tag(x_168) == 0)
{
obj* x_175; obj* x_178; 
lean::dec(x_95);
lean::dec(x_91);
x_175 = lean::cnstr_get(x_168, 0);
lean::inc(x_175);
lean::dec(x_168);
if (lean::is_scalar(x_63)) {
 x_178 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_178 = x_63;
 lean::cnstr_set_tag(x_63, 0);
}
lean::cnstr_set(x_178, 0, x_175);
x_40 = x_178;
x_41 = x_170;
goto lbl_42;
}
else
{
obj* x_181; obj* x_182; obj* x_184; 
lean::dec(x_168);
lean::inc(x_3);
x_181 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_91, x_3, x_170);
x_182 = lean::cnstr_get(x_181, 0);
lean::inc(x_182);
x_184 = lean::cnstr_get(x_181, 1);
lean::inc(x_184);
lean::dec(x_181);
if (lean::obj_tag(x_182) == 0)
{
obj* x_188; obj* x_191; 
lean::dec(x_95);
x_188 = lean::cnstr_get(x_182, 0);
lean::inc(x_188);
lean::dec(x_182);
if (lean::is_scalar(x_63)) {
 x_191 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_191 = x_63;
 lean::cnstr_set_tag(x_63, 0);
}
lean::cnstr_set(x_191, 0, x_188);
x_40 = x_191;
x_41 = x_184;
goto lbl_42;
}
else
{
obj* x_194; obj* x_195; obj* x_197; 
lean::dec(x_182);
lean::inc(x_3);
x_194 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_165, x_3, x_184);
x_195 = lean::cnstr_get(x_194, 0);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_194, 1);
lean::inc(x_197);
lean::dec(x_194);
if (lean::obj_tag(x_195) == 0)
{
obj* x_201; obj* x_204; 
lean::dec(x_95);
x_201 = lean::cnstr_get(x_195, 0);
lean::inc(x_201);
lean::dec(x_195);
if (lean::is_scalar(x_63)) {
 x_204 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_204 = x_63;
 lean::cnstr_set_tag(x_63, 0);
}
lean::cnstr_set(x_204, 0, x_201);
x_40 = x_204;
x_41 = x_197;
goto lbl_42;
}
else
{
obj* x_208; obj* x_209; obj* x_211; 
lean::dec(x_63);
lean::dec(x_195);
lean::inc(x_3);
x_208 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_95, x_3, x_197);
x_209 = lean::cnstr_get(x_208, 0);
lean::inc(x_209);
x_211 = lean::cnstr_get(x_208, 1);
lean::inc(x_211);
lean::dec(x_208);
x_40 = x_209;
x_41 = x_211;
goto lbl_42;
}
}
}
}
}
}
}
}
lbl_42:
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_217; obj* x_220; obj* x_221; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_217 = lean::cnstr_get(x_40, 0);
lean::inc(x_217);
lean::dec(x_40);
if (lean::is_scalar(x_39)) {
 x_220 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_220 = x_39;
 lean::cnstr_set_tag(x_39, 0);
}
lean::cnstr_set(x_220, 0, x_217);
if (lean::is_scalar(x_28)) {
 x_221 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_221 = x_28;
}
lean::cnstr_set(x_221, 0, x_220);
lean::cnstr_set(x_221, 1, x_41);
return x_221;
}
else
{
obj* x_223; obj* x_225; obj* x_226; obj* x_228; 
lean::dec(x_40);
x_223 = l_option_has__repr___rarg___closed__3;
lean::inc(x_3);
x_225 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_223, x_3, x_41);
x_226 = lean::cnstr_get(x_225, 0);
lean::inc(x_226);
x_228 = lean::cnstr_get(x_225, 1);
lean::inc(x_228);
lean::dec(x_225);
if (lean::obj_tag(x_226) == 0)
{
obj* x_234; obj* x_237; obj* x_238; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_234 = lean::cnstr_get(x_226, 0);
lean::inc(x_234);
lean::dec(x_226);
if (lean::is_scalar(x_39)) {
 x_237 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_237 = x_39;
 lean::cnstr_set_tag(x_39, 0);
}
lean::cnstr_set(x_237, 0, x_234);
if (lean::is_scalar(x_28)) {
 x_238 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_238 = x_28;
}
lean::cnstr_set(x_238, 0, x_237);
lean::cnstr_set(x_238, 1, x_228);
return x_238;
}
else
{
obj* x_240; obj* x_241; obj* x_242; obj* x_244; 
lean::dec(x_226);
x_240 = lean::mk_nat_obj(0u);
x_241 = l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1(x_0, x_240, x_2, x_3, x_228);
x_242 = lean::cnstr_get(x_241, 0);
lean::inc(x_242);
x_244 = lean::cnstr_get(x_241, 1);
lean::inc(x_244);
lean::dec(x_241);
if (lean::obj_tag(x_242) == 0)
{
obj* x_247; obj* x_250; obj* x_251; 
x_247 = lean::cnstr_get(x_242, 0);
lean::inc(x_247);
lean::dec(x_242);
if (lean::is_scalar(x_39)) {
 x_250 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_250 = x_39;
 lean::cnstr_set_tag(x_39, 0);
}
lean::cnstr_set(x_250, 0, x_247);
if (lean::is_scalar(x_28)) {
 x_251 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_251 = x_28;
}
lean::cnstr_set(x_251, 0, x_250);
lean::cnstr_set(x_251, 1, x_244);
return x_251;
}
else
{
obj* x_254; obj* x_255; 
lean::dec(x_242);
lean::dec(x_39);
x_254 = l_lean_ir_match__type___closed__5;
if (lean::is_scalar(x_28)) {
 x_255 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_255 = x_28;
}
lean::cnstr_set(x_255, 0, x_254);
lean::cnstr_set(x_255, 1, x_244);
return x_255;
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
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_4 = lean::usize_to_nat(x_0);
x_5 = l_nat_repr(x_4);
x_6 = lean::string_append(x_2, x_5);
lean::dec(x_5);
x_8 = l_lean_ir_match__type___closed__5;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_6);
return x_9;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__2(uint16 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_4 = lean::uint16_to_nat(x_0);
x_5 = l_nat_repr(x_4);
x_6 = lean::string_append(x_2, x_5);
lean::dec(x_5);
x_8 = l_lean_ir_match__type___closed__5;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_6);
return x_9;
}
}
obj* l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(uint16 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_4 = lean::uint16_to_nat(x_0);
x_5 = l_nat_repr(x_4);
x_6 = lean::string_append(x_2, x_5);
lean::dec(x_5);
x_8 = l_lean_ir_match__type___closed__5;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_6);
return x_9;
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
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
} else {
 lean::dec(x_10);
 x_15 = lean::box(0);
}
if (lean::obj_tag(x_11) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_19 = x_11;
} else {
 lean::dec(x_11);
 x_19 = lean::box(0);
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
obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_28; 
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_22 = x_11;
} else {
 lean::dec(x_11);
 x_22 = lean::box(0);
}
x_23 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_1);
x_25 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_23, x_1, x_13);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_32; obj* x_35; obj* x_36; 
lean::dec(x_7);
x_32 = lean::cnstr_get(x_26, 0);
lean::inc(x_32);
lean::dec(x_26);
if (lean::is_scalar(x_22)) {
 x_35 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_35 = x_22;
 lean::cnstr_set_tag(x_22, 0);
}
lean::cnstr_set(x_35, 0, x_32);
if (lean::is_scalar(x_15)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_15;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_28);
x_3 = x_36;
goto lbl_4;
}
else
{
obj* x_41; 
lean::dec(x_15);
lean::dec(x_22);
lean::dec(x_26);
lean::inc(x_1);
x_41 = l_lean_ir_cpp_emit__var(x_7, x_1, x_28);
x_3 = x_41;
goto lbl_4;
}
}
}
case 1:
{
obj* x_42; uint8 x_44; obj* x_45; obj* x_48; 
x_42 = lean::cnstr_get(x_0, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_45 = lean::cnstr_get(x_0, 1);
lean::inc(x_45);
lean::inc(x_1);
x_48 = l_lean_ir_cpp_emit__assign__lit(x_42, x_44, x_45, x_1, x_2);
x_3 = x_48;
goto lbl_4;
}
case 2:
{
obj* x_49; uint8 x_51; uint8 x_52; obj* x_53; obj* x_56; 
x_49 = lean::cnstr_get(x_0, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_52 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2 + 1);
x_53 = lean::cnstr_get(x_0, 1);
lean::inc(x_53);
lean::inc(x_1);
x_56 = l_lean_ir_cpp_emit__assign__unop(x_49, x_51, x_52, x_53, x_1, x_2);
x_3 = x_56;
goto lbl_4;
}
case 3:
{
obj* x_57; uint8 x_59; uint8 x_60; obj* x_61; obj* x_63; obj* x_66; 
x_57 = lean::cnstr_get(x_0, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_60 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3 + 1);
x_61 = lean::cnstr_get(x_0, 1);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_0, 2);
lean::inc(x_63);
lean::inc(x_1);
x_66 = l_lean_ir_cpp_emit__assign__binop(x_57, x_59, x_60, x_61, x_63, x_1, x_2);
x_3 = x_66;
goto lbl_4;
}
case 4:
{
uint8 x_67; obj* x_68; obj* x_71; 
x_67 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
x_68 = lean::cnstr_get(x_0, 0);
lean::inc(x_68);
lean::inc(x_1);
x_71 = l_lean_ir_cpp_emit__unop(x_67, x_68, x_1, x_2);
x_3 = x_71;
goto lbl_4;
}
case 5:
{
obj* x_72; obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_82; obj* x_83; obj* x_85; 
x_72 = lean::cnstr_get(x_0, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_0, 1);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_0, 2);
lean::inc(x_76);
lean::inc(x_1);
x_82 = l_lean_ir_cpp_emit__var(x_72, x_1, x_2);
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
if (lean::obj_tag(x_83) == 0)
{
obj* x_88; obj* x_90; obj* x_91; 
x_88 = lean::cnstr_get(x_83, 0);
lean::inc(x_88);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 x_90 = x_83;
} else {
 lean::dec(x_83);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_88);
x_78 = x_91;
x_79 = x_85;
goto lbl_80;
}
else
{
obj* x_93; obj* x_95; obj* x_96; obj* x_98; 
lean::dec(x_83);
x_93 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_1);
x_95 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_93, x_1, x_85);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_95, 1);
lean::inc(x_98);
lean::dec(x_95);
x_78 = x_96;
x_79 = x_98;
goto lbl_80;
}
lbl_80:
{
if (lean::obj_tag(x_78) == 0)
{
obj* x_103; obj* x_105; obj* x_106; obj* x_107; 
lean::dec(x_74);
lean::dec(x_76);
x_103 = lean::cnstr_get(x_78, 0);
lean::inc(x_103);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 x_105 = x_78;
} else {
 lean::dec(x_78);
 x_105 = lean::box(0);
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_103);
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_79);
x_3 = x_107;
goto lbl_4;
}
else
{
obj* x_108; obj* x_111; obj* x_112; obj* x_114; obj* x_116; obj* x_117; 
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 x_108 = x_78;
} else {
 lean::dec(x_78);
 x_108 = lean::box(0);
}
lean::inc(x_1);
lean::inc(x_74);
x_111 = l_lean_ir_cpp_is__const(x_74, x_1, x_79);
x_112 = lean::cnstr_get(x_111, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_111, 1);
lean::inc(x_114);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 lean::cnstr_release(x_111, 1);
 x_116 = x_111;
} else {
 lean::dec(x_111);
 x_116 = lean::box(0);
}
if (lean::obj_tag(x_112) == 0)
{
obj* x_123; obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_116);
lean::dec(x_108);
lean::dec(x_74);
lean::dec(x_76);
x_123 = lean::cnstr_get(x_112, 0);
lean::inc(x_123);
if (lean::is_exclusive(x_112)) {
 lean::cnstr_release(x_112, 0);
 x_125 = x_112;
} else {
 lean::dec(x_112);
 x_125 = lean::box(0);
}
if (lean::is_scalar(x_125)) {
 x_126 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_126 = x_125;
}
lean::cnstr_set(x_126, 0, x_123);
x_127 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_114);
x_3 = x_127;
goto lbl_4;
}
else
{
obj* x_128; uint8 x_131; 
x_128 = lean::cnstr_get(x_112, 0);
lean::inc(x_128);
lean::dec(x_112);
x_131 = lean::unbox(x_128);
lean::dec(x_128);
if (x_131 == 0)
{
obj* x_133; 
x_133 = lean::box(0);
x_117 = x_133;
goto lbl_118;
}
else
{
obj* x_138; 
lean::dec(x_116);
lean::dec(x_108);
lean::dec(x_76);
lean::inc(x_1);
x_138 = l_lean_ir_cpp_emit__global(x_74, x_1, x_114);
x_3 = x_138;
goto lbl_4;
}
}
lbl_118:
{
obj* x_141; obj* x_142; obj* x_144; 
lean::dec(x_117);
lean::inc(x_1);
x_141 = l_lean_ir_cpp_emit__fnid(x_74, x_1, x_114);
x_142 = lean::cnstr_get(x_141, 0);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_141, 1);
lean::inc(x_144);
lean::dec(x_141);
if (lean::obj_tag(x_142) == 0)
{
obj* x_148; obj* x_151; obj* x_152; 
lean::dec(x_76);
x_148 = lean::cnstr_get(x_142, 0);
lean::inc(x_148);
lean::dec(x_142);
if (lean::is_scalar(x_108)) {
 x_151 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_151 = x_108;
 lean::cnstr_set_tag(x_108, 0);
}
lean::cnstr_set(x_151, 0, x_148);
if (lean::is_scalar(x_116)) {
 x_152 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_152 = x_116;
}
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_144);
x_3 = x_152;
goto lbl_4;
}
else
{
obj* x_154; obj* x_156; obj* x_157; obj* x_159; 
lean::dec(x_142);
x_154 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_156 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_154, x_1, x_144);
x_157 = lean::cnstr_get(x_156, 0);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_156, 1);
lean::inc(x_159);
lean::dec(x_156);
if (lean::obj_tag(x_157) == 0)
{
obj* x_163; obj* x_166; obj* x_167; 
lean::dec(x_76);
x_163 = lean::cnstr_get(x_157, 0);
lean::inc(x_163);
lean::dec(x_157);
if (lean::is_scalar(x_108)) {
 x_166 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_166 = x_108;
 lean::cnstr_set_tag(x_108, 0);
}
lean::cnstr_set(x_166, 0, x_163);
if (lean::is_scalar(x_116)) {
 x_167 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_167 = x_116;
}
lean::cnstr_set(x_167, 0, x_166);
lean::cnstr_set(x_167, 1, x_159);
x_3 = x_167;
goto lbl_4;
}
else
{
obj* x_169; obj* x_170; obj* x_172; obj* x_173; obj* x_175; 
lean::dec(x_157);
x_169 = l_lean_ir_cpp_emit__apply___closed__2;
x_170 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_1);
x_172 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_169, x_170, x_76, x_1, x_159);
x_173 = lean::cnstr_get(x_172, 0);
lean::inc(x_173);
x_175 = lean::cnstr_get(x_172, 1);
lean::inc(x_175);
lean::dec(x_172);
if (lean::obj_tag(x_173) == 0)
{
obj* x_178; obj* x_181; obj* x_182; 
x_178 = lean::cnstr_get(x_173, 0);
lean::inc(x_178);
lean::dec(x_173);
if (lean::is_scalar(x_108)) {
 x_181 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_181 = x_108;
 lean::cnstr_set_tag(x_108, 0);
}
lean::cnstr_set(x_181, 0, x_178);
if (lean::is_scalar(x_116)) {
 x_182 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_182 = x_116;
}
lean::cnstr_set(x_182, 0, x_181);
lean::cnstr_set(x_182, 1, x_175);
x_3 = x_182;
goto lbl_4;
}
else
{
obj* x_183; obj* x_186; obj* x_188; obj* x_189; obj* x_191; 
x_183 = lean::cnstr_get(x_173, 0);
lean::inc(x_183);
lean::dec(x_173);
x_186 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_188 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_186, x_1, x_175);
x_189 = lean::cnstr_get(x_188, 0);
lean::inc(x_189);
x_191 = lean::cnstr_get(x_188, 1);
lean::inc(x_191);
lean::dec(x_188);
if (lean::obj_tag(x_189) == 0)
{
obj* x_195; obj* x_198; obj* x_199; 
lean::dec(x_183);
x_195 = lean::cnstr_get(x_189, 0);
lean::inc(x_195);
lean::dec(x_189);
if (lean::is_scalar(x_108)) {
 x_198 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_198 = x_108;
 lean::cnstr_set_tag(x_108, 0);
}
lean::cnstr_set(x_198, 0, x_195);
if (lean::is_scalar(x_116)) {
 x_199 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_199 = x_116;
}
lean::cnstr_set(x_199, 0, x_198);
lean::cnstr_set(x_199, 1, x_191);
x_3 = x_199;
goto lbl_4;
}
else
{
obj* x_201; obj* x_202; 
lean::dec(x_189);
if (lean::is_scalar(x_108)) {
 x_201 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_201 = x_108;
}
lean::cnstr_set(x_201, 0, x_183);
if (lean::is_scalar(x_116)) {
 x_202 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_202 = x_116;
}
lean::cnstr_set(x_202, 0, x_201);
lean::cnstr_set(x_202, 1, x_191);
x_3 = x_202;
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
obj* x_203; uint16 x_205; uint16 x_206; usize x_207; obj* x_208; obj* x_209; obj* x_211; obj* x_212; obj* x_215; obj* x_216; obj* x_218; 
x_203 = lean::cnstr_get(x_0, 0);
lean::inc(x_203);
x_205 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
x_206 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2 + 2);
x_207 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*1);
lean::inc(x_1);
x_215 = l_lean_ir_cpp_emit__var(x_203, x_1, x_2);
x_216 = lean::cnstr_get(x_215, 0);
lean::inc(x_216);
x_218 = lean::cnstr_get(x_215, 1);
lean::inc(x_218);
lean::dec(x_215);
if (lean::obj_tag(x_216) == 0)
{
obj* x_221; obj* x_223; obj* x_224; 
x_221 = lean::cnstr_get(x_216, 0);
lean::inc(x_221);
if (lean::is_exclusive(x_216)) {
 lean::cnstr_release(x_216, 0);
 x_223 = x_216;
} else {
 lean::dec(x_216);
 x_223 = lean::box(0);
}
if (lean::is_scalar(x_223)) {
 x_224 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_224 = x_223;
}
lean::cnstr_set(x_224, 0, x_221);
x_211 = x_224;
x_212 = x_218;
goto lbl_213;
}
else
{
obj* x_226; obj* x_228; obj* x_229; obj* x_231; 
lean::dec(x_216);
x_226 = l_lean_ir_cpp_emit__instr___closed__1;
lean::inc(x_1);
x_228 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_226, x_1, x_218);
x_229 = lean::cnstr_get(x_228, 0);
lean::inc(x_229);
x_231 = lean::cnstr_get(x_228, 1);
lean::inc(x_231);
lean::dec(x_228);
x_211 = x_229;
x_212 = x_231;
goto lbl_213;
}
lbl_210:
{
if (lean::obj_tag(x_208) == 0)
{
obj* x_234; obj* x_236; obj* x_237; obj* x_238; 
x_234 = lean::cnstr_get(x_208, 0);
lean::inc(x_234);
if (lean::is_exclusive(x_208)) {
 lean::cnstr_release(x_208, 0);
 x_236 = x_208;
} else {
 lean::dec(x_208);
 x_236 = lean::box(0);
}
if (lean::is_scalar(x_236)) {
 x_237 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_237 = x_236;
}
lean::cnstr_set(x_237, 0, x_234);
x_238 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_238, 0, x_237);
lean::cnstr_set(x_238, 1, x_209);
x_3 = x_238;
goto lbl_4;
}
else
{
obj* x_239; obj* x_240; obj* x_242; obj* x_243; obj* x_245; obj* x_247; 
if (lean::is_exclusive(x_208)) {
 lean::cnstr_release(x_208, 0);
 x_239 = x_208;
} else {
 lean::dec(x_208);
 x_239 = lean::box(0);
}
x_240 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_242 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_240, x_1, x_209);
x_243 = lean::cnstr_get(x_242, 0);
lean::inc(x_243);
x_245 = lean::cnstr_get(x_242, 1);
lean::inc(x_245);
if (lean::is_exclusive(x_242)) {
 lean::cnstr_release(x_242, 0);
 lean::cnstr_release(x_242, 1);
 x_247 = x_242;
} else {
 lean::dec(x_242);
 x_247 = lean::box(0);
}
if (lean::obj_tag(x_243) == 0)
{
obj* x_248; obj* x_251; obj* x_252; 
x_248 = lean::cnstr_get(x_243, 0);
lean::inc(x_248);
lean::dec(x_243);
if (lean::is_scalar(x_239)) {
 x_251 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_251 = x_239;
 lean::cnstr_set_tag(x_239, 0);
}
lean::cnstr_set(x_251, 0, x_248);
if (lean::is_scalar(x_247)) {
 x_252 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_252 = x_247;
}
lean::cnstr_set(x_252, 0, x_251);
lean::cnstr_set(x_252, 1, x_245);
x_3 = x_252;
goto lbl_4;
}
else
{
obj* x_255; obj* x_256; obj* x_258; 
lean::dec(x_243);
lean::inc(x_1);
x_255 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(x_207, x_1, x_245);
x_256 = lean::cnstr_get(x_255, 0);
lean::inc(x_256);
x_258 = lean::cnstr_get(x_255, 1);
lean::inc(x_258);
lean::dec(x_255);
if (lean::obj_tag(x_256) == 0)
{
obj* x_261; obj* x_264; obj* x_265; 
x_261 = lean::cnstr_get(x_256, 0);
lean::inc(x_261);
lean::dec(x_256);
if (lean::is_scalar(x_239)) {
 x_264 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_264 = x_239;
 lean::cnstr_set_tag(x_239, 0);
}
lean::cnstr_set(x_264, 0, x_261);
if (lean::is_scalar(x_247)) {
 x_265 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_265 = x_247;
}
lean::cnstr_set(x_265, 0, x_264);
lean::cnstr_set(x_265, 1, x_258);
x_3 = x_265;
goto lbl_4;
}
else
{
obj* x_266; obj* x_269; obj* x_271; obj* x_272; obj* x_274; 
x_266 = lean::cnstr_get(x_256, 0);
lean::inc(x_266);
lean::dec(x_256);
x_269 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_271 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_269, x_1, x_258);
x_272 = lean::cnstr_get(x_271, 0);
lean::inc(x_272);
x_274 = lean::cnstr_get(x_271, 1);
lean::inc(x_274);
lean::dec(x_271);
if (lean::obj_tag(x_272) == 0)
{
obj* x_278; obj* x_281; obj* x_282; 
lean::dec(x_266);
x_278 = lean::cnstr_get(x_272, 0);
lean::inc(x_278);
lean::dec(x_272);
if (lean::is_scalar(x_239)) {
 x_281 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_281 = x_239;
 lean::cnstr_set_tag(x_239, 0);
}
lean::cnstr_set(x_281, 0, x_278);
if (lean::is_scalar(x_247)) {
 x_282 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_282 = x_247;
}
lean::cnstr_set(x_282, 0, x_281);
lean::cnstr_set(x_282, 1, x_274);
x_3 = x_282;
goto lbl_4;
}
else
{
obj* x_284; obj* x_285; 
lean::dec(x_272);
if (lean::is_scalar(x_239)) {
 x_284 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_284 = x_239;
}
lean::cnstr_set(x_284, 0, x_266);
if (lean::is_scalar(x_247)) {
 x_285 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_285 = x_247;
}
lean::cnstr_set(x_285, 0, x_284);
lean::cnstr_set(x_285, 1, x_274);
x_3 = x_285;
goto lbl_4;
}
}
}
}
}
lbl_213:
{
if (lean::obj_tag(x_211) == 0)
{
obj* x_286; obj* x_288; obj* x_289; obj* x_290; 
x_286 = lean::cnstr_get(x_211, 0);
lean::inc(x_286);
if (lean::is_exclusive(x_211)) {
 lean::cnstr_release(x_211, 0);
 x_288 = x_211;
} else {
 lean::dec(x_211);
 x_288 = lean::box(0);
}
if (lean::is_scalar(x_288)) {
 x_289 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_289 = x_288;
}
lean::cnstr_set(x_289, 0, x_286);
x_290 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_290, 0, x_289);
lean::cnstr_set(x_290, 1, x_212);
x_3 = x_290;
goto lbl_4;
}
else
{
obj* x_291; obj* x_292; obj* x_294; obj* x_295; obj* x_297; obj* x_299; 
if (lean::is_exclusive(x_211)) {
 lean::cnstr_release(x_211, 0);
 x_291 = x_211;
} else {
 lean::dec(x_211);
 x_291 = lean::box(0);
}
x_292 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_294 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_292, x_1, x_212);
x_295 = lean::cnstr_get(x_294, 0);
lean::inc(x_295);
x_297 = lean::cnstr_get(x_294, 1);
lean::inc(x_297);
if (lean::is_exclusive(x_294)) {
 lean::cnstr_release(x_294, 0);
 lean::cnstr_release(x_294, 1);
 x_299 = x_294;
} else {
 lean::dec(x_294);
 x_299 = lean::box(0);
}
if (lean::obj_tag(x_295) == 0)
{
obj* x_300; obj* x_303; obj* x_304; 
x_300 = lean::cnstr_get(x_295, 0);
lean::inc(x_300);
lean::dec(x_295);
if (lean::is_scalar(x_291)) {
 x_303 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_303 = x_291;
 lean::cnstr_set_tag(x_291, 0);
}
lean::cnstr_set(x_303, 0, x_300);
if (lean::is_scalar(x_299)) {
 x_304 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_304 = x_299;
}
lean::cnstr_set(x_304, 0, x_303);
lean::cnstr_set(x_304, 1, x_297);
x_3 = x_304;
goto lbl_4;
}
else
{
obj* x_308; obj* x_309; obj* x_311; 
lean::dec(x_295);
lean::dec(x_299);
lean::inc(x_1);
x_308 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__2(x_205, x_1, x_297);
x_309 = lean::cnstr_get(x_308, 0);
lean::inc(x_309);
x_311 = lean::cnstr_get(x_308, 1);
lean::inc(x_311);
lean::dec(x_308);
if (lean::obj_tag(x_309) == 0)
{
obj* x_314; obj* x_317; 
x_314 = lean::cnstr_get(x_309, 0);
lean::inc(x_314);
lean::dec(x_309);
if (lean::is_scalar(x_291)) {
 x_317 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_317 = x_291;
 lean::cnstr_set_tag(x_291, 0);
}
lean::cnstr_set(x_317, 0, x_314);
x_208 = x_317;
x_209 = x_311;
goto lbl_210;
}
else
{
obj* x_319; obj* x_321; obj* x_322; obj* x_324; 
lean::dec(x_309);
x_319 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_321 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_319, x_1, x_311);
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
if (lean::is_scalar(x_291)) {
 x_330 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_330 = x_291;
 lean::cnstr_set_tag(x_291, 0);
}
lean::cnstr_set(x_330, 0, x_327);
x_208 = x_330;
x_209 = x_324;
goto lbl_210;
}
else
{
obj* x_334; obj* x_335; obj* x_337; 
lean::dec(x_322);
lean::dec(x_291);
lean::inc(x_1);
x_334 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_206, x_1, x_324);
x_335 = lean::cnstr_get(x_334, 0);
lean::inc(x_335);
x_337 = lean::cnstr_get(x_334, 1);
lean::inc(x_337);
lean::dec(x_334);
x_208 = x_335;
x_209 = x_337;
goto lbl_210;
}
}
}
}
}
}
case 7:
{
obj* x_340; uint16 x_342; obj* x_343; obj* x_345; obj* x_346; obj* x_348; obj* x_350; obj* x_351; obj* x_353; obj* x_355; 
x_340 = lean::cnstr_get(x_0, 0);
lean::inc(x_340);
x_342 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
x_343 = lean::cnstr_get(x_0, 1);
lean::inc(x_343);
x_348 = l_lean_ir_cpp_emit__instr___closed__2;
lean::inc(x_1);
x_350 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_348, x_1, x_2);
x_351 = lean::cnstr_get(x_350, 0);
lean::inc(x_351);
x_353 = lean::cnstr_get(x_350, 1);
lean::inc(x_353);
if (lean::is_exclusive(x_350)) {
 lean::cnstr_release(x_350, 0);
 lean::cnstr_release(x_350, 1);
 x_355 = x_350;
} else {
 lean::dec(x_350);
 x_355 = lean::box(0);
}
if (lean::obj_tag(x_351) == 0)
{
obj* x_358; obj* x_360; obj* x_361; obj* x_362; 
lean::dec(x_340);
lean::dec(x_343);
x_358 = lean::cnstr_get(x_351, 0);
lean::inc(x_358);
if (lean::is_exclusive(x_351)) {
 lean::cnstr_release(x_351, 0);
 x_360 = x_351;
} else {
 lean::dec(x_351);
 x_360 = lean::box(0);
}
if (lean::is_scalar(x_360)) {
 x_361 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_361 = x_360;
}
lean::cnstr_set(x_361, 0, x_358);
if (lean::is_scalar(x_355)) {
 x_362 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_362 = x_355;
}
lean::cnstr_set(x_362, 0, x_361);
lean::cnstr_set(x_362, 1, x_353);
x_3 = x_362;
goto lbl_4;
}
else
{
obj* x_363; obj* x_364; obj* x_366; obj* x_367; obj* x_369; 
if (lean::is_exclusive(x_351)) {
 lean::cnstr_release(x_351, 0);
 x_363 = x_351;
} else {
 lean::dec(x_351);
 x_363 = lean::box(0);
}
x_364 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_366 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_364, x_1, x_353);
x_367 = lean::cnstr_get(x_366, 0);
lean::inc(x_367);
x_369 = lean::cnstr_get(x_366, 1);
lean::inc(x_369);
lean::dec(x_366);
if (lean::obj_tag(x_367) == 0)
{
obj* x_374; obj* x_377; obj* x_378; 
lean::dec(x_340);
lean::dec(x_343);
x_374 = lean::cnstr_get(x_367, 0);
lean::inc(x_374);
lean::dec(x_367);
if (lean::is_scalar(x_363)) {
 x_377 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_377 = x_363;
 lean::cnstr_set_tag(x_363, 0);
}
lean::cnstr_set(x_377, 0, x_374);
if (lean::is_scalar(x_355)) {
 x_378 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_378 = x_355;
}
lean::cnstr_set(x_378, 0, x_377);
lean::cnstr_set(x_378, 1, x_369);
x_3 = x_378;
goto lbl_4;
}
else
{
obj* x_382; obj* x_383; obj* x_385; 
lean::dec(x_355);
lean::dec(x_367);
lean::inc(x_1);
x_382 = l_lean_ir_cpp_emit__var(x_340, x_1, x_369);
x_383 = lean::cnstr_get(x_382, 0);
lean::inc(x_383);
x_385 = lean::cnstr_get(x_382, 1);
lean::inc(x_385);
lean::dec(x_382);
if (lean::obj_tag(x_383) == 0)
{
obj* x_388; obj* x_391; 
x_388 = lean::cnstr_get(x_383, 0);
lean::inc(x_388);
lean::dec(x_383);
if (lean::is_scalar(x_363)) {
 x_391 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_391 = x_363;
 lean::cnstr_set_tag(x_363, 0);
}
lean::cnstr_set(x_391, 0, x_388);
x_345 = x_391;
x_346 = x_385;
goto lbl_347;
}
else
{
obj* x_393; obj* x_395; obj* x_396; obj* x_398; 
lean::dec(x_383);
x_393 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_395 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_393, x_1, x_385);
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
if (lean::is_scalar(x_363)) {
 x_404 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_404 = x_363;
 lean::cnstr_set_tag(x_363, 0);
}
lean::cnstr_set(x_404, 0, x_401);
x_345 = x_404;
x_346 = x_398;
goto lbl_347;
}
else
{
obj* x_408; obj* x_409; obj* x_411; 
lean::dec(x_363);
lean::dec(x_396);
lean::inc(x_1);
x_408 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_342, x_1, x_398);
x_409 = lean::cnstr_get(x_408, 0);
lean::inc(x_409);
x_411 = lean::cnstr_get(x_408, 1);
lean::inc(x_411);
lean::dec(x_408);
x_345 = x_409;
x_346 = x_411;
goto lbl_347;
}
}
}
}
lbl_347:
{
if (lean::obj_tag(x_345) == 0)
{
obj* x_415; obj* x_417; obj* x_418; obj* x_419; 
lean::dec(x_343);
x_415 = lean::cnstr_get(x_345, 0);
lean::inc(x_415);
if (lean::is_exclusive(x_345)) {
 lean::cnstr_release(x_345, 0);
 x_417 = x_345;
} else {
 lean::dec(x_345);
 x_417 = lean::box(0);
}
if (lean::is_scalar(x_417)) {
 x_418 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_418 = x_417;
}
lean::cnstr_set(x_418, 0, x_415);
x_419 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_419, 0, x_418);
lean::cnstr_set(x_419, 1, x_346);
x_3 = x_419;
goto lbl_4;
}
else
{
obj* x_420; obj* x_421; obj* x_423; obj* x_424; obj* x_426; obj* x_428; 
if (lean::is_exclusive(x_345)) {
 lean::cnstr_release(x_345, 0);
 x_420 = x_345;
} else {
 lean::dec(x_345);
 x_420 = lean::box(0);
}
x_421 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_423 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_421, x_1, x_346);
x_424 = lean::cnstr_get(x_423, 0);
lean::inc(x_424);
x_426 = lean::cnstr_get(x_423, 1);
lean::inc(x_426);
if (lean::is_exclusive(x_423)) {
 lean::cnstr_release(x_423, 0);
 lean::cnstr_release(x_423, 1);
 x_428 = x_423;
} else {
 lean::dec(x_423);
 x_428 = lean::box(0);
}
if (lean::obj_tag(x_424) == 0)
{
obj* x_430; obj* x_433; obj* x_434; 
lean::dec(x_343);
x_430 = lean::cnstr_get(x_424, 0);
lean::inc(x_430);
lean::dec(x_424);
if (lean::is_scalar(x_420)) {
 x_433 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_433 = x_420;
 lean::cnstr_set_tag(x_420, 0);
}
lean::cnstr_set(x_433, 0, x_430);
if (lean::is_scalar(x_428)) {
 x_434 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_434 = x_428;
}
lean::cnstr_set(x_434, 0, x_433);
lean::cnstr_set(x_434, 1, x_426);
x_3 = x_434;
goto lbl_4;
}
else
{
obj* x_437; obj* x_438; obj* x_440; 
lean::dec(x_424);
lean::inc(x_1);
x_437 = l_lean_ir_cpp_emit__var(x_343, x_1, x_426);
x_438 = lean::cnstr_get(x_437, 0);
lean::inc(x_438);
x_440 = lean::cnstr_get(x_437, 1);
lean::inc(x_440);
lean::dec(x_437);
if (lean::obj_tag(x_438) == 0)
{
obj* x_443; obj* x_446; obj* x_447; 
x_443 = lean::cnstr_get(x_438, 0);
lean::inc(x_443);
lean::dec(x_438);
if (lean::is_scalar(x_420)) {
 x_446 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_446 = x_420;
 lean::cnstr_set_tag(x_420, 0);
}
lean::cnstr_set(x_446, 0, x_443);
if (lean::is_scalar(x_428)) {
 x_447 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_447 = x_428;
}
lean::cnstr_set(x_447, 0, x_446);
lean::cnstr_set(x_447, 1, x_440);
x_3 = x_447;
goto lbl_4;
}
else
{
obj* x_448; obj* x_451; obj* x_453; obj* x_454; obj* x_456; 
x_448 = lean::cnstr_get(x_438, 0);
lean::inc(x_448);
lean::dec(x_438);
x_451 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_453 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_451, x_1, x_440);
x_454 = lean::cnstr_get(x_453, 0);
lean::inc(x_454);
x_456 = lean::cnstr_get(x_453, 1);
lean::inc(x_456);
lean::dec(x_453);
if (lean::obj_tag(x_454) == 0)
{
obj* x_460; obj* x_463; obj* x_464; 
lean::dec(x_448);
x_460 = lean::cnstr_get(x_454, 0);
lean::inc(x_460);
lean::dec(x_454);
if (lean::is_scalar(x_420)) {
 x_463 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_463 = x_420;
 lean::cnstr_set_tag(x_420, 0);
}
lean::cnstr_set(x_463, 0, x_460);
if (lean::is_scalar(x_428)) {
 x_464 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_464 = x_428;
}
lean::cnstr_set(x_464, 0, x_463);
lean::cnstr_set(x_464, 1, x_456);
x_3 = x_464;
goto lbl_4;
}
else
{
obj* x_466; obj* x_467; 
lean::dec(x_454);
if (lean::is_scalar(x_420)) {
 x_466 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_466 = x_420;
}
lean::cnstr_set(x_466, 0, x_448);
if (lean::is_scalar(x_428)) {
 x_467 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_467 = x_428;
}
lean::cnstr_set(x_467, 0, x_466);
lean::cnstr_set(x_467, 1, x_456);
x_3 = x_467;
goto lbl_4;
}
}
}
}
}
}
case 8:
{
obj* x_468; obj* x_470; uint16 x_472; obj* x_473; obj* x_474; obj* x_477; obj* x_478; obj* x_480; 
x_468 = lean::cnstr_get(x_0, 0);
lean::inc(x_468);
x_470 = lean::cnstr_get(x_0, 1);
lean::inc(x_470);
x_472 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
lean::inc(x_1);
x_477 = l_lean_ir_cpp_emit__var(x_468, x_1, x_2);
x_478 = lean::cnstr_get(x_477, 0);
lean::inc(x_478);
x_480 = lean::cnstr_get(x_477, 1);
lean::inc(x_480);
lean::dec(x_477);
if (lean::obj_tag(x_478) == 0)
{
obj* x_483; obj* x_485; obj* x_486; 
x_483 = lean::cnstr_get(x_478, 0);
lean::inc(x_483);
if (lean::is_exclusive(x_478)) {
 lean::cnstr_release(x_478, 0);
 x_485 = x_478;
} else {
 lean::dec(x_478);
 x_485 = lean::box(0);
}
if (lean::is_scalar(x_485)) {
 x_486 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_486 = x_485;
}
lean::cnstr_set(x_486, 0, x_483);
x_473 = x_486;
x_474 = x_480;
goto lbl_475;
}
else
{
obj* x_488; obj* x_490; obj* x_491; obj* x_493; 
lean::dec(x_478);
x_488 = l_lean_ir_cpp_emit__instr___closed__3;
lean::inc(x_1);
x_490 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_488, x_1, x_480);
x_491 = lean::cnstr_get(x_490, 0);
lean::inc(x_491);
x_493 = lean::cnstr_get(x_490, 1);
lean::inc(x_493);
lean::dec(x_490);
x_473 = x_491;
x_474 = x_493;
goto lbl_475;
}
lbl_475:
{
if (lean::obj_tag(x_473) == 0)
{
obj* x_497; obj* x_499; obj* x_500; obj* x_501; 
lean::dec(x_470);
x_497 = lean::cnstr_get(x_473, 0);
lean::inc(x_497);
if (lean::is_exclusive(x_473)) {
 lean::cnstr_release(x_473, 0);
 x_499 = x_473;
} else {
 lean::dec(x_473);
 x_499 = lean::box(0);
}
if (lean::is_scalar(x_499)) {
 x_500 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_500 = x_499;
}
lean::cnstr_set(x_500, 0, x_497);
x_501 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_501, 0, x_500);
lean::cnstr_set(x_501, 1, x_474);
x_3 = x_501;
goto lbl_4;
}
else
{
obj* x_502; obj* x_503; obj* x_505; obj* x_506; obj* x_508; obj* x_510; 
if (lean::is_exclusive(x_473)) {
 lean::cnstr_release(x_473, 0);
 x_502 = x_473;
} else {
 lean::dec(x_473);
 x_502 = lean::box(0);
}
x_503 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_505 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_503, x_1, x_474);
x_506 = lean::cnstr_get(x_505, 0);
lean::inc(x_506);
x_508 = lean::cnstr_get(x_505, 1);
lean::inc(x_508);
if (lean::is_exclusive(x_505)) {
 lean::cnstr_release(x_505, 0);
 lean::cnstr_release(x_505, 1);
 x_510 = x_505;
} else {
 lean::dec(x_505);
 x_510 = lean::box(0);
}
if (lean::obj_tag(x_506) == 0)
{
obj* x_512; obj* x_515; obj* x_516; 
lean::dec(x_470);
x_512 = lean::cnstr_get(x_506, 0);
lean::inc(x_512);
lean::dec(x_506);
if (lean::is_scalar(x_502)) {
 x_515 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_515 = x_502;
 lean::cnstr_set_tag(x_502, 0);
}
lean::cnstr_set(x_515, 0, x_512);
if (lean::is_scalar(x_510)) {
 x_516 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_516 = x_510;
}
lean::cnstr_set(x_516, 0, x_515);
lean::cnstr_set(x_516, 1, x_508);
x_3 = x_516;
goto lbl_4;
}
else
{
obj* x_519; obj* x_520; obj* x_522; 
lean::dec(x_506);
lean::inc(x_1);
x_519 = l_lean_ir_cpp_emit__var(x_470, x_1, x_508);
x_520 = lean::cnstr_get(x_519, 0);
lean::inc(x_520);
x_522 = lean::cnstr_get(x_519, 1);
lean::inc(x_522);
lean::dec(x_519);
if (lean::obj_tag(x_520) == 0)
{
obj* x_525; obj* x_528; obj* x_529; 
x_525 = lean::cnstr_get(x_520, 0);
lean::inc(x_525);
lean::dec(x_520);
if (lean::is_scalar(x_502)) {
 x_528 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_528 = x_502;
 lean::cnstr_set_tag(x_502, 0);
}
lean::cnstr_set(x_528, 0, x_525);
if (lean::is_scalar(x_510)) {
 x_529 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_529 = x_510;
}
lean::cnstr_set(x_529, 0, x_528);
lean::cnstr_set(x_529, 1, x_522);
x_3 = x_529;
goto lbl_4;
}
else
{
obj* x_531; obj* x_533; obj* x_534; obj* x_536; 
lean::dec(x_520);
x_531 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_533 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_531, x_1, x_522);
x_534 = lean::cnstr_get(x_533, 0);
lean::inc(x_534);
x_536 = lean::cnstr_get(x_533, 1);
lean::inc(x_536);
lean::dec(x_533);
if (lean::obj_tag(x_534) == 0)
{
obj* x_539; obj* x_542; obj* x_543; 
x_539 = lean::cnstr_get(x_534, 0);
lean::inc(x_539);
lean::dec(x_534);
if (lean::is_scalar(x_502)) {
 x_542 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_542 = x_502;
 lean::cnstr_set_tag(x_502, 0);
}
lean::cnstr_set(x_542, 0, x_539);
if (lean::is_scalar(x_510)) {
 x_543 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_543 = x_510;
}
lean::cnstr_set(x_543, 0, x_542);
lean::cnstr_set(x_543, 1, x_536);
x_3 = x_543;
goto lbl_4;
}
else
{
obj* x_546; obj* x_547; obj* x_549; 
lean::dec(x_534);
lean::inc(x_1);
x_546 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_472, x_1, x_536);
x_547 = lean::cnstr_get(x_546, 0);
lean::inc(x_547);
x_549 = lean::cnstr_get(x_546, 1);
lean::inc(x_549);
lean::dec(x_546);
if (lean::obj_tag(x_547) == 0)
{
obj* x_552; obj* x_555; obj* x_556; 
x_552 = lean::cnstr_get(x_547, 0);
lean::inc(x_552);
lean::dec(x_547);
if (lean::is_scalar(x_502)) {
 x_555 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_555 = x_502;
 lean::cnstr_set_tag(x_502, 0);
}
lean::cnstr_set(x_555, 0, x_552);
if (lean::is_scalar(x_510)) {
 x_556 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_556 = x_510;
}
lean::cnstr_set(x_556, 0, x_555);
lean::cnstr_set(x_556, 1, x_549);
x_3 = x_556;
goto lbl_4;
}
else
{
obj* x_557; obj* x_560; obj* x_562; obj* x_563; obj* x_565; 
x_557 = lean::cnstr_get(x_547, 0);
lean::inc(x_557);
lean::dec(x_547);
x_560 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_562 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_560, x_1, x_549);
x_563 = lean::cnstr_get(x_562, 0);
lean::inc(x_563);
x_565 = lean::cnstr_get(x_562, 1);
lean::inc(x_565);
lean::dec(x_562);
if (lean::obj_tag(x_563) == 0)
{
obj* x_569; obj* x_572; obj* x_573; 
lean::dec(x_557);
x_569 = lean::cnstr_get(x_563, 0);
lean::inc(x_569);
lean::dec(x_563);
if (lean::is_scalar(x_502)) {
 x_572 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_572 = x_502;
 lean::cnstr_set_tag(x_502, 0);
}
lean::cnstr_set(x_572, 0, x_569);
if (lean::is_scalar(x_510)) {
 x_573 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_573 = x_510;
}
lean::cnstr_set(x_573, 0, x_572);
lean::cnstr_set(x_573, 1, x_565);
x_3 = x_573;
goto lbl_4;
}
else
{
obj* x_575; obj* x_576; 
lean::dec(x_563);
if (lean::is_scalar(x_502)) {
 x_575 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_575 = x_502;
}
lean::cnstr_set(x_575, 0, x_557);
if (lean::is_scalar(x_510)) {
 x_576 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_576 = x_510;
}
lean::cnstr_set(x_576, 0, x_575);
lean::cnstr_set(x_576, 1, x_565);
x_3 = x_576;
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
obj* x_577; usize x_579; obj* x_580; obj* x_582; obj* x_583; obj* x_585; obj* x_587; obj* x_588; obj* x_590; obj* x_592; 
x_577 = lean::cnstr_get(x_0, 0);
lean::inc(x_577);
x_579 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
x_580 = lean::cnstr_get(x_0, 1);
lean::inc(x_580);
x_585 = l_lean_ir_cpp_emit__instr___closed__4;
lean::inc(x_1);
x_587 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_585, x_1, x_2);
x_588 = lean::cnstr_get(x_587, 0);
lean::inc(x_588);
x_590 = lean::cnstr_get(x_587, 1);
lean::inc(x_590);
if (lean::is_exclusive(x_587)) {
 lean::cnstr_release(x_587, 0);
 lean::cnstr_release(x_587, 1);
 x_592 = x_587;
} else {
 lean::dec(x_587);
 x_592 = lean::box(0);
}
if (lean::obj_tag(x_588) == 0)
{
obj* x_595; obj* x_597; obj* x_598; obj* x_599; 
lean::dec(x_577);
lean::dec(x_580);
x_595 = lean::cnstr_get(x_588, 0);
lean::inc(x_595);
if (lean::is_exclusive(x_588)) {
 lean::cnstr_release(x_588, 0);
 x_597 = x_588;
} else {
 lean::dec(x_588);
 x_597 = lean::box(0);
}
if (lean::is_scalar(x_597)) {
 x_598 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_598 = x_597;
}
lean::cnstr_set(x_598, 0, x_595);
if (lean::is_scalar(x_592)) {
 x_599 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_599 = x_592;
}
lean::cnstr_set(x_599, 0, x_598);
lean::cnstr_set(x_599, 1, x_590);
x_3 = x_599;
goto lbl_4;
}
else
{
obj* x_600; obj* x_601; obj* x_603; obj* x_604; obj* x_606; 
if (lean::is_exclusive(x_588)) {
 lean::cnstr_release(x_588, 0);
 x_600 = x_588;
} else {
 lean::dec(x_588);
 x_600 = lean::box(0);
}
x_601 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_603 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_601, x_1, x_590);
x_604 = lean::cnstr_get(x_603, 0);
lean::inc(x_604);
x_606 = lean::cnstr_get(x_603, 1);
lean::inc(x_606);
lean::dec(x_603);
if (lean::obj_tag(x_604) == 0)
{
obj* x_611; obj* x_614; obj* x_615; 
lean::dec(x_577);
lean::dec(x_580);
x_611 = lean::cnstr_get(x_604, 0);
lean::inc(x_611);
lean::dec(x_604);
if (lean::is_scalar(x_600)) {
 x_614 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_614 = x_600;
 lean::cnstr_set_tag(x_600, 0);
}
lean::cnstr_set(x_614, 0, x_611);
if (lean::is_scalar(x_592)) {
 x_615 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_615 = x_592;
}
lean::cnstr_set(x_615, 0, x_614);
lean::cnstr_set(x_615, 1, x_606);
x_3 = x_615;
goto lbl_4;
}
else
{
obj* x_619; obj* x_620; obj* x_622; 
lean::dec(x_592);
lean::dec(x_604);
lean::inc(x_1);
x_619 = l_lean_ir_cpp_emit__var(x_577, x_1, x_606);
x_620 = lean::cnstr_get(x_619, 0);
lean::inc(x_620);
x_622 = lean::cnstr_get(x_619, 1);
lean::inc(x_622);
lean::dec(x_619);
if (lean::obj_tag(x_620) == 0)
{
obj* x_625; obj* x_628; 
x_625 = lean::cnstr_get(x_620, 0);
lean::inc(x_625);
lean::dec(x_620);
if (lean::is_scalar(x_600)) {
 x_628 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_628 = x_600;
 lean::cnstr_set_tag(x_600, 0);
}
lean::cnstr_set(x_628, 0, x_625);
x_582 = x_628;
x_583 = x_622;
goto lbl_584;
}
else
{
obj* x_630; obj* x_632; obj* x_633; obj* x_635; 
lean::dec(x_620);
x_630 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_632 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_630, x_1, x_622);
x_633 = lean::cnstr_get(x_632, 0);
lean::inc(x_633);
x_635 = lean::cnstr_get(x_632, 1);
lean::inc(x_635);
lean::dec(x_632);
if (lean::obj_tag(x_633) == 0)
{
obj* x_638; obj* x_641; 
x_638 = lean::cnstr_get(x_633, 0);
lean::inc(x_638);
lean::dec(x_633);
if (lean::is_scalar(x_600)) {
 x_641 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_641 = x_600;
 lean::cnstr_set_tag(x_600, 0);
}
lean::cnstr_set(x_641, 0, x_638);
x_582 = x_641;
x_583 = x_635;
goto lbl_584;
}
else
{
obj* x_645; obj* x_646; obj* x_648; 
lean::dec(x_600);
lean::dec(x_633);
lean::inc(x_1);
x_645 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(x_579, x_1, x_635);
x_646 = lean::cnstr_get(x_645, 0);
lean::inc(x_646);
x_648 = lean::cnstr_get(x_645, 1);
lean::inc(x_648);
lean::dec(x_645);
x_582 = x_646;
x_583 = x_648;
goto lbl_584;
}
}
}
}
lbl_584:
{
if (lean::obj_tag(x_582) == 0)
{
obj* x_652; obj* x_654; obj* x_655; obj* x_656; 
lean::dec(x_580);
x_652 = lean::cnstr_get(x_582, 0);
lean::inc(x_652);
if (lean::is_exclusive(x_582)) {
 lean::cnstr_release(x_582, 0);
 x_654 = x_582;
} else {
 lean::dec(x_582);
 x_654 = lean::box(0);
}
if (lean::is_scalar(x_654)) {
 x_655 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_655 = x_654;
}
lean::cnstr_set(x_655, 0, x_652);
x_656 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_656, 0, x_655);
lean::cnstr_set(x_656, 1, x_583);
x_3 = x_656;
goto lbl_4;
}
else
{
obj* x_657; obj* x_658; obj* x_660; obj* x_661; obj* x_663; obj* x_665; 
if (lean::is_exclusive(x_582)) {
 lean::cnstr_release(x_582, 0);
 x_657 = x_582;
} else {
 lean::dec(x_582);
 x_657 = lean::box(0);
}
x_658 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_660 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_658, x_1, x_583);
x_661 = lean::cnstr_get(x_660, 0);
lean::inc(x_661);
x_663 = lean::cnstr_get(x_660, 1);
lean::inc(x_663);
if (lean::is_exclusive(x_660)) {
 lean::cnstr_release(x_660, 0);
 lean::cnstr_release(x_660, 1);
 x_665 = x_660;
} else {
 lean::dec(x_660);
 x_665 = lean::box(0);
}
if (lean::obj_tag(x_661) == 0)
{
obj* x_667; obj* x_670; obj* x_671; 
lean::dec(x_580);
x_667 = lean::cnstr_get(x_661, 0);
lean::inc(x_667);
lean::dec(x_661);
if (lean::is_scalar(x_657)) {
 x_670 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_670 = x_657;
 lean::cnstr_set_tag(x_657, 0);
}
lean::cnstr_set(x_670, 0, x_667);
if (lean::is_scalar(x_665)) {
 x_671 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_671 = x_665;
}
lean::cnstr_set(x_671, 0, x_670);
lean::cnstr_set(x_671, 1, x_663);
x_3 = x_671;
goto lbl_4;
}
else
{
obj* x_674; obj* x_675; obj* x_677; 
lean::dec(x_661);
lean::inc(x_1);
x_674 = l_lean_ir_cpp_emit__var(x_580, x_1, x_663);
x_675 = lean::cnstr_get(x_674, 0);
lean::inc(x_675);
x_677 = lean::cnstr_get(x_674, 1);
lean::inc(x_677);
lean::dec(x_674);
if (lean::obj_tag(x_675) == 0)
{
obj* x_680; obj* x_683; obj* x_684; 
x_680 = lean::cnstr_get(x_675, 0);
lean::inc(x_680);
lean::dec(x_675);
if (lean::is_scalar(x_657)) {
 x_683 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_683 = x_657;
 lean::cnstr_set_tag(x_657, 0);
}
lean::cnstr_set(x_683, 0, x_680);
if (lean::is_scalar(x_665)) {
 x_684 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_684 = x_665;
}
lean::cnstr_set(x_684, 0, x_683);
lean::cnstr_set(x_684, 1, x_677);
x_3 = x_684;
goto lbl_4;
}
else
{
obj* x_685; obj* x_688; obj* x_690; obj* x_691; obj* x_693; 
x_685 = lean::cnstr_get(x_675, 0);
lean::inc(x_685);
lean::dec(x_675);
x_688 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_690 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_688, x_1, x_677);
x_691 = lean::cnstr_get(x_690, 0);
lean::inc(x_691);
x_693 = lean::cnstr_get(x_690, 1);
lean::inc(x_693);
lean::dec(x_690);
if (lean::obj_tag(x_691) == 0)
{
obj* x_697; obj* x_700; obj* x_701; 
lean::dec(x_685);
x_697 = lean::cnstr_get(x_691, 0);
lean::inc(x_697);
lean::dec(x_691);
if (lean::is_scalar(x_657)) {
 x_700 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_700 = x_657;
 lean::cnstr_set_tag(x_657, 0);
}
lean::cnstr_set(x_700, 0, x_697);
if (lean::is_scalar(x_665)) {
 x_701 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_701 = x_665;
}
lean::cnstr_set(x_701, 0, x_700);
lean::cnstr_set(x_701, 1, x_693);
x_3 = x_701;
goto lbl_4;
}
else
{
obj* x_703; obj* x_704; 
lean::dec(x_691);
if (lean::is_scalar(x_657)) {
 x_703 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_703 = x_657;
}
lean::cnstr_set(x_703, 0, x_685);
if (lean::is_scalar(x_665)) {
 x_704 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_704 = x_665;
}
lean::cnstr_set(x_704, 0, x_703);
lean::cnstr_set(x_704, 1, x_693);
x_3 = x_704;
goto lbl_4;
}
}
}
}
}
}
case 10:
{
obj* x_705; uint8 x_707; obj* x_708; usize x_710; obj* x_711; obj* x_712; obj* x_715; obj* x_716; obj* x_718; 
x_705 = lean::cnstr_get(x_0, 0);
lean::inc(x_705);
x_707 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_708 = lean::cnstr_get(x_0, 1);
lean::inc(x_708);
x_710 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
lean::inc(x_1);
x_715 = l_lean_ir_cpp_emit__var(x_705, x_1, x_2);
x_716 = lean::cnstr_get(x_715, 0);
lean::inc(x_716);
x_718 = lean::cnstr_get(x_715, 1);
lean::inc(x_718);
lean::dec(x_715);
if (lean::obj_tag(x_716) == 0)
{
obj* x_721; obj* x_723; obj* x_724; 
x_721 = lean::cnstr_get(x_716, 0);
lean::inc(x_721);
if (lean::is_exclusive(x_716)) {
 lean::cnstr_release(x_716, 0);
 x_723 = x_716;
} else {
 lean::dec(x_716);
 x_723 = lean::box(0);
}
if (lean::is_scalar(x_723)) {
 x_724 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_724 = x_723;
}
lean::cnstr_set(x_724, 0, x_721);
x_711 = x_724;
x_712 = x_718;
goto lbl_713;
}
else
{
obj* x_725; obj* x_726; obj* x_728; obj* x_729; obj* x_731; 
if (lean::is_exclusive(x_716)) {
 lean::cnstr_release(x_716, 0);
 x_725 = x_716;
} else {
 lean::dec(x_716);
 x_725 = lean::box(0);
}
x_726 = l_lean_ir_cpp_emit__instr___closed__5;
lean::inc(x_1);
x_728 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_726, x_1, x_718);
x_729 = lean::cnstr_get(x_728, 0);
lean::inc(x_729);
x_731 = lean::cnstr_get(x_728, 1);
lean::inc(x_731);
lean::dec(x_728);
if (lean::obj_tag(x_729) == 0)
{
obj* x_734; obj* x_737; 
x_734 = lean::cnstr_get(x_729, 0);
lean::inc(x_734);
lean::dec(x_729);
if (lean::is_scalar(x_725)) {
 x_737 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_737 = x_725;
 lean::cnstr_set_tag(x_725, 0);
}
lean::cnstr_set(x_737, 0, x_734);
x_711 = x_737;
x_712 = x_731;
goto lbl_713;
}
else
{
obj* x_741; obj* x_742; obj* x_744; 
lean::dec(x_729);
lean::dec(x_725);
lean::inc(x_1);
x_741 = l_lean_ir_cpp_emit__template__param(x_707, x_1, x_731);
x_742 = lean::cnstr_get(x_741, 0);
lean::inc(x_742);
x_744 = lean::cnstr_get(x_741, 1);
lean::inc(x_744);
lean::dec(x_741);
x_711 = x_742;
x_712 = x_744;
goto lbl_713;
}
}
lbl_713:
{
if (lean::obj_tag(x_711) == 0)
{
obj* x_748; obj* x_750; obj* x_751; obj* x_752; 
lean::dec(x_708);
x_748 = lean::cnstr_get(x_711, 0);
lean::inc(x_748);
if (lean::is_exclusive(x_711)) {
 lean::cnstr_release(x_711, 0);
 x_750 = x_711;
} else {
 lean::dec(x_711);
 x_750 = lean::box(0);
}
if (lean::is_scalar(x_750)) {
 x_751 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_751 = x_750;
}
lean::cnstr_set(x_751, 0, x_748);
x_752 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_752, 0, x_751);
lean::cnstr_set(x_752, 1, x_712);
x_3 = x_752;
goto lbl_4;
}
else
{
obj* x_753; obj* x_754; obj* x_756; obj* x_757; obj* x_759; obj* x_761; 
if (lean::is_exclusive(x_711)) {
 lean::cnstr_release(x_711, 0);
 x_753 = x_711;
} else {
 lean::dec(x_711);
 x_753 = lean::box(0);
}
x_754 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_756 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_754, x_1, x_712);
x_757 = lean::cnstr_get(x_756, 0);
lean::inc(x_757);
x_759 = lean::cnstr_get(x_756, 1);
lean::inc(x_759);
if (lean::is_exclusive(x_756)) {
 lean::cnstr_release(x_756, 0);
 lean::cnstr_release(x_756, 1);
 x_761 = x_756;
} else {
 lean::dec(x_756);
 x_761 = lean::box(0);
}
if (lean::obj_tag(x_757) == 0)
{
obj* x_763; obj* x_766; obj* x_767; 
lean::dec(x_708);
x_763 = lean::cnstr_get(x_757, 0);
lean::inc(x_763);
lean::dec(x_757);
if (lean::is_scalar(x_753)) {
 x_766 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_766 = x_753;
 lean::cnstr_set_tag(x_753, 0);
}
lean::cnstr_set(x_766, 0, x_763);
if (lean::is_scalar(x_761)) {
 x_767 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_767 = x_761;
}
lean::cnstr_set(x_767, 0, x_766);
lean::cnstr_set(x_767, 1, x_759);
x_3 = x_767;
goto lbl_4;
}
else
{
obj* x_770; obj* x_771; obj* x_773; 
lean::dec(x_757);
lean::inc(x_1);
x_770 = l_lean_ir_cpp_emit__var(x_708, x_1, x_759);
x_771 = lean::cnstr_get(x_770, 0);
lean::inc(x_771);
x_773 = lean::cnstr_get(x_770, 1);
lean::inc(x_773);
lean::dec(x_770);
if (lean::obj_tag(x_771) == 0)
{
obj* x_776; obj* x_779; obj* x_780; 
x_776 = lean::cnstr_get(x_771, 0);
lean::inc(x_776);
lean::dec(x_771);
if (lean::is_scalar(x_753)) {
 x_779 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_779 = x_753;
 lean::cnstr_set_tag(x_753, 0);
}
lean::cnstr_set(x_779, 0, x_776);
if (lean::is_scalar(x_761)) {
 x_780 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_780 = x_761;
}
lean::cnstr_set(x_780, 0, x_779);
lean::cnstr_set(x_780, 1, x_773);
x_3 = x_780;
goto lbl_4;
}
else
{
obj* x_782; obj* x_784; obj* x_785; obj* x_787; 
lean::dec(x_771);
x_782 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_784 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_782, x_1, x_773);
x_785 = lean::cnstr_get(x_784, 0);
lean::inc(x_785);
x_787 = lean::cnstr_get(x_784, 1);
lean::inc(x_787);
lean::dec(x_784);
if (lean::obj_tag(x_785) == 0)
{
obj* x_790; obj* x_793; obj* x_794; 
x_790 = lean::cnstr_get(x_785, 0);
lean::inc(x_790);
lean::dec(x_785);
if (lean::is_scalar(x_753)) {
 x_793 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_793 = x_753;
 lean::cnstr_set_tag(x_753, 0);
}
lean::cnstr_set(x_793, 0, x_790);
if (lean::is_scalar(x_761)) {
 x_794 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_794 = x_761;
}
lean::cnstr_set(x_794, 0, x_793);
lean::cnstr_set(x_794, 1, x_787);
x_3 = x_794;
goto lbl_4;
}
else
{
obj* x_797; obj* x_798; obj* x_800; 
lean::dec(x_785);
lean::inc(x_1);
x_797 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(x_710, x_1, x_787);
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
if (lean::is_scalar(x_753)) {
 x_806 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_806 = x_753;
 lean::cnstr_set_tag(x_753, 0);
}
lean::cnstr_set(x_806, 0, x_803);
if (lean::is_scalar(x_761)) {
 x_807 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_807 = x_761;
}
lean::cnstr_set(x_807, 0, x_806);
lean::cnstr_set(x_807, 1, x_800);
x_3 = x_807;
goto lbl_4;
}
else
{
obj* x_808; obj* x_811; obj* x_813; obj* x_814; obj* x_816; 
x_808 = lean::cnstr_get(x_798, 0);
lean::inc(x_808);
lean::dec(x_798);
x_811 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_813 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_811, x_1, x_800);
x_814 = lean::cnstr_get(x_813, 0);
lean::inc(x_814);
x_816 = lean::cnstr_get(x_813, 1);
lean::inc(x_816);
lean::dec(x_813);
if (lean::obj_tag(x_814) == 0)
{
obj* x_820; obj* x_823; obj* x_824; 
lean::dec(x_808);
x_820 = lean::cnstr_get(x_814, 0);
lean::inc(x_820);
lean::dec(x_814);
if (lean::is_scalar(x_753)) {
 x_823 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_823 = x_753;
 lean::cnstr_set_tag(x_753, 0);
}
lean::cnstr_set(x_823, 0, x_820);
if (lean::is_scalar(x_761)) {
 x_824 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_824 = x_761;
}
lean::cnstr_set(x_824, 0, x_823);
lean::cnstr_set(x_824, 1, x_816);
x_3 = x_824;
goto lbl_4;
}
else
{
obj* x_826; obj* x_827; 
lean::dec(x_814);
if (lean::is_scalar(x_753)) {
 x_826 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_826 = x_753;
}
lean::cnstr_set(x_826, 0, x_808);
if (lean::is_scalar(x_761)) {
 x_827 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_827 = x_761;
}
lean::cnstr_set(x_827, 0, x_826);
lean::cnstr_set(x_827, 1, x_816);
x_3 = x_827;
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
obj* x_828; obj* x_830; obj* x_832; obj* x_835; 
x_828 = lean::cnstr_get(x_0, 0);
lean::inc(x_828);
x_830 = lean::cnstr_get(x_0, 1);
lean::inc(x_830);
x_832 = lean::cnstr_get(x_0, 2);
lean::inc(x_832);
lean::inc(x_1);
x_835 = l_lean_ir_cpp_emit__closure(x_828, x_830, x_832, x_1, x_2);
x_3 = x_835;
goto lbl_4;
}
case 12:
{
obj* x_836; obj* x_838; obj* x_841; 
x_836 = lean::cnstr_get(x_0, 0);
lean::inc(x_836);
x_838 = lean::cnstr_get(x_0, 1);
lean::inc(x_838);
lean::inc(x_1);
x_841 = l_lean_ir_cpp_emit__apply(x_836, x_838, x_1, x_2);
x_3 = x_841;
goto lbl_4;
}
case 13:
{
obj* x_842; obj* x_844; obj* x_846; obj* x_848; obj* x_849; obj* x_852; obj* x_853; obj* x_855; 
x_842 = lean::cnstr_get(x_0, 0);
lean::inc(x_842);
x_844 = lean::cnstr_get(x_0, 1);
lean::inc(x_844);
x_846 = lean::cnstr_get(x_0, 2);
lean::inc(x_846);
lean::inc(x_1);
x_852 = l_lean_ir_cpp_emit__var(x_842, x_1, x_2);
x_853 = lean::cnstr_get(x_852, 0);
lean::inc(x_853);
x_855 = lean::cnstr_get(x_852, 1);
lean::inc(x_855);
lean::dec(x_852);
if (lean::obj_tag(x_853) == 0)
{
obj* x_858; obj* x_860; obj* x_861; 
x_858 = lean::cnstr_get(x_853, 0);
lean::inc(x_858);
if (lean::is_exclusive(x_853)) {
 lean::cnstr_release(x_853, 0);
 x_860 = x_853;
} else {
 lean::dec(x_853);
 x_860 = lean::box(0);
}
if (lean::is_scalar(x_860)) {
 x_861 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_861 = x_860;
}
lean::cnstr_set(x_861, 0, x_858);
x_848 = x_861;
x_849 = x_855;
goto lbl_850;
}
else
{
obj* x_863; obj* x_865; obj* x_866; obj* x_868; 
lean::dec(x_853);
x_863 = l_lean_ir_cpp_emit__instr___closed__6;
lean::inc(x_1);
x_865 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_863, x_1, x_855);
x_866 = lean::cnstr_get(x_865, 0);
lean::inc(x_866);
x_868 = lean::cnstr_get(x_865, 1);
lean::inc(x_868);
lean::dec(x_865);
x_848 = x_866;
x_849 = x_868;
goto lbl_850;
}
lbl_850:
{
if (lean::obj_tag(x_848) == 0)
{
obj* x_873; obj* x_875; obj* x_876; obj* x_877; 
lean::dec(x_844);
lean::dec(x_846);
x_873 = lean::cnstr_get(x_848, 0);
lean::inc(x_873);
if (lean::is_exclusive(x_848)) {
 lean::cnstr_release(x_848, 0);
 x_875 = x_848;
} else {
 lean::dec(x_848);
 x_875 = lean::box(0);
}
if (lean::is_scalar(x_875)) {
 x_876 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_876 = x_875;
}
lean::cnstr_set(x_876, 0, x_873);
x_877 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_877, 0, x_876);
lean::cnstr_set(x_877, 1, x_849);
x_3 = x_877;
goto lbl_4;
}
else
{
obj* x_878; obj* x_879; obj* x_881; obj* x_882; obj* x_884; obj* x_886; 
if (lean::is_exclusive(x_848)) {
 lean::cnstr_release(x_848, 0);
 x_878 = x_848;
} else {
 lean::dec(x_848);
 x_878 = lean::box(0);
}
x_879 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_881 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_879, x_1, x_849);
x_882 = lean::cnstr_get(x_881, 0);
lean::inc(x_882);
x_884 = lean::cnstr_get(x_881, 1);
lean::inc(x_884);
if (lean::is_exclusive(x_881)) {
 lean::cnstr_release(x_881, 0);
 lean::cnstr_release(x_881, 1);
 x_886 = x_881;
} else {
 lean::dec(x_881);
 x_886 = lean::box(0);
}
if (lean::obj_tag(x_882) == 0)
{
obj* x_889; obj* x_892; obj* x_893; 
lean::dec(x_844);
lean::dec(x_846);
x_889 = lean::cnstr_get(x_882, 0);
lean::inc(x_889);
lean::dec(x_882);
if (lean::is_scalar(x_878)) {
 x_892 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_892 = x_878;
 lean::cnstr_set_tag(x_878, 0);
}
lean::cnstr_set(x_892, 0, x_889);
if (lean::is_scalar(x_886)) {
 x_893 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_893 = x_886;
}
lean::cnstr_set(x_893, 0, x_892);
lean::cnstr_set(x_893, 1, x_884);
x_3 = x_893;
goto lbl_4;
}
else
{
obj* x_896; obj* x_897; obj* x_899; 
lean::dec(x_882);
lean::inc(x_1);
x_896 = l_lean_ir_cpp_emit__var(x_844, x_1, x_884);
x_897 = lean::cnstr_get(x_896, 0);
lean::inc(x_897);
x_899 = lean::cnstr_get(x_896, 1);
lean::inc(x_899);
lean::dec(x_896);
if (lean::obj_tag(x_897) == 0)
{
obj* x_903; obj* x_906; obj* x_907; 
lean::dec(x_846);
x_903 = lean::cnstr_get(x_897, 0);
lean::inc(x_903);
lean::dec(x_897);
if (lean::is_scalar(x_878)) {
 x_906 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_906 = x_878;
 lean::cnstr_set_tag(x_878, 0);
}
lean::cnstr_set(x_906, 0, x_903);
if (lean::is_scalar(x_886)) {
 x_907 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_907 = x_886;
}
lean::cnstr_set(x_907, 0, x_906);
lean::cnstr_set(x_907, 1, x_899);
x_3 = x_907;
goto lbl_4;
}
else
{
obj* x_909; obj* x_911; obj* x_912; obj* x_914; 
lean::dec(x_897);
x_909 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_911 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_909, x_1, x_899);
x_912 = lean::cnstr_get(x_911, 0);
lean::inc(x_912);
x_914 = lean::cnstr_get(x_911, 1);
lean::inc(x_914);
lean::dec(x_911);
if (lean::obj_tag(x_912) == 0)
{
obj* x_918; obj* x_921; obj* x_922; 
lean::dec(x_846);
x_918 = lean::cnstr_get(x_912, 0);
lean::inc(x_918);
lean::dec(x_912);
if (lean::is_scalar(x_878)) {
 x_921 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_921 = x_878;
 lean::cnstr_set_tag(x_878, 0);
}
lean::cnstr_set(x_921, 0, x_918);
if (lean::is_scalar(x_886)) {
 x_922 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_922 = x_886;
}
lean::cnstr_set(x_922, 0, x_921);
lean::cnstr_set(x_922, 1, x_914);
x_3 = x_922;
goto lbl_4;
}
else
{
obj* x_925; obj* x_926; obj* x_928; 
lean::dec(x_912);
lean::inc(x_1);
x_925 = l_lean_ir_cpp_emit__var(x_846, x_1, x_914);
x_926 = lean::cnstr_get(x_925, 0);
lean::inc(x_926);
x_928 = lean::cnstr_get(x_925, 1);
lean::inc(x_928);
lean::dec(x_925);
if (lean::obj_tag(x_926) == 0)
{
obj* x_931; obj* x_934; obj* x_935; 
x_931 = lean::cnstr_get(x_926, 0);
lean::inc(x_931);
lean::dec(x_926);
if (lean::is_scalar(x_878)) {
 x_934 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_934 = x_878;
 lean::cnstr_set_tag(x_878, 0);
}
lean::cnstr_set(x_934, 0, x_931);
if (lean::is_scalar(x_886)) {
 x_935 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_935 = x_886;
}
lean::cnstr_set(x_935, 0, x_934);
lean::cnstr_set(x_935, 1, x_928);
x_3 = x_935;
goto lbl_4;
}
else
{
obj* x_936; obj* x_939; obj* x_941; obj* x_942; obj* x_944; 
x_936 = lean::cnstr_get(x_926, 0);
lean::inc(x_936);
lean::dec(x_926);
x_939 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_941 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_939, x_1, x_928);
x_942 = lean::cnstr_get(x_941, 0);
lean::inc(x_942);
x_944 = lean::cnstr_get(x_941, 1);
lean::inc(x_944);
lean::dec(x_941);
if (lean::obj_tag(x_942) == 0)
{
obj* x_948; obj* x_951; obj* x_952; 
lean::dec(x_936);
x_948 = lean::cnstr_get(x_942, 0);
lean::inc(x_948);
lean::dec(x_942);
if (lean::is_scalar(x_878)) {
 x_951 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_951 = x_878;
 lean::cnstr_set_tag(x_878, 0);
}
lean::cnstr_set(x_951, 0, x_948);
if (lean::is_scalar(x_886)) {
 x_952 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_952 = x_886;
}
lean::cnstr_set(x_952, 0, x_951);
lean::cnstr_set(x_952, 1, x_944);
x_3 = x_952;
goto lbl_4;
}
else
{
obj* x_954; obj* x_955; 
lean::dec(x_942);
if (lean::is_scalar(x_878)) {
 x_954 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_954 = x_878;
}
lean::cnstr_set(x_954, 0, x_936);
if (lean::is_scalar(x_886)) {
 x_955 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_955 = x_886;
}
lean::cnstr_set(x_955, 0, x_954);
lean::cnstr_set(x_955, 1, x_944);
x_3 = x_955;
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
obj* x_956; uint8 x_958; obj* x_959; obj* x_961; obj* x_963; obj* x_964; obj* x_966; obj* x_967; obj* x_970; obj* x_971; obj* x_973; 
x_956 = lean::cnstr_get(x_0, 0);
lean::inc(x_956);
x_958 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_959 = lean::cnstr_get(x_0, 1);
lean::inc(x_959);
x_961 = lean::cnstr_get(x_0, 2);
lean::inc(x_961);
lean::inc(x_1);
x_970 = l_lean_ir_cpp_emit__var(x_956, x_1, x_2);
x_971 = lean::cnstr_get(x_970, 0);
lean::inc(x_971);
x_973 = lean::cnstr_get(x_970, 1);
lean::inc(x_973);
lean::dec(x_970);
if (lean::obj_tag(x_971) == 0)
{
obj* x_976; obj* x_978; obj* x_979; 
x_976 = lean::cnstr_get(x_971, 0);
lean::inc(x_976);
if (lean::is_exclusive(x_971)) {
 lean::cnstr_release(x_971, 0);
 x_978 = x_971;
} else {
 lean::dec(x_971);
 x_978 = lean::box(0);
}
if (lean::is_scalar(x_978)) {
 x_979 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_979 = x_978;
}
lean::cnstr_set(x_979, 0, x_976);
x_966 = x_979;
x_967 = x_973;
goto lbl_968;
}
else
{
obj* x_981; obj* x_983; obj* x_984; obj* x_986; 
lean::dec(x_971);
x_981 = l_lean_ir_cpp_emit__instr___closed__7;
lean::inc(x_1);
x_983 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_981, x_1, x_973);
x_984 = lean::cnstr_get(x_983, 0);
lean::inc(x_984);
x_986 = lean::cnstr_get(x_983, 1);
lean::inc(x_986);
lean::dec(x_983);
x_966 = x_984;
x_967 = x_986;
goto lbl_968;
}
lbl_965:
{
if (lean::obj_tag(x_963) == 0)
{
obj* x_990; obj* x_992; obj* x_993; obj* x_994; 
lean::dec(x_961);
x_990 = lean::cnstr_get(x_963, 0);
lean::inc(x_990);
if (lean::is_exclusive(x_963)) {
 lean::cnstr_release(x_963, 0);
 x_992 = x_963;
} else {
 lean::dec(x_963);
 x_992 = lean::box(0);
}
if (lean::is_scalar(x_992)) {
 x_993 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_993 = x_992;
}
lean::cnstr_set(x_993, 0, x_990);
x_994 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_994, 0, x_993);
lean::cnstr_set(x_994, 1, x_964);
x_3 = x_994;
goto lbl_4;
}
else
{
obj* x_995; obj* x_996; obj* x_998; obj* x_999; obj* x_1001; obj* x_1003; 
if (lean::is_exclusive(x_963)) {
 lean::cnstr_release(x_963, 0);
 x_995 = x_963;
} else {
 lean::dec(x_963);
 x_995 = lean::box(0);
}
x_996 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_998 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_996, x_1, x_964);
x_999 = lean::cnstr_get(x_998, 0);
lean::inc(x_999);
x_1001 = lean::cnstr_get(x_998, 1);
lean::inc(x_1001);
if (lean::is_exclusive(x_998)) {
 lean::cnstr_release(x_998, 0);
 lean::cnstr_release(x_998, 1);
 x_1003 = x_998;
} else {
 lean::dec(x_998);
 x_1003 = lean::box(0);
}
if (lean::obj_tag(x_999) == 0)
{
obj* x_1005; obj* x_1008; obj* x_1009; 
lean::dec(x_961);
x_1005 = lean::cnstr_get(x_999, 0);
lean::inc(x_1005);
lean::dec(x_999);
if (lean::is_scalar(x_995)) {
 x_1008 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1008 = x_995;
 lean::cnstr_set_tag(x_995, 0);
}
lean::cnstr_set(x_1008, 0, x_1005);
if (lean::is_scalar(x_1003)) {
 x_1009 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1009 = x_1003;
}
lean::cnstr_set(x_1009, 0, x_1008);
lean::cnstr_set(x_1009, 1, x_1001);
x_3 = x_1009;
goto lbl_4;
}
else
{
obj* x_1012; obj* x_1013; obj* x_1015; 
lean::dec(x_999);
lean::inc(x_1);
x_1012 = l_lean_ir_cpp_emit__var(x_961, x_1, x_1001);
x_1013 = lean::cnstr_get(x_1012, 0);
lean::inc(x_1013);
x_1015 = lean::cnstr_get(x_1012, 1);
lean::inc(x_1015);
lean::dec(x_1012);
if (lean::obj_tag(x_1013) == 0)
{
obj* x_1018; obj* x_1021; obj* x_1022; 
x_1018 = lean::cnstr_get(x_1013, 0);
lean::inc(x_1018);
lean::dec(x_1013);
if (lean::is_scalar(x_995)) {
 x_1021 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1021 = x_995;
 lean::cnstr_set_tag(x_995, 0);
}
lean::cnstr_set(x_1021, 0, x_1018);
if (lean::is_scalar(x_1003)) {
 x_1022 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1022 = x_1003;
}
lean::cnstr_set(x_1022, 0, x_1021);
lean::cnstr_set(x_1022, 1, x_1015);
x_3 = x_1022;
goto lbl_4;
}
else
{
obj* x_1023; obj* x_1026; obj* x_1028; obj* x_1029; obj* x_1031; 
x_1023 = lean::cnstr_get(x_1013, 0);
lean::inc(x_1023);
lean::dec(x_1013);
x_1026 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_1028 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1026, x_1, x_1015);
x_1029 = lean::cnstr_get(x_1028, 0);
lean::inc(x_1029);
x_1031 = lean::cnstr_get(x_1028, 1);
lean::inc(x_1031);
lean::dec(x_1028);
if (lean::obj_tag(x_1029) == 0)
{
obj* x_1035; obj* x_1038; obj* x_1039; 
lean::dec(x_1023);
x_1035 = lean::cnstr_get(x_1029, 0);
lean::inc(x_1035);
lean::dec(x_1029);
if (lean::is_scalar(x_995)) {
 x_1038 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1038 = x_995;
 lean::cnstr_set_tag(x_995, 0);
}
lean::cnstr_set(x_1038, 0, x_1035);
if (lean::is_scalar(x_1003)) {
 x_1039 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1039 = x_1003;
}
lean::cnstr_set(x_1039, 0, x_1038);
lean::cnstr_set(x_1039, 1, x_1031);
x_3 = x_1039;
goto lbl_4;
}
else
{
obj* x_1041; obj* x_1042; 
lean::dec(x_1029);
if (lean::is_scalar(x_995)) {
 x_1041 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1041 = x_995;
}
lean::cnstr_set(x_1041, 0, x_1023);
if (lean::is_scalar(x_1003)) {
 x_1042 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1042 = x_1003;
}
lean::cnstr_set(x_1042, 0, x_1041);
lean::cnstr_set(x_1042, 1, x_1031);
x_3 = x_1042;
goto lbl_4;
}
}
}
}
}
lbl_968:
{
if (lean::obj_tag(x_966) == 0)
{
obj* x_1045; obj* x_1047; obj* x_1048; obj* x_1049; 
lean::dec(x_959);
lean::dec(x_961);
x_1045 = lean::cnstr_get(x_966, 0);
lean::inc(x_1045);
if (lean::is_exclusive(x_966)) {
 lean::cnstr_release(x_966, 0);
 x_1047 = x_966;
} else {
 lean::dec(x_966);
 x_1047 = lean::box(0);
}
if (lean::is_scalar(x_1047)) {
 x_1048 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1048 = x_1047;
}
lean::cnstr_set(x_1048, 0, x_1045);
x_1049 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1049, 0, x_1048);
lean::cnstr_set(x_1049, 1, x_967);
x_3 = x_1049;
goto lbl_4;
}
else
{
obj* x_1050; obj* x_1051; obj* x_1053; obj* x_1054; obj* x_1056; obj* x_1058; 
if (lean::is_exclusive(x_966)) {
 lean::cnstr_release(x_966, 0);
 x_1050 = x_966;
} else {
 lean::dec(x_966);
 x_1050 = lean::box(0);
}
x_1051 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_1053 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1051, x_1, x_967);
x_1054 = lean::cnstr_get(x_1053, 0);
lean::inc(x_1054);
x_1056 = lean::cnstr_get(x_1053, 1);
lean::inc(x_1056);
if (lean::is_exclusive(x_1053)) {
 lean::cnstr_release(x_1053, 0);
 lean::cnstr_release(x_1053, 1);
 x_1058 = x_1053;
} else {
 lean::dec(x_1053);
 x_1058 = lean::box(0);
}
if (lean::obj_tag(x_1054) == 0)
{
obj* x_1061; obj* x_1064; obj* x_1065; 
lean::dec(x_959);
lean::dec(x_961);
x_1061 = lean::cnstr_get(x_1054, 0);
lean::inc(x_1061);
lean::dec(x_1054);
if (lean::is_scalar(x_1050)) {
 x_1064 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1064 = x_1050;
 lean::cnstr_set_tag(x_1050, 0);
}
lean::cnstr_set(x_1064, 0, x_1061);
if (lean::is_scalar(x_1058)) {
 x_1065 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1065 = x_1058;
}
lean::cnstr_set(x_1065, 0, x_1064);
lean::cnstr_set(x_1065, 1, x_1056);
x_3 = x_1065;
goto lbl_4;
}
else
{
obj* x_1069; obj* x_1070; obj* x_1072; 
lean::dec(x_1054);
lean::dec(x_1058);
lean::inc(x_1);
x_1069 = l_lean_ir_cpp_emit__type__size(x_958, x_1, x_1056);
x_1070 = lean::cnstr_get(x_1069, 0);
lean::inc(x_1070);
x_1072 = lean::cnstr_get(x_1069, 1);
lean::inc(x_1072);
lean::dec(x_1069);
if (lean::obj_tag(x_1070) == 0)
{
obj* x_1076; obj* x_1079; 
lean::dec(x_959);
x_1076 = lean::cnstr_get(x_1070, 0);
lean::inc(x_1076);
lean::dec(x_1070);
if (lean::is_scalar(x_1050)) {
 x_1079 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1079 = x_1050;
 lean::cnstr_set_tag(x_1050, 0);
}
lean::cnstr_set(x_1079, 0, x_1076);
x_963 = x_1079;
x_964 = x_1072;
goto lbl_965;
}
else
{
obj* x_1081; obj* x_1083; obj* x_1084; obj* x_1086; 
lean::dec(x_1070);
x_1081 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_1083 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1081, x_1, x_1072);
x_1084 = lean::cnstr_get(x_1083, 0);
lean::inc(x_1084);
x_1086 = lean::cnstr_get(x_1083, 1);
lean::inc(x_1086);
lean::dec(x_1083);
if (lean::obj_tag(x_1084) == 0)
{
obj* x_1090; obj* x_1093; 
lean::dec(x_959);
x_1090 = lean::cnstr_get(x_1084, 0);
lean::inc(x_1090);
lean::dec(x_1084);
if (lean::is_scalar(x_1050)) {
 x_1093 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1093 = x_1050;
 lean::cnstr_set_tag(x_1050, 0);
}
lean::cnstr_set(x_1093, 0, x_1090);
x_963 = x_1093;
x_964 = x_1086;
goto lbl_965;
}
else
{
obj* x_1097; obj* x_1098; obj* x_1100; 
lean::dec(x_1050);
lean::dec(x_1084);
lean::inc(x_1);
x_1097 = l_lean_ir_cpp_emit__var(x_959, x_1, x_1086);
x_1098 = lean::cnstr_get(x_1097, 0);
lean::inc(x_1098);
x_1100 = lean::cnstr_get(x_1097, 1);
lean::inc(x_1100);
lean::dec(x_1097);
x_963 = x_1098;
x_964 = x_1100;
goto lbl_965;
}
}
}
}
}
}
default:
{
obj* x_1103; obj* x_1105; obj* x_1107; obj* x_1109; obj* x_1110; obj* x_1112; obj* x_1114; obj* x_1116; obj* x_1119; 
x_1103 = lean::cnstr_get(x_0, 0);
lean::inc(x_1103);
x_1105 = lean::cnstr_get(x_0, 1);
lean::inc(x_1105);
x_1107 = lean::cnstr_get(x_0, 2);
lean::inc(x_1107);
x_1116 = lean::cnstr_get(x_1, 1);
lean::inc(x_1116);
lean::inc(x_1107);
x_1119 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_1116, x_1107);
if (lean::obj_tag(x_1119) == 0)
{
obj* x_1120; 
x_1120 = lean::box(0);
x_1112 = x_1120;
goto lbl_1113;
}
else
{
obj* x_1121; uint8 x_1124; obj* x_1126; obj* x_1127; uint8 x_1128; 
x_1121 = lean::cnstr_get(x_1119, 0);
lean::inc(x_1121);
lean::dec(x_1119);
x_1124 = lean::unbox(x_1121);
lean::dec(x_1121);
x_1126 = l_lean_ir_type2id___main(x_1124);
x_1127 = l_lean_ir_valid__assign__unop__types___closed__1;
x_1128 = lean::nat_dec_eq(x_1126, x_1127);
lean::dec(x_1126);
if (x_1128 == 0)
{
obj* x_1130; 
x_1130 = lean::box(0);
x_1112 = x_1130;
goto lbl_1113;
}
else
{
obj* x_1131; 
x_1131 = lean::box(0);
x_1114 = x_1131;
goto lbl_1115;
}
}
lbl_1111:
{
if (lean::obj_tag(x_1109) == 0)
{
obj* x_1133; obj* x_1135; obj* x_1136; obj* x_1137; 
lean::dec(x_1107);
x_1133 = lean::cnstr_get(x_1109, 0);
lean::inc(x_1133);
if (lean::is_exclusive(x_1109)) {
 lean::cnstr_release(x_1109, 0);
 x_1135 = x_1109;
} else {
 lean::dec(x_1109);
 x_1135 = lean::box(0);
}
if (lean::is_scalar(x_1135)) {
 x_1136 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1136 = x_1135;
}
lean::cnstr_set(x_1136, 0, x_1133);
x_1137 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1137, 0, x_1136);
lean::cnstr_set(x_1137, 1, x_1110);
x_3 = x_1137;
goto lbl_4;
}
else
{
obj* x_1138; obj* x_1139; obj* x_1141; obj* x_1142; obj* x_1144; obj* x_1146; 
if (lean::is_exclusive(x_1109)) {
 lean::cnstr_release(x_1109, 0);
 x_1138 = x_1109;
} else {
 lean::dec(x_1109);
 x_1138 = lean::box(0);
}
x_1139 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_1141 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1139, x_1, x_1110);
x_1142 = lean::cnstr_get(x_1141, 0);
lean::inc(x_1142);
x_1144 = lean::cnstr_get(x_1141, 1);
lean::inc(x_1144);
if (lean::is_exclusive(x_1141)) {
 lean::cnstr_release(x_1141, 0);
 lean::cnstr_release(x_1141, 1);
 x_1146 = x_1141;
} else {
 lean::dec(x_1141);
 x_1146 = lean::box(0);
}
if (lean::obj_tag(x_1142) == 0)
{
obj* x_1148; obj* x_1151; obj* x_1152; 
lean::dec(x_1107);
x_1148 = lean::cnstr_get(x_1142, 0);
lean::inc(x_1148);
lean::dec(x_1142);
if (lean::is_scalar(x_1138)) {
 x_1151 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1151 = x_1138;
 lean::cnstr_set_tag(x_1138, 0);
}
lean::cnstr_set(x_1151, 0, x_1148);
if (lean::is_scalar(x_1146)) {
 x_1152 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1152 = x_1146;
}
lean::cnstr_set(x_1152, 0, x_1151);
lean::cnstr_set(x_1152, 1, x_1144);
x_3 = x_1152;
goto lbl_4;
}
else
{
obj* x_1155; obj* x_1156; obj* x_1158; 
lean::dec(x_1142);
lean::inc(x_1);
x_1155 = l_lean_ir_cpp_emit__var(x_1107, x_1, x_1144);
x_1156 = lean::cnstr_get(x_1155, 0);
lean::inc(x_1156);
x_1158 = lean::cnstr_get(x_1155, 1);
lean::inc(x_1158);
lean::dec(x_1155);
if (lean::obj_tag(x_1156) == 0)
{
obj* x_1161; obj* x_1164; obj* x_1165; 
x_1161 = lean::cnstr_get(x_1156, 0);
lean::inc(x_1161);
lean::dec(x_1156);
if (lean::is_scalar(x_1138)) {
 x_1164 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1164 = x_1138;
 lean::cnstr_set_tag(x_1138, 0);
}
lean::cnstr_set(x_1164, 0, x_1161);
if (lean::is_scalar(x_1146)) {
 x_1165 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1165 = x_1146;
}
lean::cnstr_set(x_1165, 0, x_1164);
lean::cnstr_set(x_1165, 1, x_1158);
x_3 = x_1165;
goto lbl_4;
}
else
{
obj* x_1166; obj* x_1169; obj* x_1171; obj* x_1172; obj* x_1174; 
x_1166 = lean::cnstr_get(x_1156, 0);
lean::inc(x_1166);
lean::dec(x_1156);
x_1169 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_1171 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1169, x_1, x_1158);
x_1172 = lean::cnstr_get(x_1171, 0);
lean::inc(x_1172);
x_1174 = lean::cnstr_get(x_1171, 1);
lean::inc(x_1174);
lean::dec(x_1171);
if (lean::obj_tag(x_1172) == 0)
{
obj* x_1178; obj* x_1181; obj* x_1182; 
lean::dec(x_1166);
x_1178 = lean::cnstr_get(x_1172, 0);
lean::inc(x_1178);
lean::dec(x_1172);
if (lean::is_scalar(x_1138)) {
 x_1181 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1181 = x_1138;
 lean::cnstr_set_tag(x_1138, 0);
}
lean::cnstr_set(x_1181, 0, x_1178);
if (lean::is_scalar(x_1146)) {
 x_1182 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1182 = x_1146;
}
lean::cnstr_set(x_1182, 0, x_1181);
lean::cnstr_set(x_1182, 1, x_1174);
x_3 = x_1182;
goto lbl_4;
}
else
{
obj* x_1184; obj* x_1185; 
lean::dec(x_1172);
if (lean::is_scalar(x_1138)) {
 x_1184 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1184 = x_1138;
}
lean::cnstr_set(x_1184, 0, x_1166);
if (lean::is_scalar(x_1146)) {
 x_1185 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1185 = x_1146;
}
lean::cnstr_set(x_1185, 0, x_1184);
lean::cnstr_set(x_1185, 1, x_1174);
x_3 = x_1185;
goto lbl_4;
}
}
}
}
}
lbl_1113:
{
obj* x_1187; obj* x_1189; obj* x_1190; obj* x_1192; obj* x_1194; 
lean::dec(x_1112);
x_1187 = l_lean_ir_cpp_emit__instr___closed__8;
lean::inc(x_1);
x_1189 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1187, x_1, x_2);
x_1190 = lean::cnstr_get(x_1189, 0);
lean::inc(x_1190);
x_1192 = lean::cnstr_get(x_1189, 1);
lean::inc(x_1192);
if (lean::is_exclusive(x_1189)) {
 lean::cnstr_release(x_1189, 0);
 lean::cnstr_release(x_1189, 1);
 x_1194 = x_1189;
} else {
 lean::dec(x_1189);
 x_1194 = lean::box(0);
}
if (lean::obj_tag(x_1190) == 0)
{
obj* x_1198; obj* x_1200; obj* x_1201; obj* x_1202; 
lean::dec(x_1105);
lean::dec(x_1103);
lean::dec(x_1107);
x_1198 = lean::cnstr_get(x_1190, 0);
lean::inc(x_1198);
if (lean::is_exclusive(x_1190)) {
 lean::cnstr_release(x_1190, 0);
 x_1200 = x_1190;
} else {
 lean::dec(x_1190);
 x_1200 = lean::box(0);
}
if (lean::is_scalar(x_1200)) {
 x_1201 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1201 = x_1200;
}
lean::cnstr_set(x_1201, 0, x_1198);
if (lean::is_scalar(x_1194)) {
 x_1202 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1202 = x_1194;
}
lean::cnstr_set(x_1202, 0, x_1201);
lean::cnstr_set(x_1202, 1, x_1192);
x_3 = x_1202;
goto lbl_4;
}
else
{
obj* x_1203; obj* x_1204; obj* x_1206; obj* x_1207; obj* x_1209; 
if (lean::is_exclusive(x_1190)) {
 lean::cnstr_release(x_1190, 0);
 x_1203 = x_1190;
} else {
 lean::dec(x_1190);
 x_1203 = lean::box(0);
}
x_1204 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_1206 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1204, x_1, x_1192);
x_1207 = lean::cnstr_get(x_1206, 0);
lean::inc(x_1207);
x_1209 = lean::cnstr_get(x_1206, 1);
lean::inc(x_1209);
lean::dec(x_1206);
if (lean::obj_tag(x_1207) == 0)
{
obj* x_1215; obj* x_1218; obj* x_1219; 
lean::dec(x_1105);
lean::dec(x_1103);
lean::dec(x_1107);
x_1215 = lean::cnstr_get(x_1207, 0);
lean::inc(x_1215);
lean::dec(x_1207);
if (lean::is_scalar(x_1203)) {
 x_1218 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1218 = x_1203;
 lean::cnstr_set_tag(x_1203, 0);
}
lean::cnstr_set(x_1218, 0, x_1215);
if (lean::is_scalar(x_1194)) {
 x_1219 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1219 = x_1194;
}
lean::cnstr_set(x_1219, 0, x_1218);
lean::cnstr_set(x_1219, 1, x_1209);
x_3 = x_1219;
goto lbl_4;
}
else
{
obj* x_1223; obj* x_1224; obj* x_1226; 
lean::dec(x_1194);
lean::dec(x_1207);
lean::inc(x_1);
x_1223 = l_lean_ir_cpp_emit__var(x_1103, x_1, x_1209);
x_1224 = lean::cnstr_get(x_1223, 0);
lean::inc(x_1224);
x_1226 = lean::cnstr_get(x_1223, 1);
lean::inc(x_1226);
lean::dec(x_1223);
if (lean::obj_tag(x_1224) == 0)
{
obj* x_1230; obj* x_1233; 
lean::dec(x_1105);
x_1230 = lean::cnstr_get(x_1224, 0);
lean::inc(x_1230);
lean::dec(x_1224);
if (lean::is_scalar(x_1203)) {
 x_1233 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1233 = x_1203;
 lean::cnstr_set_tag(x_1203, 0);
}
lean::cnstr_set(x_1233, 0, x_1230);
x_1109 = x_1233;
x_1110 = x_1226;
goto lbl_1111;
}
else
{
obj* x_1235; obj* x_1237; obj* x_1238; obj* x_1240; 
lean::dec(x_1224);
x_1235 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_1237 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1235, x_1, x_1226);
x_1238 = lean::cnstr_get(x_1237, 0);
lean::inc(x_1238);
x_1240 = lean::cnstr_get(x_1237, 1);
lean::inc(x_1240);
lean::dec(x_1237);
if (lean::obj_tag(x_1238) == 0)
{
obj* x_1244; obj* x_1247; 
lean::dec(x_1105);
x_1244 = lean::cnstr_get(x_1238, 0);
lean::inc(x_1244);
lean::dec(x_1238);
if (lean::is_scalar(x_1203)) {
 x_1247 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1247 = x_1203;
 lean::cnstr_set_tag(x_1203, 0);
}
lean::cnstr_set(x_1247, 0, x_1244);
x_1109 = x_1247;
x_1110 = x_1240;
goto lbl_1111;
}
else
{
obj* x_1251; obj* x_1252; obj* x_1254; 
lean::dec(x_1203);
lean::dec(x_1238);
lean::inc(x_1);
x_1251 = l_lean_ir_cpp_emit__var(x_1105, x_1, x_1240);
x_1252 = lean::cnstr_get(x_1251, 0);
lean::inc(x_1252);
x_1254 = lean::cnstr_get(x_1251, 1);
lean::inc(x_1254);
lean::dec(x_1251);
x_1109 = x_1252;
x_1110 = x_1254;
goto lbl_1111;
}
}
}
}
}
lbl_1115:
{
obj* x_1258; obj* x_1260; obj* x_1261; obj* x_1263; obj* x_1265; 
lean::dec(x_1114);
x_1258 = l_lean_ir_cpp_emit__instr___closed__9;
lean::inc(x_1);
x_1260 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1258, x_1, x_2);
x_1261 = lean::cnstr_get(x_1260, 0);
lean::inc(x_1261);
x_1263 = lean::cnstr_get(x_1260, 1);
lean::inc(x_1263);
if (lean::is_exclusive(x_1260)) {
 lean::cnstr_release(x_1260, 0);
 lean::cnstr_release(x_1260, 1);
 x_1265 = x_1260;
} else {
 lean::dec(x_1260);
 x_1265 = lean::box(0);
}
if (lean::obj_tag(x_1261) == 0)
{
obj* x_1269; obj* x_1271; obj* x_1272; obj* x_1273; 
lean::dec(x_1105);
lean::dec(x_1103);
lean::dec(x_1107);
x_1269 = lean::cnstr_get(x_1261, 0);
lean::inc(x_1269);
if (lean::is_exclusive(x_1261)) {
 lean::cnstr_release(x_1261, 0);
 x_1271 = x_1261;
} else {
 lean::dec(x_1261);
 x_1271 = lean::box(0);
}
if (lean::is_scalar(x_1271)) {
 x_1272 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1272 = x_1271;
}
lean::cnstr_set(x_1272, 0, x_1269);
if (lean::is_scalar(x_1265)) {
 x_1273 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1273 = x_1265;
}
lean::cnstr_set(x_1273, 0, x_1272);
lean::cnstr_set(x_1273, 1, x_1263);
x_3 = x_1273;
goto lbl_4;
}
else
{
obj* x_1274; obj* x_1275; obj* x_1277; obj* x_1278; obj* x_1280; 
if (lean::is_exclusive(x_1261)) {
 lean::cnstr_release(x_1261, 0);
 x_1274 = x_1261;
} else {
 lean::dec(x_1261);
 x_1274 = lean::box(0);
}
x_1275 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_1277 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1275, x_1, x_1263);
x_1278 = lean::cnstr_get(x_1277, 0);
lean::inc(x_1278);
x_1280 = lean::cnstr_get(x_1277, 1);
lean::inc(x_1280);
lean::dec(x_1277);
if (lean::obj_tag(x_1278) == 0)
{
obj* x_1286; obj* x_1289; obj* x_1290; 
lean::dec(x_1105);
lean::dec(x_1103);
lean::dec(x_1107);
x_1286 = lean::cnstr_get(x_1278, 0);
lean::inc(x_1286);
lean::dec(x_1278);
if (lean::is_scalar(x_1274)) {
 x_1289 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1289 = x_1274;
 lean::cnstr_set_tag(x_1274, 0);
}
lean::cnstr_set(x_1289, 0, x_1286);
if (lean::is_scalar(x_1265)) {
 x_1290 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1290 = x_1265;
}
lean::cnstr_set(x_1290, 0, x_1289);
lean::cnstr_set(x_1290, 1, x_1280);
x_3 = x_1290;
goto lbl_4;
}
else
{
obj* x_1294; obj* x_1295; obj* x_1297; 
lean::dec(x_1278);
lean::dec(x_1265);
lean::inc(x_1);
x_1294 = l_lean_ir_cpp_emit__var(x_1103, x_1, x_1280);
x_1295 = lean::cnstr_get(x_1294, 0);
lean::inc(x_1295);
x_1297 = lean::cnstr_get(x_1294, 1);
lean::inc(x_1297);
lean::dec(x_1294);
if (lean::obj_tag(x_1295) == 0)
{
obj* x_1301; obj* x_1304; 
lean::dec(x_1105);
x_1301 = lean::cnstr_get(x_1295, 0);
lean::inc(x_1301);
lean::dec(x_1295);
if (lean::is_scalar(x_1274)) {
 x_1304 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1304 = x_1274;
 lean::cnstr_set_tag(x_1274, 0);
}
lean::cnstr_set(x_1304, 0, x_1301);
x_1109 = x_1304;
x_1110 = x_1297;
goto lbl_1111;
}
else
{
obj* x_1306; obj* x_1308; obj* x_1309; obj* x_1311; 
lean::dec(x_1295);
x_1306 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_1308 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1306, x_1, x_1297);
x_1309 = lean::cnstr_get(x_1308, 0);
lean::inc(x_1309);
x_1311 = lean::cnstr_get(x_1308, 1);
lean::inc(x_1311);
lean::dec(x_1308);
if (lean::obj_tag(x_1309) == 0)
{
obj* x_1315; obj* x_1318; 
lean::dec(x_1105);
x_1315 = lean::cnstr_get(x_1309, 0);
lean::inc(x_1315);
lean::dec(x_1309);
if (lean::is_scalar(x_1274)) {
 x_1318 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1318 = x_1274;
 lean::cnstr_set_tag(x_1274, 0);
}
lean::cnstr_set(x_1318, 0, x_1315);
x_1109 = x_1318;
x_1110 = x_1311;
goto lbl_1111;
}
else
{
obj* x_1322; obj* x_1323; obj* x_1325; 
lean::dec(x_1309);
lean::dec(x_1274);
lean::inc(x_1);
x_1322 = l_lean_ir_cpp_emit__var(x_1105, x_1, x_1311);
x_1323 = lean::cnstr_get(x_1322, 0);
lean::inc(x_1323);
x_1325 = lean::cnstr_get(x_1322, 1);
lean::inc(x_1325);
lean::dec(x_1322);
x_1109 = x_1323;
x_1110 = x_1325;
goto lbl_1111;
}
}
}
}
}
}
}
lbl_4:
{
obj* x_1328; obj* x_1330; obj* x_1332; 
x_1328 = lean::cnstr_get(x_3, 0);
lean::inc(x_1328);
x_1330 = lean::cnstr_get(x_3, 1);
lean::inc(x_1330);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_1332 = x_3;
} else {
 lean::dec(x_3);
 x_1332 = lean::box(0);
}
if (lean::obj_tag(x_1328) == 0)
{
obj* x_1334; obj* x_1336; obj* x_1337; uint8 x_1338; obj* x_1339; obj* x_1340; obj* x_1341; obj* x_1342; obj* x_1343; obj* x_1344; obj* x_1345; obj* x_1346; obj* x_1347; obj* x_1348; obj* x_1349; obj* x_1350; obj* x_1351; 
lean::dec(x_1);
x_1334 = lean::cnstr_get(x_1328, 0);
lean::inc(x_1334);
if (lean::is_exclusive(x_1328)) {
 lean::cnstr_release(x_1328, 0);
 x_1336 = x_1328;
} else {
 lean::dec(x_1328);
 x_1336 = lean::box(0);
}
x_1337 = l_lean_ir_instr_to__format___main(x_0);
x_1338 = 0;
x_1339 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
x_1340 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1340, 0, x_1339);
lean::cnstr_set(x_1340, 1, x_1337);
lean::cnstr_set_scalar(x_1340, sizeof(void*)*2, x_1338);
x_1341 = x_1340;
x_1342 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_1343 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1343, 0, x_1341);
lean::cnstr_set(x_1343, 1, x_1342);
lean::cnstr_set_scalar(x_1343, sizeof(void*)*2, x_1338);
x_1344 = x_1343;
x_1345 = lean::box(1);
x_1346 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1346, 0, x_1344);
lean::cnstr_set(x_1346, 1, x_1345);
lean::cnstr_set_scalar(x_1346, sizeof(void*)*2, x_1338);
x_1347 = x_1346;
x_1348 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1348, 0, x_1347);
lean::cnstr_set(x_1348, 1, x_1334);
lean::cnstr_set_scalar(x_1348, sizeof(void*)*2, x_1338);
x_1349 = x_1348;
if (lean::is_scalar(x_1336)) {
 x_1350 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1350 = x_1336;
}
lean::cnstr_set(x_1350, 0, x_1349);
if (lean::is_scalar(x_1332)) {
 x_1351 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1351 = x_1332;
}
lean::cnstr_set(x_1351, 0, x_1350);
lean::cnstr_set(x_1351, 1, x_1330);
return x_1351;
}
else
{
obj* x_1352; obj* x_1353; obj* x_1354; obj* x_1356; 
if (lean::is_exclusive(x_1328)) {
 lean::cnstr_release(x_1328, 0);
 x_1352 = x_1328;
} else {
 lean::dec(x_1328);
 x_1352 = lean::box(0);
}
x_1353 = l_lean_ir_cpp_emit__eos(x_1, x_1330);
x_1354 = lean::cnstr_get(x_1353, 0);
lean::inc(x_1354);
x_1356 = lean::cnstr_get(x_1353, 1);
lean::inc(x_1356);
lean::dec(x_1353);
if (lean::obj_tag(x_1354) == 0)
{
obj* x_1359; obj* x_1362; uint8 x_1363; obj* x_1364; obj* x_1365; obj* x_1366; obj* x_1367; obj* x_1368; obj* x_1369; obj* x_1370; obj* x_1371; obj* x_1372; obj* x_1373; obj* x_1374; obj* x_1375; obj* x_1376; 
x_1359 = lean::cnstr_get(x_1354, 0);
lean::inc(x_1359);
lean::dec(x_1354);
x_1362 = l_lean_ir_instr_to__format___main(x_0);
x_1363 = 0;
x_1364 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
x_1365 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1365, 0, x_1364);
lean::cnstr_set(x_1365, 1, x_1362);
lean::cnstr_set_scalar(x_1365, sizeof(void*)*2, x_1363);
x_1366 = x_1365;
x_1367 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_1368 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1368, 0, x_1366);
lean::cnstr_set(x_1368, 1, x_1367);
lean::cnstr_set_scalar(x_1368, sizeof(void*)*2, x_1363);
x_1369 = x_1368;
x_1370 = lean::box(1);
x_1371 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1371, 0, x_1369);
lean::cnstr_set(x_1371, 1, x_1370);
lean::cnstr_set_scalar(x_1371, sizeof(void*)*2, x_1363);
x_1372 = x_1371;
x_1373 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1373, 0, x_1372);
lean::cnstr_set(x_1373, 1, x_1359);
lean::cnstr_set_scalar(x_1373, sizeof(void*)*2, x_1363);
x_1374 = x_1373;
if (lean::is_scalar(x_1352)) {
 x_1375 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1375 = x_1352;
 lean::cnstr_set_tag(x_1352, 0);
}
lean::cnstr_set(x_1375, 0, x_1374);
if (lean::is_scalar(x_1332)) {
 x_1376 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1376 = x_1332;
}
lean::cnstr_set(x_1376, 0, x_1375);
lean::cnstr_set(x_1376, 1, x_1356);
return x_1376;
}
else
{
obj* x_1379; 
lean::dec(x_1352);
lean::dec(x_0);
if (lean::is_scalar(x_1332)) {
 x_1379 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1379 = x_1332;
}
lean::cnstr_set(x_1379, 0, x_1354);
lean::cnstr_set(x_1379, 1, x_1356);
return x_1379;
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
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_cpp_emit__instr(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 x_17 = x_12;
} else {
 lean::dec(x_12);
 x_17 = lean::box(0);
}
if (lean::obj_tag(x_13) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_20 = lean::cnstr_get(x_13, 0);
lean::inc(x_20);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_22 = x_13;
} else {
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
return x_24;
}
else
{
lean::dec(x_17);
lean::dec(x_13);
x_0 = x_8;
x_2 = x_15;
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
x_13 = x_16;
x_14 = x_2;
goto lbl_15;
}
else
{
obj* x_17; 
x_17 = l_lean_ir_match__type___closed__5;
x_13 = x_17;
x_14 = x_2;
goto lbl_15;
}
lbl_15:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_6);
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
x_22 = lean::cnstr_get(x_13, 0);
lean::inc(x_22);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_24 = x_13;
} else {
 lean::dec(x_13);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_14);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_34; 
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_27 = x_13;
} else {
 lean::dec(x_13);
 x_27 = lean::box(0);
}
lean::inc(x_1);
x_29 = l_lean_ir_cpp_emit__blockid(x_6, x_1, x_14);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 lean::cnstr_release(x_29, 1);
 x_34 = x_29;
} else {
 lean::dec(x_29);
 x_34 = lean::box(0);
}
if (lean::obj_tag(x_30) == 0)
{
obj* x_38; obj* x_41; obj* x_42; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
x_38 = lean::cnstr_get(x_30, 0);
lean::inc(x_38);
lean::dec(x_30);
if (lean::is_scalar(x_27)) {
 x_41 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_41 = x_27;
 lean::cnstr_set_tag(x_27, 0);
}
lean::cnstr_set(x_41, 0, x_38);
if (lean::is_scalar(x_34)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_34;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_32);
return x_42;
}
else
{
obj* x_44; obj* x_46; obj* x_47; obj* x_49; 
lean::dec(x_30);
x_44 = l_lean_ir_cpp_emit__block___closed__1;
lean::inc(x_1);
x_46 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_44, x_1, x_32);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_55; obj* x_58; obj* x_59; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
x_55 = lean::cnstr_get(x_47, 0);
lean::inc(x_55);
lean::dec(x_47);
if (lean::is_scalar(x_27)) {
 x_58 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_58 = x_27;
 lean::cnstr_set_tag(x_27, 0);
}
lean::cnstr_set(x_58, 0, x_55);
if (lean::is_scalar(x_34)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_34;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_49);
return x_59;
}
else
{
obj* x_61; obj* x_63; obj* x_64; obj* x_66; 
lean::dec(x_47);
x_61 = l_lean_format_be___main___closed__1;
lean::inc(x_1);
x_63 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_61, x_1, x_49);
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_63, 1);
lean::inc(x_66);
lean::dec(x_63);
if (lean::obj_tag(x_64) == 0)
{
obj* x_72; obj* x_75; obj* x_76; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
x_72 = lean::cnstr_get(x_64, 0);
lean::inc(x_72);
lean::dec(x_64);
if (lean::is_scalar(x_27)) {
 x_75 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_75 = x_27;
 lean::cnstr_set_tag(x_27, 0);
}
lean::cnstr_set(x_75, 0, x_72);
if (lean::is_scalar(x_34)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_34;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_66);
return x_76;
}
else
{
obj* x_79; obj* x_80; obj* x_82; 
lean::dec(x_64);
lean::inc(x_1);
x_79 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__block___spec__1(x_8, x_1, x_66);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
if (lean::obj_tag(x_80) == 0)
{
obj* x_87; obj* x_90; obj* x_91; 
lean::dec(x_10);
lean::dec(x_1);
x_87 = lean::cnstr_get(x_80, 0);
lean::inc(x_87);
lean::dec(x_80);
if (lean::is_scalar(x_27)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_27;
 lean::cnstr_set_tag(x_27, 0);
}
lean::cnstr_set(x_90, 0, x_87);
if (lean::is_scalar(x_34)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_34;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_82);
return x_91;
}
else
{
obj* x_95; 
lean::dec(x_80);
lean::dec(x_27);
lean::dec(x_34);
x_95 = l_lean_ir_cpp_emit__terminator(x_10, x_1, x_82);
return x_95;
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
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_24 = x_17;
} else {
 lean::dec(x_17);
 x_24 = lean::box(0);
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
obj* x_27; obj* x_29; obj* x_30; obj* x_32; 
lean::dec(x_17);
x_27 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_1);
x_29 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_27, x_1, x_19);
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
lean::inc(x_38);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_40 = x_10;
} else {
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
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; 
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_43 = x_10;
} else {
 lean::dec(x_10);
 x_43 = lean::box(0);
}
lean::inc(x_1);
x_45 = l_lean_ir_cpp_emit__fnid(x_5, x_1, x_11);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_50 = x_45;
} else {
 lean::dec(x_45);
 x_50 = lean::box(0);
}
if (lean::obj_tag(x_46) == 0)
{
obj* x_53; obj* x_56; obj* x_57; 
lean::dec(x_7);
lean::dec(x_1);
x_53 = lean::cnstr_get(x_46, 0);
lean::inc(x_53);
lean::dec(x_46);
if (lean::is_scalar(x_43)) {
 x_56 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_56 = x_43;
 lean::cnstr_set_tag(x_43, 0);
}
lean::cnstr_set(x_56, 0, x_53);
if (lean::is_scalar(x_50)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_50;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_48);
return x_57;
}
else
{
obj* x_59; obj* x_61; obj* x_62; obj* x_64; 
lean::dec(x_46);
x_59 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_61 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_59, x_1, x_48);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
if (lean::obj_tag(x_62) == 0)
{
obj* x_69; obj* x_72; obj* x_73; 
lean::dec(x_7);
lean::dec(x_1);
x_69 = lean::cnstr_get(x_62, 0);
lean::inc(x_69);
lean::dec(x_62);
if (lean::is_scalar(x_43)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_43;
 lean::cnstr_set_tag(x_43, 0);
}
lean::cnstr_set(x_72, 0, x_69);
if (lean::is_scalar(x_50)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_50;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_64);
return x_73;
}
else
{
obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_81; 
lean::dec(x_62);
x_75 = l_lean_ir_cpp_emit__header___closed__1;
x_76 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_1);
x_78 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_75, x_76, x_7, x_1, x_64);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
lean::dec(x_78);
if (lean::obj_tag(x_79) == 0)
{
obj* x_85; obj* x_88; obj* x_89; 
lean::dec(x_1);
x_85 = lean::cnstr_get(x_79, 0);
lean::inc(x_85);
lean::dec(x_79);
if (lean::is_scalar(x_43)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_43;
 lean::cnstr_set_tag(x_43, 0);
}
lean::cnstr_set(x_88, 0, x_85);
if (lean::is_scalar(x_50)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_50;
}
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_81);
return x_89;
}
else
{
obj* x_90; obj* x_93; obj* x_94; obj* x_95; obj* x_97; 
x_90 = lean::cnstr_get(x_79, 0);
lean::inc(x_90);
lean::dec(x_79);
x_93 = l_option_has__repr___rarg___closed__3;
x_94 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_93, x_1, x_81);
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_94, 1);
lean::inc(x_97);
lean::dec(x_94);
if (lean::obj_tag(x_95) == 0)
{
obj* x_101; obj* x_104; obj* x_105; 
lean::dec(x_90);
x_101 = lean::cnstr_get(x_95, 0);
lean::inc(x_101);
lean::dec(x_95);
if (lean::is_scalar(x_43)) {
 x_104 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_104 = x_43;
 lean::cnstr_set_tag(x_43, 0);
}
lean::cnstr_set(x_104, 0, x_101);
if (lean::is_scalar(x_50)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_50;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_97);
return x_105;
}
else
{
obj* x_107; obj* x_108; 
lean::dec(x_95);
if (lean::is_scalar(x_43)) {
 x_107 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_107 = x_43;
}
lean::cnstr_set(x_107, 0, x_90);
if (lean::is_scalar(x_50)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_50;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_97);
return x_108;
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
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
} else {
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_0);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
} else {
 lean::dec(x_6);
 x_15 = lean::box(0);
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
obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
} else {
 lean::dec(x_6);
 x_18 = lean::box(0);
}
x_19 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_2);
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_2, x_8);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_29; obj* x_32; obj* x_33; 
lean::dec(x_0);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
lean::dec(x_22);
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_10)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_10;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_24);
return x_33;
}
else
{
obj* x_36; obj* x_37; obj* x_39; 
lean::dec(x_22);
lean::inc(x_2);
x_36 = l_lean_ir_cpp_emit__var(x_0, x_2, x_24);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
if (lean::obj_tag(x_37) == 0)
{
obj* x_43; obj* x_46; obj* x_47; 
lean::dec(x_2);
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
if (lean::is_scalar(x_10)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_10;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_39);
return x_47;
}
else
{
obj* x_51; 
lean::dec(x_10);
lean::dec(x_18);
lean::dec(x_37);
x_51 = l_lean_ir_cpp_emit__eos(x_2, x_39);
return x_51;
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
uint8 x_3; obj* x_4; 
lean::dec(x_0);
x_3 = 0;
x_4 = lean::box(x_3);
return x_4;
}
else
{
obj* x_5; obj* x_7; obj* x_10; uint8 x_13; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean_name_dec_eq(x_10, x_0);
lean::dec(x_10);
if (x_13 == 0)
{
x_1 = x_7;
goto _start;
}
else
{
uint8 x_18; obj* x_19; 
lean::dec(x_7);
lean::dec(x_0);
x_18 = 1;
x_19 = lean::box(x_18);
return x_19;
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
case 1:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_20; obj* x_21; obj* x_23; obj* x_25; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 2);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_1, 3);
lean::inc(x_15);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_0);
x_20 = l_rbnode_mfold___main___at_lean_ir_cpp_decl__locals___spec__2(x_0, x_9, x_2, x_3, x_4);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_release(x_20, 1);
 x_25 = x_20;
} else {
 lean::dec(x_20);
 x_25 = lean::box(0);
}
if (lean::obj_tag(x_21) == 0)
{
obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_15);
x_31 = lean::cnstr_get(x_21, 0);
lean::inc(x_31);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_33 = x_21;
} else {
 lean::dec(x_21);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_31);
if (lean::is_scalar(x_25)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_25;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_23);
return x_35;
}
else
{
obj* x_36; obj* x_39; uint8 x_40; 
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_36 = x_21;
} else {
 lean::dec(x_21);
 x_36 = lean::box(0);
}
lean::inc(x_0);
lean::inc(x_11);
x_39 = l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1(x_11, x_0);
x_40 = lean::unbox(x_39);
lean::dec(x_39);
if (x_40 == 0)
{
uint8 x_42; obj* x_45; obj* x_46; obj* x_48; 
x_42 = lean::unbox(x_13);
lean::dec(x_13);
lean::inc(x_3);
x_45 = l_lean_ir_cpp_decl__local(x_11, x_42, x_3, x_23);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
if (lean::obj_tag(x_46) == 0)
{
obj* x_54; obj* x_57; obj* x_58; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_15);
x_54 = lean::cnstr_get(x_46, 0);
lean::inc(x_54);
lean::dec(x_46);
if (lean::is_scalar(x_36)) {
 x_57 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_57 = x_36;
 lean::cnstr_set_tag(x_36, 0);
}
lean::cnstr_set(x_57, 0, x_54);
if (lean::is_scalar(x_25)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_25;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_48);
return x_58;
}
else
{
obj* x_62; 
lean::dec(x_25);
lean::dec(x_46);
lean::dec(x_36);
x_62 = lean::box(0);
x_1 = x_15;
x_2 = x_62;
x_4 = x_48;
goto _start;
}
}
else
{
obj* x_68; 
lean::dec(x_25);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_36);
x_68 = lean::box(0);
x_1 = x_15;
x_2 = x_68;
x_4 = x_23;
goto _start;
}
}
}
default:
{
obj* x_70; obj* x_72; obj* x_74; obj* x_76; obj* x_81; obj* x_82; obj* x_84; obj* x_86; 
x_70 = lean::cnstr_get(x_1, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_1, 1);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_1, 2);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_1, 3);
lean::inc(x_76);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_0);
x_81 = l_rbnode_mfold___main___at_lean_ir_cpp_decl__locals___spec__2(x_0, x_70, x_2, x_3, x_4);
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_81, 1);
lean::inc(x_84);
if (lean::is_exclusive(x_81)) {
 lean::cnstr_release(x_81, 0);
 lean::cnstr_release(x_81, 1);
 x_86 = x_81;
} else {
 lean::dec(x_81);
 x_86 = lean::box(0);
}
if (lean::obj_tag(x_82) == 0)
{
obj* x_92; obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_72);
lean::dec(x_76);
lean::dec(x_74);
x_92 = lean::cnstr_get(x_82, 0);
lean::inc(x_92);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_release(x_82, 0);
 x_94 = x_82;
} else {
 lean::dec(x_82);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_92);
if (lean::is_scalar(x_86)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_86;
}
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_84);
return x_96;
}
else
{
obj* x_97; obj* x_100; uint8 x_101; 
if (lean::is_exclusive(x_82)) {
 lean::cnstr_release(x_82, 0);
 x_97 = x_82;
} else {
 lean::dec(x_82);
 x_97 = lean::box(0);
}
lean::inc(x_0);
lean::inc(x_72);
x_100 = l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1(x_72, x_0);
x_101 = lean::unbox(x_100);
lean::dec(x_100);
if (x_101 == 0)
{
uint8 x_103; obj* x_106; obj* x_107; obj* x_109; 
x_103 = lean::unbox(x_74);
lean::dec(x_74);
lean::inc(x_3);
x_106 = l_lean_ir_cpp_decl__local(x_72, x_103, x_3, x_84);
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_106, 1);
lean::inc(x_109);
lean::dec(x_106);
if (lean::obj_tag(x_107) == 0)
{
obj* x_115; obj* x_118; obj* x_119; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_76);
x_115 = lean::cnstr_get(x_107, 0);
lean::inc(x_115);
lean::dec(x_107);
if (lean::is_scalar(x_97)) {
 x_118 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_118 = x_97;
 lean::cnstr_set_tag(x_97, 0);
}
lean::cnstr_set(x_118, 0, x_115);
if (lean::is_scalar(x_86)) {
 x_119 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_119 = x_86;
}
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_109);
return x_119;
}
else
{
obj* x_123; 
lean::dec(x_86);
lean::dec(x_97);
lean::dec(x_107);
x_123 = lean::box(0);
x_1 = x_76;
x_2 = x_123;
x_4 = x_109;
goto _start;
}
}
else
{
obj* x_129; 
lean::dec(x_86);
lean::dec(x_97);
lean::dec(x_72);
lean::dec(x_74);
x_129 = lean::box(0);
x_1 = x_76;
x_2 = x_129;
x_4 = x_84;
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
uint8 x_1; obj* x_2; 
x_1 = 1;
x_2 = lean::box(x_1);
return x_2;
}
else
{
obj* x_3; obj* x_5; uint8 x_8; obj* x_10; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
lean::dec(x_3);
x_10 = l_lean_ir_type2id___main(x_8);
x_11 = l_lean_ir_valid__assign__unop__types___closed__1;
x_12 = lean::nat_dec_eq(x_10, x_11);
lean::dec(x_10);
if (x_12 == 0)
{
uint8 x_15; obj* x_16; 
lean::dec(x_5);
x_15 = 0;
x_16 = lean::box(x_15);
return x_16;
}
else
{
x_0 = x_5;
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
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_3 = l_lean_ir_cpp_emit__uncurry__header___closed__1;
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
} else {
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
} else {
 lean::dec(x_6);
 x_15 = lean::box(0);
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
obj* x_18; obj* x_19; obj* x_20; obj* x_24; obj* x_25; obj* x_27; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
} else {
 lean::dec(x_6);
 x_18 = lean::box(0);
}
x_19 = l_lean_ir_decl_header___main(x_0);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
lean::dec(x_19);
lean::inc(x_1);
x_24 = l_lean_ir_cpp_emit__fnid(x_20, x_1, x_8);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_31; obj* x_34; obj* x_35; 
lean::dec(x_1);
x_31 = lean::cnstr_get(x_25, 0);
lean::inc(x_31);
lean::dec(x_25);
if (lean::is_scalar(x_18)) {
 x_34 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_34 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_34, 0, x_31);
if (lean::is_scalar(x_10)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_10;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_27);
return x_35;
}
else
{
obj* x_39; obj* x_40; 
lean::dec(x_10);
lean::dec(x_25);
lean::dec(x_18);
x_39 = l_lean_ir_cpp_emit__uncurry__header___closed__2;
x_40 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_39, x_1, x_27);
return x_40;
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
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
} else {
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
} else {
 lean::dec(x_6);
 x_15 = lean::box(0);
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
obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
} else {
 lean::dec(x_6);
 x_18 = lean::box(0);
}
x_19 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_2, x_8);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_29; obj* x_32; obj* x_33; 
lean::dec(x_1);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
lean::dec(x_22);
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_10)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_10;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_24);
return x_33;
}
else
{
obj* x_35; obj* x_37; obj* x_38; obj* x_40; 
lean::dec(x_22);
x_35 = l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___closed__1;
lean::inc(x_2);
x_37 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_35, x_2, x_24);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_45; obj* x_48; obj* x_49; 
lean::dec(x_1);
lean::dec(x_2);
x_45 = lean::cnstr_get(x_38, 0);
lean::inc(x_45);
lean::dec(x_38);
if (lean::is_scalar(x_18)) {
 x_48 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_48 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_48, 0, x_45);
if (lean::is_scalar(x_10)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_10;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_40);
return x_49;
}
else
{
obj* x_51; obj* x_52; obj* x_55; obj* x_56; obj* x_58; 
lean::dec(x_38);
x_51 = lean::mk_nat_obj(1u);
x_52 = lean::nat_add(x_1, x_51);
lean::dec(x_1);
lean::inc(x_2);
x_55 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_52, x_2, x_40);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_62; obj* x_65; obj* x_66; 
lean::dec(x_2);
x_62 = lean::cnstr_get(x_56, 0);
lean::inc(x_62);
lean::dec(x_56);
if (lean::is_scalar(x_18)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_65, 0, x_62);
if (lean::is_scalar(x_10)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_10;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_58);
return x_66;
}
else
{
obj* x_70; obj* x_71; 
lean::dec(x_10);
lean::dec(x_18);
lean::dec(x_56);
x_70 = l_list_repr___main___rarg___closed__3;
x_71 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_70, x_2, x_58);
return x_71;
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
obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_17; obj* x_20; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
lean::inc(x_0);
x_10 = l_lean_ir_decl_header___main(x_0);
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
x_14 = l_list_length__aux___main___rarg(x_11, x_5);
x_15 = lean::nat_sub(x_14, x_7);
lean::dec(x_14);
x_17 = lean::nat_sub(x_15, x_1);
lean::dec(x_1);
lean::dec(x_15);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1), 4, 2);
lean::closure_set(x_20, 0, x_2);
lean::closure_set(x_20, 1, x_17);
x_1 = x_8;
x_2 = x_20;
goto _start;
}
else
{
obj* x_24; 
lean::dec(x_1);
lean::dec(x_0);
x_24 = lean::apply_2(x_2, x_3, x_4);
return x_24;
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
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
lean::inc(x_0);
x_4 = l_lean_ir_decl_header___main(x_0);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_list_length__aux___main___rarg(x_5, x_8);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_9, x_10);
lean::dec(x_9);
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
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_19 = x_12;
} else {
 lean::dec(x_12);
 x_19 = lean::box(0);
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
obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_31; 
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_21 = x_12;
} else {
 lean::dec(x_12);
 x_21 = lean::box(0);
}
x_22 = l_lean_ir_cpp_emit__uncurry___closed__3;
lean::inc(x_1);
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_1, x_14);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
lean::inc(x_0);
x_31 = l_lean_ir_decl_header___main(x_0);
if (lean::obj_tag(x_25) == 0)
{
obj* x_33; obj* x_36; 
lean::dec(x_31);
x_33 = lean::cnstr_get(x_25, 0);
lean::inc(x_33);
lean::dec(x_25);
if (lean::is_scalar(x_21)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_21;
 lean::cnstr_set_tag(x_21, 0);
}
lean::cnstr_set(x_36, 0, x_33);
x_6 = x_36;
x_7 = x_27;
goto lbl_8;
}
else
{
obj* x_38; obj* x_41; obj* x_43; obj* x_44; obj* x_46; 
lean::dec(x_25);
x_38 = lean::cnstr_get(x_31, 0);
lean::inc(x_38);
lean::dec(x_31);
x_41 = l_lean_ir_cpp_emit__terminator___closed__1;
lean::inc(x_1);
x_43 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_41, x_1, x_27);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_50; obj* x_53; 
lean::dec(x_38);
x_50 = lean::cnstr_get(x_44, 0);
lean::inc(x_50);
lean::dec(x_44);
if (lean::is_scalar(x_21)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_21;
 lean::cnstr_set_tag(x_21, 0);
}
lean::cnstr_set(x_53, 0, x_50);
x_6 = x_53;
x_7 = x_46;
goto lbl_8;
}
else
{
obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_44);
lean::dec(x_21);
lean::inc(x_1);
x_57 = l_lean_ir_cpp_emit__fnid(x_38, x_1, x_46);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
x_6 = x_58;
x_7 = x_60;
goto lbl_8;
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_1);
x_64 = lean::cnstr_get(x_3, 0);
lean::inc(x_64);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_66 = x_3;
} else {
 lean::dec(x_3);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_64);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_4);
return x_68;
}
else
{
obj* x_69; obj* x_71; obj* x_72; obj* x_74; obj* x_76; 
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_69 = x_3;
} else {
 lean::dec(x_3);
 x_69 = lean::box(0);
}
lean::inc(x_1);
x_71 = l_lean_ir_cpp_emit__eos(x_1, x_4);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 x_76 = x_71;
} else {
 lean::dec(x_71);
 x_76 = lean::box(0);
}
if (lean::obj_tag(x_72) == 0)
{
obj* x_78; obj* x_81; obj* x_82; 
lean::dec(x_1);
x_78 = lean::cnstr_get(x_72, 0);
lean::inc(x_78);
lean::dec(x_72);
if (lean::is_scalar(x_69)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_69;
 lean::cnstr_set_tag(x_69, 0);
}
lean::cnstr_set(x_81, 0, x_78);
if (lean::is_scalar(x_76)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_76;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_74);
return x_82;
}
else
{
obj* x_86; obj* x_87; 
lean::dec(x_69);
lean::dec(x_72);
lean::dec(x_76);
x_86 = l_lean_ir_cpp_emit__uncurry___closed__1;
x_87 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_86, x_1, x_74);
return x_87;
}
}
}
lbl_8:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_89; obj* x_91; obj* x_92; 
lean::dec(x_0);
x_89 = lean::cnstr_get(x_6, 0);
lean::inc(x_89);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_91 = x_6;
} else {
 lean::dec(x_6);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_89);
x_3 = x_92;
x_4 = x_7;
goto lbl_5;
}
else
{
obj* x_93; obj* x_94; obj* x_96; obj* x_97; obj* x_99; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_93 = x_6;
} else {
 lean::dec(x_6);
 x_93 = lean::box(0);
}
x_94 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_96 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_94, x_1, x_7);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
lean::dec(x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_103; obj* x_106; 
lean::dec(x_0);
x_103 = lean::cnstr_get(x_97, 0);
lean::inc(x_103);
lean::dec(x_97);
if (lean::is_scalar(x_93)) {
 x_106 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_106 = x_93;
 lean::cnstr_set_tag(x_93, 0);
}
lean::cnstr_set(x_106, 0, x_103);
x_3 = x_106;
x_4 = x_99;
goto lbl_5;
}
else
{
obj* x_108; obj* x_110; obj* x_111; obj* x_113; 
lean::dec(x_97);
x_108 = l_lean_ir_cpp_emit__uncurry___closed__2;
lean::inc(x_1);
x_110 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_108, x_1, x_99);
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_110, 1);
lean::inc(x_113);
lean::dec(x_110);
if (lean::obj_tag(x_111) == 0)
{
obj* x_117; obj* x_120; 
lean::dec(x_0);
x_117 = lean::cnstr_get(x_111, 0);
lean::inc(x_117);
lean::dec(x_111);
if (lean::is_scalar(x_93)) {
 x_120 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_120 = x_93;
 lean::cnstr_set_tag(x_93, 0);
}
lean::cnstr_set(x_120, 0, x_117);
x_3 = x_120;
x_4 = x_113;
goto lbl_5;
}
else
{
obj* x_123; obj* x_124; obj* x_126; 
lean::dec(x_111);
lean::inc(x_1);
x_123 = l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1(x_0, x_1, x_113);
x_124 = lean::cnstr_get(x_123, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_123, 1);
lean::inc(x_126);
lean::dec(x_123);
if (lean::obj_tag(x_124) == 0)
{
obj* x_129; obj* x_132; 
x_129 = lean::cnstr_get(x_124, 0);
lean::inc(x_129);
lean::dec(x_124);
if (lean::is_scalar(x_93)) {
 x_132 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_132 = x_93;
 lean::cnstr_set_tag(x_93, 0);
}
lean::cnstr_set(x_132, 0, x_129);
x_3 = x_132;
x_4 = x_126;
goto lbl_5;
}
else
{
obj* x_133; obj* x_136; obj* x_138; obj* x_139; obj* x_141; 
x_133 = lean::cnstr_get(x_124, 0);
lean::inc(x_133);
lean::dec(x_124);
x_136 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_138 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_136, x_1, x_126);
x_139 = lean::cnstr_get(x_138, 0);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_138, 1);
lean::inc(x_141);
lean::dec(x_138);
if (lean::obj_tag(x_139) == 0)
{
obj* x_145; obj* x_148; 
lean::dec(x_133);
x_145 = lean::cnstr_get(x_139, 0);
lean::inc(x_145);
lean::dec(x_139);
if (lean::is_scalar(x_93)) {
 x_148 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_148 = x_93;
 lean::cnstr_set_tag(x_93, 0);
}
lean::cnstr_set(x_148, 0, x_145);
x_3 = x_148;
x_4 = x_141;
goto lbl_5;
}
else
{
obj* x_150; 
lean::dec(x_139);
if (lean::is_scalar(x_93)) {
 x_150 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_150 = x_93;
}
lean::cnstr_set(x_150, 0, x_133);
x_3 = x_150;
x_4 = x_141;
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
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_cpp_emit__block(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 x_17 = x_12;
} else {
 lean::dec(x_12);
 x_17 = lean::box(0);
}
if (lean::obj_tag(x_13) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_20 = lean::cnstr_get(x_13, 0);
lean::inc(x_20);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_22 = x_13;
} else {
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
return x_24;
}
else
{
lean::dec(x_17);
lean::dec(x_13);
x_0 = x_8;
x_2 = x_15;
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
x_5 = x_10;
x_6 = x_2;
goto lbl_7;
}
else
{
obj* x_11; obj* x_13; obj* x_15; obj* x_18; uint8 x_19; uint8 x_21; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
lean::inc(x_0);
x_18 = l_lean_ir_cpp_need__uncurry(x_0);
x_19 = lean::unbox(x_18);
lean::dec(x_18);
if (x_19 == 0)
{
uint8 x_23; 
x_23 = 0;
x_21 = x_23;
goto lbl_22;
}
else
{
uint8 x_24; 
x_24 = 1;
x_21 = x_24;
goto lbl_22;
}
lbl_22:
{
obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_32; 
lean::inc(x_1);
x_29 = l_lean_ir_cpp_emit__header(x_11, x_1, x_2);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_15);
x_36 = lean::cnstr_get(x_30, 0);
lean::inc(x_36);
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_38 = x_30;
} else {
 lean::dec(x_30);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
x_25 = x_39;
x_26 = x_32;
goto lbl_27;
}
else
{
obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_46; 
if (lean::is_exclusive(x_30)) {
 lean::cnstr_release(x_30, 0);
 x_40 = x_30;
} else {
 lean::dec(x_30);
 x_40 = lean::box(0);
}
x_41 = l_lean_ir_cpp_emit__case___main___closed__1;
lean::inc(x_1);
x_43 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_41, x_1, x_32);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_50; obj* x_53; 
lean::dec(x_15);
x_50 = lean::cnstr_get(x_44, 0);
lean::inc(x_50);
lean::dec(x_44);
if (lean::is_scalar(x_40)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_40;
 lean::cnstr_set_tag(x_40, 0);
}
lean::cnstr_set(x_53, 0, x_50);
x_25 = x_53;
x_26 = x_46;
goto lbl_27;
}
else
{
obj* x_55; obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_44);
x_55 = l_lean_format_be___main___closed__1;
lean::inc(x_1);
x_57 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_55, x_1, x_46);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_64; obj* x_67; 
lean::dec(x_15);
x_64 = lean::cnstr_get(x_58, 0);
lean::inc(x_64);
lean::dec(x_58);
if (lean::is_scalar(x_40)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_40;
 lean::cnstr_set_tag(x_40, 0);
}
lean::cnstr_set(x_67, 0, x_64);
x_25 = x_67;
x_26 = x_60;
goto lbl_27;
}
else
{
obj* x_71; obj* x_72; obj* x_74; 
lean::dec(x_58);
lean::dec(x_40);
lean::inc(x_1);
x_71 = l_lean_ir_cpp_decl__locals(x_15, x_1, x_60);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
lean::dec(x_71);
x_25 = x_72;
x_26 = x_74;
goto lbl_27;
}
}
}
lbl_27:
{
if (lean::obj_tag(x_25) == 0)
{
obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_13);
lean::dec(x_1);
lean::dec(x_0);
x_80 = lean::cnstr_get(x_25, 0);
lean::inc(x_80);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_82 = x_25;
} else {
 lean::dec(x_25);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_80);
x_5 = x_83;
x_6 = x_26;
goto lbl_7;
}
else
{
obj* x_84; obj* x_86; obj* x_87; obj* x_89; 
if (lean::is_exclusive(x_25)) {
 lean::cnstr_release(x_25, 0);
 x_84 = x_25;
} else {
 lean::dec(x_25);
 x_84 = lean::box(0);
}
lean::inc(x_1);
x_86 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__def__core___spec__1(x_13, x_1, x_26);
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_86, 1);
lean::inc(x_89);
lean::dec(x_86);
if (lean::obj_tag(x_87) == 0)
{
obj* x_94; obj* x_97; 
lean::dec(x_1);
lean::dec(x_0);
x_94 = lean::cnstr_get(x_87, 0);
lean::inc(x_94);
lean::dec(x_87);
if (lean::is_scalar(x_84)) {
 x_97 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_97 = x_84;
 lean::cnstr_set_tag(x_84, 0);
}
lean::cnstr_set(x_97, 0, x_94);
x_5 = x_97;
x_6 = x_89;
goto lbl_7;
}
else
{
obj* x_99; obj* x_101; obj* x_102; obj* x_104; 
lean::dec(x_87);
x_99 = l_lean_ir_cpp_emit__case___main___closed__2;
lean::inc(x_1);
x_101 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_99, x_1, x_89);
x_102 = lean::cnstr_get(x_101, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_101, 1);
lean::inc(x_104);
lean::dec(x_101);
if (lean::obj_tag(x_102) == 0)
{
obj* x_109; obj* x_112; 
lean::dec(x_1);
lean::dec(x_0);
x_109 = lean::cnstr_get(x_102, 0);
lean::inc(x_109);
lean::dec(x_102);
if (lean::is_scalar(x_84)) {
 x_112 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_112 = x_84;
 lean::cnstr_set_tag(x_84, 0);
}
lean::cnstr_set(x_112, 0, x_109);
x_5 = x_112;
x_6 = x_104;
goto lbl_7;
}
else
{
obj* x_114; obj* x_116; obj* x_117; obj* x_119; 
lean::dec(x_102);
x_114 = l_lean_format_be___main___closed__1;
lean::inc(x_1);
x_116 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_114, x_1, x_104);
x_117 = lean::cnstr_get(x_116, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_116, 1);
lean::inc(x_119);
lean::dec(x_116);
if (lean::obj_tag(x_117) == 0)
{
obj* x_124; obj* x_127; 
lean::dec(x_1);
lean::dec(x_0);
x_124 = lean::cnstr_get(x_117, 0);
lean::inc(x_124);
lean::dec(x_117);
if (lean::is_scalar(x_84)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_84;
 lean::cnstr_set_tag(x_84, 0);
}
lean::cnstr_set(x_127, 0, x_124);
x_5 = x_127;
x_6 = x_119;
goto lbl_7;
}
else
{
lean::dec(x_117);
lean::dec(x_84);
if (x_21 == 0)
{
obj* x_132; 
lean::dec(x_1);
lean::dec(x_0);
x_132 = l_lean_ir_match__type___closed__5;
x_5 = x_132;
x_6 = x_119;
goto lbl_7;
}
else
{
obj* x_133; obj* x_134; obj* x_136; 
x_133 = l_lean_ir_cpp_emit__uncurry(x_0, x_1, x_119);
x_134 = lean::cnstr_get(x_133, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_133, 1);
lean::inc(x_136);
lean::dec(x_133);
x_5 = x_134;
x_6 = x_136;
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
obj* x_139; obj* x_141; obj* x_142; obj* x_145; uint8 x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; 
x_139 = lean::cnstr_get(x_5, 0);
lean::inc(x_139);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_141 = x_5;
} else {
 lean::dec(x_5);
 x_141 = lean::box(0);
}
x_142 = lean::cnstr_get(x_4, 0);
lean::inc(x_142);
lean::dec(x_4);
x_145 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_142);
x_146 = 0;
x_147 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_148 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_145);
lean::cnstr_set_scalar(x_148, sizeof(void*)*2, x_146);
x_149 = x_148;
x_150 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_151 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_151, 0, x_149);
lean::cnstr_set(x_151, 1, x_150);
lean::cnstr_set_scalar(x_151, sizeof(void*)*2, x_146);
x_152 = x_151;
x_153 = lean::box(1);
x_154 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_154, 0, x_152);
lean::cnstr_set(x_154, 1, x_153);
lean::cnstr_set_scalar(x_154, sizeof(void*)*2, x_146);
x_155 = x_154;
x_156 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_156, 0, x_155);
lean::cnstr_set(x_156, 1, x_139);
lean::cnstr_set_scalar(x_156, sizeof(void*)*2, x_146);
x_157 = x_156;
if (lean::is_scalar(x_141)) {
 x_158 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_158 = x_141;
}
lean::cnstr_set(x_158, 0, x_157);
x_159 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_159, 0, x_158);
lean::cnstr_set(x_159, 1, x_6);
return x_159;
}
else
{
obj* x_161; 
lean::dec(x_4);
x_161 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_161, 0, x_5);
lean::cnstr_set(x_161, 1, x_6);
return x_161;
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
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_14 = x_9;
} else {
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
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_3; 
x_3 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_2);
lean::cnstr_set(x_3, 3, x_0);
return x_3;
}
case 1:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; uint8 x_16; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 3);
lean::inc(x_10);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_12 = x_0;
} else {
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_20; uint8 x_21; 
lean::inc(x_1);
lean::inc(x_6);
x_20 = l_lean_name_quick__lt___main(x_6, x_1);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_25; 
lean::dec(x_8);
lean::dec(x_6);
if (lean::is_scalar(x_12)) {
 x_25 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_25 = x_12;
}
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_1);
lean::cnstr_set(x_25, 2, x_2);
lean::cnstr_set(x_25, 3, x_10);
return x_25;
}
else
{
obj* x_26; obj* x_27; 
x_26 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_10, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_4);
lean::cnstr_set(x_27, 1, x_6);
lean::cnstr_set(x_27, 2, x_8);
lean::cnstr_set(x_27, 3, x_26);
return x_27;
}
}
else
{
obj* x_28; obj* x_29; 
x_28 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_4, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_29 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_29 = x_12;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_6);
lean::cnstr_set(x_29, 2, x_8);
lean::cnstr_set(x_29, 3, x_10);
return x_29;
}
}
default:
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_41; uint8 x_42; 
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_0, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_0, 2);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_0, 3);
lean::inc(x_36);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_38 = x_0;
} else {
 lean::dec(x_0);
 x_38 = lean::box(0);
}
lean::inc(x_32);
lean::inc(x_1);
x_41 = l_lean_name_quick__lt___main(x_1, x_32);
x_42 = lean::unbox(x_41);
lean::dec(x_41);
if (x_42 == 0)
{
obj* x_46; uint8 x_47; 
lean::inc(x_1);
lean::inc(x_32);
x_46 = l_lean_name_quick__lt___main(x_32, x_1);
x_47 = lean::unbox(x_46);
lean::dec(x_46);
if (x_47 == 0)
{
obj* x_51; 
lean::dec(x_32);
lean::dec(x_34);
if (lean::is_scalar(x_38)) {
 x_51 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_51 = x_38;
}
lean::cnstr_set(x_51, 0, x_30);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_36);
return x_51;
}
else
{
uint8 x_53; 
lean::inc(x_36);
x_53 = l_rbnode_get__color___main___rarg(x_36);
if (x_53 == 0)
{
obj* x_55; obj* x_56; 
lean::dec(x_38);
x_55 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_36, x_1, x_2);
x_56 = l_rbnode_balance2__node___main___rarg(x_55, x_32, x_34, x_30);
return x_56;
}
else
{
obj* x_57; obj* x_58; 
x_57 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_36, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_58 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_58 = x_38;
}
lean::cnstr_set(x_58, 0, x_30);
lean::cnstr_set(x_58, 1, x_32);
lean::cnstr_set(x_58, 2, x_34);
lean::cnstr_set(x_58, 3, x_57);
return x_58;
}
}
}
else
{
uint8 x_60; 
lean::inc(x_30);
x_60 = l_rbnode_get__color___main___rarg(x_30);
if (x_60 == 0)
{
obj* x_62; obj* x_63; 
lean::dec(x_38);
x_62 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_30, x_1, x_2);
x_63 = l_rbnode_balance1__node___main___rarg(x_62, x_32, x_34, x_36);
return x_63;
}
else
{
obj* x_64; obj* x_65; 
x_64 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_30, x_1, x_2);
if (lean::is_scalar(x_38)) {
 x_65 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_65 = x_38;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_32);
lean::cnstr_set(x_65, 2, x_34);
lean::cnstr_set(x_65, 3, x_36);
return x_65;
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
return x_0;
}
else
{
obj* x_2; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
switch (lean::obj_tag(x_2)) {
case 5:
{
obj* x_7; obj* x_10; obj* x_11; 
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
obj* x_13; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::dec(x_2);
x_16 = lean::box(0);
x_17 = l_rbnode_insert___at_lean_ir_cpp_collect__used___spec__2(x_0, x_13, x_16);
x_0 = x_17;
x_1 = x_4;
goto _start;
}
default:
{
lean::dec(x_2);
x_1 = x_4;
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
obj* x_2; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_2);
x_1 = x_4;
goto _start;
}
else
{
obj* x_9; obj* x_12; 
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
x_12 = l_list_foldl___main___at_lean_ir_cpp_collect__used___spec__5(x_0, x_9);
x_0 = x_12;
x_1 = x_4;
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
switch (lean::obj_tag(x_1)) {
case 0:
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
case 1:
{
obj* x_9; obj* x_11; obj* x_13; obj* x_18; obj* x_19; obj* x_21; obj* x_23; 
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
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 x_23 = x_18;
} else {
 lean::dec(x_18);
 x_23 = lean::box(0);
}
if (lean::obj_tag(x_19) == 0)
{
obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
x_28 = lean::cnstr_get(x_19, 0);
lean::inc(x_28);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 x_30 = x_19;
} else {
 lean::dec(x_19);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
if (lean::is_scalar(x_23)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_23;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_21);
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_42; 
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 x_33 = x_19;
} else {
 lean::dec(x_19);
 x_33 = lean::box(0);
}
x_37 = lean::cnstr_get(x_0, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_37, 3);
lean::inc(x_39);
lean::inc(x_11);
x_42 = lean::apply_1(x_39, x_11);
if (lean::obj_tag(x_42) == 0)
{
obj* x_45; 
lean::dec(x_11);
lean::dec(x_37);
x_45 = l_lean_ir_match__type___closed__5;
x_34 = x_45;
x_35 = x_21;
goto lbl_36;
}
else
{
obj* x_46; obj* x_49; obj* x_52; 
x_46 = lean::cnstr_get(x_42, 0);
lean::inc(x_46);
lean::dec(x_42);
x_49 = lean::cnstr_get(x_37, 4);
lean::inc(x_49);
lean::dec(x_37);
x_52 = lean::apply_1(x_49, x_11);
if (lean::obj_tag(x_52) == 0)
{
obj* x_54; obj* x_56; uint8 x_57; obj* x_60; 
lean::inc(x_46);
x_54 = l_lean_ir_decl_header___main(x_46);
lean::inc(x_46);
x_56 = l_lean_ir_cpp_need__uncurry(x_46);
x_57 = lean::unbox(x_56);
lean::dec(x_56);
lean::inc(x_3);
x_60 = l_lean_ir_cpp_emit__header(x_54, x_3, x_21);
if (x_57 == 0)
{
obj* x_62; obj* x_64; 
lean::dec(x_46);
x_62 = lean::cnstr_get(x_60, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_60, 1);
lean::inc(x_64);
lean::dec(x_60);
if (lean::obj_tag(x_62) == 0)
{
obj* x_67; obj* x_69; obj* x_70; 
x_67 = lean::cnstr_get(x_62, 0);
lean::inc(x_67);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_69 = x_62;
} else {
 lean::dec(x_62);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_67);
x_34 = x_70;
x_35 = x_64;
goto lbl_36;
}
else
{
obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_71 = x_62;
} else {
 lean::dec(x_62);
 x_71 = lean::box(0);
}
x_72 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
x_74 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_72, x_3, x_64);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
lean::dec(x_74);
if (lean::obj_tag(x_75) == 0)
{
obj* x_80; obj* x_83; 
x_80 = lean::cnstr_get(x_75, 0);
lean::inc(x_80);
lean::dec(x_75);
if (lean::is_scalar(x_71)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_71;
 lean::cnstr_set_tag(x_71, 0);
}
lean::cnstr_set(x_83, 0, x_80);
x_34 = x_83;
x_35 = x_77;
goto lbl_36;
}
else
{
obj* x_86; 
lean::dec(x_71);
lean::dec(x_75);
x_86 = l_lean_ir_match__type___closed__5;
x_34 = x_86;
x_35 = x_77;
goto lbl_36;
}
}
}
else
{
obj* x_87; obj* x_89; 
x_87 = lean::cnstr_get(x_60, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_60, 1);
lean::inc(x_89);
lean::dec(x_60);
if (lean::obj_tag(x_87) == 0)
{
obj* x_93; obj* x_95; obj* x_96; 
lean::dec(x_46);
x_93 = lean::cnstr_get(x_87, 0);
lean::inc(x_93);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 x_95 = x_87;
} else {
 lean::dec(x_87);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_93);
x_34 = x_96;
x_35 = x_89;
goto lbl_36;
}
else
{
obj* x_97; obj* x_98; obj* x_100; obj* x_101; obj* x_103; 
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 x_97 = x_87;
} else {
 lean::dec(x_87);
 x_97 = lean::box(0);
}
x_98 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
x_100 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_98, x_3, x_89);
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
lean::dec(x_100);
if (lean::obj_tag(x_101) == 0)
{
obj* x_107; obj* x_110; 
lean::dec(x_46);
x_107 = lean::cnstr_get(x_101, 0);
lean::inc(x_107);
lean::dec(x_101);
if (lean::is_scalar(x_97)) {
 x_110 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_110 = x_97;
 lean::cnstr_set_tag(x_97, 0);
}
lean::cnstr_set(x_110, 0, x_107);
x_34 = x_110;
x_35 = x_103;
goto lbl_36;
}
else
{
obj* x_113; obj* x_114; obj* x_116; 
lean::dec(x_101);
lean::inc(x_3);
x_113 = l_lean_ir_cpp_emit__uncurry__header(x_46, x_3, x_103);
x_114 = lean::cnstr_get(x_113, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_113, 1);
lean::inc(x_116);
lean::dec(x_113);
if (lean::obj_tag(x_114) == 0)
{
obj* x_119; obj* x_122; 
x_119 = lean::cnstr_get(x_114, 0);
lean::inc(x_119);
lean::dec(x_114);
if (lean::is_scalar(x_97)) {
 x_122 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_122 = x_97;
 lean::cnstr_set_tag(x_97, 0);
}
lean::cnstr_set(x_122, 0, x_119);
x_34 = x_122;
x_35 = x_116;
goto lbl_36;
}
else
{
obj* x_126; obj* x_127; obj* x_129; 
lean::dec(x_114);
lean::dec(x_97);
lean::inc(x_3);
x_126 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_98, x_3, x_116);
x_127 = lean::cnstr_get(x_126, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_126, 1);
lean::inc(x_129);
lean::dec(x_126);
x_34 = x_127;
x_35 = x_129;
goto lbl_36;
}
}
}
}
}
else
{
obj* x_133; obj* x_135; obj* x_136; obj* x_138; 
lean::dec(x_52);
x_133 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2;
lean::inc(x_3);
x_135 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_133, x_3, x_21);
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_135, 1);
lean::inc(x_138);
lean::dec(x_135);
if (lean::obj_tag(x_136) == 0)
{
obj* x_142; obj* x_144; obj* x_145; 
lean::dec(x_46);
x_142 = lean::cnstr_get(x_136, 0);
lean::inc(x_142);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 x_144 = x_136;
} else {
 lean::dec(x_136);
 x_144 = lean::box(0);
}
if (lean::is_scalar(x_144)) {
 x_145 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_145 = x_144;
}
lean::cnstr_set(x_145, 0, x_142);
x_34 = x_145;
x_35 = x_138;
goto lbl_36;
}
else
{
obj* x_146; obj* x_148; obj* x_150; uint8 x_151; obj* x_154; 
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 x_146 = x_136;
} else {
 lean::dec(x_136);
 x_146 = lean::box(0);
}
lean::inc(x_46);
x_148 = l_lean_ir_decl_header___main(x_46);
lean::inc(x_46);
x_150 = l_lean_ir_cpp_need__uncurry(x_46);
x_151 = lean::unbox(x_150);
lean::dec(x_150);
lean::inc(x_3);
x_154 = l_lean_ir_cpp_emit__header(x_148, x_3, x_138);
if (x_151 == 0)
{
obj* x_156; obj* x_158; 
lean::dec(x_46);
x_156 = lean::cnstr_get(x_154, 0);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_154, 1);
lean::inc(x_158);
lean::dec(x_154);
if (lean::obj_tag(x_156) == 0)
{
obj* x_161; obj* x_164; 
x_161 = lean::cnstr_get(x_156, 0);
lean::inc(x_161);
lean::dec(x_156);
if (lean::is_scalar(x_146)) {
 x_164 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_164 = x_146;
 lean::cnstr_set_tag(x_146, 0);
}
lean::cnstr_set(x_164, 0, x_161);
x_34 = x_164;
x_35 = x_158;
goto lbl_36;
}
else
{
obj* x_166; obj* x_168; obj* x_169; obj* x_171; 
lean::dec(x_156);
x_166 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
x_168 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_166, x_3, x_158);
x_169 = lean::cnstr_get(x_168, 0);
lean::inc(x_169);
x_171 = lean::cnstr_get(x_168, 1);
lean::inc(x_171);
lean::dec(x_168);
if (lean::obj_tag(x_169) == 0)
{
obj* x_174; obj* x_177; 
x_174 = lean::cnstr_get(x_169, 0);
lean::inc(x_174);
lean::dec(x_169);
if (lean::is_scalar(x_146)) {
 x_177 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_177 = x_146;
 lean::cnstr_set_tag(x_146, 0);
}
lean::cnstr_set(x_177, 0, x_174);
x_34 = x_177;
x_35 = x_171;
goto lbl_36;
}
else
{
obj* x_180; 
lean::dec(x_169);
lean::dec(x_146);
x_180 = l_lean_ir_match__type___closed__5;
x_34 = x_180;
x_35 = x_171;
goto lbl_36;
}
}
}
else
{
obj* x_181; obj* x_183; 
x_181 = lean::cnstr_get(x_154, 0);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_154, 1);
lean::inc(x_183);
lean::dec(x_154);
if (lean::obj_tag(x_181) == 0)
{
obj* x_187; obj* x_190; 
lean::dec(x_46);
x_187 = lean::cnstr_get(x_181, 0);
lean::inc(x_187);
lean::dec(x_181);
if (lean::is_scalar(x_146)) {
 x_190 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_190 = x_146;
 lean::cnstr_set_tag(x_146, 0);
}
lean::cnstr_set(x_190, 0, x_187);
x_34 = x_190;
x_35 = x_183;
goto lbl_36;
}
else
{
obj* x_192; obj* x_194; obj* x_195; obj* x_197; 
lean::dec(x_181);
x_192 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
x_194 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_192, x_3, x_183);
x_195 = lean::cnstr_get(x_194, 0);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_194, 1);
lean::inc(x_197);
lean::dec(x_194);
if (lean::obj_tag(x_195) == 0)
{
obj* x_201; obj* x_204; 
lean::dec(x_46);
x_201 = lean::cnstr_get(x_195, 0);
lean::inc(x_201);
lean::dec(x_195);
if (lean::is_scalar(x_146)) {
 x_204 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_204 = x_146;
 lean::cnstr_set_tag(x_146, 0);
}
lean::cnstr_set(x_204, 0, x_201);
x_34 = x_204;
x_35 = x_197;
goto lbl_36;
}
else
{
obj* x_207; obj* x_208; obj* x_210; 
lean::dec(x_195);
lean::inc(x_3);
x_207 = l_lean_ir_cpp_emit__uncurry__header(x_46, x_3, x_197);
x_208 = lean::cnstr_get(x_207, 0);
lean::inc(x_208);
x_210 = lean::cnstr_get(x_207, 1);
lean::inc(x_210);
lean::dec(x_207);
if (lean::obj_tag(x_208) == 0)
{
obj* x_213; obj* x_216; 
x_213 = lean::cnstr_get(x_208, 0);
lean::inc(x_213);
lean::dec(x_208);
if (lean::is_scalar(x_146)) {
 x_216 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_216 = x_146;
 lean::cnstr_set_tag(x_146, 0);
}
lean::cnstr_set(x_216, 0, x_213);
x_34 = x_216;
x_35 = x_210;
goto lbl_36;
}
else
{
obj* x_220; obj* x_221; obj* x_223; 
lean::dec(x_146);
lean::dec(x_208);
lean::inc(x_3);
x_220 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_192, x_3, x_210);
x_221 = lean::cnstr_get(x_220, 0);
lean::inc(x_221);
x_223 = lean::cnstr_get(x_220, 1);
lean::inc(x_223);
lean::dec(x_220);
x_34 = x_221;
x_35 = x_223;
goto lbl_36;
}
}
}
}
}
}
}
lbl_36:
{
if (lean::obj_tag(x_34) == 0)
{
obj* x_229; obj* x_232; obj* x_233; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_229 = lean::cnstr_get(x_34, 0);
lean::inc(x_229);
lean::dec(x_34);
if (lean::is_scalar(x_33)) {
 x_232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_232 = x_33;
 lean::cnstr_set_tag(x_33, 0);
}
lean::cnstr_set(x_232, 0, x_229);
if (lean::is_scalar(x_23)) {
 x_233 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_233 = x_23;
}
lean::cnstr_set(x_233, 0, x_232);
lean::cnstr_set(x_233, 1, x_35);
return x_233;
}
else
{
obj* x_237; 
lean::dec(x_34);
lean::dec(x_23);
lean::dec(x_33);
x_237 = lean::box(0);
x_1 = x_13;
x_2 = x_237;
x_4 = x_35;
goto _start;
}
}
}
}
default:
{
obj* x_239; obj* x_241; obj* x_243; obj* x_248; obj* x_249; obj* x_251; obj* x_253; 
x_239 = lean::cnstr_get(x_1, 0);
lean::inc(x_239);
x_241 = lean::cnstr_get(x_1, 1);
lean::inc(x_241);
x_243 = lean::cnstr_get(x_1, 3);
lean::inc(x_243);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_0);
x_248 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1(x_0, x_239, x_2, x_3, x_4);
x_249 = lean::cnstr_get(x_248, 0);
lean::inc(x_249);
x_251 = lean::cnstr_get(x_248, 1);
lean::inc(x_251);
if (lean::is_exclusive(x_248)) {
 lean::cnstr_release(x_248, 0);
 lean::cnstr_release(x_248, 1);
 x_253 = x_248;
} else {
 lean::dec(x_248);
 x_253 = lean::box(0);
}
if (lean::obj_tag(x_249) == 0)
{
obj* x_258; obj* x_260; obj* x_261; obj* x_262; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_243);
lean::dec(x_241);
x_258 = lean::cnstr_get(x_249, 0);
lean::inc(x_258);
if (lean::is_exclusive(x_249)) {
 lean::cnstr_release(x_249, 0);
 x_260 = x_249;
} else {
 lean::dec(x_249);
 x_260 = lean::box(0);
}
if (lean::is_scalar(x_260)) {
 x_261 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_261 = x_260;
}
lean::cnstr_set(x_261, 0, x_258);
if (lean::is_scalar(x_253)) {
 x_262 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_262 = x_253;
}
lean::cnstr_set(x_262, 0, x_261);
lean::cnstr_set(x_262, 1, x_251);
return x_262;
}
else
{
obj* x_263; obj* x_264; obj* x_265; obj* x_267; obj* x_269; obj* x_272; 
if (lean::is_exclusive(x_249)) {
 lean::cnstr_release(x_249, 0);
 x_263 = x_249;
} else {
 lean::dec(x_249);
 x_263 = lean::box(0);
}
x_267 = lean::cnstr_get(x_0, 0);
lean::inc(x_267);
x_269 = lean::cnstr_get(x_267, 3);
lean::inc(x_269);
lean::inc(x_241);
x_272 = lean::apply_1(x_269, x_241);
if (lean::obj_tag(x_272) == 0)
{
obj* x_275; 
lean::dec(x_241);
lean::dec(x_267);
x_275 = l_lean_ir_match__type___closed__5;
x_264 = x_275;
x_265 = x_251;
goto lbl_266;
}
else
{
obj* x_276; obj* x_279; obj* x_282; 
x_276 = lean::cnstr_get(x_272, 0);
lean::inc(x_276);
lean::dec(x_272);
x_279 = lean::cnstr_get(x_267, 4);
lean::inc(x_279);
lean::dec(x_267);
x_282 = lean::apply_1(x_279, x_241);
if (lean::obj_tag(x_282) == 0)
{
obj* x_284; obj* x_286; uint8 x_287; obj* x_290; 
lean::inc(x_276);
x_284 = l_lean_ir_decl_header___main(x_276);
lean::inc(x_276);
x_286 = l_lean_ir_cpp_need__uncurry(x_276);
x_287 = lean::unbox(x_286);
lean::dec(x_286);
lean::inc(x_3);
x_290 = l_lean_ir_cpp_emit__header(x_284, x_3, x_251);
if (x_287 == 0)
{
obj* x_292; obj* x_294; 
lean::dec(x_276);
x_292 = lean::cnstr_get(x_290, 0);
lean::inc(x_292);
x_294 = lean::cnstr_get(x_290, 1);
lean::inc(x_294);
lean::dec(x_290);
if (lean::obj_tag(x_292) == 0)
{
obj* x_297; obj* x_299; obj* x_300; 
x_297 = lean::cnstr_get(x_292, 0);
lean::inc(x_297);
if (lean::is_exclusive(x_292)) {
 lean::cnstr_release(x_292, 0);
 x_299 = x_292;
} else {
 lean::dec(x_292);
 x_299 = lean::box(0);
}
if (lean::is_scalar(x_299)) {
 x_300 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_300 = x_299;
}
lean::cnstr_set(x_300, 0, x_297);
x_264 = x_300;
x_265 = x_294;
goto lbl_266;
}
else
{
obj* x_301; obj* x_302; obj* x_304; obj* x_305; obj* x_307; 
if (lean::is_exclusive(x_292)) {
 lean::cnstr_release(x_292, 0);
 x_301 = x_292;
} else {
 lean::dec(x_292);
 x_301 = lean::box(0);
}
x_302 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
x_304 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_302, x_3, x_294);
x_305 = lean::cnstr_get(x_304, 0);
lean::inc(x_305);
x_307 = lean::cnstr_get(x_304, 1);
lean::inc(x_307);
lean::dec(x_304);
if (lean::obj_tag(x_305) == 0)
{
obj* x_310; obj* x_313; 
x_310 = lean::cnstr_get(x_305, 0);
lean::inc(x_310);
lean::dec(x_305);
if (lean::is_scalar(x_301)) {
 x_313 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_313 = x_301;
 lean::cnstr_set_tag(x_301, 0);
}
lean::cnstr_set(x_313, 0, x_310);
x_264 = x_313;
x_265 = x_307;
goto lbl_266;
}
else
{
obj* x_316; 
lean::dec(x_301);
lean::dec(x_305);
x_316 = l_lean_ir_match__type___closed__5;
x_264 = x_316;
x_265 = x_307;
goto lbl_266;
}
}
}
else
{
obj* x_317; obj* x_319; 
x_317 = lean::cnstr_get(x_290, 0);
lean::inc(x_317);
x_319 = lean::cnstr_get(x_290, 1);
lean::inc(x_319);
lean::dec(x_290);
if (lean::obj_tag(x_317) == 0)
{
obj* x_323; obj* x_325; obj* x_326; 
lean::dec(x_276);
x_323 = lean::cnstr_get(x_317, 0);
lean::inc(x_323);
if (lean::is_exclusive(x_317)) {
 lean::cnstr_release(x_317, 0);
 x_325 = x_317;
} else {
 lean::dec(x_317);
 x_325 = lean::box(0);
}
if (lean::is_scalar(x_325)) {
 x_326 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_326 = x_325;
}
lean::cnstr_set(x_326, 0, x_323);
x_264 = x_326;
x_265 = x_319;
goto lbl_266;
}
else
{
obj* x_327; obj* x_328; obj* x_330; obj* x_331; obj* x_333; 
if (lean::is_exclusive(x_317)) {
 lean::cnstr_release(x_317, 0);
 x_327 = x_317;
} else {
 lean::dec(x_317);
 x_327 = lean::box(0);
}
x_328 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
x_330 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_328, x_3, x_319);
x_331 = lean::cnstr_get(x_330, 0);
lean::inc(x_331);
x_333 = lean::cnstr_get(x_330, 1);
lean::inc(x_333);
lean::dec(x_330);
if (lean::obj_tag(x_331) == 0)
{
obj* x_337; obj* x_340; 
lean::dec(x_276);
x_337 = lean::cnstr_get(x_331, 0);
lean::inc(x_337);
lean::dec(x_331);
if (lean::is_scalar(x_327)) {
 x_340 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_340 = x_327;
 lean::cnstr_set_tag(x_327, 0);
}
lean::cnstr_set(x_340, 0, x_337);
x_264 = x_340;
x_265 = x_333;
goto lbl_266;
}
else
{
obj* x_343; obj* x_344; obj* x_346; 
lean::dec(x_331);
lean::inc(x_3);
x_343 = l_lean_ir_cpp_emit__uncurry__header(x_276, x_3, x_333);
x_344 = lean::cnstr_get(x_343, 0);
lean::inc(x_344);
x_346 = lean::cnstr_get(x_343, 1);
lean::inc(x_346);
lean::dec(x_343);
if (lean::obj_tag(x_344) == 0)
{
obj* x_349; obj* x_352; 
x_349 = lean::cnstr_get(x_344, 0);
lean::inc(x_349);
lean::dec(x_344);
if (lean::is_scalar(x_327)) {
 x_352 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_352 = x_327;
 lean::cnstr_set_tag(x_327, 0);
}
lean::cnstr_set(x_352, 0, x_349);
x_264 = x_352;
x_265 = x_346;
goto lbl_266;
}
else
{
obj* x_356; obj* x_357; obj* x_359; 
lean::dec(x_344);
lean::dec(x_327);
lean::inc(x_3);
x_356 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_328, x_3, x_346);
x_357 = lean::cnstr_get(x_356, 0);
lean::inc(x_357);
x_359 = lean::cnstr_get(x_356, 1);
lean::inc(x_359);
lean::dec(x_356);
x_264 = x_357;
x_265 = x_359;
goto lbl_266;
}
}
}
}
}
else
{
obj* x_363; obj* x_365; obj* x_366; obj* x_368; 
lean::dec(x_282);
x_363 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2;
lean::inc(x_3);
x_365 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_363, x_3, x_251);
x_366 = lean::cnstr_get(x_365, 0);
lean::inc(x_366);
x_368 = lean::cnstr_get(x_365, 1);
lean::inc(x_368);
lean::dec(x_365);
if (lean::obj_tag(x_366) == 0)
{
obj* x_372; obj* x_374; obj* x_375; 
lean::dec(x_276);
x_372 = lean::cnstr_get(x_366, 0);
lean::inc(x_372);
if (lean::is_exclusive(x_366)) {
 lean::cnstr_release(x_366, 0);
 x_374 = x_366;
} else {
 lean::dec(x_366);
 x_374 = lean::box(0);
}
if (lean::is_scalar(x_374)) {
 x_375 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_375 = x_374;
}
lean::cnstr_set(x_375, 0, x_372);
x_264 = x_375;
x_265 = x_368;
goto lbl_266;
}
else
{
obj* x_376; obj* x_378; obj* x_380; uint8 x_381; obj* x_384; 
if (lean::is_exclusive(x_366)) {
 lean::cnstr_release(x_366, 0);
 x_376 = x_366;
} else {
 lean::dec(x_366);
 x_376 = lean::box(0);
}
lean::inc(x_276);
x_378 = l_lean_ir_decl_header___main(x_276);
lean::inc(x_276);
x_380 = l_lean_ir_cpp_need__uncurry(x_276);
x_381 = lean::unbox(x_380);
lean::dec(x_380);
lean::inc(x_3);
x_384 = l_lean_ir_cpp_emit__header(x_378, x_3, x_368);
if (x_381 == 0)
{
obj* x_386; obj* x_388; 
lean::dec(x_276);
x_386 = lean::cnstr_get(x_384, 0);
lean::inc(x_386);
x_388 = lean::cnstr_get(x_384, 1);
lean::inc(x_388);
lean::dec(x_384);
if (lean::obj_tag(x_386) == 0)
{
obj* x_391; obj* x_394; 
x_391 = lean::cnstr_get(x_386, 0);
lean::inc(x_391);
lean::dec(x_386);
if (lean::is_scalar(x_376)) {
 x_394 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_394 = x_376;
 lean::cnstr_set_tag(x_376, 0);
}
lean::cnstr_set(x_394, 0, x_391);
x_264 = x_394;
x_265 = x_388;
goto lbl_266;
}
else
{
obj* x_396; obj* x_398; obj* x_399; obj* x_401; 
lean::dec(x_386);
x_396 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
x_398 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_396, x_3, x_388);
x_399 = lean::cnstr_get(x_398, 0);
lean::inc(x_399);
x_401 = lean::cnstr_get(x_398, 1);
lean::inc(x_401);
lean::dec(x_398);
if (lean::obj_tag(x_399) == 0)
{
obj* x_404; obj* x_407; 
x_404 = lean::cnstr_get(x_399, 0);
lean::inc(x_404);
lean::dec(x_399);
if (lean::is_scalar(x_376)) {
 x_407 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_407 = x_376;
 lean::cnstr_set_tag(x_376, 0);
}
lean::cnstr_set(x_407, 0, x_404);
x_264 = x_407;
x_265 = x_401;
goto lbl_266;
}
else
{
obj* x_410; 
lean::dec(x_376);
lean::dec(x_399);
x_410 = l_lean_ir_match__type___closed__5;
x_264 = x_410;
x_265 = x_401;
goto lbl_266;
}
}
}
else
{
obj* x_411; obj* x_413; 
x_411 = lean::cnstr_get(x_384, 0);
lean::inc(x_411);
x_413 = lean::cnstr_get(x_384, 1);
lean::inc(x_413);
lean::dec(x_384);
if (lean::obj_tag(x_411) == 0)
{
obj* x_417; obj* x_420; 
lean::dec(x_276);
x_417 = lean::cnstr_get(x_411, 0);
lean::inc(x_417);
lean::dec(x_411);
if (lean::is_scalar(x_376)) {
 x_420 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_420 = x_376;
 lean::cnstr_set_tag(x_376, 0);
}
lean::cnstr_set(x_420, 0, x_417);
x_264 = x_420;
x_265 = x_413;
goto lbl_266;
}
else
{
obj* x_422; obj* x_424; obj* x_425; obj* x_427; 
lean::dec(x_411);
x_422 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
x_424 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_422, x_3, x_413);
x_425 = lean::cnstr_get(x_424, 0);
lean::inc(x_425);
x_427 = lean::cnstr_get(x_424, 1);
lean::inc(x_427);
lean::dec(x_424);
if (lean::obj_tag(x_425) == 0)
{
obj* x_431; obj* x_434; 
lean::dec(x_276);
x_431 = lean::cnstr_get(x_425, 0);
lean::inc(x_431);
lean::dec(x_425);
if (lean::is_scalar(x_376)) {
 x_434 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_434 = x_376;
 lean::cnstr_set_tag(x_376, 0);
}
lean::cnstr_set(x_434, 0, x_431);
x_264 = x_434;
x_265 = x_427;
goto lbl_266;
}
else
{
obj* x_437; obj* x_438; obj* x_440; 
lean::dec(x_425);
lean::inc(x_3);
x_437 = l_lean_ir_cpp_emit__uncurry__header(x_276, x_3, x_427);
x_438 = lean::cnstr_get(x_437, 0);
lean::inc(x_438);
x_440 = lean::cnstr_get(x_437, 1);
lean::inc(x_440);
lean::dec(x_437);
if (lean::obj_tag(x_438) == 0)
{
obj* x_443; obj* x_446; 
x_443 = lean::cnstr_get(x_438, 0);
lean::inc(x_443);
lean::dec(x_438);
if (lean::is_scalar(x_376)) {
 x_446 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_446 = x_376;
 lean::cnstr_set_tag(x_376, 0);
}
lean::cnstr_set(x_446, 0, x_443);
x_264 = x_446;
x_265 = x_440;
goto lbl_266;
}
else
{
obj* x_450; obj* x_451; obj* x_453; 
lean::dec(x_438);
lean::dec(x_376);
lean::inc(x_3);
x_450 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_422, x_3, x_440);
x_451 = lean::cnstr_get(x_450, 0);
lean::inc(x_451);
x_453 = lean::cnstr_get(x_450, 1);
lean::inc(x_453);
lean::dec(x_450);
x_264 = x_451;
x_265 = x_453;
goto lbl_266;
}
}
}
}
}
}
}
lbl_266:
{
if (lean::obj_tag(x_264) == 0)
{
obj* x_459; obj* x_462; obj* x_463; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_243);
x_459 = lean::cnstr_get(x_264, 0);
lean::inc(x_459);
lean::dec(x_264);
if (lean::is_scalar(x_263)) {
 x_462 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_462 = x_263;
 lean::cnstr_set_tag(x_263, 0);
}
lean::cnstr_set(x_462, 0, x_459);
if (lean::is_scalar(x_253)) {
 x_463 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_463 = x_253;
}
lean::cnstr_set(x_463, 0, x_462);
lean::cnstr_set(x_463, 1, x_265);
return x_463;
}
else
{
obj* x_467; 
lean::dec(x_264);
lean::dec(x_263);
lean::dec(x_253);
x_467 = lean::box(0);
x_1 = x_243;
x_2 = x_467;
x_4 = x_265;
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
obj* x_6; obj* x_8; obj* x_11; uint8 x_12; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_lean_ir_decl_header___main(x_6);
x_12 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*3);
if (x_12 == 0)
{
lean::dec(x_11);
x_0 = x_8;
goto _start;
}
else
{
obj* x_15; uint8 x_17; obj* x_20; obj* x_21; obj* x_23; obj* x_25; 
x_15 = lean::cnstr_get(x_11, 2);
lean::inc(x_15);
x_17 = lean::unbox(x_15);
lean::dec(x_15);
lean::inc(x_1);
x_20 = l_lean_ir_cpp_emit__type(x_17, x_1, x_2);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_release(x_20, 1);
 x_25 = x_20;
} else {
 lean::dec(x_20);
 x_25 = lean::box(0);
}
if (lean::obj_tag(x_21) == 0)
{
obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_11);
lean::dec(x_8);
lean::dec(x_1);
x_29 = lean::cnstr_get(x_21, 0);
lean::inc(x_29);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_31 = x_21;
} else {
 lean::dec(x_21);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_25)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_25;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_23);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_40; 
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_34 = x_21;
} else {
 lean::dec(x_21);
 x_34 = lean::box(0);
}
x_35 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_1);
x_37 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_35, x_1, x_23);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_46; obj* x_49; obj* x_50; 
lean::dec(x_11);
lean::dec(x_8);
lean::dec(x_1);
x_46 = lean::cnstr_get(x_38, 0);
lean::inc(x_46);
lean::dec(x_38);
if (lean::is_scalar(x_34)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_34;
 lean::cnstr_set_tag(x_34, 0);
}
lean::cnstr_set(x_49, 0, x_46);
if (lean::is_scalar(x_25)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_25;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_40);
return x_50;
}
else
{
obj* x_52; obj* x_56; obj* x_57; obj* x_59; 
lean::dec(x_38);
x_52 = lean::cnstr_get(x_11, 0);
lean::inc(x_52);
lean::dec(x_11);
lean::inc(x_1);
x_56 = l_lean_ir_cpp_emit__global(x_52, x_1, x_40);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
if (lean::obj_tag(x_57) == 0)
{
obj* x_64; obj* x_67; obj* x_68; 
lean::dec(x_8);
lean::dec(x_1);
x_64 = lean::cnstr_get(x_57, 0);
lean::inc(x_64);
lean::dec(x_57);
if (lean::is_scalar(x_34)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_34;
 lean::cnstr_set_tag(x_34, 0);
}
lean::cnstr_set(x_67, 0, x_64);
if (lean::is_scalar(x_25)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_25;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_59);
return x_68;
}
else
{
obj* x_70; obj* x_72; obj* x_73; obj* x_75; 
lean::dec(x_57);
x_70 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_1);
x_72 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_70, x_1, x_59);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
lean::dec(x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_80; obj* x_83; obj* x_84; 
lean::dec(x_8);
lean::dec(x_1);
x_80 = lean::cnstr_get(x_73, 0);
lean::inc(x_80);
lean::dec(x_73);
if (lean::is_scalar(x_34)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_34;
 lean::cnstr_set_tag(x_34, 0);
}
lean::cnstr_set(x_83, 0, x_80);
if (lean::is_scalar(x_25)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_25;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_75);
return x_84;
}
else
{
lean::dec(x_73);
lean::dec(x_34);
lean::dec(x_25);
x_0 = x_8;
x_2 = x_75;
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
obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_lean_ir_cpp_initialize__prefix;
lean::inc(x_1);
x_13 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_11, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
} else {
 lean::dec(x_13);
 x_18 = lean::box(0);
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_6);
lean::dec(x_8);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_24 = x_14;
} else {
 lean::dec(x_14);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_18)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_18;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_16);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; 
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_27 = x_14;
} else {
 lean::dec(x_14);
 x_27 = lean::box(0);
}
lean::inc(x_1);
x_29 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_6, x_1, x_16);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_37; obj* x_40; obj* x_41; 
lean::dec(x_8);
lean::dec(x_1);
x_37 = lean::cnstr_get(x_30, 0);
lean::inc(x_37);
lean::dec(x_30);
if (lean::is_scalar(x_27)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_27;
 lean::cnstr_set_tag(x_27, 0);
}
lean::cnstr_set(x_40, 0, x_37);
if (lean::is_scalar(x_18)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_18;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_32);
return x_41;
}
else
{
obj* x_43; obj* x_45; obj* x_46; obj* x_48; 
lean::dec(x_30);
x_43 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_1);
x_45 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_43, x_1, x_32);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
if (lean::obj_tag(x_46) == 0)
{
obj* x_53; obj* x_56; obj* x_57; 
lean::dec(x_8);
lean::dec(x_1);
x_53 = lean::cnstr_get(x_46, 0);
lean::inc(x_53);
lean::dec(x_46);
if (lean::is_scalar(x_27)) {
 x_56 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_56 = x_27;
 lean::cnstr_set_tag(x_27, 0);
}
lean::cnstr_set(x_56, 0, x_53);
if (lean::is_scalar(x_18)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_18;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_48);
return x_57;
}
else
{
lean::dec(x_18);
lean::dec(x_27);
lean::dec(x_46);
x_0 = x_8;
x_2 = x_48;
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
obj* x_6; obj* x_8; obj* x_11; uint8 x_12; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_lean_ir_decl_header___main(x_6);
x_12 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*3);
if (x_12 == 0)
{
lean::dec(x_11);
x_0 = x_8;
goto _start;
}
else
{
obj* x_15; obj* x_20; obj* x_21; obj* x_23; obj* x_25; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
lean::dec(x_11);
lean::inc(x_1);
lean::inc(x_15);
x_20 = l_lean_ir_cpp_emit__global(x_15, x_1, x_2);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_release(x_20, 1);
 x_25 = x_20;
} else {
 lean::dec(x_20);
 x_25 = lean::box(0);
}
if (lean::obj_tag(x_21) == 0)
{
obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_15);
lean::dec(x_8);
lean::dec(x_1);
x_29 = lean::cnstr_get(x_21, 0);
lean::inc(x_29);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_31 = x_21;
} else {
 lean::dec(x_21);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_25)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_25;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_23);
return x_33;
}
else
{
obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_40; 
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 0);
 x_34 = x_21;
} else {
 lean::dec(x_21);
 x_34 = lean::box(0);
}
x_35 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_1);
x_37 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_35, x_1, x_23);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_46; obj* x_49; obj* x_50; 
lean::dec(x_15);
lean::dec(x_8);
lean::dec(x_1);
x_46 = lean::cnstr_get(x_38, 0);
lean::inc(x_46);
lean::dec(x_38);
if (lean::is_scalar(x_34)) {
 x_49 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_49 = x_34;
 lean::cnstr_set_tag(x_34, 0);
}
lean::cnstr_set(x_49, 0, x_46);
if (lean::is_scalar(x_25)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_25;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_40);
return x_50;
}
else
{
obj* x_53; obj* x_54; obj* x_56; 
lean::dec(x_38);
lean::inc(x_1);
x_53 = l_lean_ir_cpp_emit__fnid(x_15, x_1, x_40);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
lean::dec(x_53);
if (lean::obj_tag(x_54) == 0)
{
obj* x_61; obj* x_64; obj* x_65; 
lean::dec(x_8);
lean::dec(x_1);
x_61 = lean::cnstr_get(x_54, 0);
lean::inc(x_61);
lean::dec(x_54);
if (lean::is_scalar(x_34)) {
 x_64 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_64 = x_34;
 lean::cnstr_set_tag(x_34, 0);
}
lean::cnstr_set(x_64, 0, x_61);
if (lean::is_scalar(x_25)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_25;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_56);
return x_65;
}
else
{
obj* x_67; obj* x_69; obj* x_70; obj* x_72; 
lean::dec(x_54);
x_67 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_1);
x_69 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_67, x_1, x_56);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
lean::dec(x_69);
if (lean::obj_tag(x_70) == 0)
{
obj* x_77; obj* x_80; obj* x_81; 
lean::dec(x_8);
lean::dec(x_1);
x_77 = lean::cnstr_get(x_70, 0);
lean::inc(x_77);
lean::dec(x_70);
if (lean::is_scalar(x_34)) {
 x_80 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_80 = x_34;
 lean::cnstr_set_tag(x_34, 0);
}
lean::cnstr_set(x_80, 0, x_77);
if (lean::is_scalar(x_25)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_25;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_72);
return x_81;
}
else
{
lean::dec(x_70);
lean::dec(x_34);
lean::dec(x_25);
x_0 = x_8;
x_2 = x_72;
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
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_3 = l_lean_ir_cpp_emit__initialize__proc___closed__1;
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
} else {
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
} else {
 lean::dec(x_6);
 x_15 = lean::box(0);
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
obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
} else {
 lean::dec(x_6);
 x_18 = lean::box(0);
}
x_19 = l_lean_ir_cpp_initialize__prefix;
lean::inc(x_1);
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_1, x_8);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_29; obj* x_32; obj* x_33; 
lean::dec(x_1);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
lean::dec(x_22);
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_10)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_10;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_24);
return x_33;
}
else
{
obj* x_35; obj* x_37; obj* x_40; obj* x_41; obj* x_43; 
lean::dec(x_22);
x_35 = lean::cnstr_get(x_1, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_35, 0);
lean::inc(x_37);
lean::inc(x_1);
x_40 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_37, x_1, x_24);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_49; obj* x_52; obj* x_53; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_35);
x_49 = lean::cnstr_get(x_41, 0);
lean::inc(x_49);
lean::dec(x_41);
if (lean::is_scalar(x_18)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_52, 0, x_49);
if (lean::is_scalar(x_10)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_10;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_43);
return x_53;
}
else
{
obj* x_55; obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_41);
x_55 = l_lean_ir_cpp_emit__initialize__proc___closed__2;
lean::inc(x_1);
x_57 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_55, x_1, x_43);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_66; obj* x_69; obj* x_70; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_35);
x_66 = lean::cnstr_get(x_58, 0);
lean::inc(x_66);
lean::dec(x_58);
if (lean::is_scalar(x_18)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_69, 0, x_66);
if (lean::is_scalar(x_10)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_10;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_60);
return x_70;
}
else
{
obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
lean::dec(x_58);
x_72 = l_lean_ir_cpp_emit__initialize__proc___closed__3;
lean::inc(x_1);
x_74 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_72, x_1, x_60);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
lean::dec(x_74);
if (lean::obj_tag(x_75) == 0)
{
obj* x_83; obj* x_86; obj* x_87; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_35);
x_83 = lean::cnstr_get(x_75, 0);
lean::inc(x_83);
lean::dec(x_75);
if (lean::is_scalar(x_18)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_86, 0, x_83);
if (lean::is_scalar(x_10)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_10;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_77);
return x_87;
}
else
{
obj* x_89; obj* x_91; obj* x_92; obj* x_94; 
lean::dec(x_75);
x_89 = l_lean_ir_cpp_emit__initialize__proc___closed__4;
lean::inc(x_1);
x_91 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_89, x_1, x_77);
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_91, 1);
lean::inc(x_94);
lean::dec(x_91);
if (lean::obj_tag(x_92) == 0)
{
obj* x_100; obj* x_103; obj* x_104; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_35);
x_100 = lean::cnstr_get(x_92, 0);
lean::inc(x_100);
lean::dec(x_92);
if (lean::is_scalar(x_18)) {
 x_103 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_103 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_103, 0, x_100);
if (lean::is_scalar(x_10)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_10;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_94);
return x_104;
}
else
{
obj* x_106; obj* x_110; obj* x_111; obj* x_113; 
lean::dec(x_92);
x_106 = lean::cnstr_get(x_35, 1);
lean::inc(x_106);
lean::dec(x_35);
lean::inc(x_1);
x_110 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1(x_106, x_1, x_94);
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_110, 1);
lean::inc(x_113);
lean::dec(x_110);
if (lean::obj_tag(x_111) == 0)
{
obj* x_118; obj* x_121; obj* x_122; 
lean::dec(x_1);
lean::dec(x_0);
x_118 = lean::cnstr_get(x_111, 0);
lean::inc(x_118);
lean::dec(x_111);
if (lean::is_scalar(x_18)) {
 x_121 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_121 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_121, 0, x_118);
if (lean::is_scalar(x_10)) {
 x_122 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_122 = x_10;
}
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_113);
return x_122;
}
else
{
obj* x_125; obj* x_126; obj* x_128; 
lean::dec(x_111);
lean::inc(x_1);
x_125 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__2(x_0, x_1, x_113);
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_125, 1);
lean::inc(x_128);
lean::dec(x_125);
if (lean::obj_tag(x_126) == 0)
{
obj* x_132; obj* x_135; obj* x_136; 
lean::dec(x_1);
x_132 = lean::cnstr_get(x_126, 0);
lean::inc(x_132);
lean::dec(x_126);
if (lean::is_scalar(x_18)) {
 x_135 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_135 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_135, 0, x_132);
if (lean::is_scalar(x_10)) {
 x_136 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_136 = x_10;
}
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_128);
return x_136;
}
else
{
obj* x_140; obj* x_141; 
lean::dec(x_10);
lean::dec(x_18);
lean::dec(x_126);
x_140 = l_lean_ir_cpp_emit__uncurry___closed__1;
x_141 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_140, x_1, x_128);
return x_141;
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
obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_11 = l_lean_ir_cpp_finalize__prefix;
lean::inc(x_1);
x_13 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_11, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
} else {
 lean::dec(x_13);
 x_18 = lean::box(0);
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_6);
lean::dec(x_8);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_24 = x_14;
} else {
 lean::dec(x_14);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
if (lean::is_scalar(x_18)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_18;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_16);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; 
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_27 = x_14;
} else {
 lean::dec(x_14);
 x_27 = lean::box(0);
}
lean::inc(x_1);
x_29 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_6, x_1, x_16);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_37; obj* x_40; obj* x_41; 
lean::dec(x_8);
lean::dec(x_1);
x_37 = lean::cnstr_get(x_30, 0);
lean::inc(x_37);
lean::dec(x_30);
if (lean::is_scalar(x_27)) {
 x_40 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_40 = x_27;
 lean::cnstr_set_tag(x_27, 0);
}
lean::cnstr_set(x_40, 0, x_37);
if (lean::is_scalar(x_18)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_18;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_32);
return x_41;
}
else
{
obj* x_43; obj* x_45; obj* x_46; obj* x_48; 
lean::dec(x_30);
x_43 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_1);
x_45 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_43, x_1, x_32);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
if (lean::obj_tag(x_46) == 0)
{
obj* x_53; obj* x_56; obj* x_57; 
lean::dec(x_8);
lean::dec(x_1);
x_53 = lean::cnstr_get(x_46, 0);
lean::inc(x_53);
lean::dec(x_46);
if (lean::is_scalar(x_27)) {
 x_56 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_56 = x_27;
 lean::cnstr_set_tag(x_27, 0);
}
lean::cnstr_set(x_56, 0, x_53);
if (lean::is_scalar(x_18)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_18;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_48);
return x_57;
}
else
{
lean::dec(x_18);
lean::dec(x_27);
lean::dec(x_46);
x_0 = x_8;
x_2 = x_48;
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
obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_14; obj* x_15; uint8 x_17; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
x_14 = l_lean_ir_decl_header___main(x_6);
x_17 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*3);
if (x_17 == 0)
{
if (x_17 == 0)
{
obj* x_19; 
lean::dec(x_14);
x_19 = l_lean_ir_match__type___closed__5;
x_11 = x_19;
x_12 = x_2;
goto lbl_13;
}
else
{
obj* x_20; 
x_20 = lean::box(0);
x_15 = x_20;
goto lbl_16;
}
}
else
{
obj* x_21; uint8 x_23; obj* x_25; obj* x_26; uint8 x_27; 
x_21 = lean::cnstr_get(x_14, 2);
lean::inc(x_21);
x_23 = lean::unbox(x_21);
lean::dec(x_21);
x_25 = l_lean_ir_type2id___main(x_23);
x_26 = l_lean_ir_valid__assign__unop__types___closed__1;
x_27 = lean::nat_dec_eq(x_25, x_26);
lean::dec(x_25);
if (x_27 == 0)
{
obj* x_30; 
lean::dec(x_14);
x_30 = l_lean_ir_match__type___closed__5;
x_11 = x_30;
x_12 = x_2;
goto lbl_13;
}
else
{
if (x_17 == 0)
{
obj* x_32; 
lean::dec(x_14);
x_32 = l_lean_ir_match__type___closed__5;
x_11 = x_32;
x_12 = x_2;
goto lbl_13;
}
else
{
obj* x_33; 
x_33 = lean::box(0);
x_15 = x_33;
goto lbl_16;
}
}
}
lbl_13:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_36; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_8);
lean::dec(x_1);
x_36 = lean::cnstr_get(x_11, 0);
lean::inc(x_36);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_38 = x_11;
} else {
 lean::dec(x_11);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_12);
return x_40;
}
else
{
lean::dec(x_11);
x_0 = x_8;
x_2 = x_12;
goto _start;
}
}
lbl_16:
{
obj* x_44; obj* x_46; obj* x_47; obj* x_49; 
lean::dec(x_15);
x_44 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__1;
lean::inc(x_1);
x_46 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_44, x_1, x_2);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_53; obj* x_55; obj* x_56; 
lean::dec(x_14);
x_53 = lean::cnstr_get(x_47, 0);
lean::inc(x_53);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_55 = x_47;
} else {
 lean::dec(x_47);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
x_11 = x_56;
x_12 = x_49;
goto lbl_13;
}
else
{
obj* x_57; obj* x_58; obj* x_63; obj* x_64; obj* x_66; 
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_57 = x_47;
} else {
 lean::dec(x_47);
 x_57 = lean::box(0);
}
x_58 = lean::cnstr_get(x_14, 0);
lean::inc(x_58);
lean::dec(x_14);
lean::inc(x_1);
lean::inc(x_58);
x_63 = l_lean_ir_cpp_emit__global(x_58, x_1, x_49);
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_63, 1);
lean::inc(x_66);
lean::dec(x_63);
if (lean::obj_tag(x_64) == 0)
{
obj* x_70; obj* x_73; 
lean::dec(x_58);
x_70 = lean::cnstr_get(x_64, 0);
lean::inc(x_70);
lean::dec(x_64);
if (lean::is_scalar(x_57)) {
 x_73 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_73 = x_57;
 lean::cnstr_set_tag(x_57, 0);
}
lean::cnstr_set(x_73, 0, x_70);
x_11 = x_73;
x_12 = x_66;
goto lbl_13;
}
else
{
obj* x_75; obj* x_77; obj* x_78; obj* x_80; 
lean::dec(x_64);
x_75 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__2;
lean::inc(x_1);
x_77 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_75, x_1, x_66);
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_77, 1);
lean::inc(x_80);
lean::dec(x_77);
if (lean::obj_tag(x_78) == 0)
{
obj* x_84; obj* x_87; 
lean::dec(x_58);
x_84 = lean::cnstr_get(x_78, 0);
lean::inc(x_84);
lean::dec(x_78);
if (lean::is_scalar(x_57)) {
 x_87 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_87 = x_57;
 lean::cnstr_set_tag(x_57, 0);
}
lean::cnstr_set(x_87, 0, x_84);
x_11 = x_87;
x_12 = x_80;
goto lbl_13;
}
else
{
obj* x_90; obj* x_91; obj* x_93; 
lean::dec(x_78);
lean::inc(x_1);
x_90 = l_lean_ir_cpp_emit__global(x_58, x_1, x_80);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
if (lean::obj_tag(x_91) == 0)
{
obj* x_96; obj* x_99; 
x_96 = lean::cnstr_get(x_91, 0);
lean::inc(x_96);
lean::dec(x_91);
if (lean::is_scalar(x_57)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_57;
 lean::cnstr_set_tag(x_57, 0);
}
lean::cnstr_set(x_99, 0, x_96);
x_11 = x_99;
x_12 = x_93;
goto lbl_13;
}
else
{
obj* x_102; obj* x_104; obj* x_105; obj* x_107; 
lean::dec(x_91);
lean::dec(x_57);
x_102 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__3;
lean::inc(x_1);
x_104 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_102, x_1, x_93);
x_105 = lean::cnstr_get(x_104, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_104, 1);
lean::inc(x_107);
lean::dec(x_104);
x_11 = x_105;
x_12 = x_107;
goto lbl_13;
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
obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_3 = l_lean_ir_cpp_emit__initialize__proc___closed__1;
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
} else {
 lean::dec(x_5);
 x_10 = lean::box(0);
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
} else {
 lean::dec(x_6);
 x_15 = lean::box(0);
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
obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; 
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_18 = x_6;
} else {
 lean::dec(x_6);
 x_18 = lean::box(0);
}
x_19 = l_lean_ir_cpp_finalize__prefix;
lean::inc(x_1);
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_19, x_1, x_8);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_29; obj* x_32; obj* x_33; 
lean::dec(x_1);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
lean::dec(x_22);
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_32 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_10)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_10;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_24);
return x_33;
}
else
{
obj* x_35; obj* x_37; obj* x_40; obj* x_41; obj* x_43; 
lean::dec(x_22);
x_35 = lean::cnstr_get(x_1, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_35, 0);
lean::inc(x_37);
lean::inc(x_1);
x_40 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_37, x_1, x_24);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_49; obj* x_52; obj* x_53; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_35);
x_49 = lean::cnstr_get(x_41, 0);
lean::inc(x_49);
lean::dec(x_41);
if (lean::is_scalar(x_18)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_52, 0, x_49);
if (lean::is_scalar(x_10)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_10;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_43);
return x_53;
}
else
{
obj* x_55; obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_41);
x_55 = l_lean_ir_cpp_emit__initialize__proc___closed__2;
lean::inc(x_1);
x_57 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_55, x_1, x_43);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_66; obj* x_69; obj* x_70; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_35);
x_66 = lean::cnstr_get(x_58, 0);
lean::inc(x_66);
lean::dec(x_58);
if (lean::is_scalar(x_18)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_69, 0, x_66);
if (lean::is_scalar(x_10)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_10;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_60);
return x_70;
}
else
{
obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
lean::dec(x_58);
x_72 = l_lean_ir_cpp_emit__finalize__proc___closed__1;
lean::inc(x_1);
x_74 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_72, x_1, x_60);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
lean::dec(x_74);
if (lean::obj_tag(x_75) == 0)
{
obj* x_83; obj* x_86; obj* x_87; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_35);
x_83 = lean::cnstr_get(x_75, 0);
lean::inc(x_83);
lean::dec(x_75);
if (lean::is_scalar(x_18)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_86, 0, x_83);
if (lean::is_scalar(x_10)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_10;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_77);
return x_87;
}
else
{
obj* x_89; obj* x_91; obj* x_92; obj* x_94; 
lean::dec(x_75);
x_89 = l_lean_ir_cpp_emit__finalize__proc___closed__2;
lean::inc(x_1);
x_91 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_89, x_1, x_77);
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_91, 1);
lean::inc(x_94);
lean::dec(x_91);
if (lean::obj_tag(x_92) == 0)
{
obj* x_100; obj* x_103; obj* x_104; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_35);
x_100 = lean::cnstr_get(x_92, 0);
lean::inc(x_100);
lean::dec(x_92);
if (lean::is_scalar(x_18)) {
 x_103 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_103 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_103, 0, x_100);
if (lean::is_scalar(x_10)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_10;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_94);
return x_104;
}
else
{
obj* x_106; obj* x_110; obj* x_111; obj* x_113; 
lean::dec(x_92);
x_106 = lean::cnstr_get(x_35, 1);
lean::inc(x_106);
lean::dec(x_35);
lean::inc(x_1);
x_110 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__1(x_106, x_1, x_94);
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_110, 1);
lean::inc(x_113);
lean::dec(x_110);
if (lean::obj_tag(x_111) == 0)
{
obj* x_118; obj* x_121; obj* x_122; 
lean::dec(x_1);
lean::dec(x_0);
x_118 = lean::cnstr_get(x_111, 0);
lean::inc(x_118);
lean::dec(x_111);
if (lean::is_scalar(x_18)) {
 x_121 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_121 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_121, 0, x_118);
if (lean::is_scalar(x_10)) {
 x_122 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_122 = x_10;
}
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_113);
return x_122;
}
else
{
obj* x_125; obj* x_126; obj* x_128; 
lean::dec(x_111);
lean::inc(x_1);
x_125 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2(x_0, x_1, x_113);
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_125, 1);
lean::inc(x_128);
lean::dec(x_125);
if (lean::obj_tag(x_126) == 0)
{
obj* x_132; obj* x_135; obj* x_136; 
lean::dec(x_1);
x_132 = lean::cnstr_get(x_126, 0);
lean::inc(x_132);
lean::dec(x_126);
if (lean::is_scalar(x_18)) {
 x_135 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_135 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_135, 0, x_132);
if (lean::is_scalar(x_10)) {
 x_136 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_136 = x_10;
}
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_128);
return x_136;
}
else
{
obj* x_140; obj* x_141; 
lean::dec(x_10);
lean::dec(x_18);
lean::dec(x_126);
x_140 = l_lean_ir_cpp_emit__uncurry___closed__1;
x_141 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_140, x_1, x_128);
return x_141;
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
obj* x_30; obj* x_33; obj* x_34; obj* x_36; obj* x_37; uint8 x_38; obj* x_40; uint8 x_43; obj* x_45; obj* x_46; uint8 x_47; obj* x_49; uint8 x_52; 
x_30 = lean::cnstr_get(x_16, 0);
lean::inc(x_30);
lean::dec(x_16);
x_33 = l_lean_ir_decl_header___main(x_30);
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
x_36 = lean::mk_nat_obj(0u);
x_37 = l_list_length__aux___main___rarg(x_34, x_36);
x_38 = lean::nat_dec_eq(x_37, x_36);
lean::dec(x_37);
x_40 = lean::cnstr_get(x_33, 2);
lean::inc(x_40);
lean::dec(x_33);
x_43 = lean::unbox(x_40);
lean::dec(x_40);
x_45 = l_lean_ir_type2id___main(x_43);
x_46 = l_lean_ir_valid__assign__unop__types___closed__4;
x_47 = lean::nat_dec_eq(x_45, x_46);
lean::dec(x_45);
x_49 = lean::cnstr_get(x_2, 0);
lean::inc(x_49);
lean::dec(x_2);
if (x_47 == 0)
{
uint8 x_54; 
x_54 = 0;
x_52 = x_54;
goto lbl_53;
}
else
{
uint8 x_55; 
x_55 = 1;
x_52 = x_55;
goto lbl_53;
}
lbl_53:
{
obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_63; 
if (x_38 == 0)
{
obj* x_66; obj* x_67; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::inc(x_10);
x_66 = l_lean_ir_id_to__string___main(x_10);
x_67 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
x_68 = 0;
x_69 = l_lean_ir_cpp_emit__main__proc___closed__5;
x_70 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_67);
lean::cnstr_set_scalar(x_70, sizeof(void*)*2, x_68);
x_71 = x_70;
x_72 = l_lean_ir_cpp_emit__main__proc___closed__6;
x_73 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set(x_73, 1, x_72);
lean::cnstr_set_scalar(x_73, sizeof(void*)*2, x_68);
x_74 = x_73;
x_75 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_75, 0, x_74);
x_62 = x_75;
x_63 = x_1;
goto lbl_64;
}
else
{
if (x_52 == 0)
{
obj* x_77; obj* x_78; uint8 x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::inc(x_10);
x_77 = l_lean_ir_id_to__string___main(x_10);
x_78 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_78, 0, x_77);
x_79 = 0;
x_80 = l_lean_ir_cpp_emit__main__proc___closed__5;
x_81 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_78);
lean::cnstr_set_scalar(x_81, sizeof(void*)*2, x_79);
x_82 = x_81;
x_83 = l_lean_ir_cpp_emit__main__proc___closed__7;
x_84 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_83);
lean::cnstr_set_scalar(x_84, sizeof(void*)*2, x_79);
x_85 = x_84;
x_86 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_86, 0, x_85);
x_62 = x_86;
x_63 = x_1;
goto lbl_64;
}
else
{
obj* x_87; 
x_87 = l_lean_ir_match__type___closed__5;
x_62 = x_87;
x_63 = x_1;
goto lbl_64;
}
}
lbl_58:
{
if (lean::obj_tag(x_56) == 0)
{
obj* x_90; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_0);
lean::dec(x_49);
x_90 = lean::cnstr_get(x_56, 0);
lean::inc(x_90);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 x_92 = x_56;
} else {
 lean::dec(x_56);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_90);
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_57);
return x_94;
}
else
{
obj* x_95; obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_103; 
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 x_95 = x_56;
} else {
 lean::dec(x_56);
 x_95 = lean::box(0);
}
x_96 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_0);
x_98 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_96, x_0, x_57);
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_98, 1);
lean::inc(x_101);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 x_103 = x_98;
} else {
 lean::dec(x_98);
 x_103 = lean::box(0);
}
if (lean::obj_tag(x_99) == 0)
{
obj* x_106; obj* x_109; obj* x_110; 
lean::dec(x_0);
lean::dec(x_49);
x_106 = lean::cnstr_get(x_99, 0);
lean::inc(x_106);
lean::dec(x_99);
if (lean::is_scalar(x_95)) {
 x_109 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_109 = x_95;
 lean::cnstr_set_tag(x_95, 0);
}
lean::cnstr_set(x_109, 0, x_106);
if (lean::is_scalar(x_103)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_103;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_101);
return x_110;
}
else
{
obj* x_112; obj* x_114; obj* x_115; obj* x_117; 
lean::dec(x_99);
x_112 = l_lean_ir_cpp_finalize__prefix;
lean::inc(x_0);
x_114 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_112, x_0, x_101);
x_115 = lean::cnstr_get(x_114, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_114, 1);
lean::inc(x_117);
lean::dec(x_114);
if (lean::obj_tag(x_115) == 0)
{
obj* x_122; obj* x_125; obj* x_126; 
lean::dec(x_0);
lean::dec(x_49);
x_122 = lean::cnstr_get(x_115, 0);
lean::inc(x_122);
lean::dec(x_115);
if (lean::is_scalar(x_95)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_95;
 lean::cnstr_set_tag(x_95, 0);
}
lean::cnstr_set(x_125, 0, x_122);
if (lean::is_scalar(x_103)) {
 x_126 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_126 = x_103;
}
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_117);
return x_126;
}
else
{
obj* x_129; obj* x_130; obj* x_132; 
lean::dec(x_115);
lean::inc(x_0);
x_129 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_49, x_0, x_117);
x_130 = lean::cnstr_get(x_129, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_129, 1);
lean::inc(x_132);
lean::dec(x_129);
if (lean::obj_tag(x_130) == 0)
{
obj* x_136; obj* x_139; obj* x_140; 
lean::dec(x_0);
x_136 = lean::cnstr_get(x_130, 0);
lean::inc(x_136);
lean::dec(x_130);
if (lean::is_scalar(x_95)) {
 x_139 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_139 = x_95;
 lean::cnstr_set_tag(x_95, 0);
}
lean::cnstr_set(x_139, 0, x_136);
if (lean::is_scalar(x_103)) {
 x_140 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_140 = x_103;
}
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_132);
return x_140;
}
else
{
obj* x_143; obj* x_144; obj* x_146; 
lean::dec(x_130);
lean::inc(x_0);
x_143 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_96, x_0, x_132);
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
if (lean::is_scalar(x_95)) {
 x_153 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_153 = x_95;
 lean::cnstr_set_tag(x_95, 0);
}
lean::cnstr_set(x_153, 0, x_150);
if (lean::is_scalar(x_103)) {
 x_154 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_154 = x_103;
}
lean::cnstr_set(x_154, 0, x_153);
lean::cnstr_set(x_154, 1, x_146);
return x_154;
}
else
{
obj* x_158; obj* x_159; 
lean::dec(x_95);
lean::dec(x_103);
lean::dec(x_144);
x_158 = l_lean_ir_cpp_emit__main__proc___closed__2;
x_159 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_158, x_0, x_146);
return x_159;
}
}
}
}
}
}
lbl_61:
{
if (lean::obj_tag(x_59) == 0)
{
obj* x_161; obj* x_163; obj* x_164; 
lean::dec(x_10);
x_161 = lean::cnstr_get(x_59, 0);
lean::inc(x_161);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 x_163 = x_59;
} else {
 lean::dec(x_59);
 x_163 = lean::box(0);
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_161);
x_56 = x_164;
x_57 = x_60;
goto lbl_58;
}
else
{
obj* x_165; obj* x_168; obj* x_169; obj* x_171; 
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 x_165 = x_59;
} else {
 lean::dec(x_59);
 x_165 = lean::box(0);
}
lean::inc(x_0);
lean::inc(x_49);
x_168 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_49, x_0, x_60);
x_169 = lean::cnstr_get(x_168, 0);
lean::inc(x_169);
x_171 = lean::cnstr_get(x_168, 1);
lean::inc(x_171);
lean::dec(x_168);
if (lean::obj_tag(x_169) == 0)
{
obj* x_175; obj* x_178; 
lean::dec(x_10);
x_175 = lean::cnstr_get(x_169, 0);
lean::inc(x_175);
lean::dec(x_169);
if (lean::is_scalar(x_165)) {
 x_178 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_178 = x_165;
 lean::cnstr_set_tag(x_165, 0);
}
lean::cnstr_set(x_178, 0, x_175);
x_56 = x_178;
x_57 = x_171;
goto lbl_58;
}
else
{
obj* x_180; obj* x_182; obj* x_183; obj* x_185; 
lean::dec(x_169);
x_180 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_0);
x_182 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_180, x_0, x_171);
x_183 = lean::cnstr_get(x_182, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_182, 1);
lean::inc(x_185);
lean::dec(x_182);
if (lean::obj_tag(x_183) == 0)
{
obj* x_189; obj* x_192; 
lean::dec(x_10);
x_189 = lean::cnstr_get(x_183, 0);
lean::inc(x_189);
lean::dec(x_183);
if (lean::is_scalar(x_165)) {
 x_192 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_192 = x_165;
 lean::cnstr_set_tag(x_165, 0);
}
lean::cnstr_set(x_192, 0, x_189);
x_56 = x_192;
x_57 = x_185;
goto lbl_58;
}
else
{
obj* x_194; obj* x_196; obj* x_197; obj* x_199; 
lean::dec(x_183);
x_194 = l_lean_ir_cpp_emit__main__proc___closed__3;
lean::inc(x_0);
x_196 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_194, x_0, x_185);
x_197 = lean::cnstr_get(x_196, 0);
lean::inc(x_197);
x_199 = lean::cnstr_get(x_196, 1);
lean::inc(x_199);
lean::dec(x_196);
if (lean::obj_tag(x_197) == 0)
{
obj* x_203; obj* x_206; 
lean::dec(x_10);
x_203 = lean::cnstr_get(x_197, 0);
lean::inc(x_203);
lean::dec(x_197);
if (lean::is_scalar(x_165)) {
 x_206 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_206 = x_165;
 lean::cnstr_set_tag(x_165, 0);
}
lean::cnstr_set(x_206, 0, x_203);
x_56 = x_206;
x_57 = x_199;
goto lbl_58;
}
else
{
obj* x_210; obj* x_211; obj* x_213; 
lean::dec(x_197);
lean::dec(x_165);
lean::inc(x_0);
x_210 = l_lean_ir_cpp_emit__fnid(x_10, x_0, x_199);
x_211 = lean::cnstr_get(x_210, 0);
lean::inc(x_211);
x_213 = lean::cnstr_get(x_210, 1);
lean::inc(x_213);
lean::dec(x_210);
x_56 = x_211;
x_57 = x_213;
goto lbl_58;
}
}
}
}
}
lbl_64:
{
if (lean::obj_tag(x_62) == 0)
{
obj* x_216; obj* x_218; obj* x_219; 
x_216 = lean::cnstr_get(x_62, 0);
lean::inc(x_216);
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_218 = x_62;
} else {
 lean::dec(x_62);
 x_218 = lean::box(0);
}
if (lean::is_scalar(x_218)) {
 x_219 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_219 = x_218;
}
lean::cnstr_set(x_219, 0, x_216);
x_59 = x_219;
x_60 = x_63;
goto lbl_61;
}
else
{
obj* x_220; obj* x_221; obj* x_223; obj* x_224; obj* x_226; 
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_220 = x_62;
} else {
 lean::dec(x_62);
 x_220 = lean::box(0);
}
x_221 = l_lean_ir_cpp_emit__main__proc___closed__4;
lean::inc(x_0);
x_223 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_221, x_0, x_63);
x_224 = lean::cnstr_get(x_223, 0);
lean::inc(x_224);
x_226 = lean::cnstr_get(x_223, 1);
lean::inc(x_226);
lean::dec(x_223);
if (lean::obj_tag(x_224) == 0)
{
obj* x_229; obj* x_232; 
x_229 = lean::cnstr_get(x_224, 0);
lean::inc(x_229);
lean::dec(x_224);
if (lean::is_scalar(x_220)) {
 x_232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_232 = x_220;
 lean::cnstr_set_tag(x_220, 0);
}
lean::cnstr_set(x_232, 0, x_229);
x_59 = x_232;
x_60 = x_226;
goto lbl_61;
}
else
{
obj* x_235; obj* x_237; obj* x_238; obj* x_240; 
lean::dec(x_224);
lean::dec(x_220);
x_235 = l_lean_ir_cpp_initialize__prefix;
lean::inc(x_0);
x_237 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_235, x_0, x_226);
x_238 = lean::cnstr_get(x_237, 0);
lean::inc(x_238);
x_240 = lean::cnstr_get(x_237, 1);
lean::inc(x_240);
lean::dec(x_237);
x_59 = x_238;
x_60 = x_240;
goto lbl_61;
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
obj* x_6; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_cpp_emit__def(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 x_17 = x_12;
} else {
 lean::dec(x_12);
 x_17 = lean::box(0);
}
if (lean::obj_tag(x_13) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_20 = lean::cnstr_get(x_13, 0);
lean::inc(x_20);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_22 = x_13;
} else {
 lean::dec(x_13);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
return x_24;
}
else
{
lean::dec(x_17);
lean::dec(x_13);
x_0 = x_8;
x_2 = x_15;
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
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_14; obj* x_15; obj* x_17; 
x_2 = lean::cnstr_get(x_1, 2);
lean::inc(x_2);
x_4 = l_lean_ir_cpp_file__header(x_2);
x_5 = l_lean_format_be___main___closed__1;
x_6 = lean::string_append(x_4, x_5);
x_7 = l_lean_ir_mk__context;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_7);
lean::inc(x_8);
lean::inc(x_0);
x_14 = l_lean_ir_cpp_emit__used__headers(x_0, x_8, x_6);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
if (lean::obj_tag(x_15) == 0)
{
obj* x_20; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_15, 0);
lean::inc(x_20);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_22 = x_15;
} else {
 lean::dec(x_15);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_20);
x_9 = x_23;
x_10 = x_17;
goto lbl_11;
}
else
{
obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_30; 
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_24 = x_15;
} else {
 lean::dec(x_15);
 x_24 = lean::box(0);
}
x_25 = l_lean_ir_extract__cpp___closed__1;
lean::inc(x_8);
x_27 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_25, x_8, x_17);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_33; obj* x_36; 
x_33 = lean::cnstr_get(x_28, 0);
lean::inc(x_33);
lean::dec(x_28);
if (lean::is_scalar(x_24)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_24;
 lean::cnstr_set_tag(x_24, 0);
}
lean::cnstr_set(x_36, 0, x_33);
x_9 = x_36;
x_10 = x_30;
goto lbl_11;
}
else
{
obj* x_39; obj* x_41; obj* x_42; obj* x_44; 
lean::dec(x_28);
lean::dec(x_24);
x_39 = l_lean_ir_extract__cpp___closed__2;
lean::inc(x_8);
x_41 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_39, x_8, x_30);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
x_9 = x_42;
x_10 = x_44;
goto lbl_11;
}
}
lbl_11:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_10);
x_50 = lean::cnstr_get(x_9, 0);
lean::inc(x_50);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_52 = x_9;
} else {
 lean::dec(x_9);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
return x_53;
}
else
{
obj* x_54; obj* x_57; obj* x_58; obj* x_60; 
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_54 = x_9;
} else {
 lean::dec(x_9);
 x_54 = lean::box(0);
}
lean::inc(x_8);
lean::inc(x_0);
x_57 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__global__var__decls___spec__1(x_0, x_8, x_10);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_66; obj* x_69; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_60);
x_66 = lean::cnstr_get(x_58, 0);
lean::inc(x_66);
lean::dec(x_58);
if (lean::is_scalar(x_54)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_54;
 lean::cnstr_set_tag(x_54, 0);
}
lean::cnstr_set(x_69, 0, x_66);
return x_69;
}
else
{
obj* x_73; obj* x_74; obj* x_76; 
lean::dec(x_58);
lean::inc(x_8);
lean::inc(x_0);
x_73 = l_lean_ir_cpp_emit__initialize__proc(x_0, x_8, x_60);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
if (lean::obj_tag(x_74) == 0)
{
obj* x_82; obj* x_85; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_76);
x_82 = lean::cnstr_get(x_74, 0);
lean::inc(x_82);
lean::dec(x_74);
if (lean::is_scalar(x_54)) {
 x_85 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_85 = x_54;
 lean::cnstr_set_tag(x_54, 0);
}
lean::cnstr_set(x_85, 0, x_82);
return x_85;
}
else
{
obj* x_89; obj* x_90; obj* x_92; 
lean::dec(x_74);
lean::inc(x_8);
lean::inc(x_0);
x_89 = l_lean_ir_cpp_emit__finalize__proc(x_0, x_8, x_76);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_89, 1);
lean::inc(x_92);
lean::dec(x_89);
if (lean::obj_tag(x_90) == 0)
{
obj* x_98; obj* x_101; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_92);
x_98 = lean::cnstr_get(x_90, 0);
lean::inc(x_98);
lean::dec(x_90);
if (lean::is_scalar(x_54)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_54;
 lean::cnstr_set_tag(x_54, 0);
}
lean::cnstr_set(x_101, 0, x_98);
return x_101;
}
else
{
obj* x_104; obj* x_105; obj* x_107; 
lean::dec(x_90);
lean::inc(x_8);
x_104 = l_list_mmap_x_27___main___at_lean_ir_extract__cpp___spec__1(x_0, x_8, x_92);
x_105 = lean::cnstr_get(x_104, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_104, 1);
lean::inc(x_107);
lean::dec(x_104);
if (lean::obj_tag(x_105) == 0)
{
obj* x_112; obj* x_115; 
lean::dec(x_8);
lean::dec(x_107);
x_112 = lean::cnstr_get(x_105, 0);
lean::inc(x_112);
lean::dec(x_105);
if (lean::is_scalar(x_54)) {
 x_115 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_115 = x_54;
 lean::cnstr_set_tag(x_54, 0);
}
lean::cnstr_set(x_115, 0, x_112);
return x_115;
}
else
{
obj* x_117; obj* x_118; obj* x_120; 
lean::dec(x_105);
x_117 = l_lean_ir_cpp_emit__main__proc(x_8, x_107);
x_118 = lean::cnstr_get(x_117, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_117, 1);
lean::inc(x_120);
lean::dec(x_117);
if (lean::obj_tag(x_118) == 0)
{
obj* x_124; obj* x_127; 
lean::dec(x_120);
x_124 = lean::cnstr_get(x_118, 0);
lean::inc(x_124);
lean::dec(x_118);
if (lean::is_scalar(x_54)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_54;
 lean::cnstr_set_tag(x_54, 0);
}
lean::cnstr_set(x_127, 0, x_124);
return x_127;
}
else
{
obj* x_129; 
lean::dec(x_118);
if (lean::is_scalar(x_54)) {
 x_129 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_129 = x_54;
}
lean::cnstr_set(x_129, 0, x_120);
return x_129;
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
