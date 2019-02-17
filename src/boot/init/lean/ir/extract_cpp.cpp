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
lean::dec(x_23);
lean::dec(x_18);
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
x_3 = l___private_init_lean_name__mangling_1__string_mangle__aux___main___closed__2;
lean::inc(x_3);
x_5 = l___private_init_lean_name__mangling_4__name_mangle__aux___main(x_3, x_0);
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
x_5 = l___private_init_lean_name__mangling_4__name_mangle__aux___main(x_3, x_0);
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
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_11 = l_lean_ir_cpp_fid2cpp___closed__1;
lean::inc(x_11);
x_13 = l___private_init_lean_name__mangling_4__name_mangle__aux___main(x_11, x_0);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_2);
return x_15;
}
else
{
obj* x_17; obj* x_20; obj* x_21; 
lean::dec(x_0);
x_17 = lean::cnstr_get(x_10, 0);
lean::inc(x_17);
lean::dec(x_10);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_17);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_2);
return x_21;
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
obj* x_10; obj* x_12; 
x_10 = l_lean_ir_cpp_is__const___closed__1;
lean::inc(x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_16; uint8 x_17; obj* x_19; obj* x_20; obj* x_21; 
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
lean::dec(x_9);
x_16 = l_lean_ir_decl_header___main(x_13);
x_17 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*3);
lean::dec(x_16);
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
case 2:
{
obj* x_1; 
x_1 = l_lean_ir_cpp_type2cpp___main___closed__2;
lean::inc(x_1);
return x_1;
}
case 3:
{
obj* x_3; 
x_3 = l_lean_ir_cpp_type2cpp___main___closed__3;
lean::inc(x_3);
return x_3;
}
case 4:
{
obj* x_5; 
x_5 = l_lean_ir_cpp_type2cpp___main___closed__4;
lean::inc(x_5);
return x_5;
}
case 5:
{
obj* x_7; 
x_7 = l_lean_ir_cpp_type2cpp___main___closed__5;
lean::inc(x_7);
return x_7;
}
case 6:
{
obj* x_9; 
x_9 = l_lean_ir_cpp_type2cpp___main___closed__6;
lean::inc(x_9);
return x_9;
}
case 7:
{
obj* x_11; 
x_11 = l_lean_ir_cpp_type2cpp___main___closed__7;
lean::inc(x_11);
return x_11;
}
case 8:
{
obj* x_13; 
x_13 = l_lean_ir_cpp_type2cpp___main___closed__8;
lean::inc(x_13);
return x_13;
}
case 9:
{
obj* x_15; 
x_15 = l_lean_ir_cpp_type2cpp___main___closed__9;
lean::inc(x_15);
return x_15;
}
case 10:
{
obj* x_17; 
x_17 = l_lean_ir_cpp_type2cpp___main___closed__10;
lean::inc(x_17);
return x_17;
}
case 11:
{
obj* x_19; 
x_19 = l_lean_ir_cpp_type2cpp___main___closed__11;
lean::inc(x_19);
return x_19;
}
default:
{
obj* x_21; 
x_21 = l_lean_ir_cpp_type2cpp___main___closed__1;
lean::inc(x_21);
return x_21;
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
obj* x_8; obj* x_10; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_8 = l_lean_ir_match__type___closed__5;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_4);
return x_10;
}
else
{
obj* x_11; obj* x_13; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_2, 1);
lean::inc(x_13);
lean::dec(x_2);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; 
lean::dec(x_1);
x_17 = lean::apply_3(x_0, x_11, x_3, x_4);
return x_17;
}
else
{
obj* x_20; obj* x_21; obj* x_23; obj* x_25; 
lean::inc(x_3);
lean::inc(x_0);
x_20 = lean::apply_3(x_0, x_11, x_3, x_4);
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
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
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
obj* x_35; obj* x_38; obj* x_39; obj* x_41; 
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_35 = x_21;
}
lean::inc(x_3);
lean::inc(x_1);
x_38 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1, x_3, x_23);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
if (lean::obj_tag(x_39) == 0)
{
obj* x_48; obj* x_51; obj* x_52; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_48 = lean::cnstr_get(x_39, 0);
lean::inc(x_48);
lean::dec(x_39);
if (lean::is_scalar(x_35)) {
 x_51 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_51 = x_35;
 lean::cnstr_set_tag(x_35, 0);
}
lean::cnstr_set(x_51, 0, x_48);
if (lean::is_scalar(x_25)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_25;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_41);
return x_52;
}
else
{
obj* x_54; obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_39);
x_54 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_54);
x_57 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_54, x_3, x_41);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_67; obj* x_70; obj* x_71; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_67 = lean::cnstr_get(x_58, 0);
lean::inc(x_67);
lean::dec(x_58);
if (lean::is_scalar(x_35)) {
 x_70 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_70 = x_35;
 lean::cnstr_set_tag(x_35, 0);
}
lean::cnstr_set(x_70, 0, x_67);
if (lean::is_scalar(x_25)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_25;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_60);
return x_71;
}
else
{
lean::dec(x_58);
lean::dec(x_25);
lean::dec(x_35);
x_2 = x_13;
x_4 = x_60;
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
lean::dec(x_26);
lean::dec(x_19);
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
lean::dec(x_23);
lean::dec(x_18);
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
lean::dec(x_0);
x_41 = l_lean_ir_cpp_emit__var(x_38, x_1, x_25);
return x_41;
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
obj* x_6; obj* x_8; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = l_lean_ir_cpp_emit__cases___main___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
else
{
obj* x_9; obj* x_11; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
lean::dec(x_0);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_18; obj* x_19; obj* x_21; obj* x_23; 
lean::dec(x_1);
x_15 = l_lean_ir_cpp_emit__cases___main___closed__2;
lean::inc(x_2);
lean::inc(x_15);
x_18 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_15, x_2, x_3);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 x_23 = x_18;
}
if (lean::obj_tag(x_19) == 0)
{
obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_9);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_19, 0);
lean::inc(x_26);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_28 = x_19;
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
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_31 = x_19;
}
lean::inc(x_2);
x_33 = l_lean_ir_cpp_emit__blockid(x_9, x_2, x_21);
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
obj* x_49; obj* x_52; obj* x_53; obj* x_55; obj* x_57; 
x_49 = l_lean_ir_cpp_emit__cases___main___closed__3;
lean::inc(x_2);
lean::inc(x_49);
x_52 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_49, x_2, x_3);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
if (lean::is_shared(x_52)) {
 lean::dec(x_52);
 x_57 = lean::box(0);
} else {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 x_57 = x_52;
}
if (lean::obj_tag(x_53) == 0)
{
obj* x_62; obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_2);
x_62 = lean::cnstr_get(x_53, 0);
lean::inc(x_62);
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_64 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 x_64 = x_53;
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_62);
if (lean::is_scalar(x_57)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_57;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_55);
return x_66;
}
else
{
obj* x_67; obj* x_70; obj* x_71; obj* x_73; 
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_67 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 x_67 = x_53;
}
lean::inc(x_2);
lean::inc(x_1);
x_70 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_1, x_2, x_55);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
lean::dec(x_70);
if (lean::obj_tag(x_71) == 0)
{
obj* x_80; obj* x_83; obj* x_84; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_11);
lean::dec(x_2);
x_80 = lean::cnstr_get(x_71, 0);
lean::inc(x_80);
lean::dec(x_71);
if (lean::is_scalar(x_67)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_67;
 lean::cnstr_set_tag(x_67, 0);
}
lean::cnstr_set(x_83, 0, x_80);
if (lean::is_scalar(x_57)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_57;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_73);
return x_84;
}
else
{
obj* x_86; obj* x_87; obj* x_89; obj* x_92; obj* x_93; obj* x_95; 
lean::dec(x_71);
x_86 = lean::mk_nat_obj(1u);
x_87 = lean::nat_add(x_1, x_86);
lean::dec(x_1);
x_89 = l_lean_ir_cpp_emit__cases___main___closed__4;
lean::inc(x_2);
lean::inc(x_89);
x_92 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_89, x_2, x_73);
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_92, 1);
lean::inc(x_95);
lean::dec(x_92);
if (lean::obj_tag(x_93) == 0)
{
obj* x_102; obj* x_105; obj* x_106; 
lean::dec(x_9);
lean::dec(x_11);
lean::dec(x_2);
lean::dec(x_87);
x_102 = lean::cnstr_get(x_93, 0);
lean::inc(x_102);
lean::dec(x_93);
if (lean::is_scalar(x_67)) {
 x_105 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_105 = x_67;
 lean::cnstr_set_tag(x_67, 0);
}
lean::cnstr_set(x_105, 0, x_102);
if (lean::is_scalar(x_57)) {
 x_106 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_106 = x_57;
}
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_95);
return x_106;
}
else
{
obj* x_109; obj* x_110; obj* x_112; 
lean::dec(x_93);
lean::inc(x_2);
x_109 = l_lean_ir_cpp_emit__blockid(x_9, x_2, x_95);
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_109, 1);
lean::inc(x_112);
lean::dec(x_109);
if (lean::obj_tag(x_110) == 0)
{
obj* x_118; obj* x_121; obj* x_122; 
lean::dec(x_11);
lean::dec(x_2);
lean::dec(x_87);
x_118 = lean::cnstr_get(x_110, 0);
lean::inc(x_118);
lean::dec(x_110);
if (lean::is_scalar(x_67)) {
 x_121 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_121 = x_67;
 lean::cnstr_set_tag(x_67, 0);
}
lean::cnstr_set(x_121, 0, x_118);
if (lean::is_scalar(x_57)) {
 x_122 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_122 = x_57;
}
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_112);
return x_122;
}
else
{
obj* x_125; obj* x_126; obj* x_128; 
lean::dec(x_110);
lean::inc(x_2);
x_125 = l_lean_ir_cpp_emit__eos(x_2, x_112);
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_125, 1);
lean::inc(x_128);
lean::dec(x_125);
if (lean::obj_tag(x_126) == 0)
{
obj* x_134; obj* x_137; obj* x_138; 
lean::dec(x_11);
lean::dec(x_2);
lean::dec(x_87);
x_134 = lean::cnstr_get(x_126, 0);
lean::inc(x_134);
lean::dec(x_126);
if (lean::is_scalar(x_67)) {
 x_137 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_137 = x_67;
 lean::cnstr_set_tag(x_67, 0);
}
lean::cnstr_set(x_137, 0, x_134);
if (lean::is_scalar(x_57)) {
 x_138 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_138 = x_57;
}
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_128);
return x_138;
}
else
{
lean::dec(x_57);
lean::dec(x_67);
lean::dec(x_126);
x_0 = x_11;
x_1 = x_87;
x_3 = x_128;
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
obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_24; 
lean::dec(x_1);
lean::dec(x_0);
x_16 = l_lean_ir_cpp_emit__case___main___closed__4;
lean::inc(x_2);
lean::inc(x_16);
x_19 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_16, x_2, x_3);
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
obj* x_27; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_10);
lean::dec(x_2);
x_27 = lean::cnstr_get(x_20, 0);
lean::inc(x_27);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_29 = x_20;
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_27);
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
else
{
obj* x_32; obj* x_34; obj* x_35; obj* x_37; 
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_32 = x_20;
}
lean::inc(x_2);
x_34 = l_lean_ir_cpp_emit__blockid(x_10, x_2, x_22);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
if (lean::obj_tag(x_35) == 0)
{
obj* x_41; obj* x_44; obj* x_45; 
lean::dec(x_2);
x_41 = lean::cnstr_get(x_35, 0);
lean::inc(x_41);
lean::dec(x_35);
if (lean::is_scalar(x_32)) {
 x_44 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_44 = x_32;
 lean::cnstr_set_tag(x_32, 0);
}
lean::cnstr_set(x_44, 0, x_41);
if (lean::is_scalar(x_24)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_24;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_37);
return x_45;
}
else
{
obj* x_49; 
lean::dec(x_32);
lean::dec(x_24);
lean::dec(x_35);
x_49 = l_lean_ir_cpp_emit__eos(x_2, x_37);
return x_49;
}
}
}
else
{
obj* x_50; obj* x_52; 
x_50 = lean::cnstr_get(x_12, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_12, 1);
lean::inc(x_52);
lean::dec(x_12);
if (lean::obj_tag(x_52) == 0)
{
obj* x_56; obj* x_57; obj* x_59; obj* x_62; 
lean::dec(x_1);
x_59 = lean::cnstr_get(x_2, 1);
lean::inc(x_59);
lean::inc(x_0);
x_62 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_59, x_0);
if (lean::obj_tag(x_62) == 0)
{
obj* x_66; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_50);
x_66 = l_lean_ir_cpp_emit__case___main___closed__5;
lean::inc(x_66);
x_56 = x_66;
x_57 = x_3;
goto lbl_58;
}
else
{
obj* x_68; uint8 x_71; 
x_68 = lean::cnstr_get(x_62, 0);
lean::inc(x_68);
lean::dec(x_62);
x_71 = lean::unbox(x_68);
lean::dec(x_68);
switch (x_71) {
case 0:
{
obj* x_73; obj* x_76; obj* x_77; obj* x_79; 
x_73 = l_lean_ir_cpp_emit__case___main___closed__6;
lean::inc(x_2);
lean::inc(x_73);
x_76 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_73, x_2, x_3);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
if (lean::obj_tag(x_77) == 0)
{
obj* x_85; obj* x_87; obj* x_88; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_50);
x_85 = lean::cnstr_get(x_77, 0);
lean::inc(x_85);
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 x_87 = x_77;
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_85);
x_56 = x_88;
x_57 = x_79;
goto lbl_58;
}
else
{
obj* x_89; obj* x_91; obj* x_92; obj* x_94; 
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_89 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 x_89 = x_77;
}
lean::inc(x_2);
x_91 = l_lean_ir_cpp_emit__var(x_0, x_2, x_79);
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_91, 1);
lean::inc(x_94);
lean::dec(x_91);
if (lean::obj_tag(x_92) == 0)
{
obj* x_99; obj* x_102; 
lean::dec(x_10);
lean::dec(x_50);
x_99 = lean::cnstr_get(x_92, 0);
lean::inc(x_99);
lean::dec(x_92);
if (lean::is_scalar(x_89)) {
 x_102 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_102 = x_89;
 lean::cnstr_set_tag(x_89, 0);
}
lean::cnstr_set(x_102, 0, x_99);
x_56 = x_102;
x_57 = x_94;
goto lbl_58;
}
else
{
obj* x_104; obj* x_107; obj* x_108; obj* x_110; 
lean::dec(x_92);
x_104 = l_lean_ir_cpp_emit__case___main___closed__7;
lean::inc(x_2);
lean::inc(x_104);
x_107 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_104, x_2, x_94);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_107, 1);
lean::inc(x_110);
lean::dec(x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_115; obj* x_118; 
lean::dec(x_10);
lean::dec(x_50);
x_115 = lean::cnstr_get(x_108, 0);
lean::inc(x_115);
lean::dec(x_108);
if (lean::is_scalar(x_89)) {
 x_118 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_118 = x_89;
 lean::cnstr_set_tag(x_89, 0);
}
lean::cnstr_set(x_118, 0, x_115);
x_56 = x_118;
x_57 = x_110;
goto lbl_58;
}
else
{
obj* x_121; obj* x_122; obj* x_124; 
lean::dec(x_108);
lean::inc(x_2);
x_121 = l_lean_ir_cpp_emit__blockid(x_50, x_2, x_110);
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_121, 1);
lean::inc(x_124);
lean::dec(x_121);
if (lean::obj_tag(x_122) == 0)
{
obj* x_128; obj* x_131; 
lean::dec(x_10);
x_128 = lean::cnstr_get(x_122, 0);
lean::inc(x_128);
lean::dec(x_122);
if (lean::is_scalar(x_89)) {
 x_131 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_131 = x_89;
 lean::cnstr_set_tag(x_89, 0);
}
lean::cnstr_set(x_131, 0, x_128);
x_56 = x_131;
x_57 = x_124;
goto lbl_58;
}
else
{
obj* x_133; obj* x_136; obj* x_137; obj* x_139; 
lean::dec(x_122);
x_133 = l_lean_ir_cpp_emit__case___main___closed__8;
lean::inc(x_2);
lean::inc(x_133);
x_136 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_133, x_2, x_124);
x_137 = lean::cnstr_get(x_136, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_136, 1);
lean::inc(x_139);
lean::dec(x_136);
if (lean::obj_tag(x_137) == 0)
{
obj* x_143; obj* x_146; 
lean::dec(x_10);
x_143 = lean::cnstr_get(x_137, 0);
lean::inc(x_143);
lean::dec(x_137);
if (lean::is_scalar(x_89)) {
 x_146 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_146 = x_89;
 lean::cnstr_set_tag(x_89, 0);
}
lean::cnstr_set(x_146, 0, x_143);
x_56 = x_146;
x_57 = x_139;
goto lbl_58;
}
else
{
obj* x_150; obj* x_151; obj* x_153; 
lean::dec(x_89);
lean::dec(x_137);
lean::inc(x_2);
x_150 = l_lean_ir_cpp_emit__blockid(x_10, x_2, x_139);
x_151 = lean::cnstr_get(x_150, 0);
lean::inc(x_151);
x_153 = lean::cnstr_get(x_150, 1);
lean::inc(x_153);
lean::dec(x_150);
x_56 = x_151;
x_57 = x_153;
goto lbl_58;
}
}
}
}
}
}
case 3:
{
obj* x_156; obj* x_159; obj* x_160; obj* x_162; 
x_156 = l_lean_ir_cpp_emit__case___main___closed__6;
lean::inc(x_2);
lean::inc(x_156);
x_159 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_156, x_2, x_3);
x_160 = lean::cnstr_get(x_159, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_159, 1);
lean::inc(x_162);
lean::dec(x_159);
if (lean::obj_tag(x_160) == 0)
{
obj* x_168; obj* x_170; obj* x_171; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_50);
x_168 = lean::cnstr_get(x_160, 0);
lean::inc(x_168);
if (lean::is_shared(x_160)) {
 lean::dec(x_160);
 x_170 = lean::box(0);
} else {
 lean::cnstr_release(x_160, 0);
 x_170 = x_160;
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_168);
x_56 = x_171;
x_57 = x_162;
goto lbl_58;
}
else
{
obj* x_172; obj* x_174; obj* x_175; obj* x_177; 
if (lean::is_shared(x_160)) {
 lean::dec(x_160);
 x_172 = lean::box(0);
} else {
 lean::cnstr_release(x_160, 0);
 x_172 = x_160;
}
lean::inc(x_2);
x_174 = l_lean_ir_cpp_emit__var(x_0, x_2, x_162);
x_175 = lean::cnstr_get(x_174, 0);
lean::inc(x_175);
x_177 = lean::cnstr_get(x_174, 1);
lean::inc(x_177);
lean::dec(x_174);
if (lean::obj_tag(x_175) == 0)
{
obj* x_182; obj* x_185; 
lean::dec(x_10);
lean::dec(x_50);
x_182 = lean::cnstr_get(x_175, 0);
lean::inc(x_182);
lean::dec(x_175);
if (lean::is_scalar(x_172)) {
 x_185 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_185 = x_172;
 lean::cnstr_set_tag(x_172, 0);
}
lean::cnstr_set(x_185, 0, x_182);
x_56 = x_185;
x_57 = x_177;
goto lbl_58;
}
else
{
obj* x_187; obj* x_190; obj* x_191; obj* x_193; 
lean::dec(x_175);
x_187 = l_lean_ir_cpp_emit__case___main___closed__9;
lean::inc(x_2);
lean::inc(x_187);
x_190 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_187, x_2, x_177);
x_191 = lean::cnstr_get(x_190, 0);
lean::inc(x_191);
x_193 = lean::cnstr_get(x_190, 1);
lean::inc(x_193);
lean::dec(x_190);
if (lean::obj_tag(x_191) == 0)
{
obj* x_198; obj* x_201; 
lean::dec(x_10);
lean::dec(x_50);
x_198 = lean::cnstr_get(x_191, 0);
lean::inc(x_198);
lean::dec(x_191);
if (lean::is_scalar(x_172)) {
 x_201 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_201 = x_172;
 lean::cnstr_set_tag(x_172, 0);
}
lean::cnstr_set(x_201, 0, x_198);
x_56 = x_201;
x_57 = x_193;
goto lbl_58;
}
else
{
obj* x_204; obj* x_205; obj* x_207; 
lean::dec(x_191);
lean::inc(x_2);
x_204 = l_lean_ir_cpp_emit__blockid(x_10, x_2, x_193);
x_205 = lean::cnstr_get(x_204, 0);
lean::inc(x_205);
x_207 = lean::cnstr_get(x_204, 1);
lean::inc(x_207);
lean::dec(x_204);
if (lean::obj_tag(x_205) == 0)
{
obj* x_211; obj* x_214; 
lean::dec(x_50);
x_211 = lean::cnstr_get(x_205, 0);
lean::inc(x_211);
lean::dec(x_205);
if (lean::is_scalar(x_172)) {
 x_214 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_214 = x_172;
 lean::cnstr_set_tag(x_172, 0);
}
lean::cnstr_set(x_214, 0, x_211);
x_56 = x_214;
x_57 = x_207;
goto lbl_58;
}
else
{
obj* x_216; obj* x_219; obj* x_220; obj* x_222; 
lean::dec(x_205);
x_216 = l_lean_ir_cpp_emit__case___main___closed__8;
lean::inc(x_2);
lean::inc(x_216);
x_219 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_216, x_2, x_207);
x_220 = lean::cnstr_get(x_219, 0);
lean::inc(x_220);
x_222 = lean::cnstr_get(x_219, 1);
lean::inc(x_222);
lean::dec(x_219);
if (lean::obj_tag(x_220) == 0)
{
obj* x_226; obj* x_229; 
lean::dec(x_50);
x_226 = lean::cnstr_get(x_220, 0);
lean::inc(x_226);
lean::dec(x_220);
if (lean::is_scalar(x_172)) {
 x_229 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_229 = x_172;
 lean::cnstr_set_tag(x_172, 0);
}
lean::cnstr_set(x_229, 0, x_226);
x_56 = x_229;
x_57 = x_222;
goto lbl_58;
}
else
{
obj* x_233; obj* x_234; obj* x_236; 
lean::dec(x_172);
lean::dec(x_220);
lean::inc(x_2);
x_233 = l_lean_ir_cpp_emit__blockid(x_50, x_2, x_222);
x_234 = lean::cnstr_get(x_233, 0);
lean::inc(x_234);
x_236 = lean::cnstr_get(x_233, 1);
lean::inc(x_236);
lean::dec(x_233);
x_56 = x_234;
x_57 = x_236;
goto lbl_58;
}
}
}
}
}
}
default:
{
obj* x_242; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_50);
x_242 = l_lean_ir_cpp_emit__case___main___closed__5;
lean::inc(x_242);
x_56 = x_242;
x_57 = x_3;
goto lbl_58;
}
}
}
lbl_58:
{
if (lean::obj_tag(x_56) == 0)
{
obj* x_245; obj* x_247; obj* x_248; obj* x_249; 
lean::dec(x_2);
x_245 = lean::cnstr_get(x_56, 0);
lean::inc(x_245);
if (lean::is_shared(x_56)) {
 lean::dec(x_56);
 x_247 = lean::box(0);
} else {
 lean::cnstr_release(x_56, 0);
 x_247 = x_56;
}
if (lean::is_scalar(x_247)) {
 x_248 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_248 = x_247;
}
lean::cnstr_set(x_248, 0, x_245);
x_249 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_249, 0, x_248);
lean::cnstr_set(x_249, 1, x_57);
return x_249;
}
else
{
obj* x_251; 
lean::dec(x_56);
x_251 = l_lean_ir_cpp_emit__eos(x_2, x_57);
return x_251;
}
}
}
else
{
obj* x_255; 
lean::dec(x_10);
lean::dec(x_50);
lean::dec(x_52);
x_255 = lean::box(0);
x_7 = x_255;
goto lbl_8;
}
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_258; obj* x_260; obj* x_261; obj* x_262; 
lean::dec(x_1);
lean::dec(x_2);
x_258 = lean::cnstr_get(x_4, 0);
lean::inc(x_258);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_260 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_260 = x_4;
}
if (lean::is_scalar(x_260)) {
 x_261 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_261 = x_260;
}
lean::cnstr_set(x_261, 0, x_258);
x_262 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_262, 0, x_261);
lean::cnstr_set(x_262, 1, x_5);
return x_262;
}
else
{
obj* x_263; obj* x_264; obj* x_267; obj* x_268; obj* x_270; obj* x_272; 
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_263 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_263 = x_4;
}
x_264 = l_lean_ir_cpp_emit__case___main___closed__1;
lean::inc(x_2);
lean::inc(x_264);
x_267 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_264, x_2, x_5);
x_268 = lean::cnstr_get(x_267, 0);
lean::inc(x_268);
x_270 = lean::cnstr_get(x_267, 1);
lean::inc(x_270);
if (lean::is_shared(x_267)) {
 lean::dec(x_267);
 x_272 = lean::box(0);
} else {
 lean::cnstr_release(x_267, 0);
 lean::cnstr_release(x_267, 1);
 x_272 = x_267;
}
if (lean::obj_tag(x_268) == 0)
{
obj* x_275; obj* x_278; obj* x_279; 
lean::dec(x_1);
lean::dec(x_2);
x_275 = lean::cnstr_get(x_268, 0);
lean::inc(x_275);
lean::dec(x_268);
if (lean::is_scalar(x_263)) {
 x_278 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_278 = x_263;
 lean::cnstr_set_tag(x_263, 0);
}
lean::cnstr_set(x_278, 0, x_275);
if (lean::is_scalar(x_272)) {
 x_279 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_279 = x_272;
}
lean::cnstr_set(x_279, 0, x_278);
lean::cnstr_set(x_279, 1, x_270);
return x_279;
}
else
{
obj* x_281; obj* x_284; obj* x_285; obj* x_287; 
lean::dec(x_268);
x_281 = l_lean_format_be___main___closed__1;
lean::inc(x_2);
lean::inc(x_281);
x_284 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_281, x_2, x_270);
x_285 = lean::cnstr_get(x_284, 0);
lean::inc(x_285);
x_287 = lean::cnstr_get(x_284, 1);
lean::inc(x_287);
lean::dec(x_284);
if (lean::obj_tag(x_285) == 0)
{
obj* x_292; obj* x_295; obj* x_296; 
lean::dec(x_1);
lean::dec(x_2);
x_292 = lean::cnstr_get(x_285, 0);
lean::inc(x_292);
lean::dec(x_285);
if (lean::is_scalar(x_263)) {
 x_295 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_295 = x_263;
 lean::cnstr_set_tag(x_263, 0);
}
lean::cnstr_set(x_295, 0, x_292);
if (lean::is_scalar(x_272)) {
 x_296 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_296 = x_272;
}
lean::cnstr_set(x_296, 0, x_295);
lean::cnstr_set(x_296, 1, x_287);
return x_296;
}
else
{
obj* x_298; obj* x_300; obj* x_301; obj* x_303; 
lean::dec(x_285);
x_298 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_300 = l_lean_ir_cpp_emit__cases___main(x_1, x_298, x_2, x_287);
x_301 = lean::cnstr_get(x_300, 0);
lean::inc(x_301);
x_303 = lean::cnstr_get(x_300, 1);
lean::inc(x_303);
lean::dec(x_300);
if (lean::obj_tag(x_301) == 0)
{
obj* x_307; obj* x_310; obj* x_311; 
lean::dec(x_2);
x_307 = lean::cnstr_get(x_301, 0);
lean::inc(x_307);
lean::dec(x_301);
if (lean::is_scalar(x_263)) {
 x_310 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_310 = x_263;
 lean::cnstr_set_tag(x_263, 0);
}
lean::cnstr_set(x_310, 0, x_307);
if (lean::is_scalar(x_272)) {
 x_311 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_311 = x_272;
}
lean::cnstr_set(x_311, 0, x_310);
lean::cnstr_set(x_311, 1, x_303);
return x_311;
}
else
{
obj* x_313; obj* x_316; obj* x_317; obj* x_319; 
lean::dec(x_301);
x_313 = l_lean_ir_cpp_emit__case___main___closed__2;
lean::inc(x_2);
lean::inc(x_313);
x_316 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_313, x_2, x_303);
x_317 = lean::cnstr_get(x_316, 0);
lean::inc(x_317);
x_319 = lean::cnstr_get(x_316, 1);
lean::inc(x_319);
lean::dec(x_316);
if (lean::obj_tag(x_317) == 0)
{
obj* x_323; obj* x_326; obj* x_327; 
lean::dec(x_2);
x_323 = lean::cnstr_get(x_317, 0);
lean::inc(x_323);
lean::dec(x_317);
if (lean::is_scalar(x_263)) {
 x_326 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_326 = x_263;
 lean::cnstr_set_tag(x_263, 0);
}
lean::cnstr_set(x_326, 0, x_323);
if (lean::is_scalar(x_272)) {
 x_327 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_327 = x_272;
}
lean::cnstr_set(x_327, 0, x_326);
lean::cnstr_set(x_327, 1, x_319);
return x_327;
}
else
{
obj* x_332; 
lean::dec(x_317);
lean::dec(x_272);
lean::dec(x_263);
lean::inc(x_281);
x_332 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_281, x_2, x_319);
return x_332;
}
}
}
}
}
}
lbl_8:
{
obj* x_334; obj* x_337; obj* x_338; obj* x_340; obj* x_342; 
lean::dec(x_7);
x_334 = l_lean_ir_cpp_emit__case___main___closed__3;
lean::inc(x_2);
lean::inc(x_334);
x_337 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_334, x_2, x_3);
x_338 = lean::cnstr_get(x_337, 0);
lean::inc(x_338);
x_340 = lean::cnstr_get(x_337, 1);
lean::inc(x_340);
if (lean::is_shared(x_337)) {
 lean::dec(x_337);
 x_342 = lean::box(0);
} else {
 lean::cnstr_release(x_337, 0);
 lean::cnstr_release(x_337, 1);
 x_342 = x_337;
}
if (lean::obj_tag(x_338) == 0)
{
obj* x_346; obj* x_348; obj* x_349; obj* x_350; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_346 = lean::cnstr_get(x_338, 0);
lean::inc(x_346);
if (lean::is_shared(x_338)) {
 lean::dec(x_338);
 x_348 = lean::box(0);
} else {
 lean::cnstr_release(x_338, 0);
 x_348 = x_338;
}
if (lean::is_scalar(x_348)) {
 x_349 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_349 = x_348;
}
lean::cnstr_set(x_349, 0, x_346);
if (lean::is_scalar(x_342)) {
 x_350 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_350 = x_342;
}
lean::cnstr_set(x_350, 0, x_349);
lean::cnstr_set(x_350, 1, x_340);
return x_350;
}
else
{
obj* x_352; obj* x_353; obj* x_356; obj* x_357; obj* x_359; 
lean::dec(x_342);
if (lean::is_shared(x_338)) {
 lean::dec(x_338);
 x_352 = lean::box(0);
} else {
 lean::cnstr_release(x_338, 0);
 x_352 = x_338;
}
x_353 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_353);
x_356 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_353, x_2, x_340);
x_357 = lean::cnstr_get(x_356, 0);
lean::inc(x_357);
x_359 = lean::cnstr_get(x_356, 1);
lean::inc(x_359);
lean::dec(x_356);
if (lean::obj_tag(x_357) == 0)
{
obj* x_363; obj* x_366; 
lean::dec(x_0);
x_363 = lean::cnstr_get(x_357, 0);
lean::inc(x_363);
lean::dec(x_357);
if (lean::is_scalar(x_352)) {
 x_366 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_366 = x_352;
 lean::cnstr_set_tag(x_352, 0);
}
lean::cnstr_set(x_366, 0, x_363);
x_4 = x_366;
x_5 = x_359;
goto lbl_6;
}
else
{
obj* x_369; obj* x_370; obj* x_372; 
lean::dec(x_357);
lean::inc(x_2);
x_369 = l_lean_ir_cpp_emit__var(x_0, x_2, x_359);
x_370 = lean::cnstr_get(x_369, 0);
lean::inc(x_370);
x_372 = lean::cnstr_get(x_369, 1);
lean::inc(x_372);
lean::dec(x_369);
if (lean::obj_tag(x_370) == 0)
{
obj* x_375; obj* x_378; 
x_375 = lean::cnstr_get(x_370, 0);
lean::inc(x_375);
lean::dec(x_370);
if (lean::is_scalar(x_352)) {
 x_378 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_378 = x_352;
 lean::cnstr_set_tag(x_352, 0);
}
lean::cnstr_set(x_378, 0, x_375);
x_4 = x_378;
x_5 = x_372;
goto lbl_6;
}
else
{
obj* x_379; obj* x_382; obj* x_385; obj* x_386; obj* x_388; 
x_379 = lean::cnstr_get(x_370, 0);
lean::inc(x_379);
lean::dec(x_370);
x_382 = l_option_has__repr___rarg___closed__3;
lean::inc(x_2);
lean::inc(x_382);
x_385 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_382, x_2, x_372);
x_386 = lean::cnstr_get(x_385, 0);
lean::inc(x_386);
x_388 = lean::cnstr_get(x_385, 1);
lean::inc(x_388);
lean::dec(x_385);
if (lean::obj_tag(x_386) == 0)
{
obj* x_392; obj* x_395; 
lean::dec(x_379);
x_392 = lean::cnstr_get(x_386, 0);
lean::inc(x_392);
lean::dec(x_386);
if (lean::is_scalar(x_352)) {
 x_395 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_395 = x_352;
 lean::cnstr_set_tag(x_352, 0);
}
lean::cnstr_set(x_395, 0, x_392);
x_4 = x_395;
x_5 = x_388;
goto lbl_6;
}
else
{
obj* x_397; 
lean::dec(x_386);
if (lean::is_scalar(x_352)) {
 x_397 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_397 = x_352;
}
lean::cnstr_set(x_397, 0, x_379);
x_4 = x_397;
x_5 = x_388;
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
lean::dec(x_23);
lean::dec(x_26);
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
lean::dec(x_46);
lean::dec(x_39);
lean::dec(x_92);
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
x_17 = l_int_repr___main___closed__2;
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
case 11:
{
obj* x_112; obj* x_113; obj* x_115; 
lean::inc(x_5);
x_112 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_113 = lean::cnstr_get(x_112, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_112, 1);
lean::inc(x_115);
lean::dec(x_112);
if (lean::obj_tag(x_113) == 0)
{
obj* x_118; obj* x_120; obj* x_121; 
x_118 = lean::cnstr_get(x_113, 0);
lean::inc(x_118);
if (lean::is_shared(x_113)) {
 lean::dec(x_113);
 x_120 = lean::box(0);
} else {
 lean::cnstr_release(x_113, 0);
 x_120 = x_113;
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_118);
x_9 = x_121;
x_10 = x_115;
goto lbl_11;
}
else
{
obj* x_123; obj* x_126; obj* x_127; obj* x_129; 
lean::dec(x_113);
x_123 = l_lean_ir_cpp_emit__assign__binop___closed__37;
lean::inc(x_5);
lean::inc(x_123);
x_126 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_123, x_5, x_115);
x_127 = lean::cnstr_get(x_126, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_126, 1);
lean::inc(x_129);
lean::dec(x_126);
x_9 = x_127;
x_10 = x_129;
goto lbl_11;
}
}
default:
{
obj* x_132; 
x_132 = lean::box(0);
x_7 = x_132;
goto lbl_8;
}
}
}
case 24:
{
obj* x_134; obj* x_135; obj* x_137; obj* x_139; 
lean::inc(x_5);
x_134 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
x_137 = lean::cnstr_get(x_134, 1);
lean::inc(x_137);
if (lean::is_shared(x_134)) {
 lean::dec(x_134);
 x_139 = lean::box(0);
} else {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_release(x_134, 1);
 x_139 = x_134;
}
if (lean::obj_tag(x_135) == 0)
{
obj* x_143; obj* x_145; obj* x_146; obj* x_147; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_143 = lean::cnstr_get(x_135, 0);
lean::inc(x_143);
if (lean::is_shared(x_135)) {
 lean::dec(x_135);
 x_145 = lean::box(0);
} else {
 lean::cnstr_release(x_135, 0);
 x_145 = x_135;
}
if (lean::is_scalar(x_145)) {
 x_146 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_146 = x_145;
}
lean::cnstr_set(x_146, 0, x_143);
if (lean::is_scalar(x_139)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_139;
}
lean::cnstr_set(x_147, 0, x_146);
lean::cnstr_set(x_147, 1, x_137);
return x_147;
}
else
{
obj* x_148; obj* x_149; obj* x_152; obj* x_153; obj* x_155; 
if (lean::is_shared(x_135)) {
 lean::dec(x_135);
 x_148 = lean::box(0);
} else {
 lean::cnstr_release(x_135, 0);
 x_148 = x_135;
}
x_149 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_5);
lean::inc(x_149);
x_152 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_149, x_5, x_137);
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_152, 1);
lean::inc(x_155);
lean::dec(x_152);
if (lean::obj_tag(x_153) == 0)
{
obj* x_161; obj* x_164; obj* x_165; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_161 = lean::cnstr_get(x_153, 0);
lean::inc(x_161);
lean::dec(x_153);
if (lean::is_scalar(x_148)) {
 x_164 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_164 = x_148;
 lean::cnstr_set_tag(x_148, 0);
}
lean::cnstr_set(x_164, 0, x_161);
if (lean::is_scalar(x_139)) {
 x_165 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_165 = x_139;
}
lean::cnstr_set(x_165, 0, x_164);
lean::cnstr_set(x_165, 1, x_155);
return x_165;
}
else
{
obj* x_169; obj* x_172; 
lean::dec(x_153);
lean::dec(x_139);
lean::dec(x_148);
x_169 = lean::cnstr_get(x_5, 1);
lean::inc(x_169);
lean::inc(x_4);
x_172 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_169, x_4);
if (lean::obj_tag(x_172) == 0)
{
obj* x_173; obj* x_176; obj* x_177; obj* x_179; 
x_173 = l_lean_ir_cpp_emit__assign__binop___closed__38;
lean::inc(x_5);
lean::inc(x_173);
x_176 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_173, x_5, x_155);
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_176, 1);
lean::inc(x_179);
lean::dec(x_176);
x_9 = x_177;
x_10 = x_179;
goto lbl_11;
}
else
{
obj* x_182; uint8 x_185; obj* x_187; obj* x_188; uint8 x_189; 
x_182 = lean::cnstr_get(x_172, 0);
lean::inc(x_182);
lean::dec(x_172);
x_185 = lean::unbox(x_182);
lean::dec(x_182);
x_187 = l_lean_ir_type2id___main(x_185);
x_188 = l_lean_ir_valid__assign__unop__types___closed__1;
x_189 = lean::nat_dec_eq(x_187, x_188);
lean::dec(x_187);
if (x_189 == 0)
{
obj* x_191; obj* x_194; obj* x_195; obj* x_197; 
x_191 = l_lean_ir_cpp_emit__assign__binop___closed__38;
lean::inc(x_5);
lean::inc(x_191);
x_194 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_191, x_5, x_155);
x_195 = lean::cnstr_get(x_194, 0);
lean::inc(x_195);
x_197 = lean::cnstr_get(x_194, 1);
lean::inc(x_197);
lean::dec(x_194);
x_9 = x_195;
x_10 = x_197;
goto lbl_11;
}
else
{
obj* x_200; obj* x_203; obj* x_204; obj* x_206; 
x_200 = l_lean_ir_cpp_emit__assign__binop___closed__39;
lean::inc(x_5);
lean::inc(x_200);
x_203 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_200, x_5, x_155);
x_204 = lean::cnstr_get(x_203, 0);
lean::inc(x_204);
x_206 = lean::cnstr_get(x_203, 1);
lean::inc(x_206);
lean::dec(x_203);
x_9 = x_204;
x_10 = x_206;
goto lbl_11;
}
}
}
}
}
case 25:
{
obj* x_210; obj* x_211; obj* x_213; 
lean::inc(x_5);
x_210 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_211 = lean::cnstr_get(x_210, 0);
lean::inc(x_211);
x_213 = lean::cnstr_get(x_210, 1);
lean::inc(x_213);
lean::dec(x_210);
if (lean::obj_tag(x_211) == 0)
{
obj* x_216; obj* x_218; obj* x_219; 
x_216 = lean::cnstr_get(x_211, 0);
lean::inc(x_216);
if (lean::is_shared(x_211)) {
 lean::dec(x_211);
 x_218 = lean::box(0);
} else {
 lean::cnstr_release(x_211, 0);
 x_218 = x_211;
}
if (lean::is_scalar(x_218)) {
 x_219 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_219 = x_218;
}
lean::cnstr_set(x_219, 0, x_216);
x_9 = x_219;
x_10 = x_213;
goto lbl_11;
}
else
{
obj* x_221; obj* x_224; obj* x_225; obj* x_227; 
lean::dec(x_211);
x_221 = l_lean_ir_cpp_emit__assign__binop___closed__40;
lean::inc(x_5);
lean::inc(x_221);
x_224 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_221, x_5, x_213);
x_225 = lean::cnstr_get(x_224, 0);
lean::inc(x_225);
x_227 = lean::cnstr_get(x_224, 1);
lean::inc(x_227);
lean::dec(x_224);
x_9 = x_225;
x_10 = x_227;
goto lbl_11;
}
}
default:
{
obj* x_231; obj* x_232; obj* x_234; 
lean::inc(x_5);
x_231 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_232 = lean::cnstr_get(x_231, 0);
lean::inc(x_232);
x_234 = lean::cnstr_get(x_231, 1);
lean::inc(x_234);
lean::dec(x_231);
if (lean::obj_tag(x_232) == 0)
{
obj* x_237; obj* x_239; obj* x_240; 
x_237 = lean::cnstr_get(x_232, 0);
lean::inc(x_237);
if (lean::is_shared(x_232)) {
 lean::dec(x_232);
 x_239 = lean::box(0);
} else {
 lean::cnstr_release(x_232, 0);
 x_239 = x_232;
}
if (lean::is_scalar(x_239)) {
 x_240 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_240 = x_239;
}
lean::cnstr_set(x_240, 0, x_237);
x_9 = x_240;
x_10 = x_234;
goto lbl_11;
}
else
{
obj* x_242; obj* x_245; obj* x_246; obj* x_248; 
lean::dec(x_232);
x_242 = l_lean_ir_cpp_emit__assign__binop___closed__41;
lean::inc(x_5);
lean::inc(x_242);
x_245 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_242, x_5, x_234);
x_246 = lean::cnstr_get(x_245, 0);
lean::inc(x_246);
x_248 = lean::cnstr_get(x_245, 1);
lean::inc(x_248);
lean::dec(x_245);
x_9 = x_246;
x_10 = x_248;
goto lbl_11;
}
}
}
lbl_8:
{
obj* x_252; obj* x_253; obj* x_256; obj* x_257; obj* x_259; 
lean::dec(x_7);
lean::inc(x_5);
x_256 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_257 = lean::cnstr_get(x_256, 0);
lean::inc(x_257);
x_259 = lean::cnstr_get(x_256, 1);
lean::inc(x_259);
lean::dec(x_256);
if (lean::obj_tag(x_257) == 0)
{
obj* x_262; obj* x_264; obj* x_265; 
x_262 = lean::cnstr_get(x_257, 0);
lean::inc(x_262);
if (lean::is_shared(x_257)) {
 lean::dec(x_257);
 x_264 = lean::box(0);
} else {
 lean::cnstr_release(x_257, 0);
 x_264 = x_257;
}
if (lean::is_scalar(x_264)) {
 x_265 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_265 = x_264;
}
lean::cnstr_set(x_265, 0, x_262);
x_252 = x_265;
x_253 = x_259;
goto lbl_254;
}
else
{
obj* x_266; obj* x_267; obj* x_270; obj* x_271; obj* x_273; 
if (lean::is_shared(x_257)) {
 lean::dec(x_257);
 x_266 = lean::box(0);
} else {
 lean::cnstr_release(x_257, 0);
 x_266 = x_257;
}
x_267 = l_lean_ir_cpp_emit__assign__binop___closed__1;
lean::inc(x_5);
lean::inc(x_267);
x_270 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_267, x_5, x_259);
x_271 = lean::cnstr_get(x_270, 0);
lean::inc(x_271);
x_273 = lean::cnstr_get(x_270, 1);
lean::inc(x_273);
lean::dec(x_270);
if (lean::obj_tag(x_271) == 0)
{
obj* x_276; obj* x_279; 
x_276 = lean::cnstr_get(x_271, 0);
lean::inc(x_276);
lean::dec(x_271);
if (lean::is_scalar(x_266)) {
 x_279 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_279 = x_266;
 lean::cnstr_set_tag(x_266, 0);
}
lean::cnstr_set(x_279, 0, x_276);
x_252 = x_279;
x_253 = x_273;
goto lbl_254;
}
else
{
obj* x_283; obj* x_284; obj* x_286; 
lean::dec(x_271);
lean::dec(x_266);
lean::inc(x_5);
x_283 = l_lean_ir_cpp_emit__template__param(x_1, x_5, x_273);
x_284 = lean::cnstr_get(x_283, 0);
lean::inc(x_284);
x_286 = lean::cnstr_get(x_283, 1);
lean::inc(x_286);
lean::dec(x_283);
x_252 = x_284;
x_253 = x_286;
goto lbl_254;
}
}
lbl_254:
{
if (lean::obj_tag(x_252) == 0)
{
obj* x_292; obj* x_294; obj* x_295; obj* x_296; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_292 = lean::cnstr_get(x_252, 0);
lean::inc(x_292);
if (lean::is_shared(x_252)) {
 lean::dec(x_252);
 x_294 = lean::box(0);
} else {
 lean::cnstr_release(x_252, 0);
 x_294 = x_252;
}
if (lean::is_scalar(x_294)) {
 x_295 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_295 = x_294;
}
lean::cnstr_set(x_295, 0, x_292);
x_296 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_296, 0, x_295);
lean::cnstr_set(x_296, 1, x_253);
return x_296;
}
else
{
obj* x_297; obj* x_298; obj* x_301; obj* x_302; obj* x_304; obj* x_306; 
if (lean::is_shared(x_252)) {
 lean::dec(x_252);
 x_297 = lean::box(0);
} else {
 lean::cnstr_release(x_252, 0);
 x_297 = x_252;
}
x_298 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_298);
x_301 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_298, x_5, x_253);
x_302 = lean::cnstr_get(x_301, 0);
lean::inc(x_302);
x_304 = lean::cnstr_get(x_301, 1);
lean::inc(x_304);
if (lean::is_shared(x_301)) {
 lean::dec(x_301);
 x_306 = lean::box(0);
} else {
 lean::cnstr_release(x_301, 0);
 lean::cnstr_release(x_301, 1);
 x_306 = x_301;
}
if (lean::obj_tag(x_302) == 0)
{
obj* x_310; obj* x_313; obj* x_314; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_310 = lean::cnstr_get(x_302, 0);
lean::inc(x_310);
lean::dec(x_302);
if (lean::is_scalar(x_297)) {
 x_313 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_313 = x_297;
 lean::cnstr_set_tag(x_297, 0);
}
lean::cnstr_set(x_313, 0, x_310);
if (lean::is_scalar(x_306)) {
 x_314 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_314 = x_306;
}
lean::cnstr_set(x_314, 0, x_313);
lean::cnstr_set(x_314, 1, x_304);
return x_314;
}
else
{
obj* x_317; obj* x_318; obj* x_320; 
lean::dec(x_302);
lean::inc(x_5);
x_317 = l_lean_ir_cpp_emit__var(x_3, x_5, x_304);
x_318 = lean::cnstr_get(x_317, 0);
lean::inc(x_318);
x_320 = lean::cnstr_get(x_317, 1);
lean::inc(x_320);
lean::dec(x_317);
if (lean::obj_tag(x_318) == 0)
{
obj* x_325; obj* x_328; obj* x_329; 
lean::dec(x_5);
lean::dec(x_4);
x_325 = lean::cnstr_get(x_318, 0);
lean::inc(x_325);
lean::dec(x_318);
if (lean::is_scalar(x_297)) {
 x_328 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_328 = x_297;
 lean::cnstr_set_tag(x_297, 0);
}
lean::cnstr_set(x_328, 0, x_325);
if (lean::is_scalar(x_306)) {
 x_329 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_329 = x_306;
}
lean::cnstr_set(x_329, 0, x_328);
lean::cnstr_set(x_329, 1, x_320);
return x_329;
}
else
{
obj* x_331; obj* x_334; obj* x_335; obj* x_337; 
lean::dec(x_318);
x_331 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_331);
x_334 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_331, x_5, x_320);
x_335 = lean::cnstr_get(x_334, 0);
lean::inc(x_335);
x_337 = lean::cnstr_get(x_334, 1);
lean::inc(x_337);
lean::dec(x_334);
if (lean::obj_tag(x_335) == 0)
{
obj* x_342; obj* x_345; obj* x_346; 
lean::dec(x_5);
lean::dec(x_4);
x_342 = lean::cnstr_get(x_335, 0);
lean::inc(x_342);
lean::dec(x_335);
if (lean::is_scalar(x_297)) {
 x_345 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_345 = x_297;
 lean::cnstr_set_tag(x_297, 0);
}
lean::cnstr_set(x_345, 0, x_342);
if (lean::is_scalar(x_306)) {
 x_346 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_346 = x_306;
}
lean::cnstr_set(x_346, 0, x_345);
lean::cnstr_set(x_346, 1, x_337);
return x_346;
}
else
{
obj* x_349; obj* x_350; obj* x_352; 
lean::dec(x_335);
lean::inc(x_5);
x_349 = l_lean_ir_cpp_emit__var(x_4, x_5, x_337);
x_350 = lean::cnstr_get(x_349, 0);
lean::inc(x_350);
x_352 = lean::cnstr_get(x_349, 1);
lean::inc(x_352);
lean::dec(x_349);
if (lean::obj_tag(x_350) == 0)
{
obj* x_356; obj* x_359; obj* x_360; 
lean::dec(x_5);
x_356 = lean::cnstr_get(x_350, 0);
lean::inc(x_356);
lean::dec(x_350);
if (lean::is_scalar(x_297)) {
 x_359 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_359 = x_297;
 lean::cnstr_set_tag(x_297, 0);
}
lean::cnstr_set(x_359, 0, x_356);
if (lean::is_scalar(x_306)) {
 x_360 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_360 = x_306;
}
lean::cnstr_set(x_360, 0, x_359);
lean::cnstr_set(x_360, 1, x_352);
return x_360;
}
else
{
obj* x_361; obj* x_364; obj* x_366; obj* x_367; obj* x_369; 
x_361 = lean::cnstr_get(x_350, 0);
lean::inc(x_361);
lean::dec(x_350);
x_364 = l_option_has__repr___rarg___closed__3;
lean::inc(x_364);
x_366 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_364, x_5, x_352);
x_367 = lean::cnstr_get(x_366, 0);
lean::inc(x_367);
x_369 = lean::cnstr_get(x_366, 1);
lean::inc(x_369);
lean::dec(x_366);
if (lean::obj_tag(x_367) == 0)
{
obj* x_373; obj* x_376; obj* x_377; 
lean::dec(x_361);
x_373 = lean::cnstr_get(x_367, 0);
lean::inc(x_373);
lean::dec(x_367);
if (lean::is_scalar(x_297)) {
 x_376 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_376 = x_297;
 lean::cnstr_set_tag(x_297, 0);
}
lean::cnstr_set(x_376, 0, x_373);
if (lean::is_scalar(x_306)) {
 x_377 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_377 = x_306;
}
lean::cnstr_set(x_377, 0, x_376);
lean::cnstr_set(x_377, 1, x_369);
return x_377;
}
else
{
obj* x_379; obj* x_380; 
lean::dec(x_367);
if (lean::is_scalar(x_297)) {
 x_379 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_379 = x_297;
}
lean::cnstr_set(x_379, 0, x_361);
if (lean::is_scalar(x_306)) {
 x_380 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_380 = x_306;
}
lean::cnstr_set(x_380, 0, x_379);
lean::cnstr_set(x_380, 1, x_369);
return x_380;
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
obj* x_384; obj* x_386; obj* x_387; obj* x_388; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_384 = lean::cnstr_get(x_9, 0);
lean::inc(x_384);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_386 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_386 = x_9;
}
if (lean::is_scalar(x_386)) {
 x_387 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_387 = x_386;
}
lean::cnstr_set(x_387, 0, x_384);
x_388 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_388, 0, x_387);
lean::cnstr_set(x_388, 1, x_10);
return x_388;
}
else
{
obj* x_389; obj* x_390; obj* x_393; obj* x_394; obj* x_396; obj* x_398; 
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_389 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_389 = x_9;
}
x_390 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_390);
x_393 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_390, x_5, x_10);
x_394 = lean::cnstr_get(x_393, 0);
lean::inc(x_394);
x_396 = lean::cnstr_get(x_393, 1);
lean::inc(x_396);
if (lean::is_shared(x_393)) {
 lean::dec(x_393);
 x_398 = lean::box(0);
} else {
 lean::cnstr_release(x_393, 0);
 lean::cnstr_release(x_393, 1);
 x_398 = x_393;
}
if (lean::obj_tag(x_394) == 0)
{
obj* x_402; obj* x_405; obj* x_406; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_402 = lean::cnstr_get(x_394, 0);
lean::inc(x_402);
lean::dec(x_394);
if (lean::is_scalar(x_389)) {
 x_405 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_405 = x_389;
 lean::cnstr_set_tag(x_389, 0);
}
lean::cnstr_set(x_405, 0, x_402);
if (lean::is_scalar(x_398)) {
 x_406 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_406 = x_398;
}
lean::cnstr_set(x_406, 0, x_405);
lean::cnstr_set(x_406, 1, x_396);
return x_406;
}
else
{
obj* x_409; obj* x_410; obj* x_412; 
lean::dec(x_394);
lean::inc(x_5);
x_409 = l_lean_ir_cpp_emit__var(x_3, x_5, x_396);
x_410 = lean::cnstr_get(x_409, 0);
lean::inc(x_410);
x_412 = lean::cnstr_get(x_409, 1);
lean::inc(x_412);
lean::dec(x_409);
if (lean::obj_tag(x_410) == 0)
{
obj* x_417; obj* x_420; obj* x_421; 
lean::dec(x_5);
lean::dec(x_4);
x_417 = lean::cnstr_get(x_410, 0);
lean::inc(x_417);
lean::dec(x_410);
if (lean::is_scalar(x_389)) {
 x_420 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_420 = x_389;
 lean::cnstr_set_tag(x_389, 0);
}
lean::cnstr_set(x_420, 0, x_417);
if (lean::is_scalar(x_398)) {
 x_421 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_421 = x_398;
}
lean::cnstr_set(x_421, 0, x_420);
lean::cnstr_set(x_421, 1, x_412);
return x_421;
}
else
{
obj* x_423; obj* x_426; obj* x_427; obj* x_429; 
lean::dec(x_410);
x_423 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_423);
x_426 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_423, x_5, x_412);
x_427 = lean::cnstr_get(x_426, 0);
lean::inc(x_427);
x_429 = lean::cnstr_get(x_426, 1);
lean::inc(x_429);
lean::dec(x_426);
if (lean::obj_tag(x_427) == 0)
{
obj* x_434; obj* x_437; obj* x_438; 
lean::dec(x_5);
lean::dec(x_4);
x_434 = lean::cnstr_get(x_427, 0);
lean::inc(x_434);
lean::dec(x_427);
if (lean::is_scalar(x_389)) {
 x_437 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_437 = x_389;
 lean::cnstr_set_tag(x_389, 0);
}
lean::cnstr_set(x_437, 0, x_434);
if (lean::is_scalar(x_398)) {
 x_438 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_438 = x_398;
}
lean::cnstr_set(x_438, 0, x_437);
lean::cnstr_set(x_438, 1, x_429);
return x_438;
}
else
{
obj* x_441; obj* x_442; obj* x_444; 
lean::dec(x_427);
lean::inc(x_5);
x_441 = l_lean_ir_cpp_emit__var(x_4, x_5, x_429);
x_442 = lean::cnstr_get(x_441, 0);
lean::inc(x_442);
x_444 = lean::cnstr_get(x_441, 1);
lean::inc(x_444);
lean::dec(x_441);
if (lean::obj_tag(x_442) == 0)
{
obj* x_448; obj* x_451; obj* x_452; 
lean::dec(x_5);
x_448 = lean::cnstr_get(x_442, 0);
lean::inc(x_448);
lean::dec(x_442);
if (lean::is_scalar(x_389)) {
 x_451 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_451 = x_389;
 lean::cnstr_set_tag(x_389, 0);
}
lean::cnstr_set(x_451, 0, x_448);
if (lean::is_scalar(x_398)) {
 x_452 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_452 = x_398;
}
lean::cnstr_set(x_452, 0, x_451);
lean::cnstr_set(x_452, 1, x_444);
return x_452;
}
else
{
obj* x_453; obj* x_456; obj* x_458; obj* x_459; obj* x_461; 
x_453 = lean::cnstr_get(x_442, 0);
lean::inc(x_453);
lean::dec(x_442);
x_456 = l_option_has__repr___rarg___closed__3;
lean::inc(x_456);
x_458 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_456, x_5, x_444);
x_459 = lean::cnstr_get(x_458, 0);
lean::inc(x_459);
x_461 = lean::cnstr_get(x_458, 1);
lean::inc(x_461);
lean::dec(x_458);
if (lean::obj_tag(x_459) == 0)
{
obj* x_465; obj* x_468; obj* x_469; 
lean::dec(x_453);
x_465 = lean::cnstr_get(x_459, 0);
lean::inc(x_465);
lean::dec(x_459);
if (lean::is_scalar(x_389)) {
 x_468 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_468 = x_389;
 lean::cnstr_set_tag(x_389, 0);
}
lean::cnstr_set(x_468, 0, x_465);
if (lean::is_scalar(x_398)) {
 x_469 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_469 = x_398;
}
lean::cnstr_set(x_469, 0, x_468);
lean::cnstr_set(x_469, 1, x_461);
return x_469;
}
else
{
obj* x_471; obj* x_472; 
lean::dec(x_459);
if (lean::is_scalar(x_389)) {
 x_471 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_471 = x_389;
}
lean::cnstr_set(x_471, 0, x_453);
if (lean::is_scalar(x_398)) {
 x_472 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_472 = x_398;
}
lean::cnstr_set(x_472, 0, x_471);
lean::cnstr_set(x_472, 1, x_461);
return x_472;
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
x_10 = l_int_repr___main___closed__2;
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
case 3:
{
obj* x_3; obj* x_5; 
x_3 = l_lean_ir_cpp_emit__num__suffix___main___closed__1;
lean::inc(x_3);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
return x_5;
}
case 4:
{
obj* x_6; obj* x_8; 
x_6 = l_lean_ir_cpp_emit__num__suffix___main___closed__2;
lean::inc(x_6);
x_8 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_6, x_1, x_2);
return x_8;
}
case 8:
{
obj* x_9; obj* x_11; 
x_9 = l_lean_ir_cpp_emit__num__suffix___main___closed__3;
lean::inc(x_9);
x_11 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_9, x_1, x_2);
return x_11;
}
default:
{
obj* x_13; obj* x_15; 
lean::dec(x_1);
x_13 = l_lean_ir_match__type___closed__5;
lean::inc(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_2);
return x_15;
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
obj* x_0; obj* x_2; 
x_0 = l_uint32__sz;
lean::inc(x_0);
x_2 = lean::nat2int(x_0);
return x_2;
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
lean::dec(x_9);
lean::dec(x_13);
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
case 11:
{
obj* x_134; uint8 x_135; obj* x_136; obj* x_137; obj* x_140; obj* x_141; obj* x_143; 
x_134 = l_lean_ir_cpp_emit__assign__lit___closed__4;
x_135 = lean::int_dec_lt(x_129, x_134);
lean::inc(x_3);
x_140 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
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
x_136 = x_149;
x_137 = x_143;
goto lbl_138;
}
else
{
obj* x_151; obj* x_154; obj* x_155; obj* x_157; 
lean::dec(x_141);
x_151 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
lean::inc(x_151);
x_154 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_151, x_3, x_143);
x_155 = lean::cnstr_get(x_154, 0);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_154, 1);
lean::inc(x_157);
lean::dec(x_154);
x_136 = x_155;
x_137 = x_157;
goto lbl_138;
}
lbl_138:
{
if (lean::obj_tag(x_136) == 0)
{
obj* x_162; obj* x_164; obj* x_165; obj* x_166; 
lean::dec(x_129);
lean::dec(x_3);
x_162 = lean::cnstr_get(x_136, 0);
lean::inc(x_162);
if (lean::is_shared(x_136)) {
 lean::dec(x_136);
 x_164 = lean::box(0);
} else {
 lean::cnstr_release(x_136, 0);
 x_164 = x_136;
}
if (lean::is_scalar(x_164)) {
 x_165 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_165 = x_164;
}
lean::cnstr_set(x_165, 0, x_162);
x_166 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_166, 0, x_165);
lean::cnstr_set(x_166, 1, x_137);
return x_166;
}
else
{
obj* x_167; 
if (lean::is_shared(x_136)) {
 lean::dec(x_136);
 x_167 = lean::box(0);
} else {
 lean::cnstr_release(x_136, 0);
 x_167 = x_136;
}
if (x_135 == 0)
{
obj* x_168; obj* x_171; obj* x_172; obj* x_174; obj* x_176; 
x_168 = l_lean_ir_cpp_emit__assign__lit___closed__5;
lean::inc(x_3);
lean::inc(x_168);
x_171 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_168, x_3, x_137);
x_172 = lean::cnstr_get(x_171, 0);
lean::inc(x_172);
x_174 = lean::cnstr_get(x_171, 1);
lean::inc(x_174);
if (lean::is_shared(x_171)) {
 lean::dec(x_171);
 x_176 = lean::box(0);
} else {
 lean::cnstr_release(x_171, 0);
 lean::cnstr_release(x_171, 1);
 x_176 = x_171;
}
if (lean::obj_tag(x_172) == 0)
{
obj* x_179; obj* x_182; obj* x_183; 
lean::dec(x_129);
lean::dec(x_3);
x_179 = lean::cnstr_get(x_172, 0);
lean::inc(x_179);
lean::dec(x_172);
if (lean::is_scalar(x_167)) {
 x_182 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_182 = x_167;
 lean::cnstr_set_tag(x_167, 0);
}
lean::cnstr_set(x_182, 0, x_179);
if (lean::is_scalar(x_176)) {
 x_183 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_183 = x_176;
}
lean::cnstr_set(x_183, 0, x_182);
lean::cnstr_set(x_183, 1, x_174);
return x_183;
}
else
{
obj* x_186; obj* x_187; obj* x_189; 
lean::dec(x_172);
lean::inc(x_3);
x_186 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_129, x_3, x_174);
x_187 = lean::cnstr_get(x_186, 0);
lean::inc(x_187);
x_189 = lean::cnstr_get(x_186, 1);
lean::inc(x_189);
lean::dec(x_186);
if (lean::obj_tag(x_187) == 0)
{
obj* x_193; obj* x_196; obj* x_197; 
lean::dec(x_3);
x_193 = lean::cnstr_get(x_187, 0);
lean::inc(x_193);
lean::dec(x_187);
if (lean::is_scalar(x_167)) {
 x_196 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_196 = x_167;
 lean::cnstr_set_tag(x_167, 0);
}
lean::cnstr_set(x_196, 0, x_193);
if (lean::is_scalar(x_176)) {
 x_197 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_197 = x_176;
}
lean::cnstr_set(x_197, 0, x_196);
lean::cnstr_set(x_197, 1, x_189);
return x_197;
}
else
{
obj* x_201; obj* x_203; 
lean::dec(x_176);
lean::dec(x_167);
lean::dec(x_187);
x_201 = l_lean_ir_cpp_emit__assign__lit___closed__6;
lean::inc(x_201);
x_203 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_201, x_3, x_189);
return x_203;
}
}
}
else
{
obj* x_204; obj* x_207; obj* x_208; obj* x_210; obj* x_212; 
x_204 = l_lean_ir_cpp_emit__assign__lit___closed__7;
lean::inc(x_3);
lean::inc(x_204);
x_207 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_204, x_3, x_137);
x_208 = lean::cnstr_get(x_207, 0);
lean::inc(x_208);
x_210 = lean::cnstr_get(x_207, 1);
lean::inc(x_210);
if (lean::is_shared(x_207)) {
 lean::dec(x_207);
 x_212 = lean::box(0);
} else {
 lean::cnstr_release(x_207, 0);
 lean::cnstr_release(x_207, 1);
 x_212 = x_207;
}
if (lean::obj_tag(x_208) == 0)
{
obj* x_215; obj* x_218; obj* x_219; 
lean::dec(x_129);
lean::dec(x_3);
x_215 = lean::cnstr_get(x_208, 0);
lean::inc(x_215);
lean::dec(x_208);
if (lean::is_scalar(x_167)) {
 x_218 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_218 = x_167;
 lean::cnstr_set_tag(x_167, 0);
}
lean::cnstr_set(x_218, 0, x_215);
if (lean::is_scalar(x_212)) {
 x_219 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_219 = x_212;
}
lean::cnstr_set(x_219, 0, x_218);
lean::cnstr_set(x_219, 1, x_210);
return x_219;
}
else
{
obj* x_221; obj* x_224; obj* x_225; obj* x_227; 
lean::dec(x_208);
x_221 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_221);
x_224 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_221, x_3, x_210);
x_225 = lean::cnstr_get(x_224, 0);
lean::inc(x_225);
x_227 = lean::cnstr_get(x_224, 1);
lean::inc(x_227);
lean::dec(x_224);
if (lean::obj_tag(x_225) == 0)
{
obj* x_232; obj* x_235; obj* x_236; 
lean::dec(x_129);
lean::dec(x_3);
x_232 = lean::cnstr_get(x_225, 0);
lean::inc(x_232);
lean::dec(x_225);
if (lean::is_scalar(x_167)) {
 x_235 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_235 = x_167;
 lean::cnstr_set_tag(x_167, 0);
}
lean::cnstr_set(x_235, 0, x_232);
if (lean::is_scalar(x_212)) {
 x_236 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_236 = x_212;
}
lean::cnstr_set(x_236, 0, x_235);
lean::cnstr_set(x_236, 1, x_227);
return x_236;
}
else
{
obj* x_239; obj* x_240; obj* x_242; 
lean::dec(x_225);
lean::inc(x_3);
x_239 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_129, x_3, x_227);
x_240 = lean::cnstr_get(x_239, 0);
lean::inc(x_240);
x_242 = lean::cnstr_get(x_239, 1);
lean::inc(x_242);
lean::dec(x_239);
if (lean::obj_tag(x_240) == 0)
{
obj* x_246; obj* x_249; obj* x_250; 
lean::dec(x_3);
x_246 = lean::cnstr_get(x_240, 0);
lean::inc(x_246);
lean::dec(x_240);
if (lean::is_scalar(x_167)) {
 x_249 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_249 = x_167;
 lean::cnstr_set_tag(x_167, 0);
}
lean::cnstr_set(x_249, 0, x_246);
if (lean::is_scalar(x_212)) {
 x_250 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_250 = x_212;
}
lean::cnstr_set(x_250, 0, x_249);
lean::cnstr_set(x_250, 1, x_242);
return x_250;
}
else
{
obj* x_252; obj* x_255; obj* x_256; obj* x_258; 
lean::dec(x_240);
x_252 = l_lean_ir_cpp_emit__num__suffix___main___closed__1;
lean::inc(x_3);
lean::inc(x_252);
x_255 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_252, x_3, x_242);
x_256 = lean::cnstr_get(x_255, 0);
lean::inc(x_256);
x_258 = lean::cnstr_get(x_255, 1);
lean::inc(x_258);
lean::dec(x_255);
if (lean::obj_tag(x_256) == 0)
{
obj* x_262; obj* x_265; obj* x_266; 
lean::dec(x_3);
x_262 = lean::cnstr_get(x_256, 0);
lean::inc(x_262);
lean::dec(x_256);
if (lean::is_scalar(x_167)) {
 x_265 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_265 = x_167;
 lean::cnstr_set_tag(x_167, 0);
}
lean::cnstr_set(x_265, 0, x_262);
if (lean::is_scalar(x_212)) {
 x_266 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_266 = x_212;
}
lean::cnstr_set(x_266, 0, x_265);
lean::cnstr_set(x_266, 1, x_258);
return x_266;
}
else
{
obj* x_267; obj* x_270; obj* x_272; obj* x_273; obj* x_275; 
x_267 = lean::cnstr_get(x_256, 0);
lean::inc(x_267);
lean::dec(x_256);
x_270 = l_option_has__repr___rarg___closed__3;
lean::inc(x_270);
x_272 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_270, x_3, x_258);
x_273 = lean::cnstr_get(x_272, 0);
lean::inc(x_273);
x_275 = lean::cnstr_get(x_272, 1);
lean::inc(x_275);
lean::dec(x_272);
if (lean::obj_tag(x_273) == 0)
{
obj* x_279; obj* x_282; obj* x_283; 
lean::dec(x_267);
x_279 = lean::cnstr_get(x_273, 0);
lean::inc(x_279);
lean::dec(x_273);
if (lean::is_scalar(x_167)) {
 x_282 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_282 = x_167;
 lean::cnstr_set_tag(x_167, 0);
}
lean::cnstr_set(x_282, 0, x_279);
if (lean::is_scalar(x_212)) {
 x_283 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_283 = x_212;
}
lean::cnstr_set(x_283, 0, x_282);
lean::cnstr_set(x_283, 1, x_275);
return x_283;
}
else
{
obj* x_285; obj* x_286; 
lean::dec(x_273);
if (lean::is_scalar(x_167)) {
 x_285 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_285 = x_167;
}
lean::cnstr_set(x_285, 0, x_267);
if (lean::is_scalar(x_212)) {
 x_286 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_286 = x_212;
}
lean::cnstr_set(x_286, 0, x_285);
lean::cnstr_set(x_286, 1, x_275);
return x_286;
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
obj* x_287; 
x_287 = lean::box(0);
x_132 = x_287;
goto lbl_133;
}
}
lbl_133:
{
obj* x_290; obj* x_291; obj* x_293; obj* x_295; 
lean::dec(x_132);
lean::inc(x_3);
x_290 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_291 = lean::cnstr_get(x_290, 0);
lean::inc(x_291);
x_293 = lean::cnstr_get(x_290, 1);
lean::inc(x_293);
if (lean::is_shared(x_290)) {
 lean::dec(x_290);
 x_295 = lean::box(0);
} else {
 lean::cnstr_release(x_290, 0);
 lean::cnstr_release(x_290, 1);
 x_295 = x_290;
}
if (lean::obj_tag(x_291) == 0)
{
obj* x_298; obj* x_300; obj* x_301; obj* x_302; 
lean::dec(x_129);
lean::dec(x_3);
x_298 = lean::cnstr_get(x_291, 0);
lean::inc(x_298);
if (lean::is_shared(x_291)) {
 lean::dec(x_291);
 x_300 = lean::box(0);
} else {
 lean::cnstr_release(x_291, 0);
 x_300 = x_291;
}
if (lean::is_scalar(x_300)) {
 x_301 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_301 = x_300;
}
lean::cnstr_set(x_301, 0, x_298);
if (lean::is_scalar(x_295)) {
 x_302 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_302 = x_295;
}
lean::cnstr_set(x_302, 0, x_301);
lean::cnstr_set(x_302, 1, x_293);
return x_302;
}
else
{
obj* x_303; obj* x_304; obj* x_307; obj* x_308; obj* x_310; 
if (lean::is_shared(x_291)) {
 lean::dec(x_291);
 x_303 = lean::box(0);
} else {
 lean::cnstr_release(x_291, 0);
 x_303 = x_291;
}
x_304 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
lean::inc(x_304);
x_307 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_304, x_3, x_293);
x_308 = lean::cnstr_get(x_307, 0);
lean::inc(x_308);
x_310 = lean::cnstr_get(x_307, 1);
lean::inc(x_310);
lean::dec(x_307);
if (lean::obj_tag(x_308) == 0)
{
obj* x_315; obj* x_318; obj* x_319; 
lean::dec(x_129);
lean::dec(x_3);
x_315 = lean::cnstr_get(x_308, 0);
lean::inc(x_315);
lean::dec(x_308);
if (lean::is_scalar(x_303)) {
 x_318 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_318 = x_303;
 lean::cnstr_set_tag(x_303, 0);
}
lean::cnstr_set(x_318, 0, x_315);
if (lean::is_scalar(x_295)) {
 x_319 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_319 = x_295;
}
lean::cnstr_set(x_319, 0, x_318);
lean::cnstr_set(x_319, 1, x_310);
return x_319;
}
else
{
obj* x_322; obj* x_323; obj* x_325; 
lean::dec(x_308);
lean::inc(x_3);
x_322 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_129, x_3, x_310);
x_323 = lean::cnstr_get(x_322, 0);
lean::inc(x_323);
x_325 = lean::cnstr_get(x_322, 1);
lean::inc(x_325);
lean::dec(x_322);
if (lean::obj_tag(x_323) == 0)
{
obj* x_329; obj* x_332; obj* x_333; 
lean::dec(x_3);
x_329 = lean::cnstr_get(x_323, 0);
lean::inc(x_329);
lean::dec(x_323);
if (lean::is_scalar(x_303)) {
 x_332 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_332 = x_303;
 lean::cnstr_set_tag(x_303, 0);
}
lean::cnstr_set(x_332, 0, x_329);
if (lean::is_scalar(x_295)) {
 x_333 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_333 = x_295;
}
lean::cnstr_set(x_333, 0, x_332);
lean::cnstr_set(x_333, 1, x_325);
return x_333;
}
else
{
obj* x_337; 
lean::dec(x_303);
lean::dec(x_323);
lean::dec(x_295);
x_337 = l_lean_ir_cpp_emit__num__suffix___main(x_1, x_3, x_325);
return x_337;
}
}
}
}
}
default:
{
obj* x_338; obj* x_342; obj* x_343; obj* x_345; obj* x_347; 
x_338 = lean::cnstr_get(x_2, 0);
lean::inc(x_338);
lean::dec(x_2);
lean::inc(x_3);
x_342 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_343 = lean::cnstr_get(x_342, 0);
lean::inc(x_343);
x_345 = lean::cnstr_get(x_342, 1);
lean::inc(x_345);
if (lean::is_shared(x_342)) {
 lean::dec(x_342);
 x_347 = lean::box(0);
} else {
 lean::cnstr_release(x_342, 0);
 lean::cnstr_release(x_342, 1);
 x_347 = x_342;
}
if (lean::obj_tag(x_343) == 0)
{
obj* x_350; obj* x_352; obj* x_353; obj* x_354; 
lean::dec(x_338);
lean::dec(x_3);
x_350 = lean::cnstr_get(x_343, 0);
lean::inc(x_350);
if (lean::is_shared(x_343)) {
 lean::dec(x_343);
 x_352 = lean::box(0);
} else {
 lean::cnstr_release(x_343, 0);
 x_352 = x_343;
}
if (lean::is_scalar(x_352)) {
 x_353 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_353 = x_352;
}
lean::cnstr_set(x_353, 0, x_350);
if (lean::is_scalar(x_347)) {
 x_354 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_354 = x_347;
}
lean::cnstr_set(x_354, 0, x_353);
lean::cnstr_set(x_354, 1, x_345);
return x_354;
}
else
{
obj* x_355; obj* x_356; obj* x_359; obj* x_360; obj* x_362; 
if (lean::is_shared(x_343)) {
 lean::dec(x_343);
 x_355 = lean::box(0);
} else {
 lean::cnstr_release(x_343, 0);
 x_355 = x_343;
}
x_356 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
lean::inc(x_356);
x_359 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_356, x_3, x_345);
x_360 = lean::cnstr_get(x_359, 0);
lean::inc(x_360);
x_362 = lean::cnstr_get(x_359, 1);
lean::inc(x_362);
lean::dec(x_359);
if (lean::obj_tag(x_360) == 0)
{
obj* x_367; obj* x_370; obj* x_371; 
lean::dec(x_338);
lean::dec(x_3);
x_367 = lean::cnstr_get(x_360, 0);
lean::inc(x_367);
lean::dec(x_360);
if (lean::is_scalar(x_355)) {
 x_370 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_370 = x_355;
 lean::cnstr_set_tag(x_355, 0);
}
lean::cnstr_set(x_370, 0, x_367);
if (lean::is_scalar(x_347)) {
 x_371 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_371 = x_347;
}
lean::cnstr_set(x_371, 0, x_370);
lean::cnstr_set(x_371, 1, x_362);
return x_371;
}
else
{
obj* x_375; 
lean::dec(x_360);
lean::dec(x_355);
lean::dec(x_347);
x_375 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_338, x_3, x_362);
return x_375;
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
obj* x_6; obj* x_8; 
lean::dec(x_0);
lean::dec(x_2);
x_6 = l_lean_ir_cpp_emit__apply___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; uint8 x_17; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 1);
lean::inc(x_11);
x_13 = lean::mk_nat_obj(0u);
lean::inc(x_11);
x_15 = l_list_length__aux___main___rarg(x_11, x_13);
x_16 = l_lean_closure__max__args;
x_17 = lean::nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_27; 
lean::dec(x_9);
lean::dec(x_11);
lean::inc(x_2);
x_24 = l_lean_ir_cpp_emit__var(x_0, x_2, x_3);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_30; obj* x_32; obj* x_33; 
x_30 = lean::cnstr_get(x_25, 0);
lean::inc(x_30);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 x_32 = x_25;
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
x_20 = x_33;
x_21 = x_27;
goto lbl_22;
}
else
{
obj* x_35; obj* x_38; obj* x_39; obj* x_41; 
lean::dec(x_25);
x_35 = l_lean_ir_cpp_emit__apply___closed__3;
lean::inc(x_2);
lean::inc(x_35);
x_38 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_35, x_2, x_27);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
x_20 = x_39;
x_21 = x_41;
goto lbl_22;
}
lbl_22:
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_47; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_15);
lean::dec(x_1);
lean::dec(x_2);
x_47 = lean::cnstr_get(x_20, 0);
lean::inc(x_47);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_49 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_49 = x_20;
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_47);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_21);
return x_51;
}
else
{
obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; 
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_52 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_52 = x_20;
}
lean::inc(x_2);
x_54 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_15, x_2, x_21);
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
obj* x_62; obj* x_65; obj* x_66; 
lean::dec(x_1);
lean::dec(x_2);
x_62 = lean::cnstr_get(x_55, 0);
lean::inc(x_62);
lean::dec(x_55);
if (lean::is_scalar(x_52)) {
 x_65 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_65 = x_52;
 lean::cnstr_set_tag(x_52, 0);
}
lean::cnstr_set(x_65, 0, x_62);
if (lean::is_scalar(x_59)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_59;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_57);
return x_66;
}
else
{
obj* x_68; obj* x_71; obj* x_72; obj* x_74; 
lean::dec(x_55);
x_68 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_68);
x_71 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_68, x_2, x_57);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
lean::dec(x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_79; obj* x_82; obj* x_83; 
lean::dec(x_1);
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
if (lean::is_scalar(x_59)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_59;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_74);
return x_83;
}
else
{
obj* x_85; obj* x_86; obj* x_90; obj* x_91; obj* x_93; 
lean::dec(x_72);
x_85 = l_lean_ir_cpp_emit__apply___closed__2;
x_86 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_2);
lean::inc(x_86);
lean::inc(x_85);
x_90 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_85, x_86, x_1, x_2, x_74);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
if (lean::obj_tag(x_91) == 0)
{
obj* x_97; obj* x_100; obj* x_101; 
lean::dec(x_2);
x_97 = lean::cnstr_get(x_91, 0);
lean::inc(x_97);
lean::dec(x_91);
if (lean::is_scalar(x_52)) {
 x_100 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_100 = x_52;
 lean::cnstr_set_tag(x_52, 0);
}
lean::cnstr_set(x_100, 0, x_97);
if (lean::is_scalar(x_59)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_59;
}
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_93);
return x_101;
}
else
{
obj* x_102; obj* x_105; obj* x_107; obj* x_108; obj* x_110; 
x_102 = lean::cnstr_get(x_91, 0);
lean::inc(x_102);
lean::dec(x_91);
x_105 = l_option_has__repr___rarg___closed__3;
lean::inc(x_105);
x_107 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_105, x_2, x_93);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_107, 1);
lean::inc(x_110);
lean::dec(x_107);
if (lean::obj_tag(x_108) == 0)
{
obj* x_114; obj* x_117; obj* x_118; 
lean::dec(x_102);
x_114 = lean::cnstr_get(x_108, 0);
lean::inc(x_114);
lean::dec(x_108);
if (lean::is_scalar(x_52)) {
 x_117 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_117 = x_52;
 lean::cnstr_set_tag(x_52, 0);
}
lean::cnstr_set(x_117, 0, x_114);
if (lean::is_scalar(x_59)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_59;
}
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_110);
return x_118;
}
else
{
obj* x_120; obj* x_121; 
lean::dec(x_108);
if (lean::is_scalar(x_52)) {
 x_120 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_120 = x_52;
}
lean::cnstr_set(x_120, 0, x_102);
if (lean::is_scalar(x_59)) {
 x_121 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_121 = x_59;
}
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_110);
return x_121;
}
}
}
}
}
}
}
else
{
obj* x_123; obj* x_124; obj* x_126; obj* x_127; obj* x_129; obj* x_130; obj* x_132; obj* x_133; obj* x_135; obj* x_138; obj* x_139; obj* x_141; 
lean::dec(x_1);
x_135 = l_lean_ir_cpp_emit__apply___closed__8;
lean::inc(x_2);
lean::inc(x_135);
x_138 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_135, x_2, x_3);
x_139 = lean::cnstr_get(x_138, 0);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_138, 1);
lean::inc(x_141);
lean::dec(x_138);
if (lean::obj_tag(x_139) == 0)
{
obj* x_144; obj* x_146; obj* x_147; 
x_144 = lean::cnstr_get(x_139, 0);
lean::inc(x_144);
if (lean::is_shared(x_139)) {
 lean::dec(x_139);
 x_146 = lean::box(0);
} else {
 lean::cnstr_release(x_139, 0);
 x_146 = x_139;
}
if (lean::is_scalar(x_146)) {
 x_147 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_147 = x_146;
}
lean::cnstr_set(x_147, 0, x_144);
x_132 = x_147;
x_133 = x_141;
goto lbl_134;
}
else
{
obj* x_148; obj* x_151; obj* x_152; obj* x_154; 
if (lean::is_shared(x_139)) {
 lean::dec(x_139);
 x_148 = lean::box(0);
} else {
 lean::cnstr_release(x_139, 0);
 x_148 = x_139;
}
lean::inc(x_2);
lean::inc(x_15);
x_151 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_15, x_2, x_141);
x_152 = lean::cnstr_get(x_151, 0);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_151, 1);
lean::inc(x_154);
lean::dec(x_151);
if (lean::obj_tag(x_152) == 0)
{
obj* x_157; obj* x_160; 
x_157 = lean::cnstr_get(x_152, 0);
lean::inc(x_157);
lean::dec(x_152);
if (lean::is_scalar(x_148)) {
 x_160 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_160 = x_148;
 lean::cnstr_set_tag(x_148, 0);
}
lean::cnstr_set(x_160, 0, x_157);
x_132 = x_160;
x_133 = x_154;
goto lbl_134;
}
else
{
obj* x_163; obj* x_166; obj* x_167; obj* x_169; 
lean::dec(x_152);
lean::dec(x_148);
x_163 = l_lean_ir_cpp_emit__apply___closed__9;
lean::inc(x_2);
lean::inc(x_163);
x_166 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_163, x_2, x_154);
x_167 = lean::cnstr_get(x_166, 0);
lean::inc(x_167);
x_169 = lean::cnstr_get(x_166, 1);
lean::inc(x_169);
lean::dec(x_166);
x_132 = x_167;
x_133 = x_169;
goto lbl_134;
}
}
lbl_125:
{
if (lean::obj_tag(x_123) == 0)
{
obj* x_173; obj* x_175; obj* x_176; obj* x_177; 
lean::dec(x_2);
x_173 = lean::cnstr_get(x_123, 0);
lean::inc(x_173);
if (lean::is_shared(x_123)) {
 lean::dec(x_123);
 x_175 = lean::box(0);
} else {
 lean::cnstr_release(x_123, 0);
 x_175 = x_123;
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_173);
x_177 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_177, 0, x_176);
lean::cnstr_set(x_177, 1, x_124);
return x_177;
}
else
{
obj* x_179; obj* x_181; 
lean::dec(x_123);
x_179 = l_lean_ir_cpp_emit__apply___closed__4;
lean::inc(x_179);
x_181 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_179, x_2, x_124);
return x_181;
}
}
lbl_128:
{
if (lean::obj_tag(x_126) == 0)
{
obj* x_182; obj* x_184; obj* x_185; 
x_182 = lean::cnstr_get(x_126, 0);
lean::inc(x_182);
if (lean::is_shared(x_126)) {
 lean::dec(x_126);
 x_184 = lean::box(0);
} else {
 lean::cnstr_release(x_126, 0);
 x_184 = x_126;
}
if (lean::is_scalar(x_184)) {
 x_185 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_185 = x_184;
}
lean::cnstr_set(x_185, 0, x_182);
x_123 = x_185;
x_124 = x_127;
goto lbl_125;
}
else
{
obj* x_186; obj* x_187; obj* x_190; obj* x_191; obj* x_193; 
if (lean::is_shared(x_126)) {
 lean::dec(x_126);
 x_186 = lean::box(0);
} else {
 lean::cnstr_release(x_126, 0);
 x_186 = x_126;
}
x_187 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_187);
x_190 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_187, x_2, x_127);
x_191 = lean::cnstr_get(x_190, 0);
lean::inc(x_191);
x_193 = lean::cnstr_get(x_190, 1);
lean::inc(x_193);
lean::dec(x_190);
if (lean::obj_tag(x_191) == 0)
{
obj* x_196; obj* x_199; 
x_196 = lean::cnstr_get(x_191, 0);
lean::inc(x_196);
lean::dec(x_191);
if (lean::is_scalar(x_186)) {
 x_199 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_199 = x_186;
 lean::cnstr_set_tag(x_186, 0);
}
lean::cnstr_set(x_199, 0, x_196);
x_123 = x_199;
x_124 = x_193;
goto lbl_125;
}
else
{
obj* x_201; obj* x_204; obj* x_205; obj* x_207; 
lean::dec(x_191);
x_201 = l_lean_ir_cpp_emit__apply___closed__5;
lean::inc(x_2);
lean::inc(x_201);
x_204 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_201, x_2, x_193);
x_205 = lean::cnstr_get(x_204, 0);
lean::inc(x_205);
x_207 = lean::cnstr_get(x_204, 1);
lean::inc(x_207);
lean::dec(x_204);
if (lean::obj_tag(x_205) == 0)
{
obj* x_210; obj* x_213; 
x_210 = lean::cnstr_get(x_205, 0);
lean::inc(x_210);
lean::dec(x_205);
if (lean::is_scalar(x_186)) {
 x_213 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_213 = x_186;
 lean::cnstr_set_tag(x_186, 0);
}
lean::cnstr_set(x_213, 0, x_210);
x_123 = x_213;
x_124 = x_207;
goto lbl_125;
}
else
{
obj* x_214; obj* x_217; obj* x_220; obj* x_221; obj* x_223; 
x_214 = lean::cnstr_get(x_205, 0);
lean::inc(x_214);
lean::dec(x_205);
x_217 = l_option_has__repr___rarg___closed__3;
lean::inc(x_2);
lean::inc(x_217);
x_220 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_217, x_2, x_207);
x_221 = lean::cnstr_get(x_220, 0);
lean::inc(x_221);
x_223 = lean::cnstr_get(x_220, 1);
lean::inc(x_223);
lean::dec(x_220);
if (lean::obj_tag(x_221) == 0)
{
obj* x_227; obj* x_230; 
lean::dec(x_214);
x_227 = lean::cnstr_get(x_221, 0);
lean::inc(x_227);
lean::dec(x_221);
if (lean::is_scalar(x_186)) {
 x_230 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_230 = x_186;
 lean::cnstr_set_tag(x_186, 0);
}
lean::cnstr_set(x_230, 0, x_227);
x_123 = x_230;
x_124 = x_223;
goto lbl_125;
}
else
{
obj* x_232; 
lean::dec(x_221);
if (lean::is_scalar(x_186)) {
 x_232 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_232 = x_186;
}
lean::cnstr_set(x_232, 0, x_214);
x_123 = x_232;
x_124 = x_223;
goto lbl_125;
}
}
}
}
}
lbl_131:
{
if (lean::obj_tag(x_129) == 0)
{
obj* x_235; obj* x_237; obj* x_238; 
lean::dec(x_15);
lean::dec(x_9);
x_235 = lean::cnstr_get(x_129, 0);
lean::inc(x_235);
if (lean::is_shared(x_129)) {
 lean::dec(x_129);
 x_237 = lean::box(0);
} else {
 lean::cnstr_release(x_129, 0);
 x_237 = x_129;
}
if (lean::is_scalar(x_237)) {
 x_238 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_238 = x_237;
}
lean::cnstr_set(x_238, 0, x_235);
x_123 = x_238;
x_124 = x_130;
goto lbl_125;
}
else
{
obj* x_239; obj* x_240; obj* x_243; obj* x_244; obj* x_246; 
if (lean::is_shared(x_129)) {
 lean::dec(x_129);
 x_239 = lean::box(0);
} else {
 lean::cnstr_release(x_129, 0);
 x_239 = x_129;
}
x_240 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_240);
x_243 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_240, x_2, x_130);
x_244 = lean::cnstr_get(x_243, 0);
lean::inc(x_244);
x_246 = lean::cnstr_get(x_243, 1);
lean::inc(x_246);
lean::dec(x_243);
if (lean::obj_tag(x_244) == 0)
{
obj* x_251; obj* x_254; 
lean::dec(x_15);
lean::dec(x_9);
x_251 = lean::cnstr_get(x_244, 0);
lean::inc(x_251);
lean::dec(x_244);
if (lean::is_scalar(x_239)) {
 x_254 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_254 = x_239;
 lean::cnstr_set_tag(x_239, 0);
}
lean::cnstr_set(x_254, 0, x_251);
x_123 = x_254;
x_124 = x_246;
goto lbl_125;
}
else
{
obj* x_257; obj* x_258; obj* x_260; 
lean::dec(x_244);
lean::inc(x_2);
x_257 = l_lean_ir_cpp_emit__var(x_9, x_2, x_246);
x_258 = lean::cnstr_get(x_257, 0);
lean::inc(x_258);
x_260 = lean::cnstr_get(x_257, 1);
lean::inc(x_260);
lean::dec(x_257);
if (lean::obj_tag(x_258) == 0)
{
obj* x_264; obj* x_267; 
lean::dec(x_15);
x_264 = lean::cnstr_get(x_258, 0);
lean::inc(x_264);
lean::dec(x_258);
if (lean::is_scalar(x_239)) {
 x_267 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_267 = x_239;
 lean::cnstr_set_tag(x_239, 0);
}
lean::cnstr_set(x_267, 0, x_264);
x_126 = x_267;
x_127 = x_260;
goto lbl_128;
}
else
{
obj* x_269; obj* x_272; obj* x_273; obj* x_275; 
lean::dec(x_258);
x_269 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_269);
x_272 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_269, x_2, x_260);
x_273 = lean::cnstr_get(x_272, 0);
lean::inc(x_273);
x_275 = lean::cnstr_get(x_272, 1);
lean::inc(x_275);
lean::dec(x_272);
if (lean::obj_tag(x_273) == 0)
{
obj* x_279; obj* x_282; 
lean::dec(x_15);
x_279 = lean::cnstr_get(x_273, 0);
lean::inc(x_279);
lean::dec(x_273);
if (lean::is_scalar(x_239)) {
 x_282 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_282 = x_239;
 lean::cnstr_set_tag(x_239, 0);
}
lean::cnstr_set(x_282, 0, x_279);
x_126 = x_282;
x_127 = x_275;
goto lbl_128;
}
else
{
obj* x_286; obj* x_287; obj* x_289; 
lean::dec(x_273);
lean::dec(x_239);
lean::inc(x_2);
x_286 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_15, x_2, x_275);
x_287 = lean::cnstr_get(x_286, 0);
lean::inc(x_287);
x_289 = lean::cnstr_get(x_286, 1);
lean::inc(x_289);
lean::dec(x_286);
x_126 = x_287;
x_127 = x_289;
goto lbl_128;
}
}
}
}
}
lbl_134:
{
if (lean::obj_tag(x_132) == 0)
{
obj* x_294; obj* x_296; obj* x_297; 
lean::dec(x_0);
lean::dec(x_11);
x_294 = lean::cnstr_get(x_132, 0);
lean::inc(x_294);
if (lean::is_shared(x_132)) {
 lean::dec(x_132);
 x_296 = lean::box(0);
} else {
 lean::cnstr_release(x_132, 0);
 x_296 = x_132;
}
if (lean::is_scalar(x_296)) {
 x_297 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_297 = x_296;
}
lean::cnstr_set(x_297, 0, x_294);
x_129 = x_297;
x_130 = x_133;
goto lbl_131;
}
else
{
obj* x_298; obj* x_299; obj* x_300; obj* x_304; obj* x_305; obj* x_307; 
if (lean::is_shared(x_132)) {
 lean::dec(x_132);
 x_298 = lean::box(0);
} else {
 lean::cnstr_release(x_132, 0);
 x_298 = x_132;
}
x_299 = l_lean_ir_cpp_emit__apply___closed__2;
x_300 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_2);
lean::inc(x_300);
lean::inc(x_299);
x_304 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_299, x_300, x_11, x_2, x_133);
x_305 = lean::cnstr_get(x_304, 0);
lean::inc(x_305);
x_307 = lean::cnstr_get(x_304, 1);
lean::inc(x_307);
lean::dec(x_304);
if (lean::obj_tag(x_305) == 0)
{
obj* x_311; obj* x_314; 
lean::dec(x_0);
x_311 = lean::cnstr_get(x_305, 0);
lean::inc(x_311);
lean::dec(x_305);
if (lean::is_scalar(x_298)) {
 x_314 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_314 = x_298;
 lean::cnstr_set_tag(x_298, 0);
}
lean::cnstr_set(x_314, 0, x_311);
x_129 = x_314;
x_130 = x_307;
goto lbl_131;
}
else
{
obj* x_316; obj* x_319; obj* x_320; obj* x_322; 
lean::dec(x_305);
x_316 = l_lean_ir_cpp_emit__apply___closed__6;
lean::inc(x_2);
lean::inc(x_316);
x_319 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_316, x_2, x_307);
x_320 = lean::cnstr_get(x_319, 0);
lean::inc(x_320);
x_322 = lean::cnstr_get(x_319, 1);
lean::inc(x_322);
lean::dec(x_319);
if (lean::obj_tag(x_320) == 0)
{
obj* x_326; obj* x_329; 
lean::dec(x_0);
x_326 = lean::cnstr_get(x_320, 0);
lean::inc(x_326);
lean::dec(x_320);
if (lean::is_scalar(x_298)) {
 x_329 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_329 = x_298;
 lean::cnstr_set_tag(x_298, 0);
}
lean::cnstr_set(x_329, 0, x_326);
x_129 = x_329;
x_130 = x_322;
goto lbl_131;
}
else
{
obj* x_332; obj* x_333; obj* x_335; 
lean::dec(x_320);
lean::inc(x_2);
x_332 = l_lean_ir_cpp_emit__var(x_0, x_2, x_322);
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
if (lean::is_scalar(x_298)) {
 x_341 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_341 = x_298;
 lean::cnstr_set_tag(x_298, 0);
}
lean::cnstr_set(x_341, 0, x_338);
x_129 = x_341;
x_130 = x_335;
goto lbl_131;
}
else
{
obj* x_344; obj* x_347; obj* x_348; obj* x_350; 
lean::dec(x_298);
lean::dec(x_333);
x_344 = l_lean_ir_cpp_emit__apply___closed__7;
lean::inc(x_2);
lean::inc(x_344);
x_347 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_344, x_2, x_335);
x_348 = lean::cnstr_get(x_347, 0);
lean::inc(x_348);
x_350 = lean::cnstr_get(x_347, 1);
lean::inc(x_350);
lean::dec(x_347);
x_129 = x_348;
x_130 = x_350;
goto lbl_131;
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
obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_28; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 1);
lean::inc(x_11);
lean::dec(x_2);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_add(x_1, x_14);
x_22 = l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_22);
x_25 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_3, x_4);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_33; obj* x_35; obj* x_36; 
lean::dec(x_9);
lean::dec(x_1);
x_33 = lean::cnstr_get(x_26, 0);
lean::inc(x_33);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_35 = x_26;
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
x_16 = x_36;
x_17 = x_28;
goto lbl_18;
}
else
{
obj* x_37; obj* x_38; obj* x_41; obj* x_42; obj* x_44; 
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_37 = x_26;
}
x_38 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_38);
x_41 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_38, x_3, x_28);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
if (lean::obj_tag(x_42) == 0)
{
obj* x_49; obj* x_52; 
lean::dec(x_9);
lean::dec(x_1);
x_49 = lean::cnstr_get(x_42, 0);
lean::inc(x_49);
lean::dec(x_42);
if (lean::is_scalar(x_37)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_37;
 lean::cnstr_set_tag(x_37, 0);
}
lean::cnstr_set(x_52, 0, x_49);
x_16 = x_52;
x_17 = x_44;
goto lbl_18;
}
else
{
obj* x_56; obj* x_57; obj* x_59; 
lean::dec(x_42);
lean::inc(x_3);
lean::inc(x_0);
x_56 = l_lean_ir_cpp_emit__var(x_0, x_3, x_44);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
if (lean::obj_tag(x_57) == 0)
{
obj* x_63; obj* x_66; 
lean::dec(x_1);
x_63 = lean::cnstr_get(x_57, 0);
lean::inc(x_63);
lean::dec(x_57);
if (lean::is_scalar(x_37)) {
 x_66 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_66 = x_37;
 lean::cnstr_set_tag(x_37, 0);
}
lean::cnstr_set(x_66, 0, x_63);
x_19 = x_66;
x_20 = x_59;
goto lbl_21;
}
else
{
obj* x_68; obj* x_71; obj* x_72; obj* x_74; 
lean::dec(x_57);
x_68 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_68);
x_71 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_68, x_3, x_59);
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
if (lean::is_scalar(x_37)) {
 x_81 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_81 = x_37;
 lean::cnstr_set_tag(x_37, 0);
}
lean::cnstr_set(x_81, 0, x_78);
x_19 = x_81;
x_20 = x_74;
goto lbl_21;
}
else
{
obj* x_85; obj* x_86; obj* x_88; 
lean::dec(x_72);
lean::dec(x_37);
lean::inc(x_3);
x_85 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_1, x_3, x_74);
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_85, 1);
lean::inc(x_88);
lean::dec(x_85);
x_19 = x_86;
x_20 = x_88;
goto lbl_21;
}
}
}
}
lbl_18:
{
if (lean::obj_tag(x_16) == 0)
{
obj* x_95; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_95 = lean::cnstr_get(x_16, 0);
lean::inc(x_95);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_97 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_97 = x_16;
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_17);
return x_99;
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
obj* x_103; obj* x_105; obj* x_106; 
lean::dec(x_9);
x_103 = lean::cnstr_get(x_19, 0);
lean::inc(x_103);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_105 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_105 = x_19;
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_103);
x_16 = x_106;
x_17 = x_20;
goto lbl_18;
}
else
{
obj* x_107; obj* x_108; obj* x_111; obj* x_112; obj* x_114; 
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_107 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_107 = x_19;
}
x_108 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_108);
x_111 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_108, x_3, x_20);
x_112 = lean::cnstr_get(x_111, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_111, 1);
lean::inc(x_114);
lean::dec(x_111);
if (lean::obj_tag(x_112) == 0)
{
obj* x_118; obj* x_121; 
lean::dec(x_9);
x_118 = lean::cnstr_get(x_112, 0);
lean::inc(x_118);
lean::dec(x_112);
if (lean::is_scalar(x_107)) {
 x_121 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_121 = x_107;
 lean::cnstr_set_tag(x_107, 0);
}
lean::cnstr_set(x_121, 0, x_118);
x_16 = x_121;
x_17 = x_114;
goto lbl_18;
}
else
{
obj* x_124; obj* x_125; obj* x_127; 
lean::dec(x_112);
lean::inc(x_3);
x_124 = l_lean_ir_cpp_emit__var(x_9, x_3, x_114);
x_125 = lean::cnstr_get(x_124, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_124, 1);
lean::inc(x_127);
lean::dec(x_124);
if (lean::obj_tag(x_125) == 0)
{
obj* x_130; obj* x_133; 
x_130 = lean::cnstr_get(x_125, 0);
lean::inc(x_130);
lean::dec(x_125);
if (lean::is_scalar(x_107)) {
 x_133 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_133 = x_107;
 lean::cnstr_set_tag(x_107, 0);
}
lean::cnstr_set(x_133, 0, x_130);
x_16 = x_133;
x_17 = x_127;
goto lbl_18;
}
else
{
obj* x_134; obj* x_137; obj* x_140; obj* x_141; obj* x_143; 
x_134 = lean::cnstr_get(x_125, 0);
lean::inc(x_134);
lean::dec(x_125);
x_137 = l_option_has__repr___rarg___closed__3;
lean::inc(x_3);
lean::inc(x_137);
x_140 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_137, x_3, x_127);
x_141 = lean::cnstr_get(x_140, 0);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_140, 1);
lean::inc(x_143);
lean::dec(x_140);
if (lean::obj_tag(x_141) == 0)
{
obj* x_147; obj* x_150; 
lean::dec(x_134);
x_147 = lean::cnstr_get(x_141, 0);
lean::inc(x_147);
lean::dec(x_141);
if (lean::is_scalar(x_107)) {
 x_150 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_150 = x_107;
 lean::cnstr_set_tag(x_107, 0);
}
lean::cnstr_set(x_150, 0, x_147);
x_16 = x_150;
x_17 = x_143;
goto lbl_18;
}
else
{
obj* x_152; 
lean::dec(x_141);
if (lean::is_scalar(x_107)) {
 x_152 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_152 = x_107;
}
lean::cnstr_set(x_152, 0, x_134);
x_16 = x_152;
x_17 = x_143;
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
obj* x_16; obj* x_18; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_16 = l_lean_ir_cpp_emit__closure___closed__1;
lean::inc(x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_4);
return x_18;
}
else
{
obj* x_19; obj* x_24; obj* x_25; obj* x_27; obj* x_29; 
x_19 = lean::cnstr_get(x_11, 0);
lean::inc(x_19);
lean::dec(x_11);
lean::inc(x_3);
lean::inc(x_0);
x_24 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 x_29 = x_24;
}
if (lean::obj_tag(x_25) == 0)
{
obj* x_35; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_19);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_35 = lean::cnstr_get(x_25, 0);
lean::inc(x_35);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 x_37 = x_25;
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_35);
if (lean::is_scalar(x_29)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_29;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_27);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_47; obj* x_48; obj* x_50; obj* x_52; 
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 x_40 = x_25;
}
x_44 = l_lean_ir_cpp_emit__closure___closed__2;
lean::inc(x_3);
lean::inc(x_44);
x_47 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_44, x_3, x_27);
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
obj* x_60; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_19);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_40);
lean::dec(x_29);
x_60 = lean::cnstr_get(x_48, 0);
lean::inc(x_60);
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_62 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 x_62 = x_48;
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_60);
if (lean::is_scalar(x_52)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_52;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_50);
return x_64;
}
else
{
obj* x_65; obj* x_67; obj* x_68; obj* x_70; 
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_65 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 x_65 = x_48;
}
lean::inc(x_3);
x_67 = l_lean_ir_cpp_fid2cpp(x_1, x_3, x_50);
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
if (lean::obj_tag(x_68) == 0)
{
obj* x_79; obj* x_82; obj* x_83; 
lean::dec(x_19);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_40);
lean::dec(x_29);
x_79 = lean::cnstr_get(x_68, 0);
lean::inc(x_79);
lean::dec(x_68);
if (lean::is_scalar(x_65)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_65;
 lean::cnstr_set_tag(x_65, 0);
}
lean::cnstr_set(x_82, 0, x_79);
if (lean::is_scalar(x_52)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_52;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_70);
return x_83;
}
else
{
obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_92; obj* x_93; obj* x_94; uint8 x_95; obj* x_97; obj* x_98; obj* x_101; obj* x_102; obj* x_103; 
lean::dec(x_52);
x_85 = lean::cnstr_get(x_68, 0);
lean::inc(x_85);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_87 = x_68;
}
x_88 = l_lean_ir_decl_header___main(x_19);
x_89 = lean::cnstr_get(x_88, 1);
lean::inc(x_89);
lean::dec(x_88);
x_92 = lean::mk_nat_obj(0u);
x_93 = l_list_length__aux___main___rarg(x_89, x_92);
x_94 = l_lean_closure__max__args;
x_95 = lean::nat_dec_lt(x_94, x_93);
lean::inc(x_2);
x_97 = l_list_length__aux___main___rarg(x_2, x_92);
x_98 = l_lean_ir_cpp_emit__closure___closed__3;
lean::inc(x_3);
lean::inc(x_98);
x_101 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_98, x_3, x_70);
if (x_95 == 0)
{
obj* x_105; obj* x_107; 
x_105 = lean::cnstr_get(x_101, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_101, 1);
lean::inc(x_107);
lean::dec(x_101);
if (lean::obj_tag(x_105) == 0)
{
obj* x_111; obj* x_114; 
lean::dec(x_85);
x_111 = lean::cnstr_get(x_105, 0);
lean::inc(x_111);
lean::dec(x_105);
if (lean::is_scalar(x_87)) {
 x_114 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_114 = x_87;
 lean::cnstr_set_tag(x_87, 0);
}
lean::cnstr_set(x_114, 0, x_111);
x_102 = x_114;
x_103 = x_107;
goto lbl_104;
}
else
{
obj* x_118; obj* x_119; obj* x_121; 
lean::dec(x_87);
lean::dec(x_105);
lean::inc(x_3);
x_118 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_85, x_3, x_107);
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_118, 1);
lean::inc(x_121);
lean::dec(x_118);
x_102 = x_119;
x_103 = x_121;
goto lbl_104;
}
}
else
{
obj* x_124; obj* x_126; 
x_124 = lean::cnstr_get(x_101, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_101, 1);
lean::inc(x_126);
lean::dec(x_101);
if (lean::obj_tag(x_124) == 0)
{
obj* x_130; obj* x_133; 
lean::dec(x_85);
x_130 = lean::cnstr_get(x_124, 0);
lean::inc(x_130);
lean::dec(x_124);
if (lean::is_scalar(x_87)) {
 x_133 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_133 = x_87;
 lean::cnstr_set_tag(x_87, 0);
}
lean::cnstr_set(x_133, 0, x_130);
x_102 = x_133;
x_103 = x_126;
goto lbl_104;
}
else
{
obj* x_136; obj* x_138; obj* x_141; obj* x_142; obj* x_144; 
lean::dec(x_87);
lean::dec(x_124);
x_136 = l_lean_ir_cpp_emit__closure___closed__4;
lean::inc(x_136);
x_138 = lean::string_append(x_136, x_85);
lean::dec(x_85);
lean::inc(x_3);
x_141 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_138, x_3, x_126);
x_142 = lean::cnstr_get(x_141, 0);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_141, 1);
lean::inc(x_144);
lean::dec(x_141);
x_102 = x_142;
x_103 = x_144;
goto lbl_104;
}
}
lbl_104:
{
if (lean::obj_tag(x_102) == 0)
{
obj* x_149; obj* x_152; 
lean::dec(x_97);
lean::dec(x_93);
x_149 = lean::cnstr_get(x_102, 0);
lean::inc(x_149);
lean::dec(x_102);
if (lean::is_scalar(x_65)) {
 x_152 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_152 = x_65;
 lean::cnstr_set_tag(x_65, 0);
}
lean::cnstr_set(x_152, 0, x_149);
x_41 = x_152;
x_42 = x_103;
goto lbl_43;
}
else
{
obj* x_154; obj* x_157; obj* x_158; obj* x_160; 
lean::dec(x_102);
x_154 = l_option_has__repr___rarg___closed__3;
lean::inc(x_3);
lean::inc(x_154);
x_157 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_154, x_3, x_103);
x_158 = lean::cnstr_get(x_157, 0);
lean::inc(x_158);
x_160 = lean::cnstr_get(x_157, 1);
lean::inc(x_160);
lean::dec(x_157);
if (lean::obj_tag(x_158) == 0)
{
obj* x_165; obj* x_168; 
lean::dec(x_97);
lean::dec(x_93);
x_165 = lean::cnstr_get(x_158, 0);
lean::inc(x_165);
lean::dec(x_158);
if (lean::is_scalar(x_65)) {
 x_168 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_168 = x_65;
 lean::cnstr_set_tag(x_65, 0);
}
lean::cnstr_set(x_168, 0, x_165);
x_41 = x_168;
x_42 = x_160;
goto lbl_43;
}
else
{
obj* x_170; obj* x_173; obj* x_174; obj* x_176; 
lean::dec(x_158);
x_170 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_170);
x_173 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_170, x_3, x_160);
x_174 = lean::cnstr_get(x_173, 0);
lean::inc(x_174);
x_176 = lean::cnstr_get(x_173, 1);
lean::inc(x_176);
lean::dec(x_173);
if (lean::obj_tag(x_174) == 0)
{
obj* x_181; obj* x_184; 
lean::dec(x_97);
lean::dec(x_93);
x_181 = lean::cnstr_get(x_174, 0);
lean::inc(x_181);
lean::dec(x_174);
if (lean::is_scalar(x_65)) {
 x_184 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_184 = x_65;
 lean::cnstr_set_tag(x_65, 0);
}
lean::cnstr_set(x_184, 0, x_181);
x_41 = x_184;
x_42 = x_176;
goto lbl_43;
}
else
{
obj* x_187; obj* x_188; obj* x_190; 
lean::dec(x_174);
lean::inc(x_3);
x_187 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_93, x_3, x_176);
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
x_190 = lean::cnstr_get(x_187, 1);
lean::inc(x_190);
lean::dec(x_187);
if (lean::obj_tag(x_188) == 0)
{
obj* x_194; obj* x_197; 
lean::dec(x_97);
x_194 = lean::cnstr_get(x_188, 0);
lean::inc(x_194);
lean::dec(x_188);
if (lean::is_scalar(x_65)) {
 x_197 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_197 = x_65;
 lean::cnstr_set_tag(x_65, 0);
}
lean::cnstr_set(x_197, 0, x_194);
x_41 = x_197;
x_42 = x_190;
goto lbl_43;
}
else
{
obj* x_201; obj* x_202; obj* x_204; 
lean::dec(x_188);
lean::inc(x_3);
lean::inc(x_170);
x_201 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_170, x_3, x_190);
x_202 = lean::cnstr_get(x_201, 0);
lean::inc(x_202);
x_204 = lean::cnstr_get(x_201, 1);
lean::inc(x_204);
lean::dec(x_201);
if (lean::obj_tag(x_202) == 0)
{
obj* x_208; obj* x_211; 
lean::dec(x_97);
x_208 = lean::cnstr_get(x_202, 0);
lean::inc(x_208);
lean::dec(x_202);
if (lean::is_scalar(x_65)) {
 x_211 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_211 = x_65;
 lean::cnstr_set_tag(x_65, 0);
}
lean::cnstr_set(x_211, 0, x_208);
x_41 = x_211;
x_42 = x_204;
goto lbl_43;
}
else
{
obj* x_215; obj* x_216; obj* x_218; 
lean::dec(x_202);
lean::dec(x_65);
lean::inc(x_3);
x_215 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_97, x_3, x_204);
x_216 = lean::cnstr_get(x_215, 0);
lean::inc(x_216);
x_218 = lean::cnstr_get(x_215, 1);
lean::inc(x_218);
lean::dec(x_215);
x_41 = x_216;
x_42 = x_218;
goto lbl_43;
}
}
}
}
}
}
}
}
lbl_43:
{
if (lean::obj_tag(x_41) == 0)
{
obj* x_224; obj* x_227; obj* x_228; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_224 = lean::cnstr_get(x_41, 0);
lean::inc(x_224);
lean::dec(x_41);
if (lean::is_scalar(x_40)) {
 x_227 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_227 = x_40;
 lean::cnstr_set_tag(x_40, 0);
}
lean::cnstr_set(x_227, 0, x_224);
if (lean::is_scalar(x_29)) {
 x_228 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_228 = x_29;
}
lean::cnstr_set(x_228, 0, x_227);
lean::cnstr_set(x_228, 1, x_42);
return x_228;
}
else
{
obj* x_230; obj* x_233; obj* x_234; obj* x_236; 
lean::dec(x_41);
x_230 = l_option_has__repr___rarg___closed__3;
lean::inc(x_3);
lean::inc(x_230);
x_233 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_230, x_3, x_42);
x_234 = lean::cnstr_get(x_233, 0);
lean::inc(x_234);
x_236 = lean::cnstr_get(x_233, 1);
lean::inc(x_236);
lean::dec(x_233);
if (lean::obj_tag(x_234) == 0)
{
obj* x_242; obj* x_245; obj* x_246; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_242 = lean::cnstr_get(x_234, 0);
lean::inc(x_242);
lean::dec(x_234);
if (lean::is_scalar(x_40)) {
 x_245 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_245 = x_40;
 lean::cnstr_set_tag(x_40, 0);
}
lean::cnstr_set(x_245, 0, x_242);
if (lean::is_scalar(x_29)) {
 x_246 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_246 = x_29;
}
lean::cnstr_set(x_246, 0, x_245);
lean::cnstr_set(x_246, 1, x_236);
return x_246;
}
else
{
obj* x_248; obj* x_249; obj* x_250; obj* x_252; 
lean::dec(x_234);
x_248 = lean::mk_nat_obj(0u);
x_249 = l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1(x_0, x_248, x_2, x_3, x_236);
x_250 = lean::cnstr_get(x_249, 0);
lean::inc(x_250);
x_252 = lean::cnstr_get(x_249, 1);
lean::inc(x_252);
lean::dec(x_249);
if (lean::obj_tag(x_250) == 0)
{
obj* x_255; obj* x_258; obj* x_259; 
x_255 = lean::cnstr_get(x_250, 0);
lean::inc(x_255);
lean::dec(x_250);
if (lean::is_scalar(x_40)) {
 x_258 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_258 = x_40;
 lean::cnstr_set_tag(x_40, 0);
}
lean::cnstr_set(x_258, 0, x_255);
if (lean::is_scalar(x_29)) {
 x_259 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_259 = x_29;
}
lean::cnstr_set(x_259, 0, x_258);
lean::cnstr_set(x_259, 1, x_252);
return x_259;
}
else
{
obj* x_262; obj* x_264; 
lean::dec(x_250);
lean::dec(x_40);
x_262 = l_lean_ir_match__type___closed__5;
lean::inc(x_262);
if (lean::is_scalar(x_29)) {
 x_264 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_264 = x_29;
}
lean::cnstr_set(x_264, 0, x_262);
lean::cnstr_set(x_264, 1, x_252);
return x_264;
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
lean::dec(x_15);
lean::dec(x_22);
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
lean::dec(x_110);
lean::dec(x_118);
lean::dec(x_75);
lean::dec(x_77);
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
lean::dec(x_110);
lean::dec(x_118);
lean::dec(x_77);
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
lean::dec(x_309);
lean::dec(x_305);
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
lean::dec(x_300);
lean::dec(x_333);
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
lean::dec(x_354);
lean::dec(x_351);
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
lean::dec(x_354);
lean::dec(x_351);
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
lean::dec(x_367);
lean::dec(x_380);
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
lean::dec(x_410);
lean::dec(x_375);
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
lean::dec(x_597);
lean::dec(x_600);
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
lean::dec(x_597);
lean::dec(x_600);
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
lean::dec(x_873);
lean::dec(x_875);
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
lean::dec(x_873);
lean::dec(x_875);
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
lean::dec(x_994);
lean::dec(x_992);
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
lean::dec(x_994);
lean::dec(x_992);
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
obj* x_1158; 
x_1158 = lean::box(0);
x_1150 = x_1158;
goto lbl_1151;
}
else
{
obj* x_1159; uint8 x_1162; obj* x_1164; obj* x_1165; uint8 x_1166; 
x_1159 = lean::cnstr_get(x_1157, 0);
lean::inc(x_1159);
lean::dec(x_1157);
x_1162 = lean::unbox(x_1159);
lean::dec(x_1159);
x_1164 = l_lean_ir_type2id___main(x_1162);
x_1165 = l_lean_ir_valid__assign__unop__types___closed__1;
x_1166 = lean::nat_dec_eq(x_1164, x_1165);
lean::dec(x_1164);
if (x_1166 == 0)
{
obj* x_1168; 
x_1168 = lean::box(0);
x_1150 = x_1168;
goto lbl_1151;
}
else
{
obj* x_1169; 
x_1169 = lean::box(0);
x_1152 = x_1169;
goto lbl_1153;
}
}
lbl_1149:
{
if (lean::obj_tag(x_1147) == 0)
{
obj* x_1171; obj* x_1173; obj* x_1174; obj* x_1175; 
lean::dec(x_1145);
x_1171 = lean::cnstr_get(x_1147, 0);
lean::inc(x_1171);
if (lean::is_shared(x_1147)) {
 lean::dec(x_1147);
 x_1173 = lean::box(0);
} else {
 lean::cnstr_release(x_1147, 0);
 x_1173 = x_1147;
}
if (lean::is_scalar(x_1173)) {
 x_1174 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1174 = x_1173;
}
lean::cnstr_set(x_1174, 0, x_1171);
x_1175 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1175, 0, x_1174);
lean::cnstr_set(x_1175, 1, x_1148);
x_3 = x_1175;
goto lbl_4;
}
else
{
obj* x_1176; obj* x_1177; obj* x_1180; obj* x_1181; obj* x_1183; obj* x_1185; 
if (lean::is_shared(x_1147)) {
 lean::dec(x_1147);
 x_1176 = lean::box(0);
} else {
 lean::cnstr_release(x_1147, 0);
 x_1176 = x_1147;
}
x_1177 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_1177);
x_1180 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1177, x_1, x_1148);
x_1181 = lean::cnstr_get(x_1180, 0);
lean::inc(x_1181);
x_1183 = lean::cnstr_get(x_1180, 1);
lean::inc(x_1183);
if (lean::is_shared(x_1180)) {
 lean::dec(x_1180);
 x_1185 = lean::box(0);
} else {
 lean::cnstr_release(x_1180, 0);
 lean::cnstr_release(x_1180, 1);
 x_1185 = x_1180;
}
if (lean::obj_tag(x_1181) == 0)
{
obj* x_1187; obj* x_1190; obj* x_1191; 
lean::dec(x_1145);
x_1187 = lean::cnstr_get(x_1181, 0);
lean::inc(x_1187);
lean::dec(x_1181);
if (lean::is_scalar(x_1176)) {
 x_1190 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1190 = x_1176;
 lean::cnstr_set_tag(x_1176, 0);
}
lean::cnstr_set(x_1190, 0, x_1187);
if (lean::is_scalar(x_1185)) {
 x_1191 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1191 = x_1185;
}
lean::cnstr_set(x_1191, 0, x_1190);
lean::cnstr_set(x_1191, 1, x_1183);
x_3 = x_1191;
goto lbl_4;
}
else
{
obj* x_1194; obj* x_1195; obj* x_1197; 
lean::dec(x_1181);
lean::inc(x_1);
x_1194 = l_lean_ir_cpp_emit__var(x_1145, x_1, x_1183);
x_1195 = lean::cnstr_get(x_1194, 0);
lean::inc(x_1195);
x_1197 = lean::cnstr_get(x_1194, 1);
lean::inc(x_1197);
lean::dec(x_1194);
if (lean::obj_tag(x_1195) == 0)
{
obj* x_1200; obj* x_1203; obj* x_1204; 
x_1200 = lean::cnstr_get(x_1195, 0);
lean::inc(x_1200);
lean::dec(x_1195);
if (lean::is_scalar(x_1176)) {
 x_1203 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1203 = x_1176;
 lean::cnstr_set_tag(x_1176, 0);
}
lean::cnstr_set(x_1203, 0, x_1200);
if (lean::is_scalar(x_1185)) {
 x_1204 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1204 = x_1185;
}
lean::cnstr_set(x_1204, 0, x_1203);
lean::cnstr_set(x_1204, 1, x_1197);
x_3 = x_1204;
goto lbl_4;
}
else
{
obj* x_1205; obj* x_1208; obj* x_1211; obj* x_1212; obj* x_1214; 
x_1205 = lean::cnstr_get(x_1195, 0);
lean::inc(x_1205);
lean::dec(x_1195);
x_1208 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
lean::inc(x_1208);
x_1211 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1208, x_1, x_1197);
x_1212 = lean::cnstr_get(x_1211, 0);
lean::inc(x_1212);
x_1214 = lean::cnstr_get(x_1211, 1);
lean::inc(x_1214);
lean::dec(x_1211);
if (lean::obj_tag(x_1212) == 0)
{
obj* x_1218; obj* x_1221; obj* x_1222; 
lean::dec(x_1205);
x_1218 = lean::cnstr_get(x_1212, 0);
lean::inc(x_1218);
lean::dec(x_1212);
if (lean::is_scalar(x_1176)) {
 x_1221 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1221 = x_1176;
 lean::cnstr_set_tag(x_1176, 0);
}
lean::cnstr_set(x_1221, 0, x_1218);
if (lean::is_scalar(x_1185)) {
 x_1222 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1222 = x_1185;
}
lean::cnstr_set(x_1222, 0, x_1221);
lean::cnstr_set(x_1222, 1, x_1214);
x_3 = x_1222;
goto lbl_4;
}
else
{
obj* x_1224; obj* x_1225; 
lean::dec(x_1212);
if (lean::is_scalar(x_1176)) {
 x_1224 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1224 = x_1176;
}
lean::cnstr_set(x_1224, 0, x_1205);
if (lean::is_scalar(x_1185)) {
 x_1225 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1225 = x_1185;
}
lean::cnstr_set(x_1225, 0, x_1224);
lean::cnstr_set(x_1225, 1, x_1214);
x_3 = x_1225;
goto lbl_4;
}
}
}
}
}
lbl_1151:
{
obj* x_1227; obj* x_1230; obj* x_1231; obj* x_1233; obj* x_1235; 
lean::dec(x_1150);
x_1227 = l_lean_ir_cpp_emit__instr___closed__8;
lean::inc(x_1);
lean::inc(x_1227);
x_1230 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1227, x_1, x_2);
x_1231 = lean::cnstr_get(x_1230, 0);
lean::inc(x_1231);
x_1233 = lean::cnstr_get(x_1230, 1);
lean::inc(x_1233);
if (lean::is_shared(x_1230)) {
 lean::dec(x_1230);
 x_1235 = lean::box(0);
} else {
 lean::cnstr_release(x_1230, 0);
 lean::cnstr_release(x_1230, 1);
 x_1235 = x_1230;
}
if (lean::obj_tag(x_1231) == 0)
{
obj* x_1239; obj* x_1241; obj* x_1242; obj* x_1243; 
lean::dec(x_1145);
lean::dec(x_1143);
lean::dec(x_1141);
x_1239 = lean::cnstr_get(x_1231, 0);
lean::inc(x_1239);
if (lean::is_shared(x_1231)) {
 lean::dec(x_1231);
 x_1241 = lean::box(0);
} else {
 lean::cnstr_release(x_1231, 0);
 x_1241 = x_1231;
}
if (lean::is_scalar(x_1241)) {
 x_1242 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1242 = x_1241;
}
lean::cnstr_set(x_1242, 0, x_1239);
if (lean::is_scalar(x_1235)) {
 x_1243 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1243 = x_1235;
}
lean::cnstr_set(x_1243, 0, x_1242);
lean::cnstr_set(x_1243, 1, x_1233);
x_3 = x_1243;
goto lbl_4;
}
else
{
obj* x_1244; obj* x_1245; obj* x_1248; obj* x_1249; obj* x_1251; 
if (lean::is_shared(x_1231)) {
 lean::dec(x_1231);
 x_1244 = lean::box(0);
} else {
 lean::cnstr_release(x_1231, 0);
 x_1244 = x_1231;
}
x_1245 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_1245);
x_1248 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1245, x_1, x_1233);
x_1249 = lean::cnstr_get(x_1248, 0);
lean::inc(x_1249);
x_1251 = lean::cnstr_get(x_1248, 1);
lean::inc(x_1251);
lean::dec(x_1248);
if (lean::obj_tag(x_1249) == 0)
{
obj* x_1257; obj* x_1260; obj* x_1261; 
lean::dec(x_1145);
lean::dec(x_1143);
lean::dec(x_1141);
x_1257 = lean::cnstr_get(x_1249, 0);
lean::inc(x_1257);
lean::dec(x_1249);
if (lean::is_scalar(x_1244)) {
 x_1260 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1260 = x_1244;
 lean::cnstr_set_tag(x_1244, 0);
}
lean::cnstr_set(x_1260, 0, x_1257);
if (lean::is_scalar(x_1235)) {
 x_1261 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_1261 = x_1235;
}
lean::cnstr_set(x_1261, 0, x_1260);
lean::cnstr_set(x_1261, 1, x_1251);
x_3 = x_1261;
goto lbl_4;
}
else
{
obj* x_1265; obj* x_1266; obj* x_1268; 
lean::dec(x_1235);
lean::dec(x_1249);
lean::inc(x_1);
x_1265 = l_lean_ir_cpp_emit__var(x_1141, x_1, x_1251);
x_1266 = lean::cnstr_get(x_1265, 0);
lean::inc(x_1266);
x_1268 = lean::cnstr_get(x_1265, 1);
lean::inc(x_1268);
lean::dec(x_1265);
if (lean::obj_tag(x_1266) == 0)
{
obj* x_1272; obj* x_1275; 
lean::dec(x_1143);
x_1272 = lean::cnstr_get(x_1266, 0);
lean::inc(x_1272);
lean::dec(x_1266);
if (lean::is_scalar(x_1244)) {
 x_1275 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1275 = x_1244;
 lean::cnstr_set_tag(x_1244, 0);
}
lean::cnstr_set(x_1275, 0, x_1272);
x_1147 = x_1275;
x_1148 = x_1268;
goto lbl_1149;
}
else
{
obj* x_1277; obj* x_1280; obj* x_1281; obj* x_1283; 
lean::dec(x_1266);
x_1277 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_1277);
x_1280 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1277, x_1, x_1268);
x_1281 = lean::cnstr_get(x_1280, 0);
lean::inc(x_1281);
x_1283 = lean::cnstr_get(x_1280, 1);
lean::inc(x_1283);
lean::dec(x_1280);
if (lean::obj_tag(x_1281) == 0)
{
obj* x_1287; obj* x_1290; 
lean::dec(x_1143);
x_1287 = lean::cnstr_get(x_1281, 0);
lean::inc(x_1287);
lean::dec(x_1281);
if (lean::is_scalar(x_1244)) {
 x_1290 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1290 = x_1244;
 lean::cnstr_set_tag(x_1244, 0);
}
lean::cnstr_set(x_1290, 0, x_1287);
x_1147 = x_1290;
x_1148 = x_1283;
goto lbl_1149;
}
else
{
obj* x_1294; obj* x_1295; obj* x_1297; 
lean::dec(x_1281);
lean::dec(x_1244);
lean::inc(x_1);
x_1294 = l_lean_ir_cpp_emit__var(x_1143, x_1, x_1283);
x_1295 = lean::cnstr_get(x_1294, 0);
lean::inc(x_1295);
x_1297 = lean::cnstr_get(x_1294, 1);
lean::inc(x_1297);
lean::dec(x_1294);
x_1147 = x_1295;
x_1148 = x_1297;
goto lbl_1149;
}
}
}
}
}
lbl_1153:
{
obj* x_1301; obj* x_1304; obj* x_1305; obj* x_1307; obj* x_1309; 
lean::dec(x_1152);
x_1301 = l_lean_ir_cpp_emit__instr___closed__9;
lean::inc(x_1);
lean::inc(x_1301);
x_1304 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1301, x_1, x_2);
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
lean::dec(x_1145);
lean::dec(x_1143);
lean::dec(x_1141);
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
x_1319 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_1319);
x_1322 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1319, x_1, x_1307);
x_1323 = lean::cnstr_get(x_1322, 0);
lean::inc(x_1323);
x_1325 = lean::cnstr_get(x_1322, 1);
lean::inc(x_1325);
lean::dec(x_1322);
if (lean::obj_tag(x_1323) == 0)
{
obj* x_1331; obj* x_1334; obj* x_1335; 
lean::dec(x_1145);
lean::dec(x_1143);
lean::dec(x_1141);
x_1331 = lean::cnstr_get(x_1323, 0);
lean::inc(x_1331);
lean::dec(x_1323);
if (lean::is_scalar(x_1318)) {
 x_1334 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1334 = x_1318;
 lean::cnstr_set_tag(x_1318, 0);
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
x_1339 = l_lean_ir_cpp_emit__var(x_1141, x_1, x_1325);
x_1340 = lean::cnstr_get(x_1339, 0);
lean::inc(x_1340);
x_1342 = lean::cnstr_get(x_1339, 1);
lean::inc(x_1342);
lean::dec(x_1339);
if (lean::obj_tag(x_1340) == 0)
{
obj* x_1346; obj* x_1349; 
lean::dec(x_1143);
x_1346 = lean::cnstr_get(x_1340, 0);
lean::inc(x_1346);
lean::dec(x_1340);
if (lean::is_scalar(x_1318)) {
 x_1349 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1349 = x_1318;
 lean::cnstr_set_tag(x_1318, 0);
}
lean::cnstr_set(x_1349, 0, x_1346);
x_1147 = x_1349;
x_1148 = x_1342;
goto lbl_1149;
}
else
{
obj* x_1351; obj* x_1354; obj* x_1355; obj* x_1357; 
lean::dec(x_1340);
x_1351 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_1351);
x_1354 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1351, x_1, x_1342);
x_1355 = lean::cnstr_get(x_1354, 0);
lean::inc(x_1355);
x_1357 = lean::cnstr_get(x_1354, 1);
lean::inc(x_1357);
lean::dec(x_1354);
if (lean::obj_tag(x_1355) == 0)
{
obj* x_1361; obj* x_1364; 
lean::dec(x_1143);
x_1361 = lean::cnstr_get(x_1355, 0);
lean::inc(x_1361);
lean::dec(x_1355);
if (lean::is_scalar(x_1318)) {
 x_1364 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1364 = x_1318;
 lean::cnstr_set_tag(x_1318, 0);
}
lean::cnstr_set(x_1364, 0, x_1361);
x_1147 = x_1364;
x_1148 = x_1357;
goto lbl_1149;
}
else
{
obj* x_1368; obj* x_1369; obj* x_1371; 
lean::dec(x_1355);
lean::dec(x_1318);
lean::inc(x_1);
x_1368 = l_lean_ir_cpp_emit__var(x_1143, x_1, x_1357);
x_1369 = lean::cnstr_get(x_1368, 0);
lean::inc(x_1369);
x_1371 = lean::cnstr_get(x_1368, 1);
lean::inc(x_1371);
lean::dec(x_1368);
x_1147 = x_1369;
x_1148 = x_1371;
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
obj* x_1380; obj* x_1382; obj* x_1383; uint8 x_1384; obj* x_1385; obj* x_1387; obj* x_1388; obj* x_1389; obj* x_1391; obj* x_1392; obj* x_1393; obj* x_1394; obj* x_1395; obj* x_1396; obj* x_1397; obj* x_1398; obj* x_1399; 
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
x_1383 = l_lean_ir_instr_to__format___main(x_0);
x_1384 = 0;
x_1385 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_1385);
x_1387 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1387, 0, x_1385);
lean::cnstr_set(x_1387, 1, x_1383);
lean::cnstr_set_scalar(x_1387, sizeof(void*)*2, x_1384);
x_1388 = x_1387;
x_1389 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_1389);
x_1391 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1391, 0, x_1388);
lean::cnstr_set(x_1391, 1, x_1389);
lean::cnstr_set_scalar(x_1391, sizeof(void*)*2, x_1384);
x_1392 = x_1391;
x_1393 = lean::box(1);
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
x_1401 = l_lean_ir_cpp_emit__eos(x_1, x_1376);
x_1402 = lean::cnstr_get(x_1401, 0);
lean::inc(x_1402);
x_1404 = lean::cnstr_get(x_1401, 1);
lean::inc(x_1404);
lean::dec(x_1401);
if (lean::obj_tag(x_1402) == 0)
{
obj* x_1407; obj* x_1410; uint8 x_1411; obj* x_1412; obj* x_1414; obj* x_1415; obj* x_1416; obj* x_1418; obj* x_1419; obj* x_1420; obj* x_1421; obj* x_1422; obj* x_1423; obj* x_1424; obj* x_1425; obj* x_1426; 
x_1407 = lean::cnstr_get(x_1402, 0);
lean::inc(x_1407);
lean::dec(x_1402);
x_1410 = l_lean_ir_instr_to__format___main(x_0);
x_1411 = 0;
x_1412 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
lean::inc(x_1412);
x_1414 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1414, 0, x_1412);
lean::cnstr_set(x_1414, 1, x_1410);
lean::cnstr_set_scalar(x_1414, sizeof(void*)*2, x_1411);
x_1415 = x_1414;
x_1416 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_1416);
x_1418 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1418, 0, x_1415);
lean::cnstr_set(x_1418, 1, x_1416);
lean::cnstr_set_scalar(x_1418, sizeof(void*)*2, x_1411);
x_1419 = x_1418;
x_1420 = lean::box(1);
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
 lean::cnstr_set_tag(x_1400, 0);
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
lean::dec(x_1400);
lean::dec(x_0);
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_lean_ir_cpp_emit__instr(x_7, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_0 = x_9;
x_2 = x_16;
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
lean::dec(x_84);
lean::dec(x_36);
lean::dec(x_29);
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
obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_15);
x_31 = lean::cnstr_get(x_21, 0);
lean::inc(x_31);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_33 = x_21;
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
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_36 = x_21;
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
if (lean::is_shared(x_81)) {
 lean::dec(x_81);
 x_86 = lean::box(0);
} else {
 lean::cnstr_release(x_81, 0);
 lean::cnstr_release(x_81, 1);
 x_86 = x_81;
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
if (lean::is_shared(x_82)) {
 lean::dec(x_82);
 x_94 = lean::box(0);
} else {
 lean::cnstr_release(x_82, 0);
 x_94 = x_82;
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
if (lean::is_shared(x_82)) {
 lean::dec(x_82);
 x_97 = lean::box(0);
} else {
 lean::cnstr_release(x_82, 0);
 x_97 = x_82;
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
lean::dec(x_26);
lean::dec(x_19);
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
obj* x_53; obj* x_54; obj* x_57; obj* x_58; obj* x_60; 
lean::dec(x_40);
x_53 = lean::mk_nat_obj(1u);
x_54 = lean::nat_add(x_1, x_53);
lean::dec(x_1);
lean::inc(x_2);
x_57 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_54, x_2, x_42);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_64; obj* x_67; obj* x_68; 
lean::dec(x_2);
x_64 = lean::cnstr_get(x_58, 0);
lean::inc(x_64);
lean::dec(x_58);
if (lean::is_scalar(x_18)) {
 x_67 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_67 = x_18;
 lean::cnstr_set_tag(x_18, 0);
}
lean::cnstr_set(x_67, 0, x_64);
if (lean::is_scalar(x_10)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_10;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_60);
return x_68;
}
else
{
obj* x_72; obj* x_74; 
lean::dec(x_10);
lean::dec(x_18);
lean::dec(x_58);
x_72 = l_list_repr___main___rarg___closed__3;
lean::inc(x_72);
x_74 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_72, x_2, x_60);
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
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
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
lean::inc(x_13);
x_15 = l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3(x_0, x_11, x_13, x_1, x_2);
return x_15;
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
lean::dec(x_46);
lean::dec(x_21);
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
lean::dec(x_78);
lean::dec(x_74);
lean::dec(x_71);
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_lean_ir_cpp_emit__block(x_7, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_0 = x_9;
x_2 = x_16;
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
lean::dec(x_61);
lean::dec(x_41);
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
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_12 = x_0;
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
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_38 = x_0;
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
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 x_23 = x_18;
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
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_30 = x_19;
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
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_33 = x_19;
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
lean::inc(x_45);
x_34 = x_45;
x_35 = x_21;
goto lbl_36;
}
else
{
obj* x_47; obj* x_50; obj* x_53; 
x_47 = lean::cnstr_get(x_42, 0);
lean::inc(x_47);
lean::dec(x_42);
x_50 = lean::cnstr_get(x_37, 4);
lean::inc(x_50);
lean::dec(x_37);
x_53 = lean::apply_1(x_50, x_11);
if (lean::obj_tag(x_53) == 0)
{
obj* x_55; obj* x_57; uint8 x_58; obj* x_61; 
lean::inc(x_47);
x_55 = l_lean_ir_decl_header___main(x_47);
lean::inc(x_47);
x_57 = l_lean_ir_cpp_need__uncurry(x_47);
x_58 = lean::unbox(x_57);
lean::dec(x_57);
lean::inc(x_3);
x_61 = l_lean_ir_cpp_emit__header(x_55, x_3, x_21);
if (x_58 == 0)
{
obj* x_63; obj* x_65; 
lean::dec(x_47);
x_63 = lean::cnstr_get(x_61, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_61, 1);
lean::inc(x_65);
lean::dec(x_61);
if (lean::obj_tag(x_63) == 0)
{
obj* x_68; obj* x_70; obj* x_71; 
x_68 = lean::cnstr_get(x_63, 0);
lean::inc(x_68);
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_70 = x_63;
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_68);
x_34 = x_71;
x_35 = x_65;
goto lbl_36;
}
else
{
obj* x_72; obj* x_73; obj* x_76; obj* x_77; obj* x_79; 
if (lean::is_shared(x_63)) {
 lean::dec(x_63);
 x_72 = lean::box(0);
} else {
 lean::cnstr_release(x_63, 0);
 x_72 = x_63;
}
x_73 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_73);
x_76 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_73, x_3, x_65);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
if (lean::obj_tag(x_77) == 0)
{
obj* x_82; obj* x_85; 
x_82 = lean::cnstr_get(x_77, 0);
lean::inc(x_82);
lean::dec(x_77);
if (lean::is_scalar(x_72)) {
 x_85 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_85 = x_72;
 lean::cnstr_set_tag(x_72, 0);
}
lean::cnstr_set(x_85, 0, x_82);
x_34 = x_85;
x_35 = x_79;
goto lbl_36;
}
else
{
obj* x_88; 
lean::dec(x_72);
lean::dec(x_77);
x_88 = l_lean_ir_match__type___closed__5;
lean::inc(x_88);
x_34 = x_88;
x_35 = x_79;
goto lbl_36;
}
}
}
else
{
obj* x_90; obj* x_92; 
x_90 = lean::cnstr_get(x_61, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_61, 1);
lean::inc(x_92);
lean::dec(x_61);
if (lean::obj_tag(x_90) == 0)
{
obj* x_96; obj* x_98; obj* x_99; 
lean::dec(x_47);
x_96 = lean::cnstr_get(x_90, 0);
lean::inc(x_96);
if (lean::is_shared(x_90)) {
 lean::dec(x_90);
 x_98 = lean::box(0);
} else {
 lean::cnstr_release(x_90, 0);
 x_98 = x_90;
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
x_34 = x_99;
x_35 = x_92;
goto lbl_36;
}
else
{
obj* x_100; obj* x_101; obj* x_104; obj* x_105; obj* x_107; 
if (lean::is_shared(x_90)) {
 lean::dec(x_90);
 x_100 = lean::box(0);
} else {
 lean::cnstr_release(x_90, 0);
 x_100 = x_90;
}
x_101 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_101);
x_104 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_101, x_3, x_92);
x_105 = lean::cnstr_get(x_104, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_104, 1);
lean::inc(x_107);
lean::dec(x_104);
if (lean::obj_tag(x_105) == 0)
{
obj* x_111; obj* x_114; 
lean::dec(x_47);
x_111 = lean::cnstr_get(x_105, 0);
lean::inc(x_111);
lean::dec(x_105);
if (lean::is_scalar(x_100)) {
 x_114 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_114 = x_100;
 lean::cnstr_set_tag(x_100, 0);
}
lean::cnstr_set(x_114, 0, x_111);
x_34 = x_114;
x_35 = x_107;
goto lbl_36;
}
else
{
obj* x_117; obj* x_118; obj* x_120; 
lean::dec(x_105);
lean::inc(x_3);
x_117 = l_lean_ir_cpp_emit__uncurry__header(x_47, x_3, x_107);
x_118 = lean::cnstr_get(x_117, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_117, 1);
lean::inc(x_120);
lean::dec(x_117);
if (lean::obj_tag(x_118) == 0)
{
obj* x_123; obj* x_126; 
x_123 = lean::cnstr_get(x_118, 0);
lean::inc(x_123);
lean::dec(x_118);
if (lean::is_scalar(x_100)) {
 x_126 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_126 = x_100;
 lean::cnstr_set_tag(x_100, 0);
}
lean::cnstr_set(x_126, 0, x_123);
x_34 = x_126;
x_35 = x_120;
goto lbl_36;
}
else
{
obj* x_131; obj* x_132; obj* x_134; 
lean::dec(x_118);
lean::dec(x_100);
lean::inc(x_3);
lean::inc(x_101);
x_131 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_101, x_3, x_120);
x_132 = lean::cnstr_get(x_131, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_131, 1);
lean::inc(x_134);
lean::dec(x_131);
x_34 = x_132;
x_35 = x_134;
goto lbl_36;
}
}
}
}
}
else
{
obj* x_138; obj* x_141; obj* x_142; obj* x_144; 
lean::dec(x_53);
x_138 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2;
lean::inc(x_3);
lean::inc(x_138);
x_141 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_138, x_3, x_21);
x_142 = lean::cnstr_get(x_141, 0);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_141, 1);
lean::inc(x_144);
lean::dec(x_141);
if (lean::obj_tag(x_142) == 0)
{
obj* x_148; obj* x_150; obj* x_151; 
lean::dec(x_47);
x_148 = lean::cnstr_get(x_142, 0);
lean::inc(x_148);
if (lean::is_shared(x_142)) {
 lean::dec(x_142);
 x_150 = lean::box(0);
} else {
 lean::cnstr_release(x_142, 0);
 x_150 = x_142;
}
if (lean::is_scalar(x_150)) {
 x_151 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_151 = x_150;
}
lean::cnstr_set(x_151, 0, x_148);
x_34 = x_151;
x_35 = x_144;
goto lbl_36;
}
else
{
obj* x_152; obj* x_154; obj* x_156; uint8 x_157; obj* x_160; 
if (lean::is_shared(x_142)) {
 lean::dec(x_142);
 x_152 = lean::box(0);
} else {
 lean::cnstr_release(x_142, 0);
 x_152 = x_142;
}
lean::inc(x_47);
x_154 = l_lean_ir_decl_header___main(x_47);
lean::inc(x_47);
x_156 = l_lean_ir_cpp_need__uncurry(x_47);
x_157 = lean::unbox(x_156);
lean::dec(x_156);
lean::inc(x_3);
x_160 = l_lean_ir_cpp_emit__header(x_154, x_3, x_144);
if (x_157 == 0)
{
obj* x_162; obj* x_164; 
lean::dec(x_47);
x_162 = lean::cnstr_get(x_160, 0);
lean::inc(x_162);
x_164 = lean::cnstr_get(x_160, 1);
lean::inc(x_164);
lean::dec(x_160);
if (lean::obj_tag(x_162) == 0)
{
obj* x_167; obj* x_170; 
x_167 = lean::cnstr_get(x_162, 0);
lean::inc(x_167);
lean::dec(x_162);
if (lean::is_scalar(x_152)) {
 x_170 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_170 = x_152;
 lean::cnstr_set_tag(x_152, 0);
}
lean::cnstr_set(x_170, 0, x_167);
x_34 = x_170;
x_35 = x_164;
goto lbl_36;
}
else
{
obj* x_172; obj* x_175; obj* x_176; obj* x_178; 
lean::dec(x_162);
x_172 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_172);
x_175 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_172, x_3, x_164);
x_176 = lean::cnstr_get(x_175, 0);
lean::inc(x_176);
x_178 = lean::cnstr_get(x_175, 1);
lean::inc(x_178);
lean::dec(x_175);
if (lean::obj_tag(x_176) == 0)
{
obj* x_181; obj* x_184; 
x_181 = lean::cnstr_get(x_176, 0);
lean::inc(x_181);
lean::dec(x_176);
if (lean::is_scalar(x_152)) {
 x_184 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_184 = x_152;
 lean::cnstr_set_tag(x_152, 0);
}
lean::cnstr_set(x_184, 0, x_181);
x_34 = x_184;
x_35 = x_178;
goto lbl_36;
}
else
{
obj* x_187; 
lean::dec(x_176);
lean::dec(x_152);
x_187 = l_lean_ir_match__type___closed__5;
lean::inc(x_187);
x_34 = x_187;
x_35 = x_178;
goto lbl_36;
}
}
}
else
{
obj* x_189; obj* x_191; 
x_189 = lean::cnstr_get(x_160, 0);
lean::inc(x_189);
x_191 = lean::cnstr_get(x_160, 1);
lean::inc(x_191);
lean::dec(x_160);
if (lean::obj_tag(x_189) == 0)
{
obj* x_195; obj* x_198; 
lean::dec(x_47);
x_195 = lean::cnstr_get(x_189, 0);
lean::inc(x_195);
lean::dec(x_189);
if (lean::is_scalar(x_152)) {
 x_198 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_198 = x_152;
 lean::cnstr_set_tag(x_152, 0);
}
lean::cnstr_set(x_198, 0, x_195);
x_34 = x_198;
x_35 = x_191;
goto lbl_36;
}
else
{
obj* x_200; obj* x_203; obj* x_204; obj* x_206; 
lean::dec(x_189);
x_200 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_200);
x_203 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_200, x_3, x_191);
x_204 = lean::cnstr_get(x_203, 0);
lean::inc(x_204);
x_206 = lean::cnstr_get(x_203, 1);
lean::inc(x_206);
lean::dec(x_203);
if (lean::obj_tag(x_204) == 0)
{
obj* x_210; obj* x_213; 
lean::dec(x_47);
x_210 = lean::cnstr_get(x_204, 0);
lean::inc(x_210);
lean::dec(x_204);
if (lean::is_scalar(x_152)) {
 x_213 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_213 = x_152;
 lean::cnstr_set_tag(x_152, 0);
}
lean::cnstr_set(x_213, 0, x_210);
x_34 = x_213;
x_35 = x_206;
goto lbl_36;
}
else
{
obj* x_216; obj* x_217; obj* x_219; 
lean::dec(x_204);
lean::inc(x_3);
x_216 = l_lean_ir_cpp_emit__uncurry__header(x_47, x_3, x_206);
x_217 = lean::cnstr_get(x_216, 0);
lean::inc(x_217);
x_219 = lean::cnstr_get(x_216, 1);
lean::inc(x_219);
lean::dec(x_216);
if (lean::obj_tag(x_217) == 0)
{
obj* x_222; obj* x_225; 
x_222 = lean::cnstr_get(x_217, 0);
lean::inc(x_222);
lean::dec(x_217);
if (lean::is_scalar(x_152)) {
 x_225 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_225 = x_152;
 lean::cnstr_set_tag(x_152, 0);
}
lean::cnstr_set(x_225, 0, x_222);
x_34 = x_225;
x_35 = x_219;
goto lbl_36;
}
else
{
obj* x_230; obj* x_231; obj* x_233; 
lean::dec(x_152);
lean::dec(x_217);
lean::inc(x_3);
lean::inc(x_200);
x_230 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_200, x_3, x_219);
x_231 = lean::cnstr_get(x_230, 0);
lean::inc(x_231);
x_233 = lean::cnstr_get(x_230, 1);
lean::inc(x_233);
lean::dec(x_230);
x_34 = x_231;
x_35 = x_233;
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
obj* x_239; obj* x_242; obj* x_243; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_239 = lean::cnstr_get(x_34, 0);
lean::inc(x_239);
lean::dec(x_34);
if (lean::is_scalar(x_33)) {
 x_242 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_242 = x_33;
 lean::cnstr_set_tag(x_33, 0);
}
lean::cnstr_set(x_242, 0, x_239);
if (lean::is_scalar(x_23)) {
 x_243 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_243 = x_23;
}
lean::cnstr_set(x_243, 0, x_242);
lean::cnstr_set(x_243, 1, x_35);
return x_243;
}
else
{
obj* x_247; 
lean::dec(x_23);
lean::dec(x_34);
lean::dec(x_33);
x_247 = lean::box(0);
x_1 = x_13;
x_2 = x_247;
x_4 = x_35;
goto _start;
}
}
}
}
default:
{
obj* x_249; obj* x_251; obj* x_253; obj* x_258; obj* x_259; obj* x_261; obj* x_263; 
x_249 = lean::cnstr_get(x_1, 0);
lean::inc(x_249);
x_251 = lean::cnstr_get(x_1, 1);
lean::inc(x_251);
x_253 = lean::cnstr_get(x_1, 3);
lean::inc(x_253);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_0);
x_258 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1(x_0, x_249, x_2, x_3, x_4);
x_259 = lean::cnstr_get(x_258, 0);
lean::inc(x_259);
x_261 = lean::cnstr_get(x_258, 1);
lean::inc(x_261);
if (lean::is_shared(x_258)) {
 lean::dec(x_258);
 x_263 = lean::box(0);
} else {
 lean::cnstr_release(x_258, 0);
 lean::cnstr_release(x_258, 1);
 x_263 = x_258;
}
if (lean::obj_tag(x_259) == 0)
{
obj* x_268; obj* x_270; obj* x_271; obj* x_272; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_253);
lean::dec(x_251);
x_268 = lean::cnstr_get(x_259, 0);
lean::inc(x_268);
if (lean::is_shared(x_259)) {
 lean::dec(x_259);
 x_270 = lean::box(0);
} else {
 lean::cnstr_release(x_259, 0);
 x_270 = x_259;
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_268);
if (lean::is_scalar(x_263)) {
 x_272 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_272 = x_263;
}
lean::cnstr_set(x_272, 0, x_271);
lean::cnstr_set(x_272, 1, x_261);
return x_272;
}
else
{
obj* x_273; obj* x_274; obj* x_275; obj* x_277; obj* x_279; obj* x_282; 
if (lean::is_shared(x_259)) {
 lean::dec(x_259);
 x_273 = lean::box(0);
} else {
 lean::cnstr_release(x_259, 0);
 x_273 = x_259;
}
x_277 = lean::cnstr_get(x_0, 0);
lean::inc(x_277);
x_279 = lean::cnstr_get(x_277, 3);
lean::inc(x_279);
lean::inc(x_251);
x_282 = lean::apply_1(x_279, x_251);
if (lean::obj_tag(x_282) == 0)
{
obj* x_285; 
lean::dec(x_251);
lean::dec(x_277);
x_285 = l_lean_ir_match__type___closed__5;
lean::inc(x_285);
x_274 = x_285;
x_275 = x_261;
goto lbl_276;
}
else
{
obj* x_287; obj* x_290; obj* x_293; 
x_287 = lean::cnstr_get(x_282, 0);
lean::inc(x_287);
lean::dec(x_282);
x_290 = lean::cnstr_get(x_277, 4);
lean::inc(x_290);
lean::dec(x_277);
x_293 = lean::apply_1(x_290, x_251);
if (lean::obj_tag(x_293) == 0)
{
obj* x_295; obj* x_297; uint8 x_298; obj* x_301; 
lean::inc(x_287);
x_295 = l_lean_ir_decl_header___main(x_287);
lean::inc(x_287);
x_297 = l_lean_ir_cpp_need__uncurry(x_287);
x_298 = lean::unbox(x_297);
lean::dec(x_297);
lean::inc(x_3);
x_301 = l_lean_ir_cpp_emit__header(x_295, x_3, x_261);
if (x_298 == 0)
{
obj* x_303; obj* x_305; 
lean::dec(x_287);
x_303 = lean::cnstr_get(x_301, 0);
lean::inc(x_303);
x_305 = lean::cnstr_get(x_301, 1);
lean::inc(x_305);
lean::dec(x_301);
if (lean::obj_tag(x_303) == 0)
{
obj* x_308; obj* x_310; obj* x_311; 
x_308 = lean::cnstr_get(x_303, 0);
lean::inc(x_308);
if (lean::is_shared(x_303)) {
 lean::dec(x_303);
 x_310 = lean::box(0);
} else {
 lean::cnstr_release(x_303, 0);
 x_310 = x_303;
}
if (lean::is_scalar(x_310)) {
 x_311 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_311 = x_310;
}
lean::cnstr_set(x_311, 0, x_308);
x_274 = x_311;
x_275 = x_305;
goto lbl_276;
}
else
{
obj* x_312; obj* x_313; obj* x_316; obj* x_317; obj* x_319; 
if (lean::is_shared(x_303)) {
 lean::dec(x_303);
 x_312 = lean::box(0);
} else {
 lean::cnstr_release(x_303, 0);
 x_312 = x_303;
}
x_313 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_313);
x_316 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_313, x_3, x_305);
x_317 = lean::cnstr_get(x_316, 0);
lean::inc(x_317);
x_319 = lean::cnstr_get(x_316, 1);
lean::inc(x_319);
lean::dec(x_316);
if (lean::obj_tag(x_317) == 0)
{
obj* x_322; obj* x_325; 
x_322 = lean::cnstr_get(x_317, 0);
lean::inc(x_322);
lean::dec(x_317);
if (lean::is_scalar(x_312)) {
 x_325 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_325 = x_312;
 lean::cnstr_set_tag(x_312, 0);
}
lean::cnstr_set(x_325, 0, x_322);
x_274 = x_325;
x_275 = x_319;
goto lbl_276;
}
else
{
obj* x_328; 
lean::dec(x_312);
lean::dec(x_317);
x_328 = l_lean_ir_match__type___closed__5;
lean::inc(x_328);
x_274 = x_328;
x_275 = x_319;
goto lbl_276;
}
}
}
else
{
obj* x_330; obj* x_332; 
x_330 = lean::cnstr_get(x_301, 0);
lean::inc(x_330);
x_332 = lean::cnstr_get(x_301, 1);
lean::inc(x_332);
lean::dec(x_301);
if (lean::obj_tag(x_330) == 0)
{
obj* x_336; obj* x_338; obj* x_339; 
lean::dec(x_287);
x_336 = lean::cnstr_get(x_330, 0);
lean::inc(x_336);
if (lean::is_shared(x_330)) {
 lean::dec(x_330);
 x_338 = lean::box(0);
} else {
 lean::cnstr_release(x_330, 0);
 x_338 = x_330;
}
if (lean::is_scalar(x_338)) {
 x_339 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_339 = x_338;
}
lean::cnstr_set(x_339, 0, x_336);
x_274 = x_339;
x_275 = x_332;
goto lbl_276;
}
else
{
obj* x_340; obj* x_341; obj* x_344; obj* x_345; obj* x_347; 
if (lean::is_shared(x_330)) {
 lean::dec(x_330);
 x_340 = lean::box(0);
} else {
 lean::cnstr_release(x_330, 0);
 x_340 = x_330;
}
x_341 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_341);
x_344 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_341, x_3, x_332);
x_345 = lean::cnstr_get(x_344, 0);
lean::inc(x_345);
x_347 = lean::cnstr_get(x_344, 1);
lean::inc(x_347);
lean::dec(x_344);
if (lean::obj_tag(x_345) == 0)
{
obj* x_351; obj* x_354; 
lean::dec(x_287);
x_351 = lean::cnstr_get(x_345, 0);
lean::inc(x_351);
lean::dec(x_345);
if (lean::is_scalar(x_340)) {
 x_354 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_354 = x_340;
 lean::cnstr_set_tag(x_340, 0);
}
lean::cnstr_set(x_354, 0, x_351);
x_274 = x_354;
x_275 = x_347;
goto lbl_276;
}
else
{
obj* x_357; obj* x_358; obj* x_360; 
lean::dec(x_345);
lean::inc(x_3);
x_357 = l_lean_ir_cpp_emit__uncurry__header(x_287, x_3, x_347);
x_358 = lean::cnstr_get(x_357, 0);
lean::inc(x_358);
x_360 = lean::cnstr_get(x_357, 1);
lean::inc(x_360);
lean::dec(x_357);
if (lean::obj_tag(x_358) == 0)
{
obj* x_363; obj* x_366; 
x_363 = lean::cnstr_get(x_358, 0);
lean::inc(x_363);
lean::dec(x_358);
if (lean::is_scalar(x_340)) {
 x_366 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_366 = x_340;
 lean::cnstr_set_tag(x_340, 0);
}
lean::cnstr_set(x_366, 0, x_363);
x_274 = x_366;
x_275 = x_360;
goto lbl_276;
}
else
{
obj* x_371; obj* x_372; obj* x_374; 
lean::dec(x_358);
lean::dec(x_340);
lean::inc(x_3);
lean::inc(x_341);
x_371 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_341, x_3, x_360);
x_372 = lean::cnstr_get(x_371, 0);
lean::inc(x_372);
x_374 = lean::cnstr_get(x_371, 1);
lean::inc(x_374);
lean::dec(x_371);
x_274 = x_372;
x_275 = x_374;
goto lbl_276;
}
}
}
}
}
else
{
obj* x_378; obj* x_381; obj* x_382; obj* x_384; 
lean::dec(x_293);
x_378 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2;
lean::inc(x_3);
lean::inc(x_378);
x_381 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_378, x_3, x_261);
x_382 = lean::cnstr_get(x_381, 0);
lean::inc(x_382);
x_384 = lean::cnstr_get(x_381, 1);
lean::inc(x_384);
lean::dec(x_381);
if (lean::obj_tag(x_382) == 0)
{
obj* x_388; obj* x_390; obj* x_391; 
lean::dec(x_287);
x_388 = lean::cnstr_get(x_382, 0);
lean::inc(x_388);
if (lean::is_shared(x_382)) {
 lean::dec(x_382);
 x_390 = lean::box(0);
} else {
 lean::cnstr_release(x_382, 0);
 x_390 = x_382;
}
if (lean::is_scalar(x_390)) {
 x_391 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_391 = x_390;
}
lean::cnstr_set(x_391, 0, x_388);
x_274 = x_391;
x_275 = x_384;
goto lbl_276;
}
else
{
obj* x_392; obj* x_394; obj* x_396; uint8 x_397; obj* x_400; 
if (lean::is_shared(x_382)) {
 lean::dec(x_382);
 x_392 = lean::box(0);
} else {
 lean::cnstr_release(x_382, 0);
 x_392 = x_382;
}
lean::inc(x_287);
x_394 = l_lean_ir_decl_header___main(x_287);
lean::inc(x_287);
x_396 = l_lean_ir_cpp_need__uncurry(x_287);
x_397 = lean::unbox(x_396);
lean::dec(x_396);
lean::inc(x_3);
x_400 = l_lean_ir_cpp_emit__header(x_394, x_3, x_384);
if (x_397 == 0)
{
obj* x_402; obj* x_404; 
lean::dec(x_287);
x_402 = lean::cnstr_get(x_400, 0);
lean::inc(x_402);
x_404 = lean::cnstr_get(x_400, 1);
lean::inc(x_404);
lean::dec(x_400);
if (lean::obj_tag(x_402) == 0)
{
obj* x_407; obj* x_410; 
x_407 = lean::cnstr_get(x_402, 0);
lean::inc(x_407);
lean::dec(x_402);
if (lean::is_scalar(x_392)) {
 x_410 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_410 = x_392;
 lean::cnstr_set_tag(x_392, 0);
}
lean::cnstr_set(x_410, 0, x_407);
x_274 = x_410;
x_275 = x_404;
goto lbl_276;
}
else
{
obj* x_412; obj* x_415; obj* x_416; obj* x_418; 
lean::dec(x_402);
x_412 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_412);
x_415 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_412, x_3, x_404);
x_416 = lean::cnstr_get(x_415, 0);
lean::inc(x_416);
x_418 = lean::cnstr_get(x_415, 1);
lean::inc(x_418);
lean::dec(x_415);
if (lean::obj_tag(x_416) == 0)
{
obj* x_421; obj* x_424; 
x_421 = lean::cnstr_get(x_416, 0);
lean::inc(x_421);
lean::dec(x_416);
if (lean::is_scalar(x_392)) {
 x_424 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_424 = x_392;
 lean::cnstr_set_tag(x_392, 0);
}
lean::cnstr_set(x_424, 0, x_421);
x_274 = x_424;
x_275 = x_418;
goto lbl_276;
}
else
{
obj* x_427; 
lean::dec(x_392);
lean::dec(x_416);
x_427 = l_lean_ir_match__type___closed__5;
lean::inc(x_427);
x_274 = x_427;
x_275 = x_418;
goto lbl_276;
}
}
}
else
{
obj* x_429; obj* x_431; 
x_429 = lean::cnstr_get(x_400, 0);
lean::inc(x_429);
x_431 = lean::cnstr_get(x_400, 1);
lean::inc(x_431);
lean::dec(x_400);
if (lean::obj_tag(x_429) == 0)
{
obj* x_435; obj* x_438; 
lean::dec(x_287);
x_435 = lean::cnstr_get(x_429, 0);
lean::inc(x_435);
lean::dec(x_429);
if (lean::is_scalar(x_392)) {
 x_438 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_438 = x_392;
 lean::cnstr_set_tag(x_392, 0);
}
lean::cnstr_set(x_438, 0, x_435);
x_274 = x_438;
x_275 = x_431;
goto lbl_276;
}
else
{
obj* x_440; obj* x_443; obj* x_444; obj* x_446; 
lean::dec(x_429);
x_440 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
lean::inc(x_440);
x_443 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_440, x_3, x_431);
x_444 = lean::cnstr_get(x_443, 0);
lean::inc(x_444);
x_446 = lean::cnstr_get(x_443, 1);
lean::inc(x_446);
lean::dec(x_443);
if (lean::obj_tag(x_444) == 0)
{
obj* x_450; obj* x_453; 
lean::dec(x_287);
x_450 = lean::cnstr_get(x_444, 0);
lean::inc(x_450);
lean::dec(x_444);
if (lean::is_scalar(x_392)) {
 x_453 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_453 = x_392;
 lean::cnstr_set_tag(x_392, 0);
}
lean::cnstr_set(x_453, 0, x_450);
x_274 = x_453;
x_275 = x_446;
goto lbl_276;
}
else
{
obj* x_456; obj* x_457; obj* x_459; 
lean::dec(x_444);
lean::inc(x_3);
x_456 = l_lean_ir_cpp_emit__uncurry__header(x_287, x_3, x_446);
x_457 = lean::cnstr_get(x_456, 0);
lean::inc(x_457);
x_459 = lean::cnstr_get(x_456, 1);
lean::inc(x_459);
lean::dec(x_456);
if (lean::obj_tag(x_457) == 0)
{
obj* x_462; obj* x_465; 
x_462 = lean::cnstr_get(x_457, 0);
lean::inc(x_462);
lean::dec(x_457);
if (lean::is_scalar(x_392)) {
 x_465 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_465 = x_392;
 lean::cnstr_set_tag(x_392, 0);
}
lean::cnstr_set(x_465, 0, x_462);
x_274 = x_465;
x_275 = x_459;
goto lbl_276;
}
else
{
obj* x_470; obj* x_471; obj* x_473; 
lean::dec(x_392);
lean::dec(x_457);
lean::inc(x_3);
lean::inc(x_440);
x_470 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_440, x_3, x_459);
x_471 = lean::cnstr_get(x_470, 0);
lean::inc(x_471);
x_473 = lean::cnstr_get(x_470, 1);
lean::inc(x_473);
lean::dec(x_470);
x_274 = x_471;
x_275 = x_473;
goto lbl_276;
}
}
}
}
}
}
}
lbl_276:
{
if (lean::obj_tag(x_274) == 0)
{
obj* x_479; obj* x_482; obj* x_483; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_253);
x_479 = lean::cnstr_get(x_274, 0);
lean::inc(x_479);
lean::dec(x_274);
if (lean::is_scalar(x_273)) {
 x_482 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_482 = x_273;
 lean::cnstr_set_tag(x_273, 0);
}
lean::cnstr_set(x_482, 0, x_479);
if (lean::is_scalar(x_263)) {
 x_483 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_483 = x_263;
}
lean::cnstr_set(x_483, 0, x_482);
lean::cnstr_set(x_483, 1, x_275);
return x_483;
}
else
{
obj* x_487; 
lean::dec(x_263);
lean::dec(x_274);
lean::dec(x_273);
x_487 = lean::box(0);
x_1 = x_253;
x_2 = x_487;
x_4 = x_275;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; uint8 x_13; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_lean_ir_decl_header___main(x_7);
x_13 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*3);
if (x_13 == 0)
{
lean::dec(x_12);
x_0 = x_9;
goto _start;
}
else
{
obj* x_16; uint8 x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; 
x_16 = lean::cnstr_get(x_12, 2);
lean::inc(x_16);
x_18 = lean::unbox(x_16);
lean::dec(x_16);
lean::inc(x_1);
x_21 = l_lean_ir_cpp_emit__type(x_18, x_1, x_2);
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
obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_12);
x_30 = lean::cnstr_get(x_22, 0);
lean::inc(x_30);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_32 = x_22;
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
if (lean::is_scalar(x_26)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_26;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_24);
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_39; obj* x_40; obj* x_42; 
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_35 = x_22;
}
x_36 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_36);
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_36, x_1, x_24);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
if (lean::obj_tag(x_40) == 0)
{
obj* x_48; obj* x_51; obj* x_52; 
lean::dec(x_9);
lean::dec(x_1);
lean::dec(x_12);
x_48 = lean::cnstr_get(x_40, 0);
lean::inc(x_48);
lean::dec(x_40);
if (lean::is_scalar(x_35)) {
 x_51 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_51 = x_35;
 lean::cnstr_set_tag(x_35, 0);
}
lean::cnstr_set(x_51, 0, x_48);
if (lean::is_scalar(x_26)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_26;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_42);
return x_52;
}
else
{
obj* x_54; obj* x_58; obj* x_59; obj* x_61; 
lean::dec(x_40);
x_54 = lean::cnstr_get(x_12, 0);
lean::inc(x_54);
lean::dec(x_12);
lean::inc(x_1);
x_58 = l_lean_ir_cpp_emit__global(x_54, x_1, x_42);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
if (lean::obj_tag(x_59) == 0)
{
obj* x_66; obj* x_69; obj* x_70; 
lean::dec(x_9);
lean::dec(x_1);
x_66 = lean::cnstr_get(x_59, 0);
lean::inc(x_66);
lean::dec(x_59);
if (lean::is_scalar(x_35)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_35;
 lean::cnstr_set_tag(x_35, 0);
}
lean::cnstr_set(x_69, 0, x_66);
if (lean::is_scalar(x_26)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_26;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_61);
return x_70;
}
else
{
obj* x_72; obj* x_75; obj* x_76; obj* x_78; 
lean::dec(x_59);
x_72 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_1);
lean::inc(x_72);
x_75 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_72, x_1, x_61);
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
lean::dec(x_75);
if (lean::obj_tag(x_76) == 0)
{
obj* x_83; obj* x_86; obj* x_87; 
lean::dec(x_9);
lean::dec(x_1);
x_83 = lean::cnstr_get(x_76, 0);
lean::inc(x_83);
lean::dec(x_76);
if (lean::is_scalar(x_35)) {
 x_86 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_86 = x_35;
 lean::cnstr_set_tag(x_35, 0);
}
lean::cnstr_set(x_86, 0, x_83);
if (lean::is_scalar(x_26)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_26;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_78);
return x_87;
}
else
{
lean::dec(x_26);
lean::dec(x_76);
lean::dec(x_35);
x_0 = x_9;
x_2 = x_78;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_20; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_lean_ir_cpp_initialize__prefix;
lean::inc(x_1);
lean::inc(x_12);
x_15 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_12, x_1, x_2);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_20 = x_15;
}
if (lean::obj_tag(x_16) == 0)
{
obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_1);
x_24 = lean::cnstr_get(x_16, 0);
lean::inc(x_24);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_26 = x_16;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
if (lean::is_scalar(x_20)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_20;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_18);
return x_28;
}
else
{
obj* x_29; obj* x_31; obj* x_32; obj* x_34; 
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_29 = x_16;
}
lean::inc(x_1);
x_31 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_7, x_1, x_18);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
if (lean::obj_tag(x_32) == 0)
{
obj* x_39; obj* x_42; obj* x_43; 
lean::dec(x_9);
lean::dec(x_1);
x_39 = lean::cnstr_get(x_32, 0);
lean::inc(x_39);
lean::dec(x_32);
if (lean::is_scalar(x_29)) {
 x_42 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_42 = x_29;
 lean::cnstr_set_tag(x_29, 0);
}
lean::cnstr_set(x_42, 0, x_39);
if (lean::is_scalar(x_20)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_20;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_34);
return x_43;
}
else
{
obj* x_45; obj* x_48; obj* x_49; obj* x_51; 
lean::dec(x_32);
x_45 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_1);
lean::inc(x_45);
x_48 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_45, x_1, x_34);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_56; obj* x_59; obj* x_60; 
lean::dec(x_9);
lean::dec(x_1);
x_56 = lean::cnstr_get(x_49, 0);
lean::inc(x_56);
lean::dec(x_49);
if (lean::is_scalar(x_29)) {
 x_59 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_59 = x_29;
 lean::cnstr_set_tag(x_29, 0);
}
lean::cnstr_set(x_59, 0, x_56);
if (lean::is_scalar(x_20)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_20;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_51);
return x_60;
}
else
{
lean::dec(x_20);
lean::dec(x_29);
lean::dec(x_49);
x_0 = x_9;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; uint8 x_13; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_lean_ir_decl_header___main(x_7);
x_13 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*3);
if (x_13 == 0)
{
lean::dec(x_12);
x_0 = x_9;
goto _start;
}
else
{
obj* x_16; obj* x_21; obj* x_22; obj* x_24; obj* x_26; 
x_16 = lean::cnstr_get(x_12, 0);
lean::inc(x_16);
lean::dec(x_12);
lean::inc(x_1);
lean::inc(x_16);
x_21 = l_lean_ir_cpp_emit__global(x_16, x_1, x_2);
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
obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_16);
lean::dec(x_9);
lean::dec(x_1);
x_30 = lean::cnstr_get(x_22, 0);
lean::inc(x_30);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_32 = x_22;
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_30);
if (lean::is_scalar(x_26)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_26;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_24);
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_39; obj* x_40; obj* x_42; 
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_35 = x_22;
}
x_36 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_1);
lean::inc(x_36);
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_36, x_1, x_24);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
if (lean::obj_tag(x_40) == 0)
{
obj* x_48; obj* x_51; obj* x_52; 
lean::dec(x_16);
lean::dec(x_9);
lean::dec(x_1);
x_48 = lean::cnstr_get(x_40, 0);
lean::inc(x_48);
lean::dec(x_40);
if (lean::is_scalar(x_35)) {
 x_51 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_51 = x_35;
 lean::cnstr_set_tag(x_35, 0);
}
lean::cnstr_set(x_51, 0, x_48);
if (lean::is_scalar(x_26)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_26;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_42);
return x_52;
}
else
{
obj* x_55; obj* x_56; obj* x_58; 
lean::dec(x_40);
lean::inc(x_1);
x_55 = l_lean_ir_cpp_emit__fnid(x_16, x_1, x_42);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_63; obj* x_66; obj* x_67; 
lean::dec(x_9);
lean::dec(x_1);
x_63 = lean::cnstr_get(x_56, 0);
lean::inc(x_63);
lean::dec(x_56);
if (lean::is_scalar(x_35)) {
 x_66 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_66 = x_35;
 lean::cnstr_set_tag(x_35, 0);
}
lean::cnstr_set(x_66, 0, x_63);
if (lean::is_scalar(x_26)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_26;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_58);
return x_67;
}
else
{
obj* x_69; obj* x_72; obj* x_73; obj* x_75; 
lean::dec(x_56);
x_69 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_1);
lean::inc(x_69);
x_72 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_69, x_1, x_58);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
lean::dec(x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_80; obj* x_83; obj* x_84; 
lean::dec(x_9);
lean::dec(x_1);
x_80 = lean::cnstr_get(x_73, 0);
lean::inc(x_80);
lean::dec(x_73);
if (lean::is_scalar(x_35)) {
 x_83 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_83 = x_35;
 lean::cnstr_set_tag(x_35, 0);
}
lean::cnstr_set(x_83, 0, x_80);
if (lean::is_scalar(x_26)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_26;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_75);
return x_84;
}
else
{
lean::dec(x_73);
lean::dec(x_35);
lean::dec(x_26);
x_0 = x_9;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_20; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
x_12 = l_lean_ir_cpp_finalize__prefix;
lean::inc(x_1);
lean::inc(x_12);
x_15 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_12, x_1, x_2);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_20 = x_15;
}
if (lean::obj_tag(x_16) == 0)
{
obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_9);
lean::dec(x_7);
lean::dec(x_1);
x_24 = lean::cnstr_get(x_16, 0);
lean::inc(x_24);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_26 = x_16;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
if (lean::is_scalar(x_20)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_20;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_18);
return x_28;
}
else
{
obj* x_29; obj* x_31; obj* x_32; obj* x_34; 
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_29 = x_16;
}
lean::inc(x_1);
x_31 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_7, x_1, x_18);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
if (lean::obj_tag(x_32) == 0)
{
obj* x_39; obj* x_42; obj* x_43; 
lean::dec(x_9);
lean::dec(x_1);
x_39 = lean::cnstr_get(x_32, 0);
lean::inc(x_39);
lean::dec(x_32);
if (lean::is_scalar(x_29)) {
 x_42 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_42 = x_29;
 lean::cnstr_set_tag(x_29, 0);
}
lean::cnstr_set(x_42, 0, x_39);
if (lean::is_scalar(x_20)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_20;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_34);
return x_43;
}
else
{
obj* x_45; obj* x_48; obj* x_49; obj* x_51; 
lean::dec(x_32);
x_45 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_1);
lean::inc(x_45);
x_48 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_45, x_1, x_34);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_56; obj* x_59; obj* x_60; 
lean::dec(x_9);
lean::dec(x_1);
x_56 = lean::cnstr_get(x_49, 0);
lean::inc(x_56);
lean::dec(x_49);
if (lean::is_scalar(x_29)) {
 x_59 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_59 = x_29;
 lean::cnstr_set_tag(x_29, 0);
}
lean::cnstr_set(x_59, 0, x_56);
if (lean::is_scalar(x_20)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_20;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_51);
return x_60;
}
else
{
lean::dec(x_20);
lean::dec(x_29);
lean::dec(x_49);
x_0 = x_9;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_15; obj* x_16; uint8 x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
x_15 = l_lean_ir_decl_header___main(x_7);
x_18 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*3);
if (x_18 == 0)
{
if (x_18 == 0)
{
obj* x_20; 
lean::dec(x_15);
x_20 = l_lean_ir_match__type___closed__5;
lean::inc(x_20);
x_12 = x_20;
x_13 = x_2;
goto lbl_14;
}
else
{
obj* x_22; 
x_22 = lean::box(0);
x_16 = x_22;
goto lbl_17;
}
}
else
{
obj* x_23; uint8 x_25; obj* x_27; obj* x_28; uint8 x_29; 
x_23 = lean::cnstr_get(x_15, 2);
lean::inc(x_23);
x_25 = lean::unbox(x_23);
lean::dec(x_23);
x_27 = l_lean_ir_type2id___main(x_25);
x_28 = l_lean_ir_valid__assign__unop__types___closed__1;
x_29 = lean::nat_dec_eq(x_27, x_28);
lean::dec(x_27);
if (x_29 == 0)
{
obj* x_32; 
lean::dec(x_15);
x_32 = l_lean_ir_match__type___closed__5;
lean::inc(x_32);
x_12 = x_32;
x_13 = x_2;
goto lbl_14;
}
else
{
if (x_18 == 0)
{
obj* x_35; 
lean::dec(x_15);
x_35 = l_lean_ir_match__type___closed__5;
lean::inc(x_35);
x_12 = x_35;
x_13 = x_2;
goto lbl_14;
}
else
{
obj* x_37; 
x_37 = lean::box(0);
x_16 = x_37;
goto lbl_17;
}
}
}
lbl_14:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_9);
lean::dec(x_1);
x_40 = lean::cnstr_get(x_12, 0);
lean::inc(x_40);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_42 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_42 = x_12;
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_40);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_13);
return x_44;
}
else
{
lean::dec(x_12);
x_0 = x_9;
x_2 = x_13;
goto _start;
}
}
lbl_17:
{
obj* x_48; obj* x_51; obj* x_52; obj* x_54; 
lean::dec(x_16);
x_48 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__1;
lean::inc(x_1);
lean::inc(x_48);
x_51 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_48, x_1, x_2);
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
lean::dec(x_51);
if (lean::obj_tag(x_52) == 0)
{
obj* x_58; obj* x_60; obj* x_61; 
lean::dec(x_15);
x_58 = lean::cnstr_get(x_52, 0);
lean::inc(x_58);
if (lean::is_shared(x_52)) {
 lean::dec(x_52);
 x_60 = lean::box(0);
} else {
 lean::cnstr_release(x_52, 0);
 x_60 = x_52;
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_58);
x_12 = x_61;
x_13 = x_54;
goto lbl_14;
}
else
{
obj* x_62; obj* x_63; obj* x_68; obj* x_69; obj* x_71; 
if (lean::is_shared(x_52)) {
 lean::dec(x_52);
 x_62 = lean::box(0);
} else {
 lean::cnstr_release(x_52, 0);
 x_62 = x_52;
}
x_63 = lean::cnstr_get(x_15, 0);
lean::inc(x_63);
lean::dec(x_15);
lean::inc(x_1);
lean::inc(x_63);
x_68 = l_lean_ir_cpp_emit__global(x_63, x_1, x_54);
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_68, 1);
lean::inc(x_71);
lean::dec(x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_75; obj* x_78; 
lean::dec(x_63);
x_75 = lean::cnstr_get(x_69, 0);
lean::inc(x_75);
lean::dec(x_69);
if (lean::is_scalar(x_62)) {
 x_78 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_78 = x_62;
 lean::cnstr_set_tag(x_62, 0);
}
lean::cnstr_set(x_78, 0, x_75);
x_12 = x_78;
x_13 = x_71;
goto lbl_14;
}
else
{
obj* x_80; obj* x_83; obj* x_84; obj* x_86; 
lean::dec(x_69);
x_80 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__2;
lean::inc(x_1);
lean::inc(x_80);
x_83 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_80, x_1, x_71);
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
lean::dec(x_83);
if (lean::obj_tag(x_84) == 0)
{
obj* x_90; obj* x_93; 
lean::dec(x_63);
x_90 = lean::cnstr_get(x_84, 0);
lean::inc(x_90);
lean::dec(x_84);
if (lean::is_scalar(x_62)) {
 x_93 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_93 = x_62;
 lean::cnstr_set_tag(x_62, 0);
}
lean::cnstr_set(x_93, 0, x_90);
x_12 = x_93;
x_13 = x_86;
goto lbl_14;
}
else
{
obj* x_96; obj* x_97; obj* x_99; 
lean::dec(x_84);
lean::inc(x_1);
x_96 = l_lean_ir_cpp_emit__global(x_63, x_1, x_86);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_96, 1);
lean::inc(x_99);
lean::dec(x_96);
if (lean::obj_tag(x_97) == 0)
{
obj* x_102; obj* x_105; 
x_102 = lean::cnstr_get(x_97, 0);
lean::inc(x_102);
lean::dec(x_97);
if (lean::is_scalar(x_62)) {
 x_105 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_105 = x_62;
 lean::cnstr_set_tag(x_62, 0);
}
lean::cnstr_set(x_105, 0, x_102);
x_12 = x_105;
x_13 = x_99;
goto lbl_14;
}
else
{
obj* x_108; obj* x_111; obj* x_112; obj* x_114; 
lean::dec(x_62);
lean::dec(x_97);
x_108 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__3;
lean::inc(x_1);
lean::inc(x_108);
x_111 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_108, x_1, x_99);
x_112 = lean::cnstr_get(x_111, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_111, 1);
lean::inc(x_114);
lean::dec(x_111);
x_12 = x_112;
x_13 = x_114;
goto lbl_14;
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
obj* x_8; obj* x_10; 
lean::dec(x_0);
lean::dec(x_2);
x_8 = l_lean_ir_match__type___closed__5;
lean::inc(x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_1);
return x_10;
}
else
{
obj* x_11; obj* x_14; obj* x_17; 
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
lean::dec(x_4);
x_14 = lean::cnstr_get(x_2, 3);
lean::inc(x_14);
lean::inc(x_11);
x_17 = lean::apply_1(x_14, x_11);
if (lean::obj_tag(x_17) == 0)
{
obj* x_20; obj* x_21; uint8 x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_2);
x_20 = l_lean_ir_id_to__string___main(x_11);
x_21 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
x_22 = 0;
x_23 = l_lean_ir_cpp_emit__main__proc___closed__1;
lean::inc(x_23);
x_25 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_21);
lean::cnstr_set_scalar(x_25, sizeof(void*)*2, x_22);
x_26 = x_25;
x_27 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
lean::inc(x_27);
x_29 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_29, 0, x_26);
lean::cnstr_set(x_29, 1, x_27);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_22);
x_30 = x_29;
x_31 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_31, 0, x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_1);
return x_32;
}
else
{
obj* x_33; obj* x_36; obj* x_37; obj* x_39; obj* x_40; uint8 x_41; obj* x_43; uint8 x_46; obj* x_48; obj* x_49; uint8 x_50; obj* x_52; uint8 x_55; 
x_33 = lean::cnstr_get(x_17, 0);
lean::inc(x_33);
lean::dec(x_17);
x_36 = l_lean_ir_decl_header___main(x_33);
x_37 = lean::cnstr_get(x_36, 1);
lean::inc(x_37);
x_39 = lean::mk_nat_obj(0u);
x_40 = l_list_length__aux___main___rarg(x_37, x_39);
x_41 = lean::nat_dec_eq(x_40, x_39);
lean::dec(x_40);
x_43 = lean::cnstr_get(x_36, 2);
lean::inc(x_43);
lean::dec(x_36);
x_46 = lean::unbox(x_43);
lean::dec(x_43);
x_48 = l_lean_ir_type2id___main(x_46);
x_49 = l_lean_ir_valid__assign__unop__types___closed__4;
x_50 = lean::nat_dec_eq(x_48, x_49);
lean::dec(x_48);
x_52 = lean::cnstr_get(x_2, 0);
lean::inc(x_52);
lean::dec(x_2);
if (x_50 == 0)
{
uint8 x_57; 
x_57 = 0;
x_55 = x_57;
goto lbl_56;
}
else
{
uint8 x_58; 
x_58 = 1;
x_55 = x_58;
goto lbl_56;
}
lbl_56:
{
obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_65; obj* x_66; 
if (x_41 == 0)
{
obj* x_69; obj* x_70; uint8 x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_80; 
lean::inc(x_11);
x_69 = l_lean_ir_id_to__string___main(x_11);
x_70 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
x_71 = 0;
x_72 = l_lean_ir_cpp_emit__main__proc___closed__5;
lean::inc(x_72);
x_74 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_70);
lean::cnstr_set_scalar(x_74, sizeof(void*)*2, x_71);
x_75 = x_74;
x_76 = l_lean_ir_cpp_emit__main__proc___closed__6;
lean::inc(x_76);
x_78 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_76);
lean::cnstr_set_scalar(x_78, sizeof(void*)*2, x_71);
x_79 = x_78;
x_80 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
x_65 = x_80;
x_66 = x_1;
goto lbl_67;
}
else
{
if (x_55 == 0)
{
obj* x_82; obj* x_83; uint8 x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_91; obj* x_92; obj* x_93; 
lean::inc(x_11);
x_82 = l_lean_ir_id_to__string___main(x_11);
x_83 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
x_84 = 0;
x_85 = l_lean_ir_cpp_emit__main__proc___closed__5;
lean::inc(x_85);
x_87 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set(x_87, 1, x_83);
lean::cnstr_set_scalar(x_87, sizeof(void*)*2, x_84);
x_88 = x_87;
x_89 = l_lean_ir_cpp_emit__main__proc___closed__7;
lean::inc(x_89);
x_91 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_91, 0, x_88);
lean::cnstr_set(x_91, 1, x_89);
lean::cnstr_set_scalar(x_91, sizeof(void*)*2, x_84);
x_92 = x_91;
x_93 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
x_65 = x_93;
x_66 = x_1;
goto lbl_67;
}
else
{
obj* x_94; 
x_94 = l_lean_ir_match__type___closed__5;
lean::inc(x_94);
x_65 = x_94;
x_66 = x_1;
goto lbl_67;
}
}
lbl_61:
{
if (lean::obj_tag(x_59) == 0)
{
obj* x_98; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_0);
lean::dec(x_52);
x_98 = lean::cnstr_get(x_59, 0);
lean::inc(x_98);
if (lean::is_shared(x_59)) {
 lean::dec(x_59);
 x_100 = lean::box(0);
} else {
 lean::cnstr_release(x_59, 0);
 x_100 = x_59;
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_98);
x_102 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_60);
return x_102;
}
else
{
obj* x_103; obj* x_104; obj* x_107; obj* x_108; obj* x_110; obj* x_112; 
if (lean::is_shared(x_59)) {
 lean::dec(x_59);
 x_103 = lean::box(0);
} else {
 lean::cnstr_release(x_59, 0);
 x_103 = x_59;
}
x_104 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_0);
lean::inc(x_104);
x_107 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_104, x_0, x_60);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_107, 1);
lean::inc(x_110);
if (lean::is_shared(x_107)) {
 lean::dec(x_107);
 x_112 = lean::box(0);
} else {
 lean::cnstr_release(x_107, 0);
 lean::cnstr_release(x_107, 1);
 x_112 = x_107;
}
if (lean::obj_tag(x_108) == 0)
{
obj* x_115; obj* x_118; obj* x_119; 
lean::dec(x_0);
lean::dec(x_52);
x_115 = lean::cnstr_get(x_108, 0);
lean::inc(x_115);
lean::dec(x_108);
if (lean::is_scalar(x_103)) {
 x_118 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_118 = x_103;
 lean::cnstr_set_tag(x_103, 0);
}
lean::cnstr_set(x_118, 0, x_115);
if (lean::is_scalar(x_112)) {
 x_119 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_119 = x_112;
}
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_110);
return x_119;
}
else
{
obj* x_121; obj* x_124; obj* x_125; obj* x_127; 
lean::dec(x_108);
x_121 = l_lean_ir_cpp_finalize__prefix;
lean::inc(x_0);
lean::inc(x_121);
x_124 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_121, x_0, x_110);
x_125 = lean::cnstr_get(x_124, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get(x_124, 1);
lean::inc(x_127);
lean::dec(x_124);
if (lean::obj_tag(x_125) == 0)
{
obj* x_132; obj* x_135; obj* x_136; 
lean::dec(x_0);
lean::dec(x_52);
x_132 = lean::cnstr_get(x_125, 0);
lean::inc(x_132);
lean::dec(x_125);
if (lean::is_scalar(x_103)) {
 x_135 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_135 = x_103;
 lean::cnstr_set_tag(x_103, 0);
}
lean::cnstr_set(x_135, 0, x_132);
if (lean::is_scalar(x_112)) {
 x_136 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_136 = x_112;
}
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_127);
return x_136;
}
else
{
obj* x_139; obj* x_140; obj* x_142; 
lean::dec(x_125);
lean::inc(x_0);
x_139 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_52, x_0, x_127);
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_139, 1);
lean::inc(x_142);
lean::dec(x_139);
if (lean::obj_tag(x_140) == 0)
{
obj* x_146; obj* x_149; obj* x_150; 
lean::dec(x_0);
x_146 = lean::cnstr_get(x_140, 0);
lean::inc(x_146);
lean::dec(x_140);
if (lean::is_scalar(x_103)) {
 x_149 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_149 = x_103;
 lean::cnstr_set_tag(x_103, 0);
}
lean::cnstr_set(x_149, 0, x_146);
if (lean::is_scalar(x_112)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_112;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_142);
return x_150;
}
else
{
obj* x_154; obj* x_155; obj* x_157; 
lean::dec(x_140);
lean::inc(x_0);
lean::inc(x_104);
x_154 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_104, x_0, x_142);
x_155 = lean::cnstr_get(x_154, 0);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_154, 1);
lean::inc(x_157);
lean::dec(x_154);
if (lean::obj_tag(x_155) == 0)
{
obj* x_161; obj* x_164; obj* x_165; 
lean::dec(x_0);
x_161 = lean::cnstr_get(x_155, 0);
lean::inc(x_161);
lean::dec(x_155);
if (lean::is_scalar(x_103)) {
 x_164 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_164 = x_103;
 lean::cnstr_set_tag(x_103, 0);
}
lean::cnstr_set(x_164, 0, x_161);
if (lean::is_scalar(x_112)) {
 x_165 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_165 = x_112;
}
lean::cnstr_set(x_165, 0, x_164);
lean::cnstr_set(x_165, 1, x_157);
return x_165;
}
else
{
obj* x_169; obj* x_171; 
lean::dec(x_155);
lean::dec(x_112);
lean::dec(x_103);
x_169 = l_lean_ir_cpp_emit__main__proc___closed__2;
lean::inc(x_169);
x_171 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_169, x_0, x_157);
return x_171;
}
}
}
}
}
}
lbl_64:
{
if (lean::obj_tag(x_62) == 0)
{
obj* x_173; obj* x_175; obj* x_176; 
lean::dec(x_11);
x_173 = lean::cnstr_get(x_62, 0);
lean::inc(x_173);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_175 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_175 = x_62;
}
if (lean::is_scalar(x_175)) {
 x_176 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_176 = x_175;
}
lean::cnstr_set(x_176, 0, x_173);
x_59 = x_176;
x_60 = x_63;
goto lbl_61;
}
else
{
obj* x_177; obj* x_180; obj* x_181; obj* x_183; 
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_177 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_177 = x_62;
}
lean::inc(x_0);
lean::inc(x_52);
x_180 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_52, x_0, x_63);
x_181 = lean::cnstr_get(x_180, 0);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_180, 1);
lean::inc(x_183);
lean::dec(x_180);
if (lean::obj_tag(x_181) == 0)
{
obj* x_187; obj* x_190; 
lean::dec(x_11);
x_187 = lean::cnstr_get(x_181, 0);
lean::inc(x_187);
lean::dec(x_181);
if (lean::is_scalar(x_177)) {
 x_190 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_190 = x_177;
 lean::cnstr_set_tag(x_177, 0);
}
lean::cnstr_set(x_190, 0, x_187);
x_59 = x_190;
x_60 = x_183;
goto lbl_61;
}
else
{
obj* x_192; obj* x_195; obj* x_196; obj* x_198; 
lean::dec(x_181);
x_192 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_0);
lean::inc(x_192);
x_195 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_192, x_0, x_183);
x_196 = lean::cnstr_get(x_195, 0);
lean::inc(x_196);
x_198 = lean::cnstr_get(x_195, 1);
lean::inc(x_198);
lean::dec(x_195);
if (lean::obj_tag(x_196) == 0)
{
obj* x_202; obj* x_205; 
lean::dec(x_11);
x_202 = lean::cnstr_get(x_196, 0);
lean::inc(x_202);
lean::dec(x_196);
if (lean::is_scalar(x_177)) {
 x_205 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_205 = x_177;
 lean::cnstr_set_tag(x_177, 0);
}
lean::cnstr_set(x_205, 0, x_202);
x_59 = x_205;
x_60 = x_198;
goto lbl_61;
}
else
{
obj* x_207; obj* x_210; obj* x_211; obj* x_213; 
lean::dec(x_196);
x_207 = l_lean_ir_cpp_emit__main__proc___closed__3;
lean::inc(x_0);
lean::inc(x_207);
x_210 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_207, x_0, x_198);
x_211 = lean::cnstr_get(x_210, 0);
lean::inc(x_211);
x_213 = lean::cnstr_get(x_210, 1);
lean::inc(x_213);
lean::dec(x_210);
if (lean::obj_tag(x_211) == 0)
{
obj* x_217; obj* x_220; 
lean::dec(x_11);
x_217 = lean::cnstr_get(x_211, 0);
lean::inc(x_217);
lean::dec(x_211);
if (lean::is_scalar(x_177)) {
 x_220 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_220 = x_177;
 lean::cnstr_set_tag(x_177, 0);
}
lean::cnstr_set(x_220, 0, x_217);
x_59 = x_220;
x_60 = x_213;
goto lbl_61;
}
else
{
obj* x_224; obj* x_225; obj* x_227; 
lean::dec(x_211);
lean::dec(x_177);
lean::inc(x_0);
x_224 = l_lean_ir_cpp_emit__fnid(x_11, x_0, x_213);
x_225 = lean::cnstr_get(x_224, 0);
lean::inc(x_225);
x_227 = lean::cnstr_get(x_224, 1);
lean::inc(x_227);
lean::dec(x_224);
x_59 = x_225;
x_60 = x_227;
goto lbl_61;
}
}
}
}
}
lbl_67:
{
if (lean::obj_tag(x_65) == 0)
{
obj* x_230; obj* x_232; obj* x_233; 
x_230 = lean::cnstr_get(x_65, 0);
lean::inc(x_230);
if (lean::is_shared(x_65)) {
 lean::dec(x_65);
 x_232 = lean::box(0);
} else {
 lean::cnstr_release(x_65, 0);
 x_232 = x_65;
}
if (lean::is_scalar(x_232)) {
 x_233 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_233 = x_232;
}
lean::cnstr_set(x_233, 0, x_230);
x_62 = x_233;
x_63 = x_66;
goto lbl_64;
}
else
{
obj* x_234; obj* x_235; obj* x_238; obj* x_239; obj* x_241; 
if (lean::is_shared(x_65)) {
 lean::dec(x_65);
 x_234 = lean::box(0);
} else {
 lean::cnstr_release(x_65, 0);
 x_234 = x_65;
}
x_235 = l_lean_ir_cpp_emit__main__proc___closed__4;
lean::inc(x_0);
lean::inc(x_235);
x_238 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_235, x_0, x_66);
x_239 = lean::cnstr_get(x_238, 0);
lean::inc(x_239);
x_241 = lean::cnstr_get(x_238, 1);
lean::inc(x_241);
lean::dec(x_238);
if (lean::obj_tag(x_239) == 0)
{
obj* x_244; obj* x_247; 
x_244 = lean::cnstr_get(x_239, 0);
lean::inc(x_244);
lean::dec(x_239);
if (lean::is_scalar(x_234)) {
 x_247 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_247 = x_234;
 lean::cnstr_set_tag(x_234, 0);
}
lean::cnstr_set(x_247, 0, x_244);
x_62 = x_247;
x_63 = x_241;
goto lbl_64;
}
else
{
obj* x_250; obj* x_253; obj* x_254; obj* x_256; 
lean::dec(x_239);
lean::dec(x_234);
x_250 = l_lean_ir_cpp_initialize__prefix;
lean::inc(x_0);
lean::inc(x_250);
x_253 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_250, x_0, x_241);
x_254 = lean::cnstr_get(x_253, 0);
lean::inc(x_254);
x_256 = lean::cnstr_get(x_253, 1);
lean::inc(x_256);
lean::dec(x_253);
x_62 = x_254;
x_63 = x_256;
goto lbl_64;
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
obj* x_4; obj* x_6; 
lean::dec(x_1);
x_4 = l_lean_ir_match__type___closed__5;
lean::inc(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_18; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
x_13 = l_lean_ir_cpp_emit__def(x_7, x_1, x_2);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 x_18 = x_13;
}
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_9);
lean::dec(x_1);
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_23 = x_14;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
return x_25;
}
else
{
lean::dec(x_18);
lean::dec(x_14);
x_0 = x_9;
x_2 = x_16;
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
lean::dec(x_30);
lean::dec(x_25);
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
 l_lean_ir_cpp_extract__m_monad = _init_l_lean_ir_cpp_extract__m_monad();
 l_lean_ir_cpp_extract__m_monad__except = _init_l_lean_ir_cpp_extract__m_monad__except();
 l_lean_ir_cpp_extract__m_monad__state = _init_l_lean_ir_cpp_extract__m_monad__state();
 l_lean_ir_cpp_extract__m_monad__reader = _init_l_lean_ir_cpp_extract__m_monad__reader();
 l_lean_ir_cpp_extract__m_monad__run = _init_l_lean_ir_cpp_extract__m_monad__run();
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
