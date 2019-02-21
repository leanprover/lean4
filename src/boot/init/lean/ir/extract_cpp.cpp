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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
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
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; obj* x_23; obj* x_24; 
lean::dec(x_6);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
lean::inc(x_1);
x_23 = lean::apply_2(x_0, x_1, x_19);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_27 = lean::cnstr_get(x_23, 1);
lean::inc(x_27);
lean::dec(x_23);
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
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_27);
return x_34;
}
else
{
obj* x_35; obj* x_38; obj* x_41; obj* x_42; obj* x_43; 
x_35 = lean::cnstr_get(x_23, 1);
lean::inc(x_35);
lean::dec(x_23);
x_38 = lean::cnstr_get(x_24, 0);
lean::inc(x_38);
lean::dec(x_24);
x_41 = l_option_has__repr___rarg___closed__3;
x_42 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_41, x_1, x_35);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
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
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_46);
return x_53;
}
else
{
obj* x_54; obj* x_55; obj* x_58; obj* x_59; 
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_54 = x_43;
} else {
 lean::dec(x_43);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_42, 1);
lean::inc(x_55);
lean::dec(x_42);
if (lean::is_scalar(x_54)) {
 x_58 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_58 = x_54;
}
lean::cnstr_set(x_58, 0, x_38);
x_59 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_ir_cpp_paren___rarg), 3, 0);
return x_2;
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
obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
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
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_6);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_2, x_19);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_34 = x_25;
} else {
 lean::inc(x_32);
 lean::dec(x_25);
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
lean::cnstr_set(x_36, 1, x_29);
return x_36;
}
else
{
obj* x_38; obj* x_41; 
lean::dec(x_25);
x_38 = lean::cnstr_get(x_24, 1);
lean::inc(x_38);
lean::dec(x_24);
x_41 = lean::apply_2(x_1, x_2, x_38);
return x_41;
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
obj* x_4; obj* x_5; 
lean::inc(x_1);
x_4 = l_lean_ir_cpp_fid2cpp(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
lean::dec(x_4);
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
x_15 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_3; obj* x_4; 
x_3 = l_lean_ir_cpp_fid2cpp(x_0, x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
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
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_6);
return x_13;
}
else
{
obj* x_14; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; 
x_14 = lean::cnstr_get(x_3, 1);
lean::inc(x_14);
lean::dec(x_3);
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
x_24 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
lean::dec(x_4);
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
x_15 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_10; 
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_16; 
lean::dec(x_1);
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
lean::dec(x_2);
x_16 = lean::apply_3(x_0, x_13, x_3, x_4);
return x_16;
}
else
{
obj* x_17; obj* x_22; obj* x_23; 
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
lean::dec(x_2);
lean::inc(x_3);
lean::inc(x_0);
x_22 = lean::apply_3(x_0, x_17, x_3, x_4);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_22, 1);
lean::inc(x_29);
lean::dec(x_22);
x_32 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_34 = x_23;
} else {
 lean::inc(x_32);
 lean::dec(x_23);
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
lean::cnstr_set(x_36, 1, x_29);
return x_36;
}
else
{
obj* x_38; obj* x_43; obj* x_44; 
lean::dec(x_23);
x_38 = lean::cnstr_get(x_22, 1);
lean::inc(x_38);
lean::dec(x_22);
lean::inc(x_3);
lean::inc(x_1);
x_43 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1, x_3, x_38);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_50; obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_50 = lean::cnstr_get(x_43, 1);
lean::inc(x_50);
lean::dec(x_43);
x_53 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 x_55 = x_44;
} else {
 lean::inc(x_53);
 lean::dec(x_44);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_50);
return x_57;
}
else
{
obj* x_59; obj* x_62; obj* x_64; obj* x_65; 
lean::dec(x_44);
x_59 = lean::cnstr_get(x_43, 1);
lean::inc(x_59);
lean::dec(x_43);
x_62 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_3);
x_64 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_62, x_3, x_59);
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
if (lean::obj_tag(x_65) == 0)
{
obj* x_71; obj* x_74; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_71 = lean::cnstr_get(x_64, 1);
lean::inc(x_71);
lean::dec(x_64);
x_74 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_76 = x_65;
} else {
 lean::inc(x_74);
 lean::dec(x_65);
 x_76 = lean::box(0);
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_74);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_71);
return x_78;
}
else
{
obj* x_80; 
lean::dec(x_65);
x_80 = lean::cnstr_get(x_64, 1);
lean::inc(x_80);
lean::dec(x_64);
x_2 = x_10;
x_4 = x_80;
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = l_lean_ir_cpp_emit__template__params___closed__1;
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
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
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_26; 
lean::dec(x_6);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_lean_ir_cpp_emit__template__params___closed__2;
x_23 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_1);
x_25 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_22, x_23, x_0, x_1, x_19);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
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
x_36 = lean::alloc_cnstr(0, 2, 0);
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
x_41 = l_lean_ir_cpp_emit__template__params___closed__4;
x_42 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_41, x_1, x_38);
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
uint8 x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit__type(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
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
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_6);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_1);
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_1, x_19);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_34 = x_25;
} else {
 lean::inc(x_32);
 lean::dec(x_25);
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
lean::cnstr_set(x_36, 1, x_29);
return x_36;
}
else
{
obj* x_38; obj* x_41; obj* x_44; 
lean::dec(x_25);
x_38 = lean::cnstr_get(x_24, 1);
lean::inc(x_38);
lean::dec(x_24);
x_41 = lean::cnstr_get(x_0, 0);
lean::inc(x_41);
lean::dec(x_0);
x_44 = l_lean_ir_cpp_emit__var(x_41, x_1, x_38);
return x_44;
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
obj* x_2; obj* x_4; obj* x_5; 
x_2 = l_lean_ir_cpp_emit__eos___closed__1;
lean::inc(x_0);
x_4 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_2, x_0, x_1);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_0);
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
lean::dec(x_4);
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
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_8);
return x_15;
}
else
{
obj* x_17; obj* x_20; obj* x_21; 
lean::dec(x_5);
x_17 = lean::cnstr_get(x_4, 1);
lean::inc(x_17);
lean::dec(x_4);
x_20 = l_lean_format_be___main___closed__1;
x_21 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_20, x_0, x_17);
return x_21;
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
obj* x_8; 
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_11; obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_1);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = l_lean_ir_cpp_emit__cases___main___closed__2;
lean::inc(x_2);
x_16 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_14, x_2, x_3);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_11);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_16, 1);
lean::inc(x_21);
lean::dec(x_16);
x_24 = lean::cnstr_get(x_17, 0);
if (lean::is_exclusive(x_17)) {
 x_26 = x_17;
} else {
 lean::inc(x_24);
 lean::dec(x_17);
 x_26 = lean::box(0);
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_24);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_21);
return x_28;
}
else
{
obj* x_30; obj* x_34; obj* x_35; 
lean::dec(x_17);
x_30 = lean::cnstr_get(x_16, 1);
lean::inc(x_30);
lean::dec(x_16);
lean::inc(x_2);
x_34 = l_lean_ir_cpp_emit__blockid(x_11, x_2, x_30);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
if (lean::obj_tag(x_35) == 0)
{
obj* x_38; obj* x_41; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_2);
x_38 = lean::cnstr_get(x_34, 1);
lean::inc(x_38);
lean::dec(x_34);
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
x_45 = lean::alloc_cnstr(0, 2, 0);
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
return x_50;
}
}
}
else
{
obj* x_51; obj* x_54; obj* x_56; obj* x_57; 
x_51 = lean::cnstr_get(x_0, 0);
lean::inc(x_51);
lean::dec(x_0);
x_54 = l_lean_ir_cpp_emit__cases___main___closed__3;
lean::inc(x_2);
x_56 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_54, x_2, x_3);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
if (lean::obj_tag(x_57) == 0)
{
obj* x_63; obj* x_66; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_51);
x_63 = lean::cnstr_get(x_56, 1);
lean::inc(x_63);
lean::dec(x_56);
x_66 = lean::cnstr_get(x_57, 0);
if (lean::is_exclusive(x_57)) {
 x_68 = x_57;
} else {
 lean::inc(x_66);
 lean::dec(x_57);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_66);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_63);
return x_70;
}
else
{
obj* x_72; obj* x_77; obj* x_78; 
lean::dec(x_57);
x_72 = lean::cnstr_get(x_56, 1);
lean::inc(x_72);
lean::dec(x_56);
lean::inc(x_2);
lean::inc(x_1);
x_77 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_1, x_2, x_72);
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
if (lean::obj_tag(x_78) == 0)
{
obj* x_84; obj* x_87; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_8);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_51);
x_84 = lean::cnstr_get(x_77, 1);
lean::inc(x_84);
lean::dec(x_77);
x_87 = lean::cnstr_get(x_78, 0);
if (lean::is_exclusive(x_78)) {
 x_89 = x_78;
} else {
 lean::inc(x_87);
 lean::dec(x_78);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_87);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_84);
return x_91;
}
else
{
obj* x_93; obj* x_96; obj* x_97; obj* x_99; obj* x_101; obj* x_102; 
lean::dec(x_78);
x_93 = lean::cnstr_get(x_77, 1);
lean::inc(x_93);
lean::dec(x_77);
x_96 = lean::mk_nat_obj(1u);
x_97 = lean::nat_add(x_1, x_96);
lean::dec(x_1);
x_99 = l_lean_ir_cpp_emit__cases___main___closed__4;
lean::inc(x_2);
x_101 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_99, x_2, x_93);
x_102 = lean::cnstr_get(x_101, 0);
lean::inc(x_102);
if (lean::obj_tag(x_102) == 0)
{
obj* x_108; obj* x_111; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_8);
lean::dec(x_2);
lean::dec(x_51);
lean::dec(x_97);
x_108 = lean::cnstr_get(x_101, 1);
lean::inc(x_108);
lean::dec(x_101);
x_111 = lean::cnstr_get(x_102, 0);
if (lean::is_exclusive(x_102)) {
 x_113 = x_102;
} else {
 lean::inc(x_111);
 lean::dec(x_102);
 x_113 = lean::box(0);
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_111);
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_108);
return x_115;
}
else
{
obj* x_117; obj* x_121; obj* x_122; 
lean::dec(x_102);
x_117 = lean::cnstr_get(x_101, 1);
lean::inc(x_117);
lean::dec(x_101);
lean::inc(x_2);
x_121 = l_lean_ir_cpp_emit__blockid(x_51, x_2, x_117);
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
if (lean::obj_tag(x_122) == 0)
{
obj* x_127; obj* x_130; obj* x_132; obj* x_133; obj* x_134; 
lean::dec(x_8);
lean::dec(x_2);
lean::dec(x_97);
x_127 = lean::cnstr_get(x_121, 1);
lean::inc(x_127);
lean::dec(x_121);
x_130 = lean::cnstr_get(x_122, 0);
if (lean::is_exclusive(x_122)) {
 x_132 = x_122;
} else {
 lean::inc(x_130);
 lean::dec(x_122);
 x_132 = lean::box(0);
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_130);
x_134 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_134, 0, x_133);
lean::cnstr_set(x_134, 1, x_127);
return x_134;
}
else
{
obj* x_136; obj* x_140; obj* x_141; 
lean::dec(x_122);
x_136 = lean::cnstr_get(x_121, 1);
lean::inc(x_136);
lean::dec(x_121);
lean::inc(x_2);
x_140 = l_lean_ir_cpp_emit__eos(x_2, x_136);
x_141 = lean::cnstr_get(x_140, 0);
lean::inc(x_141);
if (lean::obj_tag(x_141) == 0)
{
obj* x_146; obj* x_149; obj* x_151; obj* x_152; obj* x_153; 
lean::dec(x_8);
lean::dec(x_2);
lean::dec(x_97);
x_146 = lean::cnstr_get(x_140, 1);
lean::inc(x_146);
lean::dec(x_140);
x_149 = lean::cnstr_get(x_141, 0);
if (lean::is_exclusive(x_141)) {
 x_151 = x_141;
} else {
 lean::inc(x_149);
 lean::dec(x_141);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_149);
x_153 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_153, 0, x_152);
lean::cnstr_set(x_153, 1, x_146);
return x_153;
}
else
{
obj* x_155; 
lean::dec(x_141);
x_155 = lean::cnstr_get(x_140, 1);
lean::inc(x_155);
lean::dec(x_140);
x_0 = x_8;
x_1 = x_97;
x_3 = x_155;
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
obj* x_10; 
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_16; obj* x_18; obj* x_19; 
lean::dec(x_0);
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_16 = l_lean_ir_cpp_emit__case___main___closed__4;
lean::inc(x_2);
x_18 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_16, x_2, x_3);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
if (lean::obj_tag(x_19) == 0)
{
obj* x_23; obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_13);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_18, 1);
lean::inc(x_23);
lean::dec(x_18);
x_26 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_28 = x_19;
} else {
 lean::inc(x_26);
 lean::dec(x_19);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_26);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_23);
return x_30;
}
else
{
obj* x_32; obj* x_36; obj* x_37; 
lean::dec(x_19);
x_32 = lean::cnstr_get(x_18, 1);
lean::inc(x_32);
lean::dec(x_18);
lean::inc(x_2);
x_36 = l_lean_ir_cpp_emit__blockid(x_13, x_2, x_32);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_40; obj* x_43; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_2);
x_40 = lean::cnstr_get(x_36, 1);
lean::inc(x_40);
lean::dec(x_36);
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
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_40);
return x_47;
}
else
{
obj* x_49; obj* x_52; 
lean::dec(x_37);
x_49 = lean::cnstr_get(x_36, 1);
lean::inc(x_49);
lean::dec(x_36);
x_52 = l_lean_ir_cpp_emit__eos(x_2, x_49);
return x_52;
}
}
}
else
{
obj* x_53; 
x_53 = lean::cnstr_get(x_10, 1);
lean::inc(x_53);
if (lean::obj_tag(x_53) == 0)
{
obj* x_55; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_67; 
x_55 = lean::cnstr_get(x_1, 0);
lean::inc(x_55);
lean::dec(x_1);
x_58 = lean::cnstr_get(x_10, 0);
lean::inc(x_58);
lean::dec(x_10);
x_64 = lean::cnstr_get(x_2, 1);
lean::inc(x_64);
lean::inc(x_0);
x_67 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_64, x_0);
if (lean::obj_tag(x_67) == 0)
{
obj* x_71; 
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_55);
x_71 = l_lean_ir_cpp_emit__case___main___closed__5;
x_61 = x_71;
x_62 = x_3;
goto lbl_63;
}
else
{
obj* x_72; uint8 x_75; 
x_72 = lean::cnstr_get(x_67, 0);
lean::inc(x_72);
lean::dec(x_67);
x_75 = lean::unbox(x_72);
switch (x_75) {
case 0:
{
obj* x_76; obj* x_78; obj* x_79; 
x_76 = l_lean_ir_cpp_emit__case___main___closed__6;
lean::inc(x_2);
x_78 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_76, x_2, x_3);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
if (lean::obj_tag(x_79) == 0)
{
obj* x_84; obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_55);
x_84 = lean::cnstr_get(x_78, 1);
lean::inc(x_84);
lean::dec(x_78);
x_87 = lean::cnstr_get(x_79, 0);
if (lean::is_exclusive(x_79)) {
 x_89 = x_79;
} else {
 lean::inc(x_87);
 lean::dec(x_79);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_87);
x_61 = x_90;
x_62 = x_84;
goto lbl_63;
}
else
{
obj* x_92; obj* x_96; obj* x_97; 
lean::dec(x_79);
x_92 = lean::cnstr_get(x_78, 1);
lean::inc(x_92);
lean::dec(x_78);
lean::inc(x_2);
x_96 = l_lean_ir_cpp_emit__var(x_0, x_2, x_92);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
if (lean::obj_tag(x_97) == 0)
{
obj* x_101; obj* x_104; obj* x_106; obj* x_107; 
lean::dec(x_58);
lean::dec(x_55);
x_101 = lean::cnstr_get(x_96, 1);
lean::inc(x_101);
lean::dec(x_96);
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
x_61 = x_107;
x_62 = x_101;
goto lbl_63;
}
else
{
obj* x_109; obj* x_112; obj* x_114; obj* x_115; 
lean::dec(x_97);
x_109 = lean::cnstr_get(x_96, 1);
lean::inc(x_109);
lean::dec(x_96);
x_112 = l_lean_ir_cpp_emit__case___main___closed__7;
lean::inc(x_2);
x_114 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_112, x_2, x_109);
x_115 = lean::cnstr_get(x_114, 0);
lean::inc(x_115);
if (lean::obj_tag(x_115) == 0)
{
obj* x_119; obj* x_122; obj* x_124; obj* x_125; 
lean::dec(x_58);
lean::dec(x_55);
x_119 = lean::cnstr_get(x_114, 1);
lean::inc(x_119);
lean::dec(x_114);
x_122 = lean::cnstr_get(x_115, 0);
if (lean::is_exclusive(x_115)) {
 x_124 = x_115;
} else {
 lean::inc(x_122);
 lean::dec(x_115);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_122);
x_61 = x_125;
x_62 = x_119;
goto lbl_63;
}
else
{
obj* x_127; obj* x_131; obj* x_132; 
lean::dec(x_115);
x_127 = lean::cnstr_get(x_114, 1);
lean::inc(x_127);
lean::dec(x_114);
lean::inc(x_2);
x_131 = l_lean_ir_cpp_emit__blockid(x_58, x_2, x_127);
x_132 = lean::cnstr_get(x_131, 0);
lean::inc(x_132);
if (lean::obj_tag(x_132) == 0)
{
obj* x_135; obj* x_138; obj* x_140; obj* x_141; 
lean::dec(x_55);
x_135 = lean::cnstr_get(x_131, 1);
lean::inc(x_135);
lean::dec(x_131);
x_138 = lean::cnstr_get(x_132, 0);
if (lean::is_exclusive(x_132)) {
 x_140 = x_132;
} else {
 lean::inc(x_138);
 lean::dec(x_132);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_138);
x_61 = x_141;
x_62 = x_135;
goto lbl_63;
}
else
{
obj* x_143; obj* x_146; obj* x_148; obj* x_149; 
lean::dec(x_132);
x_143 = lean::cnstr_get(x_131, 1);
lean::inc(x_143);
lean::dec(x_131);
x_146 = l_lean_ir_cpp_emit__case___main___closed__8;
lean::inc(x_2);
x_148 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_146, x_2, x_143);
x_149 = lean::cnstr_get(x_148, 0);
lean::inc(x_149);
if (lean::obj_tag(x_149) == 0)
{
obj* x_152; obj* x_155; obj* x_157; obj* x_158; 
lean::dec(x_55);
x_152 = lean::cnstr_get(x_148, 1);
lean::inc(x_152);
lean::dec(x_148);
x_155 = lean::cnstr_get(x_149, 0);
if (lean::is_exclusive(x_149)) {
 x_157 = x_149;
} else {
 lean::inc(x_155);
 lean::dec(x_149);
 x_157 = lean::box(0);
}
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_155);
x_61 = x_158;
x_62 = x_152;
goto lbl_63;
}
else
{
obj* x_160; obj* x_164; obj* x_165; obj* x_167; 
lean::dec(x_149);
x_160 = lean::cnstr_get(x_148, 1);
lean::inc(x_160);
lean::dec(x_148);
lean::inc(x_2);
x_164 = l_lean_ir_cpp_emit__blockid(x_55, x_2, x_160);
x_165 = lean::cnstr_get(x_164, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_164, 1);
lean::inc(x_167);
lean::dec(x_164);
x_61 = x_165;
x_62 = x_167;
goto lbl_63;
}
}
}
}
}
}
case 3:
{
obj* x_170; obj* x_172; obj* x_173; 
x_170 = l_lean_ir_cpp_emit__case___main___closed__6;
lean::inc(x_2);
x_172 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_170, x_2, x_3);
x_173 = lean::cnstr_get(x_172, 0);
lean::inc(x_173);
if (lean::obj_tag(x_173) == 0)
{
obj* x_178; obj* x_181; obj* x_183; obj* x_184; 
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_55);
x_178 = lean::cnstr_get(x_172, 1);
lean::inc(x_178);
lean::dec(x_172);
x_181 = lean::cnstr_get(x_173, 0);
if (lean::is_exclusive(x_173)) {
 x_183 = x_173;
} else {
 lean::inc(x_181);
 lean::dec(x_173);
 x_183 = lean::box(0);
}
if (lean::is_scalar(x_183)) {
 x_184 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_184 = x_183;
}
lean::cnstr_set(x_184, 0, x_181);
x_61 = x_184;
x_62 = x_178;
goto lbl_63;
}
else
{
obj* x_186; obj* x_190; obj* x_191; 
lean::dec(x_173);
x_186 = lean::cnstr_get(x_172, 1);
lean::inc(x_186);
lean::dec(x_172);
lean::inc(x_2);
x_190 = l_lean_ir_cpp_emit__var(x_0, x_2, x_186);
x_191 = lean::cnstr_get(x_190, 0);
lean::inc(x_191);
if (lean::obj_tag(x_191) == 0)
{
obj* x_195; obj* x_198; obj* x_200; obj* x_201; 
lean::dec(x_58);
lean::dec(x_55);
x_195 = lean::cnstr_get(x_190, 1);
lean::inc(x_195);
lean::dec(x_190);
x_198 = lean::cnstr_get(x_191, 0);
if (lean::is_exclusive(x_191)) {
 x_200 = x_191;
} else {
 lean::inc(x_198);
 lean::dec(x_191);
 x_200 = lean::box(0);
}
if (lean::is_scalar(x_200)) {
 x_201 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_201 = x_200;
}
lean::cnstr_set(x_201, 0, x_198);
x_61 = x_201;
x_62 = x_195;
goto lbl_63;
}
else
{
obj* x_203; obj* x_206; obj* x_208; obj* x_209; 
lean::dec(x_191);
x_203 = lean::cnstr_get(x_190, 1);
lean::inc(x_203);
lean::dec(x_190);
x_206 = l_lean_ir_cpp_emit__case___main___closed__9;
lean::inc(x_2);
x_208 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_206, x_2, x_203);
x_209 = lean::cnstr_get(x_208, 0);
lean::inc(x_209);
if (lean::obj_tag(x_209) == 0)
{
obj* x_213; obj* x_216; obj* x_218; obj* x_219; 
lean::dec(x_58);
lean::dec(x_55);
x_213 = lean::cnstr_get(x_208, 1);
lean::inc(x_213);
lean::dec(x_208);
x_216 = lean::cnstr_get(x_209, 0);
if (lean::is_exclusive(x_209)) {
 x_218 = x_209;
} else {
 lean::inc(x_216);
 lean::dec(x_209);
 x_218 = lean::box(0);
}
if (lean::is_scalar(x_218)) {
 x_219 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_219 = x_218;
}
lean::cnstr_set(x_219, 0, x_216);
x_61 = x_219;
x_62 = x_213;
goto lbl_63;
}
else
{
obj* x_221; obj* x_225; obj* x_226; 
lean::dec(x_209);
x_221 = lean::cnstr_get(x_208, 1);
lean::inc(x_221);
lean::dec(x_208);
lean::inc(x_2);
x_225 = l_lean_ir_cpp_emit__blockid(x_55, x_2, x_221);
x_226 = lean::cnstr_get(x_225, 0);
lean::inc(x_226);
if (lean::obj_tag(x_226) == 0)
{
obj* x_229; obj* x_232; obj* x_234; obj* x_235; 
lean::dec(x_58);
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
x_61 = x_235;
x_62 = x_229;
goto lbl_63;
}
else
{
obj* x_237; obj* x_240; obj* x_242; obj* x_243; 
lean::dec(x_226);
x_237 = lean::cnstr_get(x_225, 1);
lean::inc(x_237);
lean::dec(x_225);
x_240 = l_lean_ir_cpp_emit__case___main___closed__8;
lean::inc(x_2);
x_242 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_240, x_2, x_237);
x_243 = lean::cnstr_get(x_242, 0);
lean::inc(x_243);
if (lean::obj_tag(x_243) == 0)
{
obj* x_246; obj* x_249; obj* x_251; obj* x_252; 
lean::dec(x_58);
x_246 = lean::cnstr_get(x_242, 1);
lean::inc(x_246);
lean::dec(x_242);
x_249 = lean::cnstr_get(x_243, 0);
if (lean::is_exclusive(x_243)) {
 x_251 = x_243;
} else {
 lean::inc(x_249);
 lean::dec(x_243);
 x_251 = lean::box(0);
}
if (lean::is_scalar(x_251)) {
 x_252 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_252 = x_251;
}
lean::cnstr_set(x_252, 0, x_249);
x_61 = x_252;
x_62 = x_246;
goto lbl_63;
}
else
{
obj* x_254; obj* x_258; obj* x_259; obj* x_261; 
lean::dec(x_243);
x_254 = lean::cnstr_get(x_242, 1);
lean::inc(x_254);
lean::dec(x_242);
lean::inc(x_2);
x_258 = l_lean_ir_cpp_emit__blockid(x_58, x_2, x_254);
x_259 = lean::cnstr_get(x_258, 0);
lean::inc(x_259);
x_261 = lean::cnstr_get(x_258, 1);
lean::inc(x_261);
lean::dec(x_258);
x_61 = x_259;
x_62 = x_261;
goto lbl_63;
}
}
}
}
}
}
default:
{
obj* x_267; 
lean::dec(x_0);
lean::dec(x_58);
lean::dec(x_55);
x_267 = l_lean_ir_cpp_emit__case___main___closed__5;
x_61 = x_267;
x_62 = x_3;
goto lbl_63;
}
}
}
lbl_63:
{
if (lean::obj_tag(x_61) == 0)
{
obj* x_269; obj* x_271; obj* x_272; obj* x_273; 
lean::dec(x_2);
x_269 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_271 = x_61;
} else {
 lean::inc(x_269);
 lean::dec(x_61);
 x_271 = lean::box(0);
}
if (lean::is_scalar(x_271)) {
 x_272 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_272 = x_271;
}
lean::cnstr_set(x_272, 0, x_269);
x_273 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_273, 0, x_272);
lean::cnstr_set(x_273, 1, x_62);
return x_273;
}
else
{
obj* x_275; 
lean::dec(x_61);
x_275 = l_lean_ir_cpp_emit__eos(x_2, x_62);
return x_275;
}
}
}
else
{
obj* x_278; 
lean::dec(x_10);
lean::dec(x_53);
x_278 = lean::box(0);
x_7 = x_278;
goto lbl_8;
}
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_281; obj* x_283; obj* x_284; obj* x_285; 
lean::dec(x_1);
lean::dec(x_2);
x_281 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_283 = x_4;
} else {
 lean::inc(x_281);
 lean::dec(x_4);
 x_283 = lean::box(0);
}
if (lean::is_scalar(x_283)) {
 x_284 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_284 = x_283;
}
lean::cnstr_set(x_284, 0, x_281);
x_285 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_285, 0, x_284);
lean::cnstr_set(x_285, 1, x_5);
return x_285;
}
else
{
obj* x_287; obj* x_289; obj* x_290; 
lean::dec(x_4);
x_287 = l_lean_ir_cpp_emit__case___main___closed__1;
lean::inc(x_2);
x_289 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_287, x_2, x_5);
x_290 = lean::cnstr_get(x_289, 0);
lean::inc(x_290);
if (lean::obj_tag(x_290) == 0)
{
obj* x_294; obj* x_297; obj* x_299; obj* x_300; obj* x_301; 
lean::dec(x_1);
lean::dec(x_2);
x_294 = lean::cnstr_get(x_289, 1);
lean::inc(x_294);
lean::dec(x_289);
x_297 = lean::cnstr_get(x_290, 0);
if (lean::is_exclusive(x_290)) {
 x_299 = x_290;
} else {
 lean::inc(x_297);
 lean::dec(x_290);
 x_299 = lean::box(0);
}
if (lean::is_scalar(x_299)) {
 x_300 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_300 = x_299;
}
lean::cnstr_set(x_300, 0, x_297);
x_301 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_301, 0, x_300);
lean::cnstr_set(x_301, 1, x_294);
return x_301;
}
else
{
obj* x_303; obj* x_306; obj* x_308; obj* x_309; 
lean::dec(x_290);
x_303 = lean::cnstr_get(x_289, 1);
lean::inc(x_303);
lean::dec(x_289);
x_306 = l_lean_format_be___main___closed__1;
lean::inc(x_2);
x_308 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_306, x_2, x_303);
x_309 = lean::cnstr_get(x_308, 0);
lean::inc(x_309);
if (lean::obj_tag(x_309) == 0)
{
obj* x_313; obj* x_316; obj* x_318; obj* x_319; obj* x_320; 
lean::dec(x_1);
lean::dec(x_2);
x_313 = lean::cnstr_get(x_308, 1);
lean::inc(x_313);
lean::dec(x_308);
x_316 = lean::cnstr_get(x_309, 0);
if (lean::is_exclusive(x_309)) {
 x_318 = x_309;
} else {
 lean::inc(x_316);
 lean::dec(x_309);
 x_318 = lean::box(0);
}
if (lean::is_scalar(x_318)) {
 x_319 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_319 = x_318;
}
lean::cnstr_set(x_319, 0, x_316);
x_320 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_320, 0, x_319);
lean::cnstr_set(x_320, 1, x_313);
return x_320;
}
else
{
obj* x_322; obj* x_325; obj* x_327; obj* x_328; 
lean::dec(x_309);
x_322 = lean::cnstr_get(x_308, 1);
lean::inc(x_322);
lean::dec(x_308);
x_325 = lean::mk_nat_obj(0u);
lean::inc(x_2);
x_327 = l_lean_ir_cpp_emit__cases___main(x_1, x_325, x_2, x_322);
x_328 = lean::cnstr_get(x_327, 0);
lean::inc(x_328);
if (lean::obj_tag(x_328) == 0)
{
obj* x_331; obj* x_334; obj* x_336; obj* x_337; obj* x_338; 
lean::dec(x_2);
x_331 = lean::cnstr_get(x_327, 1);
lean::inc(x_331);
lean::dec(x_327);
x_334 = lean::cnstr_get(x_328, 0);
if (lean::is_exclusive(x_328)) {
 x_336 = x_328;
} else {
 lean::inc(x_334);
 lean::dec(x_328);
 x_336 = lean::box(0);
}
if (lean::is_scalar(x_336)) {
 x_337 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_337 = x_336;
}
lean::cnstr_set(x_337, 0, x_334);
x_338 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_338, 0, x_337);
lean::cnstr_set(x_338, 1, x_331);
return x_338;
}
else
{
obj* x_340; obj* x_343; obj* x_345; obj* x_346; 
lean::dec(x_328);
x_340 = lean::cnstr_get(x_327, 1);
lean::inc(x_340);
lean::dec(x_327);
x_343 = l_lean_ir_cpp_emit__case___main___closed__2;
lean::inc(x_2);
x_345 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_343, x_2, x_340);
x_346 = lean::cnstr_get(x_345, 0);
lean::inc(x_346);
if (lean::obj_tag(x_346) == 0)
{
obj* x_349; obj* x_352; obj* x_354; obj* x_355; obj* x_356; 
lean::dec(x_2);
x_349 = lean::cnstr_get(x_345, 1);
lean::inc(x_349);
lean::dec(x_345);
x_352 = lean::cnstr_get(x_346, 0);
if (lean::is_exclusive(x_346)) {
 x_354 = x_346;
} else {
 lean::inc(x_352);
 lean::dec(x_346);
 x_354 = lean::box(0);
}
if (lean::is_scalar(x_354)) {
 x_355 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_355 = x_354;
}
lean::cnstr_set(x_355, 0, x_352);
x_356 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_356, 0, x_355);
lean::cnstr_set(x_356, 1, x_349);
return x_356;
}
else
{
obj* x_358; obj* x_361; 
lean::dec(x_346);
x_358 = lean::cnstr_get(x_345, 1);
lean::inc(x_358);
lean::dec(x_345);
x_361 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_306, x_2, x_358);
return x_361;
}
}
}
}
}
}
lbl_8:
{
obj* x_363; obj* x_365; obj* x_366; 
lean::dec(x_7);
x_363 = l_lean_ir_cpp_emit__case___main___closed__3;
lean::inc(x_2);
x_365 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_363, x_2, x_3);
x_366 = lean::cnstr_get(x_365, 0);
lean::inc(x_366);
if (lean::obj_tag(x_366) == 0)
{
obj* x_371; obj* x_374; obj* x_376; obj* x_377; obj* x_378; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_371 = lean::cnstr_get(x_365, 1);
lean::inc(x_371);
lean::dec(x_365);
x_374 = lean::cnstr_get(x_366, 0);
if (lean::is_exclusive(x_366)) {
 x_376 = x_366;
} else {
 lean::inc(x_374);
 lean::dec(x_366);
 x_376 = lean::box(0);
}
if (lean::is_scalar(x_376)) {
 x_377 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_377 = x_376;
}
lean::cnstr_set(x_377, 0, x_374);
x_378 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_378, 0, x_377);
lean::cnstr_set(x_378, 1, x_371);
return x_378;
}
else
{
obj* x_380; obj* x_383; obj* x_385; obj* x_386; 
lean::dec(x_366);
x_380 = lean::cnstr_get(x_365, 1);
lean::inc(x_380);
lean::dec(x_365);
x_383 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
x_385 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_383, x_2, x_380);
x_386 = lean::cnstr_get(x_385, 0);
lean::inc(x_386);
if (lean::obj_tag(x_386) == 0)
{
obj* x_389; obj* x_392; obj* x_394; obj* x_395; 
lean::dec(x_0);
x_389 = lean::cnstr_get(x_385, 1);
lean::inc(x_389);
lean::dec(x_385);
x_392 = lean::cnstr_get(x_386, 0);
if (lean::is_exclusive(x_386)) {
 x_394 = x_386;
} else {
 lean::inc(x_392);
 lean::dec(x_386);
 x_394 = lean::box(0);
}
if (lean::is_scalar(x_394)) {
 x_395 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_395 = x_394;
}
lean::cnstr_set(x_395, 0, x_392);
x_4 = x_395;
x_5 = x_389;
goto lbl_6;
}
else
{
obj* x_397; obj* x_401; obj* x_402; 
lean::dec(x_386);
x_397 = lean::cnstr_get(x_385, 1);
lean::inc(x_397);
lean::dec(x_385);
lean::inc(x_2);
x_401 = l_lean_ir_cpp_emit__var(x_0, x_2, x_397);
x_402 = lean::cnstr_get(x_401, 0);
lean::inc(x_402);
if (lean::obj_tag(x_402) == 0)
{
obj* x_404; obj* x_407; obj* x_409; obj* x_410; 
x_404 = lean::cnstr_get(x_401, 1);
lean::inc(x_404);
lean::dec(x_401);
x_407 = lean::cnstr_get(x_402, 0);
if (lean::is_exclusive(x_402)) {
 x_409 = x_402;
} else {
 lean::inc(x_407);
 lean::dec(x_402);
 x_409 = lean::box(0);
}
if (lean::is_scalar(x_409)) {
 x_410 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_410 = x_409;
}
lean::cnstr_set(x_410, 0, x_407);
x_4 = x_410;
x_5 = x_404;
goto lbl_6;
}
else
{
obj* x_411; obj* x_414; obj* x_417; obj* x_419; obj* x_420; 
x_411 = lean::cnstr_get(x_401, 1);
lean::inc(x_411);
lean::dec(x_401);
x_414 = lean::cnstr_get(x_402, 0);
lean::inc(x_414);
lean::dec(x_402);
x_417 = l_option_has__repr___rarg___closed__3;
lean::inc(x_2);
x_419 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_417, x_2, x_411);
x_420 = lean::cnstr_get(x_419, 0);
lean::inc(x_420);
if (lean::obj_tag(x_420) == 0)
{
obj* x_423; obj* x_426; obj* x_428; obj* x_429; 
lean::dec(x_414);
x_423 = lean::cnstr_get(x_419, 1);
lean::inc(x_423);
lean::dec(x_419);
x_426 = lean::cnstr_get(x_420, 0);
if (lean::is_exclusive(x_420)) {
 x_428 = x_420;
} else {
 lean::inc(x_426);
 lean::dec(x_420);
 x_428 = lean::box(0);
}
if (lean::is_scalar(x_428)) {
 x_429 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_429 = x_428;
}
lean::cnstr_set(x_429, 0, x_426);
x_4 = x_429;
x_5 = x_423;
goto lbl_6;
}
else
{
obj* x_430; obj* x_431; obj* x_434; 
if (lean::is_exclusive(x_420)) {
 lean::cnstr_release(x_420, 0);
 x_430 = x_420;
} else {
 lean::dec(x_420);
 x_430 = lean::box(0);
}
x_431 = lean::cnstr_get(x_419, 1);
lean::inc(x_431);
lean::dec(x_419);
if (lean::is_scalar(x_430)) {
 x_434 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_434 = x_430;
}
lean::cnstr_set(x_434, 0, x_414);
x_4 = x_434;
x_5 = x_431;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = l_lean_ir_cpp_emit__terminator___closed__1;
lean::inc(x_1);
x_10 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_8, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_6);
lean::dec(x_1);
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
lean::dec(x_10);
x_18 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_20 = x_11;
} else {
 lean::inc(x_18);
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
x_4 = x_15;
goto lbl_5;
}
else
{
obj* x_23; obj* x_27; obj* x_28; 
lean::dec(x_11);
x_23 = lean::cnstr_get(x_10, 1);
lean::inc(x_23);
lean::dec(x_10);
lean::inc(x_1);
x_27 = l_lean_ir_cpp_emit__var(x_6, x_1, x_23);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_31; obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_1);
x_31 = lean::cnstr_get(x_27, 1);
lean::inc(x_31);
lean::dec(x_27);
x_34 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_36 = x_28;
} else {
 lean::inc(x_34);
 lean::dec(x_28);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
x_3 = x_37;
x_4 = x_31;
goto lbl_5;
}
else
{
obj* x_39; obj* x_42; obj* x_43; obj* x_45; 
lean::dec(x_28);
x_39 = lean::cnstr_get(x_27, 1);
lean::inc(x_39);
lean::dec(x_27);
x_42 = l_lean_ir_cpp_emit__eos(x_1, x_39);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
x_3 = x_43;
x_4 = x_45;
goto lbl_5;
}
}
}
case 1:
{
obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_55; 
x_48 = lean::cnstr_get(x_0, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_0, 1);
lean::inc(x_50);
x_52 = l_lean_ir_cpp_emit__case___main(x_48, x_50, x_1, x_2);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
x_3 = x_53;
x_4 = x_55;
goto lbl_5;
}
default:
{
obj* x_58; obj* x_60; obj* x_62; obj* x_63; 
x_58 = lean::cnstr_get(x_0, 0);
lean::inc(x_58);
x_60 = l_lean_ir_cpp_emit__case___main___closed__4;
lean::inc(x_1);
x_62 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_60, x_1, x_2);
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
if (lean::obj_tag(x_63) == 0)
{
obj* x_67; obj* x_70; obj* x_72; obj* x_73; 
lean::dec(x_1);
lean::dec(x_58);
x_67 = lean::cnstr_get(x_62, 1);
lean::inc(x_67);
lean::dec(x_62);
x_70 = lean::cnstr_get(x_63, 0);
if (lean::is_exclusive(x_63)) {
 x_72 = x_63;
} else {
 lean::inc(x_70);
 lean::dec(x_63);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_70);
x_3 = x_73;
x_4 = x_67;
goto lbl_5;
}
else
{
obj* x_75; obj* x_79; obj* x_80; 
lean::dec(x_63);
x_75 = lean::cnstr_get(x_62, 1);
lean::inc(x_75);
lean::dec(x_62);
lean::inc(x_1);
x_79 = l_lean_ir_cpp_emit__blockid(x_58, x_1, x_75);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
if (lean::obj_tag(x_80) == 0)
{
obj* x_83; obj* x_86; obj* x_88; obj* x_89; 
lean::dec(x_1);
x_83 = lean::cnstr_get(x_79, 1);
lean::inc(x_83);
lean::dec(x_79);
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
x_3 = x_89;
x_4 = x_83;
goto lbl_5;
}
else
{
obj* x_91; obj* x_94; obj* x_95; obj* x_97; 
lean::dec(x_80);
x_91 = lean::cnstr_get(x_79, 1);
lean::inc(x_91);
lean::dec(x_79);
x_94 = l_lean_ir_cpp_emit__eos(x_1, x_91);
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_94, 1);
lean::inc(x_97);
lean::dec(x_94);
x_3 = x_95;
x_4 = x_97;
goto lbl_5;
}
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_100; obj* x_102; obj* x_103; uint8 x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_100 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_102 = x_3;
} else {
 lean::inc(x_100);
 lean::dec(x_3);
 x_102 = lean::box(0);
}
x_103 = l_lean_ir_terminator_to__format___main(x_0);
x_104 = 0;
x_105 = l_lean_ir_terminator_decorate__error___rarg___lambda__1___closed__1;
x_106 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_103);
lean::cnstr_set_scalar(x_106, sizeof(void*)*2, x_104);
x_107 = x_106;
x_108 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_109 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_109, 0, x_107);
lean::cnstr_set(x_109, 1, x_108);
lean::cnstr_set_scalar(x_109, sizeof(void*)*2, x_104);
x_110 = x_109;
x_111 = lean::box(1);
x_112 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_112, 0, x_110);
lean::cnstr_set(x_112, 1, x_111);
lean::cnstr_set_scalar(x_112, sizeof(void*)*2, x_104);
x_113 = x_112;
x_114 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_100);
lean::cnstr_set_scalar(x_114, sizeof(void*)*2, x_104);
x_115 = x_114;
if (lean::is_scalar(x_102)) {
 x_116 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_116 = x_102;
}
lean::cnstr_set(x_116, 0, x_115);
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_4);
return x_117;
}
else
{
obj* x_119; 
lean::dec(x_0);
x_119 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_119, 0, x_3);
lean::cnstr_set(x_119, 1, x_4);
return x_119;
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = l_lean_ir_cpp_emit__type__size___closed__1;
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
x_9 = lean::cnstr_get(x_5, 1);
lean::inc(x_9);
lean::dec(x_5);
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
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_9);
return x_16;
}
else
{
obj* x_18; obj* x_21; obj* x_23; obj* x_24; 
lean::dec(x_6);
x_18 = lean::cnstr_get(x_5, 1);
lean::inc(x_18);
lean::dec(x_5);
x_21 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_23 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_21, x_1, x_18);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_27 = lean::cnstr_get(x_23, 1);
lean::inc(x_27);
lean::dec(x_23);
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
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_27);
return x_34;
}
else
{
obj* x_36; obj* x_40; obj* x_41; 
lean::dec(x_24);
x_36 = lean::cnstr_get(x_23, 1);
lean::inc(x_36);
lean::dec(x_23);
lean::inc(x_1);
x_40 = l_lean_ir_cpp_emit__type(x_0, x_1, x_36);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_44; obj* x_47; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_1);
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
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_44);
return x_51;
}
else
{
obj* x_52; obj* x_55; obj* x_58; obj* x_59; obj* x_60; 
x_52 = lean::cnstr_get(x_40, 1);
lean::inc(x_52);
lean::dec(x_40);
x_55 = lean::cnstr_get(x_41, 0);
lean::inc(x_55);
lean::dec(x_41);
x_58 = l_option_has__repr___rarg___closed__3;
x_59 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_58, x_1, x_52);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
if (lean::obj_tag(x_60) == 0)
{
obj* x_63; obj* x_66; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_55);
x_63 = lean::cnstr_get(x_59, 1);
lean::inc(x_63);
lean::dec(x_59);
x_66 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_68 = x_60;
} else {
 lean::inc(x_66);
 lean::dec(x_60);
 x_68 = lean::box(0);
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_66);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_63);
return x_70;
}
else
{
obj* x_71; obj* x_72; obj* x_75; obj* x_76; 
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_71 = x_60;
} else {
 lean::dec(x_60);
 x_71 = lean::box(0);
}
x_72 = lean::cnstr_get(x_59, 1);
lean::inc(x_72);
lean::dec(x_59);
if (lean::is_scalar(x_71)) {
 x_75 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_75 = x_71;
}
lean::cnstr_set(x_75, 0, x_55);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_72);
return x_76;
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
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_0, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
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
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_6);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_2, x_19);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_34 = x_25;
} else {
 lean::inc(x_32);
 lean::dec(x_25);
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
lean::cnstr_set(x_36, 1, x_29);
return x_36;
}
else
{
obj* x_38; obj* x_42; obj* x_43; 
lean::dec(x_25);
x_38 = lean::cnstr_get(x_24, 1);
lean::inc(x_38);
lean::dec(x_24);
lean::inc(x_2);
x_42 = l_lean_ir_cpp_emit__var(x_1, x_2, x_38);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_2);
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
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_46);
return x_53;
}
else
{
obj* x_54; obj* x_57; obj* x_60; obj* x_61; obj* x_62; 
x_54 = lean::cnstr_get(x_42, 1);
lean::inc(x_54);
lean::dec(x_42);
x_57 = lean::cnstr_get(x_43, 0);
lean::inc(x_57);
lean::dec(x_43);
x_60 = l_option_has__repr___rarg___closed__3;
x_61 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_60, x_2, x_54);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
obj* x_65; obj* x_68; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_57);
x_65 = lean::cnstr_get(x_61, 1);
lean::inc(x_65);
lean::dec(x_61);
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
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_65);
return x_72;
}
else
{
obj* x_73; obj* x_74; obj* x_77; obj* x_78; 
if (lean::is_exclusive(x_62)) {
 lean::cnstr_release(x_62, 0);
 x_73 = x_62;
} else {
 lean::dec(x_62);
 x_73 = lean::box(0);
}
x_74 = lean::cnstr_get(x_61, 1);
lean::inc(x_74);
lean::dec(x_61);
if (lean::is_scalar(x_73)) {
 x_77 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_77 = x_73;
}
lean::cnstr_set(x_77, 0, x_57);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_74);
return x_78;
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
obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
lean::inc(x_4);
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
x_6 = x_19;
x_7 = x_13;
goto lbl_8;
}
else
{
obj* x_21; obj* x_24; obj* x_26; obj* x_27; obj* x_29; 
lean::dec(x_11);
x_21 = lean::cnstr_get(x_10, 1);
lean::inc(x_21);
lean::dec(x_10);
x_24 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_4);
x_26 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_24, x_4, x_21);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
x_6 = x_27;
x_7 = x_29;
goto lbl_8;
}
lbl_8:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_36; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_36 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_38 = x_6;
} else {
 lean::inc(x_36);
 lean::dec(x_6);
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
lean::cnstr_set(x_40, 1, x_7);
return x_40;
}
else
{
obj* x_43; obj* x_44; 
lean::dec(x_6);
lean::inc(x_4);
x_43 = l_lean_ir_cpp_emit__var(x_1, x_4, x_7);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_49; obj* x_52; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_49 = lean::cnstr_get(x_43, 1);
lean::inc(x_49);
lean::dec(x_43);
x_52 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 x_54 = x_44;
} else {
 lean::inc(x_52);
 lean::dec(x_44);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_52);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_49);
return x_56;
}
else
{
obj* x_58; obj* x_61; obj* x_63; obj* x_64; 
lean::dec(x_44);
x_58 = lean::cnstr_get(x_43, 1);
lean::inc(x_58);
lean::dec(x_43);
x_61 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_4);
x_63 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_61, x_4, x_58);
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
if (lean::obj_tag(x_64) == 0)
{
obj* x_69; obj* x_72; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_69 = lean::cnstr_get(x_63, 1);
lean::inc(x_69);
lean::dec(x_63);
x_72 = lean::cnstr_get(x_64, 0);
if (lean::is_exclusive(x_64)) {
 x_74 = x_64;
} else {
 lean::inc(x_72);
 lean::dec(x_64);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_72);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_69);
return x_76;
}
else
{
obj* x_78; obj* x_82; obj* x_83; 
lean::dec(x_64);
x_78 = lean::cnstr_get(x_63, 1);
lean::inc(x_78);
lean::dec(x_63);
lean::inc(x_4);
x_82 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_4, x_78);
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
if (lean::obj_tag(x_83) == 0)
{
obj* x_87; obj* x_90; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_4);
lean::dec(x_2);
x_87 = lean::cnstr_get(x_82, 1);
lean::inc(x_87);
lean::dec(x_82);
x_90 = lean::cnstr_get(x_83, 0);
if (lean::is_exclusive(x_83)) {
 x_92 = x_83;
} else {
 lean::inc(x_90);
 lean::dec(x_83);
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
lean::cnstr_set(x_94, 1, x_87);
return x_94;
}
else
{
obj* x_96; obj* x_100; obj* x_101; 
lean::dec(x_83);
x_96 = lean::cnstr_get(x_82, 1);
lean::inc(x_96);
lean::dec(x_82);
lean::inc(x_4);
x_100 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_61, x_4, x_96);
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
if (lean::obj_tag(x_101) == 0)
{
obj* x_105; obj* x_108; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_4);
lean::dec(x_2);
x_105 = lean::cnstr_get(x_100, 1);
lean::inc(x_105);
lean::dec(x_100);
x_108 = lean::cnstr_get(x_101, 0);
if (lean::is_exclusive(x_101)) {
 x_110 = x_101;
} else {
 lean::inc(x_108);
 lean::dec(x_101);
 x_110 = lean::box(0);
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_108);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_105);
return x_112;
}
else
{
obj* x_114; obj* x_117; 
lean::dec(x_101);
x_114 = lean::cnstr_get(x_100, 1);
lean::inc(x_114);
lean::dec(x_100);
x_117 = l_lean_ir_cpp_emit__var(x_2, x_4, x_114);
return x_117;
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
obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
lean::inc(x_4);
x_10 = l_lean_ir_cpp_emit__var(x_0, x_4, x_5);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_3);
x_14 = lean::cnstr_get(x_10, 1);
lean::inc(x_14);
lean::dec(x_10);
x_17 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_19 = x_11;
} else {
 lean::inc(x_17);
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
x_7 = x_14;
goto lbl_8;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_28; 
lean::dec(x_11);
x_22 = lean::cnstr_get(x_10, 1);
lean::inc(x_22);
lean::dec(x_10);
x_25 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_4);
x_27 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_25, x_4, x_22);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_31; obj* x_34; obj* x_36; obj* x_37; 
lean::dec(x_3);
x_31 = lean::cnstr_get(x_27, 1);
lean::inc(x_31);
lean::dec(x_27);
x_34 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_36 = x_28;
} else {
 lean::inc(x_34);
 lean::dec(x_28);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
x_6 = x_37;
x_7 = x_31;
goto lbl_8;
}
else
{
obj* x_39; obj* x_43; obj* x_44; obj* x_46; 
lean::dec(x_28);
x_39 = lean::cnstr_get(x_27, 1);
lean::inc(x_39);
lean::dec(x_27);
lean::inc(x_4);
x_43 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_4, x_39);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
x_6 = x_44;
x_7 = x_46;
goto lbl_8;
}
}
lbl_8:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_52; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
x_52 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_54 = x_6;
} else {
 lean::inc(x_52);
 lean::dec(x_6);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_52);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_7);
return x_56;
}
else
{
obj* x_58; obj* x_60; obj* x_61; 
lean::dec(x_6);
x_58 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_4);
x_60 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_58, x_4, x_7);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
if (lean::obj_tag(x_61) == 0)
{
obj* x_66; obj* x_69; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
x_66 = lean::cnstr_get(x_60, 1);
lean::inc(x_66);
lean::dec(x_60);
x_69 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_71 = x_61;
} else {
 lean::inc(x_69);
 lean::dec(x_61);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_69);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_66);
return x_73;
}
else
{
obj* x_75; obj* x_79; obj* x_80; 
lean::dec(x_61);
x_75 = lean::cnstr_get(x_60, 1);
lean::inc(x_75);
lean::dec(x_60);
lean::inc(x_4);
x_79 = l_lean_ir_cpp_emit__var(x_1, x_4, x_75);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
if (lean::obj_tag(x_80) == 0)
{
obj* x_84; obj* x_87; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_4);
lean::dec(x_2);
x_84 = lean::cnstr_get(x_79, 1);
lean::inc(x_84);
lean::dec(x_79);
x_87 = lean::cnstr_get(x_80, 0);
if (lean::is_exclusive(x_80)) {
 x_89 = x_80;
} else {
 lean::inc(x_87);
 lean::dec(x_80);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_87);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_84);
return x_91;
}
else
{
obj* x_93; obj* x_96; obj* x_98; obj* x_99; 
lean::dec(x_80);
x_93 = lean::cnstr_get(x_79, 1);
lean::inc(x_93);
lean::dec(x_79);
x_96 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_4);
x_98 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_96, x_4, x_93);
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
if (lean::obj_tag(x_99) == 0)
{
obj* x_103; obj* x_106; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_4);
lean::dec(x_2);
x_103 = lean::cnstr_get(x_98, 1);
lean::inc(x_103);
lean::dec(x_98);
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
x_110 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_103);
return x_110;
}
else
{
obj* x_112; obj* x_116; obj* x_117; 
lean::dec(x_99);
x_112 = lean::cnstr_get(x_98, 1);
lean::inc(x_112);
lean::dec(x_98);
lean::inc(x_4);
x_116 = l_lean_ir_cpp_emit__var(x_2, x_4, x_112);
x_117 = lean::cnstr_get(x_116, 0);
lean::inc(x_117);
if (lean::obj_tag(x_117) == 0)
{
obj* x_120; obj* x_123; obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_4);
x_120 = lean::cnstr_get(x_116, 1);
lean::inc(x_120);
lean::dec(x_116);
x_123 = lean::cnstr_get(x_117, 0);
if (lean::is_exclusive(x_117)) {
 x_125 = x_117;
} else {
 lean::inc(x_123);
 lean::dec(x_117);
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
lean::cnstr_set(x_127, 1, x_120);
return x_127;
}
else
{
obj* x_128; obj* x_131; obj* x_134; obj* x_135; obj* x_136; 
x_128 = lean::cnstr_get(x_116, 1);
lean::inc(x_128);
lean::dec(x_116);
x_131 = lean::cnstr_get(x_117, 0);
lean::inc(x_131);
lean::dec(x_117);
x_134 = l_option_has__repr___rarg___closed__3;
x_135 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_134, x_4, x_128);
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
if (lean::obj_tag(x_136) == 0)
{
obj* x_139; obj* x_142; obj* x_144; obj* x_145; obj* x_146; 
lean::dec(x_131);
x_139 = lean::cnstr_get(x_135, 1);
lean::inc(x_139);
lean::dec(x_135);
x_142 = lean::cnstr_get(x_136, 0);
if (lean::is_exclusive(x_136)) {
 x_144 = x_136;
} else {
 lean::inc(x_142);
 lean::dec(x_136);
 x_144 = lean::box(0);
}
if (lean::is_scalar(x_144)) {
 x_145 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_145 = x_144;
}
lean::cnstr_set(x_145, 0, x_142);
x_146 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_139);
return x_146;
}
else
{
obj* x_147; obj* x_148; obj* x_151; obj* x_152; 
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 x_147 = x_136;
} else {
 lean::dec(x_136);
 x_147 = lean::box(0);
}
x_148 = lean::cnstr_get(x_135, 1);
lean::inc(x_148);
lean::dec(x_135);
if (lean::is_scalar(x_147)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_147;
}
lean::cnstr_set(x_151, 0, x_131);
x_152 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_148);
return x_152;
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
obj* x_74; obj* x_75; 
lean::inc(x_5);
x_74 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
if (lean::obj_tag(x_75) == 0)
{
obj* x_77; obj* x_80; obj* x_82; obj* x_83; 
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
lean::dec(x_74);
x_80 = lean::cnstr_get(x_75, 0);
if (lean::is_exclusive(x_75)) {
 x_82 = x_75;
} else {
 lean::inc(x_80);
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
obj* x_85; obj* x_88; obj* x_90; obj* x_91; obj* x_93; 
lean::dec(x_75);
x_85 = lean::cnstr_get(x_74, 1);
lean::inc(x_85);
lean::dec(x_74);
x_88 = l_lean_ir_cpp_emit__assign__binop___closed__37;
lean::inc(x_5);
x_90 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_88, x_5, x_85);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
x_9 = x_91;
x_10 = x_93;
goto lbl_11;
}
}
default:
{
obj* x_96; 
x_96 = lean::box(0);
x_7 = x_96;
goto lbl_8;
}
}
}
case 24:
{
obj* x_98; obj* x_99; 
lean::inc(x_5);
x_98 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
if (lean::obj_tag(x_99) == 0)
{
obj* x_104; obj* x_107; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_104 = lean::cnstr_get(x_98, 1);
lean::inc(x_104);
lean::dec(x_98);
x_107 = lean::cnstr_get(x_99, 0);
if (lean::is_exclusive(x_99)) {
 x_109 = x_99;
} else {
 lean::inc(x_107);
 lean::dec(x_99);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
x_111 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_104);
return x_111;
}
else
{
obj* x_113; obj* x_116; obj* x_118; obj* x_119; 
lean::dec(x_99);
x_113 = lean::cnstr_get(x_98, 1);
lean::inc(x_113);
lean::dec(x_98);
x_116 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_5);
x_118 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_116, x_5, x_113);
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
if (lean::obj_tag(x_119) == 0)
{
obj* x_124; obj* x_127; obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_124 = lean::cnstr_get(x_118, 1);
lean::inc(x_124);
lean::dec(x_118);
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
x_131 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_124);
return x_131;
}
else
{
obj* x_133; obj* x_136; obj* x_139; 
lean::dec(x_119);
x_133 = lean::cnstr_get(x_118, 1);
lean::inc(x_133);
lean::dec(x_118);
x_136 = lean::cnstr_get(x_5, 1);
lean::inc(x_136);
lean::inc(x_4);
x_139 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_136, x_4);
if (lean::obj_tag(x_139) == 0)
{
obj* x_140; obj* x_142; obj* x_143; obj* x_145; 
x_140 = l_lean_ir_cpp_emit__assign__binop___closed__38;
lean::inc(x_5);
x_142 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_140, x_5, x_133);
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_142, 1);
lean::inc(x_145);
lean::dec(x_142);
x_9 = x_143;
x_10 = x_145;
goto lbl_11;
}
else
{
obj* x_148; uint8 x_151; obj* x_152; obj* x_153; uint8 x_154; 
x_148 = lean::cnstr_get(x_139, 0);
lean::inc(x_148);
lean::dec(x_139);
x_151 = lean::unbox(x_148);
x_152 = l_lean_ir_type2id___main(x_151);
x_153 = l_lean_ir_valid__assign__unop__types___closed__1;
x_154 = lean::nat_dec_eq(x_152, x_153);
lean::dec(x_152);
if (x_154 == 0)
{
obj* x_156; obj* x_158; obj* x_159; obj* x_161; 
x_156 = l_lean_ir_cpp_emit__assign__binop___closed__38;
lean::inc(x_5);
x_158 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_156, x_5, x_133);
x_159 = lean::cnstr_get(x_158, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_158, 1);
lean::inc(x_161);
lean::dec(x_158);
x_9 = x_159;
x_10 = x_161;
goto lbl_11;
}
else
{
obj* x_164; obj* x_166; obj* x_167; obj* x_169; 
x_164 = l_lean_ir_cpp_emit__assign__binop___closed__39;
lean::inc(x_5);
x_166 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_164, x_5, x_133);
x_167 = lean::cnstr_get(x_166, 0);
lean::inc(x_167);
x_169 = lean::cnstr_get(x_166, 1);
lean::inc(x_169);
lean::dec(x_166);
x_9 = x_167;
x_10 = x_169;
goto lbl_11;
}
}
}
}
}
case 25:
{
obj* x_173; obj* x_174; 
lean::inc(x_5);
x_173 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_174 = lean::cnstr_get(x_173, 0);
lean::inc(x_174);
if (lean::obj_tag(x_174) == 0)
{
obj* x_176; obj* x_179; obj* x_181; obj* x_182; 
x_176 = lean::cnstr_get(x_173, 1);
lean::inc(x_176);
lean::dec(x_173);
x_179 = lean::cnstr_get(x_174, 0);
if (lean::is_exclusive(x_174)) {
 x_181 = x_174;
} else {
 lean::inc(x_179);
 lean::dec(x_174);
 x_181 = lean::box(0);
}
if (lean::is_scalar(x_181)) {
 x_182 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_182 = x_181;
}
lean::cnstr_set(x_182, 0, x_179);
x_9 = x_182;
x_10 = x_176;
goto lbl_11;
}
else
{
obj* x_184; obj* x_187; obj* x_189; obj* x_190; obj* x_192; 
lean::dec(x_174);
x_184 = lean::cnstr_get(x_173, 1);
lean::inc(x_184);
lean::dec(x_173);
x_187 = l_lean_ir_cpp_emit__assign__binop___closed__40;
lean::inc(x_5);
x_189 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_187, x_5, x_184);
x_190 = lean::cnstr_get(x_189, 0);
lean::inc(x_190);
x_192 = lean::cnstr_get(x_189, 1);
lean::inc(x_192);
lean::dec(x_189);
x_9 = x_190;
x_10 = x_192;
goto lbl_11;
}
}
default:
{
obj* x_196; obj* x_197; 
lean::inc(x_5);
x_196 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_197 = lean::cnstr_get(x_196, 0);
lean::inc(x_197);
if (lean::obj_tag(x_197) == 0)
{
obj* x_199; obj* x_202; obj* x_204; obj* x_205; 
x_199 = lean::cnstr_get(x_196, 1);
lean::inc(x_199);
lean::dec(x_196);
x_202 = lean::cnstr_get(x_197, 0);
if (lean::is_exclusive(x_197)) {
 x_204 = x_197;
} else {
 lean::inc(x_202);
 lean::dec(x_197);
 x_204 = lean::box(0);
}
if (lean::is_scalar(x_204)) {
 x_205 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_205 = x_204;
}
lean::cnstr_set(x_205, 0, x_202);
x_9 = x_205;
x_10 = x_199;
goto lbl_11;
}
else
{
obj* x_207; obj* x_210; obj* x_212; obj* x_213; obj* x_215; 
lean::dec(x_197);
x_207 = lean::cnstr_get(x_196, 1);
lean::inc(x_207);
lean::dec(x_196);
x_210 = l_lean_ir_cpp_emit__assign__binop___closed__41;
lean::inc(x_5);
x_212 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_210, x_5, x_207);
x_213 = lean::cnstr_get(x_212, 0);
lean::inc(x_213);
x_215 = lean::cnstr_get(x_212, 1);
lean::inc(x_215);
lean::dec(x_212);
x_9 = x_213;
x_10 = x_215;
goto lbl_11;
}
}
}
lbl_8:
{
obj* x_219; obj* x_220; obj* x_223; obj* x_224; 
lean::dec(x_7);
lean::inc(x_5);
x_223 = l_lean_ir_cpp_emit__var(x_0, x_5, x_6);
x_224 = lean::cnstr_get(x_223, 0);
lean::inc(x_224);
if (lean::obj_tag(x_224) == 0)
{
obj* x_226; obj* x_229; obj* x_231; obj* x_232; 
x_226 = lean::cnstr_get(x_223, 1);
lean::inc(x_226);
lean::dec(x_223);
x_229 = lean::cnstr_get(x_224, 0);
if (lean::is_exclusive(x_224)) {
 x_231 = x_224;
} else {
 lean::inc(x_229);
 lean::dec(x_224);
 x_231 = lean::box(0);
}
if (lean::is_scalar(x_231)) {
 x_232 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_232 = x_231;
}
lean::cnstr_set(x_232, 0, x_229);
x_219 = x_232;
x_220 = x_226;
goto lbl_221;
}
else
{
obj* x_234; obj* x_237; obj* x_239; obj* x_240; 
lean::dec(x_224);
x_234 = lean::cnstr_get(x_223, 1);
lean::inc(x_234);
lean::dec(x_223);
x_237 = l_lean_ir_cpp_emit__assign__binop___closed__1;
lean::inc(x_5);
x_239 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_237, x_5, x_234);
x_240 = lean::cnstr_get(x_239, 0);
lean::inc(x_240);
if (lean::obj_tag(x_240) == 0)
{
obj* x_242; obj* x_245; obj* x_247; obj* x_248; 
x_242 = lean::cnstr_get(x_239, 1);
lean::inc(x_242);
lean::dec(x_239);
x_245 = lean::cnstr_get(x_240, 0);
if (lean::is_exclusive(x_240)) {
 x_247 = x_240;
} else {
 lean::inc(x_245);
 lean::dec(x_240);
 x_247 = lean::box(0);
}
if (lean::is_scalar(x_247)) {
 x_248 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_248 = x_247;
}
lean::cnstr_set(x_248, 0, x_245);
x_219 = x_248;
x_220 = x_242;
goto lbl_221;
}
else
{
obj* x_250; obj* x_254; obj* x_255; obj* x_257; 
lean::dec(x_240);
x_250 = lean::cnstr_get(x_239, 1);
lean::inc(x_250);
lean::dec(x_239);
lean::inc(x_5);
x_254 = l_lean_ir_cpp_emit__template__param(x_1, x_5, x_250);
x_255 = lean::cnstr_get(x_254, 0);
lean::inc(x_255);
x_257 = lean::cnstr_get(x_254, 1);
lean::inc(x_257);
lean::dec(x_254);
x_219 = x_255;
x_220 = x_257;
goto lbl_221;
}
}
lbl_221:
{
if (lean::obj_tag(x_219) == 0)
{
obj* x_263; obj* x_265; obj* x_266; obj* x_267; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_263 = lean::cnstr_get(x_219, 0);
if (lean::is_exclusive(x_219)) {
 x_265 = x_219;
} else {
 lean::inc(x_263);
 lean::dec(x_219);
 x_265 = lean::box(0);
}
if (lean::is_scalar(x_265)) {
 x_266 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_266 = x_265;
}
lean::cnstr_set(x_266, 0, x_263);
x_267 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_267, 0, x_266);
lean::cnstr_set(x_267, 1, x_220);
return x_267;
}
else
{
obj* x_269; obj* x_271; obj* x_272; 
lean::dec(x_219);
x_269 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_5);
x_271 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_269, x_5, x_220);
x_272 = lean::cnstr_get(x_271, 0);
lean::inc(x_272);
if (lean::obj_tag(x_272) == 0)
{
obj* x_277; obj* x_280; obj* x_282; obj* x_283; obj* x_284; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_277 = lean::cnstr_get(x_271, 1);
lean::inc(x_277);
lean::dec(x_271);
x_280 = lean::cnstr_get(x_272, 0);
if (lean::is_exclusive(x_272)) {
 x_282 = x_272;
} else {
 lean::inc(x_280);
 lean::dec(x_272);
 x_282 = lean::box(0);
}
if (lean::is_scalar(x_282)) {
 x_283 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_283 = x_282;
}
lean::cnstr_set(x_283, 0, x_280);
x_284 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_284, 0, x_283);
lean::cnstr_set(x_284, 1, x_277);
return x_284;
}
else
{
obj* x_286; obj* x_290; obj* x_291; 
lean::dec(x_272);
x_286 = lean::cnstr_get(x_271, 1);
lean::inc(x_286);
lean::dec(x_271);
lean::inc(x_5);
x_290 = l_lean_ir_cpp_emit__var(x_3, x_5, x_286);
x_291 = lean::cnstr_get(x_290, 0);
lean::inc(x_291);
if (lean::obj_tag(x_291) == 0)
{
obj* x_295; obj* x_298; obj* x_300; obj* x_301; obj* x_302; 
lean::dec(x_5);
lean::dec(x_4);
x_295 = lean::cnstr_get(x_290, 1);
lean::inc(x_295);
lean::dec(x_290);
x_298 = lean::cnstr_get(x_291, 0);
if (lean::is_exclusive(x_291)) {
 x_300 = x_291;
} else {
 lean::inc(x_298);
 lean::dec(x_291);
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
lean::cnstr_set(x_302, 1, x_295);
return x_302;
}
else
{
obj* x_304; obj* x_307; obj* x_309; obj* x_310; 
lean::dec(x_291);
x_304 = lean::cnstr_get(x_290, 1);
lean::inc(x_304);
lean::dec(x_290);
x_307 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_5);
x_309 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_307, x_5, x_304);
x_310 = lean::cnstr_get(x_309, 0);
lean::inc(x_310);
if (lean::obj_tag(x_310) == 0)
{
obj* x_314; obj* x_317; obj* x_319; obj* x_320; obj* x_321; 
lean::dec(x_5);
lean::dec(x_4);
x_314 = lean::cnstr_get(x_309, 1);
lean::inc(x_314);
lean::dec(x_309);
x_317 = lean::cnstr_get(x_310, 0);
if (lean::is_exclusive(x_310)) {
 x_319 = x_310;
} else {
 lean::inc(x_317);
 lean::dec(x_310);
 x_319 = lean::box(0);
}
if (lean::is_scalar(x_319)) {
 x_320 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_320 = x_319;
}
lean::cnstr_set(x_320, 0, x_317);
x_321 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_321, 0, x_320);
lean::cnstr_set(x_321, 1, x_314);
return x_321;
}
else
{
obj* x_323; obj* x_327; obj* x_328; 
lean::dec(x_310);
x_323 = lean::cnstr_get(x_309, 1);
lean::inc(x_323);
lean::dec(x_309);
lean::inc(x_5);
x_327 = l_lean_ir_cpp_emit__var(x_4, x_5, x_323);
x_328 = lean::cnstr_get(x_327, 0);
lean::inc(x_328);
if (lean::obj_tag(x_328) == 0)
{
obj* x_331; obj* x_334; obj* x_336; obj* x_337; obj* x_338; 
lean::dec(x_5);
x_331 = lean::cnstr_get(x_327, 1);
lean::inc(x_331);
lean::dec(x_327);
x_334 = lean::cnstr_get(x_328, 0);
if (lean::is_exclusive(x_328)) {
 x_336 = x_328;
} else {
 lean::inc(x_334);
 lean::dec(x_328);
 x_336 = lean::box(0);
}
if (lean::is_scalar(x_336)) {
 x_337 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_337 = x_336;
}
lean::cnstr_set(x_337, 0, x_334);
x_338 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_338, 0, x_337);
lean::cnstr_set(x_338, 1, x_331);
return x_338;
}
else
{
obj* x_339; obj* x_342; obj* x_345; obj* x_346; obj* x_347; 
x_339 = lean::cnstr_get(x_327, 1);
lean::inc(x_339);
lean::dec(x_327);
x_342 = lean::cnstr_get(x_328, 0);
lean::inc(x_342);
lean::dec(x_328);
x_345 = l_option_has__repr___rarg___closed__3;
x_346 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_345, x_5, x_339);
x_347 = lean::cnstr_get(x_346, 0);
lean::inc(x_347);
if (lean::obj_tag(x_347) == 0)
{
obj* x_350; obj* x_353; obj* x_355; obj* x_356; obj* x_357; 
lean::dec(x_342);
x_350 = lean::cnstr_get(x_346, 1);
lean::inc(x_350);
lean::dec(x_346);
x_353 = lean::cnstr_get(x_347, 0);
if (lean::is_exclusive(x_347)) {
 x_355 = x_347;
} else {
 lean::inc(x_353);
 lean::dec(x_347);
 x_355 = lean::box(0);
}
if (lean::is_scalar(x_355)) {
 x_356 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_356 = x_355;
}
lean::cnstr_set(x_356, 0, x_353);
x_357 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_357, 0, x_356);
lean::cnstr_set(x_357, 1, x_350);
return x_357;
}
else
{
obj* x_358; obj* x_359; obj* x_362; obj* x_363; 
if (lean::is_exclusive(x_347)) {
 lean::cnstr_release(x_347, 0);
 x_358 = x_347;
} else {
 lean::dec(x_347);
 x_358 = lean::box(0);
}
x_359 = lean::cnstr_get(x_346, 1);
lean::inc(x_359);
lean::dec(x_346);
if (lean::is_scalar(x_358)) {
 x_362 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_362 = x_358;
}
lean::cnstr_set(x_362, 0, x_342);
x_363 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_363, 0, x_362);
lean::cnstr_set(x_363, 1, x_359);
return x_363;
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
obj* x_367; obj* x_369; obj* x_370; obj* x_371; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_367 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_369 = x_9;
} else {
 lean::inc(x_367);
 lean::dec(x_9);
 x_369 = lean::box(0);
}
if (lean::is_scalar(x_369)) {
 x_370 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_370 = x_369;
}
lean::cnstr_set(x_370, 0, x_367);
x_371 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_371, 0, x_370);
lean::cnstr_set(x_371, 1, x_10);
return x_371;
}
else
{
obj* x_373; obj* x_375; obj* x_376; 
lean::dec(x_9);
x_373 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_5);
x_375 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_373, x_5, x_10);
x_376 = lean::cnstr_get(x_375, 0);
lean::inc(x_376);
if (lean::obj_tag(x_376) == 0)
{
obj* x_381; obj* x_384; obj* x_386; obj* x_387; obj* x_388; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_381 = lean::cnstr_get(x_375, 1);
lean::inc(x_381);
lean::dec(x_375);
x_384 = lean::cnstr_get(x_376, 0);
if (lean::is_exclusive(x_376)) {
 x_386 = x_376;
} else {
 lean::inc(x_384);
 lean::dec(x_376);
 x_386 = lean::box(0);
}
if (lean::is_scalar(x_386)) {
 x_387 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_387 = x_386;
}
lean::cnstr_set(x_387, 0, x_384);
x_388 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_388, 0, x_387);
lean::cnstr_set(x_388, 1, x_381);
return x_388;
}
else
{
obj* x_390; obj* x_394; obj* x_395; 
lean::dec(x_376);
x_390 = lean::cnstr_get(x_375, 1);
lean::inc(x_390);
lean::dec(x_375);
lean::inc(x_5);
x_394 = l_lean_ir_cpp_emit__var(x_3, x_5, x_390);
x_395 = lean::cnstr_get(x_394, 0);
lean::inc(x_395);
if (lean::obj_tag(x_395) == 0)
{
obj* x_399; obj* x_402; obj* x_404; obj* x_405; obj* x_406; 
lean::dec(x_5);
lean::dec(x_4);
x_399 = lean::cnstr_get(x_394, 1);
lean::inc(x_399);
lean::dec(x_394);
x_402 = lean::cnstr_get(x_395, 0);
if (lean::is_exclusive(x_395)) {
 x_404 = x_395;
} else {
 lean::inc(x_402);
 lean::dec(x_395);
 x_404 = lean::box(0);
}
if (lean::is_scalar(x_404)) {
 x_405 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_405 = x_404;
}
lean::cnstr_set(x_405, 0, x_402);
x_406 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_406, 0, x_405);
lean::cnstr_set(x_406, 1, x_399);
return x_406;
}
else
{
obj* x_408; obj* x_411; obj* x_413; obj* x_414; 
lean::dec(x_395);
x_408 = lean::cnstr_get(x_394, 1);
lean::inc(x_408);
lean::dec(x_394);
x_411 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_5);
x_413 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_411, x_5, x_408);
x_414 = lean::cnstr_get(x_413, 0);
lean::inc(x_414);
if (lean::obj_tag(x_414) == 0)
{
obj* x_418; obj* x_421; obj* x_423; obj* x_424; obj* x_425; 
lean::dec(x_5);
lean::dec(x_4);
x_418 = lean::cnstr_get(x_413, 1);
lean::inc(x_418);
lean::dec(x_413);
x_421 = lean::cnstr_get(x_414, 0);
if (lean::is_exclusive(x_414)) {
 x_423 = x_414;
} else {
 lean::inc(x_421);
 lean::dec(x_414);
 x_423 = lean::box(0);
}
if (lean::is_scalar(x_423)) {
 x_424 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_424 = x_423;
}
lean::cnstr_set(x_424, 0, x_421);
x_425 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_425, 0, x_424);
lean::cnstr_set(x_425, 1, x_418);
return x_425;
}
else
{
obj* x_427; obj* x_431; obj* x_432; 
lean::dec(x_414);
x_427 = lean::cnstr_get(x_413, 1);
lean::inc(x_427);
lean::dec(x_413);
lean::inc(x_5);
x_431 = l_lean_ir_cpp_emit__var(x_4, x_5, x_427);
x_432 = lean::cnstr_get(x_431, 0);
lean::inc(x_432);
if (lean::obj_tag(x_432) == 0)
{
obj* x_435; obj* x_438; obj* x_440; obj* x_441; obj* x_442; 
lean::dec(x_5);
x_435 = lean::cnstr_get(x_431, 1);
lean::inc(x_435);
lean::dec(x_431);
x_438 = lean::cnstr_get(x_432, 0);
if (lean::is_exclusive(x_432)) {
 x_440 = x_432;
} else {
 lean::inc(x_438);
 lean::dec(x_432);
 x_440 = lean::box(0);
}
if (lean::is_scalar(x_440)) {
 x_441 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_441 = x_440;
}
lean::cnstr_set(x_441, 0, x_438);
x_442 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_442, 0, x_441);
lean::cnstr_set(x_442, 1, x_435);
return x_442;
}
else
{
obj* x_443; obj* x_446; obj* x_449; obj* x_450; obj* x_451; 
x_443 = lean::cnstr_get(x_431, 1);
lean::inc(x_443);
lean::dec(x_431);
x_446 = lean::cnstr_get(x_432, 0);
lean::inc(x_446);
lean::dec(x_432);
x_449 = l_option_has__repr___rarg___closed__3;
x_450 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_449, x_5, x_443);
x_451 = lean::cnstr_get(x_450, 0);
lean::inc(x_451);
if (lean::obj_tag(x_451) == 0)
{
obj* x_454; obj* x_457; obj* x_459; obj* x_460; obj* x_461; 
lean::dec(x_446);
x_454 = lean::cnstr_get(x_450, 1);
lean::inc(x_454);
lean::dec(x_450);
x_457 = lean::cnstr_get(x_451, 0);
if (lean::is_exclusive(x_451)) {
 x_459 = x_451;
} else {
 lean::inc(x_457);
 lean::dec(x_451);
 x_459 = lean::box(0);
}
if (lean::is_scalar(x_459)) {
 x_460 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_460 = x_459;
}
lean::cnstr_set(x_460, 0, x_457);
x_461 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_461, 0, x_460);
lean::cnstr_set(x_461, 1, x_454);
return x_461;
}
else
{
obj* x_462; obj* x_463; obj* x_466; obj* x_467; 
if (lean::is_exclusive(x_451)) {
 lean::cnstr_release(x_451, 0);
 x_462 = x_451;
} else {
 lean::dec(x_451);
 x_462 = lean::box(0);
}
x_463 = lean::cnstr_get(x_450, 1);
lean::inc(x_463);
lean::dec(x_450);
if (lean::is_scalar(x_462)) {
 x_466 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_466 = x_462;
}
lean::cnstr_set(x_466, 0, x_446);
x_467 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_467, 0, x_466);
lean::cnstr_set(x_467, 1, x_463);
return x_467;
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
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
lean::inc(x_3);
x_9 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
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
x_5 = x_18;
x_6 = x_12;
goto lbl_7;
}
else
{
obj* x_20; obj* x_23; obj* x_25; obj* x_26; obj* x_28; 
lean::dec(x_10);
x_20 = lean::cnstr_get(x_9, 1);
lean::inc(x_20);
lean::dec(x_9);
x_23 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
x_25 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_23, x_3, x_20);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_5 = x_26;
x_6 = x_28;
goto lbl_7;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_34 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_36 = x_5;
} else {
 lean::inc(x_34);
 lean::dec(x_5);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_6);
return x_38;
}
else
{
obj* x_41; obj* x_42; 
lean::dec(x_5);
lean::inc(x_3);
x_41 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1, x_3, x_6);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
if (lean::obj_tag(x_42) == 0)
{
obj* x_46; obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_3);
lean::dec(x_2);
x_46 = lean::cnstr_get(x_41, 1);
lean::inc(x_46);
lean::dec(x_41);
x_49 = lean::cnstr_get(x_42, 0);
if (lean::is_exclusive(x_42)) {
 x_51 = x_42;
} else {
 lean::inc(x_49);
 lean::dec(x_42);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_46);
return x_53;
}
else
{
obj* x_55; obj* x_58; obj* x_60; obj* x_61; 
lean::dec(x_42);
x_55 = lean::cnstr_get(x_41, 1);
lean::inc(x_55);
lean::dec(x_41);
x_58 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
x_60 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_58, x_3, x_55);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
if (lean::obj_tag(x_61) == 0)
{
obj* x_65; obj* x_68; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_3);
lean::dec(x_2);
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
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_65);
return x_72;
}
else
{
obj* x_74; obj* x_78; obj* x_79; 
lean::dec(x_61);
x_74 = lean::cnstr_get(x_60, 1);
lean::inc(x_74);
lean::dec(x_60);
lean::inc(x_3);
x_78 = l_lean_ir_cpp_emit__var(x_2, x_3, x_74);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
if (lean::obj_tag(x_79) == 0)
{
obj* x_82; obj* x_85; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_3);
x_82 = lean::cnstr_get(x_78, 1);
lean::inc(x_82);
lean::dec(x_78);
x_85 = lean::cnstr_get(x_79, 0);
if (lean::is_exclusive(x_79)) {
 x_87 = x_79;
} else {
 lean::inc(x_85);
 lean::dec(x_79);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_85);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_82);
return x_89;
}
else
{
obj* x_90; obj* x_93; obj* x_96; obj* x_97; obj* x_98; 
x_90 = lean::cnstr_get(x_78, 1);
lean::inc(x_90);
lean::dec(x_78);
x_93 = lean::cnstr_get(x_79, 0);
lean::inc(x_93);
lean::dec(x_79);
x_96 = l_option_has__repr___rarg___closed__3;
x_97 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_96, x_3, x_90);
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
if (lean::obj_tag(x_98) == 0)
{
obj* x_101; obj* x_104; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_93);
x_101 = lean::cnstr_get(x_97, 1);
lean::inc(x_101);
lean::dec(x_97);
x_104 = lean::cnstr_get(x_98, 0);
if (lean::is_exclusive(x_98)) {
 x_106 = x_98;
} else {
 lean::inc(x_104);
 lean::dec(x_98);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_104);
x_108 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_101);
return x_108;
}
else
{
obj* x_109; obj* x_110; obj* x_113; obj* x_114; 
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 x_109 = x_98;
} else {
 lean::dec(x_98);
 x_109 = lean::box(0);
}
x_110 = lean::cnstr_get(x_97, 1);
lean::inc(x_110);
lean::dec(x_97);
if (lean::is_scalar(x_109)) {
 x_113 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_113 = x_109;
}
lean::cnstr_set(x_113, 0, x_93);
x_114 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_110);
return x_114;
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
obj* x_6; obj* x_7; obj* x_8; obj* x_11; obj* x_12; 
x_6 = l_lean_ir_cpp_assign__unop2cpp___main(x_1, x_2);
lean::inc(x_4);
x_11 = l_lean_ir_cpp_emit__var(x_0, x_4, x_5);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_17; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_19 = x_12;
} else {
 lean::inc(x_17);
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
obj* x_22; obj* x_25; obj* x_27; obj* x_28; obj* x_30; 
lean::dec(x_12);
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
lean::dec(x_11);
x_25 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_4);
x_27 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_25, x_4, x_22);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
x_7 = x_28;
x_8 = x_30;
goto lbl_9;
}
lbl_9:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_36; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_3);
x_36 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_38 = x_7;
} else {
 lean::inc(x_36);
 lean::dec(x_7);
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
lean::cnstr_set(x_40, 1, x_8);
return x_40;
}
else
{
obj* x_43; obj* x_44; 
lean::dec(x_7);
lean::inc(x_4);
x_43 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_6, x_4, x_8);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_48; obj* x_51; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_4);
lean::dec(x_3);
x_48 = lean::cnstr_get(x_43, 1);
lean::inc(x_48);
lean::dec(x_43);
x_51 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 x_53 = x_44;
} else {
 lean::inc(x_51);
 lean::dec(x_44);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_48);
return x_55;
}
else
{
obj* x_57; obj* x_60; obj* x_62; obj* x_63; 
lean::dec(x_44);
x_57 = lean::cnstr_get(x_43, 1);
lean::inc(x_57);
lean::dec(x_43);
x_60 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_4);
x_62 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_60, x_4, x_57);
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
if (lean::obj_tag(x_63) == 0)
{
obj* x_67; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_4);
lean::dec(x_3);
x_67 = lean::cnstr_get(x_62, 1);
lean::inc(x_67);
lean::dec(x_62);
x_70 = lean::cnstr_get(x_63, 0);
if (lean::is_exclusive(x_63)) {
 x_72 = x_63;
} else {
 lean::inc(x_70);
 lean::dec(x_63);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_70);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_67);
return x_74;
}
else
{
obj* x_76; obj* x_80; obj* x_81; 
lean::dec(x_63);
x_76 = lean::cnstr_get(x_62, 1);
lean::inc(x_76);
lean::dec(x_62);
lean::inc(x_4);
x_80 = l_lean_ir_cpp_emit__var(x_3, x_4, x_76);
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
if (lean::obj_tag(x_81) == 0)
{
obj* x_84; obj* x_87; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_4);
x_84 = lean::cnstr_get(x_80, 1);
lean::inc(x_84);
lean::dec(x_80);
x_87 = lean::cnstr_get(x_81, 0);
if (lean::is_exclusive(x_81)) {
 x_89 = x_81;
} else {
 lean::inc(x_87);
 lean::dec(x_81);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_87);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_84);
return x_91;
}
else
{
obj* x_92; obj* x_95; obj* x_98; obj* x_99; obj* x_100; 
x_92 = lean::cnstr_get(x_80, 1);
lean::inc(x_92);
lean::dec(x_80);
x_95 = lean::cnstr_get(x_81, 0);
lean::inc(x_95);
lean::dec(x_81);
x_98 = l_option_has__repr___rarg___closed__3;
x_99 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_98, x_4, x_92);
x_100 = lean::cnstr_get(x_99, 0);
lean::inc(x_100);
if (lean::obj_tag(x_100) == 0)
{
obj* x_103; obj* x_106; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_95);
x_103 = lean::cnstr_get(x_99, 1);
lean::inc(x_103);
lean::dec(x_99);
x_106 = lean::cnstr_get(x_100, 0);
if (lean::is_exclusive(x_100)) {
 x_108 = x_100;
} else {
 lean::inc(x_106);
 lean::dec(x_100);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_106);
x_110 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_103);
return x_110;
}
else
{
obj* x_111; obj* x_112; obj* x_115; obj* x_116; 
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 x_111 = x_100;
} else {
 lean::dec(x_100);
 x_111 = lean::box(0);
}
x_112 = lean::cnstr_get(x_99, 1);
lean::inc(x_112);
lean::dec(x_99);
if (lean::is_scalar(x_111)) {
 x_115 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_115 = x_111;
}
lean::cnstr_set(x_115, 0, x_95);
x_116 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_112);
return x_116;
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
obj* x_8; obj* x_9; 
lean::inc(x_3);
x_8 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; obj* x_15; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_3);
x_12 = lean::cnstr_get(x_8, 1);
lean::inc(x_12);
lean::dec(x_8);
x_15 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_17 = x_9;
} else {
 lean::inc(x_15);
 lean::dec(x_9);
 x_17 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_18 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_18 = x_17;
}
lean::cnstr_set(x_18, 0, x_15);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_12);
return x_19;
}
else
{
obj* x_21; obj* x_24; obj* x_25; 
lean::dec(x_9);
x_21 = lean::cnstr_get(x_8, 1);
lean::inc(x_21);
lean::dec(x_8);
x_24 = l_lean_ir_cpp_emit__assign__lit___closed__1;
x_25 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_24, x_3, x_21);
return x_25;
}
}
else
{
obj* x_27; obj* x_28; 
lean::inc(x_3);
x_27 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_31; obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_3);
x_31 = lean::cnstr_get(x_27, 1);
lean::inc(x_31);
lean::dec(x_27);
x_34 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_36 = x_28;
} else {
 lean::inc(x_34);
 lean::dec(x_28);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_31);
return x_38;
}
else
{
obj* x_40; obj* x_43; obj* x_44; 
lean::dec(x_28);
x_40 = lean::cnstr_get(x_27, 1);
lean::inc(x_40);
lean::dec(x_27);
x_43 = l_lean_ir_cpp_emit__assign__lit___closed__2;
x_44 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_43, x_3, x_40);
return x_44;
}
}
}
case 1:
{
obj* x_45; obj* x_49; obj* x_50; 
x_45 = lean::cnstr_get(x_2, 0);
lean::inc(x_45);
lean::dec(x_2);
lean::inc(x_3);
x_49 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_54; obj* x_57; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_3);
lean::dec(x_45);
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
lean::dec(x_49);
x_57 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_59 = x_50;
} else {
 lean::inc(x_57);
 lean::dec(x_50);
 x_59 = lean::box(0);
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_57);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_54);
return x_61;
}
else
{
obj* x_63; obj* x_66; obj* x_68; obj* x_69; 
lean::dec(x_50);
x_63 = lean::cnstr_get(x_49, 1);
lean::inc(x_63);
lean::dec(x_49);
x_66 = l_lean_ir_cpp_emit__assign__lit___closed__3;
lean::inc(x_3);
x_68 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_66, x_3, x_63);
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
if (lean::obj_tag(x_69) == 0)
{
obj* x_73; obj* x_76; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_3);
lean::dec(x_45);
x_73 = lean::cnstr_get(x_68, 1);
lean::inc(x_73);
lean::dec(x_68);
x_76 = lean::cnstr_get(x_69, 0);
if (lean::is_exclusive(x_69)) {
 x_78 = x_69;
} else {
 lean::inc(x_76);
 lean::dec(x_69);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_76);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_73);
return x_80;
}
else
{
obj* x_82; obj* x_85; obj* x_86; obj* x_88; obj* x_89; 
lean::dec(x_69);
x_82 = lean::cnstr_get(x_68, 1);
lean::inc(x_82);
lean::dec(x_68);
x_85 = l_string_quote(x_45);
x_86 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
x_88 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_86, x_3, x_82);
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
if (lean::obj_tag(x_89) == 0)
{
obj* x_93; obj* x_96; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_3);
lean::dec(x_85);
x_93 = lean::cnstr_get(x_88, 1);
lean::inc(x_93);
lean::dec(x_88);
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
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_93);
return x_100;
}
else
{
obj* x_102; obj* x_106; obj* x_107; 
lean::dec(x_89);
x_102 = lean::cnstr_get(x_88, 1);
lean::inc(x_102);
lean::dec(x_88);
lean::inc(x_3);
x_106 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_85, x_3, x_102);
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
if (lean::obj_tag(x_107) == 0)
{
obj* x_110; obj* x_113; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_3);
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
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_110);
return x_117;
}
else
{
obj* x_118; obj* x_121; obj* x_124; obj* x_125; obj* x_126; 
x_118 = lean::cnstr_get(x_106, 1);
lean::inc(x_118);
lean::dec(x_106);
x_121 = lean::cnstr_get(x_107, 0);
lean::inc(x_121);
lean::dec(x_107);
x_124 = l_option_has__repr___rarg___closed__3;
x_125 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_124, x_3, x_118);
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
if (lean::obj_tag(x_126) == 0)
{
obj* x_129; obj* x_132; obj* x_134; obj* x_135; obj* x_136; 
lean::dec(x_121);
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
x_136 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_129);
return x_136;
}
else
{
obj* x_137; obj* x_138; obj* x_141; obj* x_142; 
if (lean::is_exclusive(x_126)) {
 lean::cnstr_release(x_126, 0);
 x_137 = x_126;
} else {
 lean::dec(x_126);
 x_137 = lean::box(0);
}
x_138 = lean::cnstr_get(x_125, 1);
lean::inc(x_138);
lean::dec(x_125);
if (lean::is_scalar(x_137)) {
 x_141 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_141 = x_137;
}
lean::cnstr_set(x_141, 0, x_121);
x_142 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_138);
return x_142;
}
}
}
}
}
}
case 2:
{
obj* x_143; obj* x_146; 
x_143 = lean::cnstr_get(x_2, 0);
lean::inc(x_143);
lean::dec(x_2);
switch (x_1) {
case 11:
{
obj* x_148; uint8 x_149; obj* x_150; obj* x_151; obj* x_154; obj* x_155; 
x_148 = l_lean_ir_cpp_emit__assign__lit___closed__4;
x_149 = lean::int_dec_lt(x_143, x_148);
lean::inc(x_3);
x_154 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_155 = lean::cnstr_get(x_154, 0);
lean::inc(x_155);
if (lean::obj_tag(x_155) == 0)
{
obj* x_157; obj* x_160; obj* x_162; obj* x_163; 
x_157 = lean::cnstr_get(x_154, 1);
lean::inc(x_157);
lean::dec(x_154);
x_160 = lean::cnstr_get(x_155, 0);
if (lean::is_exclusive(x_155)) {
 x_162 = x_155;
} else {
 lean::inc(x_160);
 lean::dec(x_155);
 x_162 = lean::box(0);
}
if (lean::is_scalar(x_162)) {
 x_163 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_163 = x_162;
}
lean::cnstr_set(x_163, 0, x_160);
x_150 = x_163;
x_151 = x_157;
goto lbl_152;
}
else
{
obj* x_165; obj* x_168; obj* x_170; obj* x_171; obj* x_173; 
lean::dec(x_155);
x_165 = lean::cnstr_get(x_154, 1);
lean::inc(x_165);
lean::dec(x_154);
x_168 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
x_170 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_168, x_3, x_165);
x_171 = lean::cnstr_get(x_170, 0);
lean::inc(x_171);
x_173 = lean::cnstr_get(x_170, 1);
lean::inc(x_173);
lean::dec(x_170);
x_150 = x_171;
x_151 = x_173;
goto lbl_152;
}
lbl_152:
{
if (lean::obj_tag(x_150) == 0)
{
obj* x_178; obj* x_180; obj* x_181; obj* x_182; 
lean::dec(x_143);
lean::dec(x_3);
x_178 = lean::cnstr_get(x_150, 0);
if (lean::is_exclusive(x_150)) {
 x_180 = x_150;
} else {
 lean::inc(x_178);
 lean::dec(x_150);
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
lean::cnstr_set(x_182, 1, x_151);
return x_182;
}
else
{
lean::dec(x_150);
if (x_149 == 0)
{
obj* x_184; obj* x_186; obj* x_187; 
x_184 = l_lean_ir_cpp_emit__assign__lit___closed__5;
lean::inc(x_3);
x_186 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_184, x_3, x_151);
x_187 = lean::cnstr_get(x_186, 0);
lean::inc(x_187);
if (lean::obj_tag(x_187) == 0)
{
obj* x_191; obj* x_194; obj* x_196; obj* x_197; obj* x_198; 
lean::dec(x_143);
lean::dec(x_3);
x_191 = lean::cnstr_get(x_186, 1);
lean::inc(x_191);
lean::dec(x_186);
x_194 = lean::cnstr_get(x_187, 0);
if (lean::is_exclusive(x_187)) {
 x_196 = x_187;
} else {
 lean::inc(x_194);
 lean::dec(x_187);
 x_196 = lean::box(0);
}
if (lean::is_scalar(x_196)) {
 x_197 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_197 = x_196;
}
lean::cnstr_set(x_197, 0, x_194);
x_198 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_198, 0, x_197);
lean::cnstr_set(x_198, 1, x_191);
return x_198;
}
else
{
obj* x_200; obj* x_204; obj* x_205; 
lean::dec(x_187);
x_200 = lean::cnstr_get(x_186, 1);
lean::inc(x_200);
lean::dec(x_186);
lean::inc(x_3);
x_204 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_143, x_3, x_200);
x_205 = lean::cnstr_get(x_204, 0);
lean::inc(x_205);
if (lean::obj_tag(x_205) == 0)
{
obj* x_208; obj* x_211; obj* x_213; obj* x_214; obj* x_215; 
lean::dec(x_3);
x_208 = lean::cnstr_get(x_204, 1);
lean::inc(x_208);
lean::dec(x_204);
x_211 = lean::cnstr_get(x_205, 0);
if (lean::is_exclusive(x_205)) {
 x_213 = x_205;
} else {
 lean::inc(x_211);
 lean::dec(x_205);
 x_213 = lean::box(0);
}
if (lean::is_scalar(x_213)) {
 x_214 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_214 = x_213;
}
lean::cnstr_set(x_214, 0, x_211);
x_215 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_215, 0, x_214);
lean::cnstr_set(x_215, 1, x_208);
return x_215;
}
else
{
obj* x_217; obj* x_220; obj* x_221; 
lean::dec(x_205);
x_217 = lean::cnstr_get(x_204, 1);
lean::inc(x_217);
lean::dec(x_204);
x_220 = l_lean_ir_cpp_emit__assign__lit___closed__6;
x_221 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_220, x_3, x_217);
return x_221;
}
}
}
else
{
obj* x_222; obj* x_224; obj* x_225; 
x_222 = l_lean_ir_cpp_emit__assign__lit___closed__7;
lean::inc(x_3);
x_224 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_222, x_3, x_151);
x_225 = lean::cnstr_get(x_224, 0);
lean::inc(x_225);
if (lean::obj_tag(x_225) == 0)
{
obj* x_229; obj* x_232; obj* x_234; obj* x_235; obj* x_236; 
lean::dec(x_143);
lean::dec(x_3);
x_229 = lean::cnstr_get(x_224, 1);
lean::inc(x_229);
lean::dec(x_224);
x_232 = lean::cnstr_get(x_225, 0);
if (lean::is_exclusive(x_225)) {
 x_234 = x_225;
} else {
 lean::inc(x_232);
 lean::dec(x_225);
 x_234 = lean::box(0);
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_232);
x_236 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_236, 0, x_235);
lean::cnstr_set(x_236, 1, x_229);
return x_236;
}
else
{
obj* x_238; obj* x_241; obj* x_243; obj* x_244; 
lean::dec(x_225);
x_238 = lean::cnstr_get(x_224, 1);
lean::inc(x_238);
lean::dec(x_224);
x_241 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
x_243 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_241, x_3, x_238);
x_244 = lean::cnstr_get(x_243, 0);
lean::inc(x_244);
if (lean::obj_tag(x_244) == 0)
{
obj* x_248; obj* x_251; obj* x_253; obj* x_254; obj* x_255; 
lean::dec(x_143);
lean::dec(x_3);
x_248 = lean::cnstr_get(x_243, 1);
lean::inc(x_248);
lean::dec(x_243);
x_251 = lean::cnstr_get(x_244, 0);
if (lean::is_exclusive(x_244)) {
 x_253 = x_244;
} else {
 lean::inc(x_251);
 lean::dec(x_244);
 x_253 = lean::box(0);
}
if (lean::is_scalar(x_253)) {
 x_254 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_254 = x_253;
}
lean::cnstr_set(x_254, 0, x_251);
x_255 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_255, 0, x_254);
lean::cnstr_set(x_255, 1, x_248);
return x_255;
}
else
{
obj* x_257; obj* x_261; obj* x_262; 
lean::dec(x_244);
x_257 = lean::cnstr_get(x_243, 1);
lean::inc(x_257);
lean::dec(x_243);
lean::inc(x_3);
x_261 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_143, x_3, x_257);
x_262 = lean::cnstr_get(x_261, 0);
lean::inc(x_262);
if (lean::obj_tag(x_262) == 0)
{
obj* x_265; obj* x_268; obj* x_270; obj* x_271; obj* x_272; 
lean::dec(x_3);
x_265 = lean::cnstr_get(x_261, 1);
lean::inc(x_265);
lean::dec(x_261);
x_268 = lean::cnstr_get(x_262, 0);
if (lean::is_exclusive(x_262)) {
 x_270 = x_262;
} else {
 lean::inc(x_268);
 lean::dec(x_262);
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
lean::cnstr_set(x_272, 1, x_265);
return x_272;
}
else
{
obj* x_274; obj* x_277; obj* x_279; obj* x_280; 
lean::dec(x_262);
x_274 = lean::cnstr_get(x_261, 1);
lean::inc(x_274);
lean::dec(x_261);
x_277 = l_lean_ir_cpp_emit__num__suffix___main___closed__1;
lean::inc(x_3);
x_279 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_277, x_3, x_274);
x_280 = lean::cnstr_get(x_279, 0);
lean::inc(x_280);
if (lean::obj_tag(x_280) == 0)
{
obj* x_283; obj* x_286; obj* x_288; obj* x_289; obj* x_290; 
lean::dec(x_3);
x_283 = lean::cnstr_get(x_279, 1);
lean::inc(x_283);
lean::dec(x_279);
x_286 = lean::cnstr_get(x_280, 0);
if (lean::is_exclusive(x_280)) {
 x_288 = x_280;
} else {
 lean::inc(x_286);
 lean::dec(x_280);
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
lean::cnstr_set(x_290, 1, x_283);
return x_290;
}
else
{
obj* x_291; obj* x_294; obj* x_297; obj* x_298; obj* x_299; 
x_291 = lean::cnstr_get(x_279, 1);
lean::inc(x_291);
lean::dec(x_279);
x_294 = lean::cnstr_get(x_280, 0);
lean::inc(x_294);
lean::dec(x_280);
x_297 = l_option_has__repr___rarg___closed__3;
x_298 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_297, x_3, x_291);
x_299 = lean::cnstr_get(x_298, 0);
lean::inc(x_299);
if (lean::obj_tag(x_299) == 0)
{
obj* x_302; obj* x_305; obj* x_307; obj* x_308; obj* x_309; 
lean::dec(x_294);
x_302 = lean::cnstr_get(x_298, 1);
lean::inc(x_302);
lean::dec(x_298);
x_305 = lean::cnstr_get(x_299, 0);
if (lean::is_exclusive(x_299)) {
 x_307 = x_299;
} else {
 lean::inc(x_305);
 lean::dec(x_299);
 x_307 = lean::box(0);
}
if (lean::is_scalar(x_307)) {
 x_308 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_308 = x_307;
}
lean::cnstr_set(x_308, 0, x_305);
x_309 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_309, 0, x_308);
lean::cnstr_set(x_309, 1, x_302);
return x_309;
}
else
{
obj* x_310; obj* x_311; obj* x_314; obj* x_315; 
if (lean::is_exclusive(x_299)) {
 lean::cnstr_release(x_299, 0);
 x_310 = x_299;
} else {
 lean::dec(x_299);
 x_310 = lean::box(0);
}
x_311 = lean::cnstr_get(x_298, 1);
lean::inc(x_311);
lean::dec(x_298);
if (lean::is_scalar(x_310)) {
 x_314 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_314 = x_310;
}
lean::cnstr_set(x_314, 0, x_294);
x_315 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_315, 0, x_314);
lean::cnstr_set(x_315, 1, x_311);
return x_315;
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
obj* x_316; 
x_316 = lean::box(0);
x_146 = x_316;
goto lbl_147;
}
}
lbl_147:
{
obj* x_319; obj* x_320; 
lean::dec(x_146);
lean::inc(x_3);
x_319 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_320 = lean::cnstr_get(x_319, 0);
lean::inc(x_320);
if (lean::obj_tag(x_320) == 0)
{
obj* x_324; obj* x_327; obj* x_329; obj* x_330; obj* x_331; 
lean::dec(x_143);
lean::dec(x_3);
x_324 = lean::cnstr_get(x_319, 1);
lean::inc(x_324);
lean::dec(x_319);
x_327 = lean::cnstr_get(x_320, 0);
if (lean::is_exclusive(x_320)) {
 x_329 = x_320;
} else {
 lean::inc(x_327);
 lean::dec(x_320);
 x_329 = lean::box(0);
}
if (lean::is_scalar(x_329)) {
 x_330 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_330 = x_329;
}
lean::cnstr_set(x_330, 0, x_327);
x_331 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_331, 0, x_330);
lean::cnstr_set(x_331, 1, x_324);
return x_331;
}
else
{
obj* x_333; obj* x_336; obj* x_338; obj* x_339; 
lean::dec(x_320);
x_333 = lean::cnstr_get(x_319, 1);
lean::inc(x_333);
lean::dec(x_319);
x_336 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
x_338 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_336, x_3, x_333);
x_339 = lean::cnstr_get(x_338, 0);
lean::inc(x_339);
if (lean::obj_tag(x_339) == 0)
{
obj* x_343; obj* x_346; obj* x_348; obj* x_349; obj* x_350; 
lean::dec(x_143);
lean::dec(x_3);
x_343 = lean::cnstr_get(x_338, 1);
lean::inc(x_343);
lean::dec(x_338);
x_346 = lean::cnstr_get(x_339, 0);
if (lean::is_exclusive(x_339)) {
 x_348 = x_339;
} else {
 lean::inc(x_346);
 lean::dec(x_339);
 x_348 = lean::box(0);
}
if (lean::is_scalar(x_348)) {
 x_349 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_349 = x_348;
}
lean::cnstr_set(x_349, 0, x_346);
x_350 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_350, 0, x_349);
lean::cnstr_set(x_350, 1, x_343);
return x_350;
}
else
{
obj* x_352; obj* x_356; obj* x_357; 
lean::dec(x_339);
x_352 = lean::cnstr_get(x_338, 1);
lean::inc(x_352);
lean::dec(x_338);
lean::inc(x_3);
x_356 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__assign__lit___spec__1(x_143, x_3, x_352);
x_357 = lean::cnstr_get(x_356, 0);
lean::inc(x_357);
if (lean::obj_tag(x_357) == 0)
{
obj* x_360; obj* x_363; obj* x_365; obj* x_366; obj* x_367; 
lean::dec(x_3);
x_360 = lean::cnstr_get(x_356, 1);
lean::inc(x_360);
lean::dec(x_356);
x_363 = lean::cnstr_get(x_357, 0);
if (lean::is_exclusive(x_357)) {
 x_365 = x_357;
} else {
 lean::inc(x_363);
 lean::dec(x_357);
 x_365 = lean::box(0);
}
if (lean::is_scalar(x_365)) {
 x_366 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_366 = x_365;
}
lean::cnstr_set(x_366, 0, x_363);
x_367 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_367, 0, x_366);
lean::cnstr_set(x_367, 1, x_360);
return x_367;
}
else
{
obj* x_369; obj* x_372; 
lean::dec(x_357);
x_369 = lean::cnstr_get(x_356, 1);
lean::inc(x_369);
lean::dec(x_356);
x_372 = l_lean_ir_cpp_emit__num__suffix___main(x_1, x_3, x_369);
return x_372;
}
}
}
}
}
default:
{
obj* x_373; obj* x_377; obj* x_378; 
x_373 = lean::cnstr_get(x_2, 0);
lean::inc(x_373);
lean::dec(x_2);
lean::inc(x_3);
x_377 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_378 = lean::cnstr_get(x_377, 0);
lean::inc(x_378);
if (lean::obj_tag(x_378) == 0)
{
obj* x_382; obj* x_385; obj* x_387; obj* x_388; obj* x_389; 
lean::dec(x_373);
lean::dec(x_3);
x_382 = lean::cnstr_get(x_377, 1);
lean::inc(x_382);
lean::dec(x_377);
x_385 = lean::cnstr_get(x_378, 0);
if (lean::is_exclusive(x_378)) {
 x_387 = x_378;
} else {
 lean::inc(x_385);
 lean::dec(x_378);
 x_387 = lean::box(0);
}
if (lean::is_scalar(x_387)) {
 x_388 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_388 = x_387;
}
lean::cnstr_set(x_388, 0, x_385);
x_389 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_389, 0, x_388);
lean::cnstr_set(x_389, 1, x_382);
return x_389;
}
else
{
obj* x_391; obj* x_394; obj* x_396; obj* x_397; 
lean::dec(x_378);
x_391 = lean::cnstr_get(x_377, 1);
lean::inc(x_391);
lean::dec(x_377);
x_394 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_3);
x_396 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_394, x_3, x_391);
x_397 = lean::cnstr_get(x_396, 0);
lean::inc(x_397);
if (lean::obj_tag(x_397) == 0)
{
obj* x_401; obj* x_404; obj* x_406; obj* x_407; obj* x_408; 
lean::dec(x_373);
lean::dec(x_3);
x_401 = lean::cnstr_get(x_396, 1);
lean::inc(x_401);
lean::dec(x_396);
x_404 = lean::cnstr_get(x_397, 0);
if (lean::is_exclusive(x_397)) {
 x_406 = x_397;
} else {
 lean::inc(x_404);
 lean::dec(x_397);
 x_406 = lean::box(0);
}
if (lean::is_scalar(x_406)) {
 x_407 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_407 = x_406;
}
lean::cnstr_set(x_407, 0, x_404);
x_408 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_408, 0, x_407);
lean::cnstr_set(x_408, 1, x_401);
return x_408;
}
else
{
obj* x_410; obj* x_413; 
lean::dec(x_397);
x_410 = lean::cnstr_get(x_396, 1);
lean::inc(x_410);
lean::dec(x_396);
x_413 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_373, x_3, x_410);
return x_413;
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
obj* x_4; obj* x_6; obj* x_7; 
x_4 = l_lean_ir_cpp_unop2cpp___main(x_0);
lean::inc(x_2);
x_6 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_4, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_11; obj* x_14; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_1);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
x_14 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_16 = x_7;
} else {
 lean::inc(x_14);
 lean::dec(x_7);
 x_16 = lean::box(0);
}
if (lean::is_scalar(x_16)) {
 x_17 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_17 = x_16;
}
lean::cnstr_set(x_17, 0, x_14);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_11);
return x_18;
}
else
{
obj* x_20; obj* x_23; obj* x_25; obj* x_26; 
lean::dec(x_7);
x_20 = lean::cnstr_get(x_6, 1);
lean::inc(x_20);
lean::dec(x_6);
x_23 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
x_25 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_23, x_2, x_20);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_30; obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_1);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::dec(x_25);
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
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_30);
return x_37;
}
else
{
obj* x_39; obj* x_43; obj* x_44; 
lean::dec(x_26);
x_39 = lean::cnstr_get(x_25, 1);
lean::inc(x_39);
lean::dec(x_25);
lean::inc(x_2);
x_43 = l_lean_ir_cpp_emit__var(x_1, x_2, x_39);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_47; obj* x_50; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_2);
x_47 = lean::cnstr_get(x_43, 1);
lean::inc(x_47);
lean::dec(x_43);
x_50 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 x_52 = x_44;
} else {
 lean::inc(x_50);
 lean::dec(x_44);
 x_52 = lean::box(0);
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_50);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_47);
return x_54;
}
else
{
obj* x_55; obj* x_58; obj* x_61; obj* x_62; obj* x_63; 
x_55 = lean::cnstr_get(x_43, 1);
lean::inc(x_55);
lean::dec(x_43);
x_58 = lean::cnstr_get(x_44, 0);
lean::inc(x_58);
lean::dec(x_44);
x_61 = l_option_has__repr___rarg___closed__3;
x_62 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_61, x_2, x_55);
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
if (lean::obj_tag(x_63) == 0)
{
obj* x_66; obj* x_69; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_58);
x_66 = lean::cnstr_get(x_62, 1);
lean::inc(x_66);
lean::dec(x_62);
x_69 = lean::cnstr_get(x_63, 0);
if (lean::is_exclusive(x_63)) {
 x_71 = x_63;
} else {
 lean::inc(x_69);
 lean::dec(x_63);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_69);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_66);
return x_73;
}
else
{
obj* x_74; obj* x_75; obj* x_78; obj* x_79; 
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 x_74 = x_63;
} else {
 lean::dec(x_63);
 x_74 = lean::box(0);
}
x_75 = lean::cnstr_get(x_62, 1);
lean::inc(x_75);
lean::dec(x_62);
if (lean::is_scalar(x_74)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_74;
}
lean::cnstr_set(x_78, 0, x_58);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_75);
return x_79;
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
obj* x_19; obj* x_20; obj* x_23; obj* x_24; 
lean::dec(x_10);
lean::dec(x_8);
lean::inc(x_2);
x_23 = l_lean_ir_cpp_emit__var(x_0, x_2, x_3);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; obj* x_29; obj* x_31; obj* x_32; 
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
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
x_19 = x_32;
x_20 = x_26;
goto lbl_21;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_40; obj* x_42; 
lean::dec(x_24);
x_34 = lean::cnstr_get(x_23, 1);
lean::inc(x_34);
lean::dec(x_23);
x_37 = l_lean_ir_cpp_emit__apply___closed__3;
lean::inc(x_2);
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_37, x_2, x_34);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
x_19 = x_40;
x_20 = x_42;
goto lbl_21;
}
lbl_21:
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_48; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_1);
lean::dec(x_14);
lean::dec(x_2);
x_48 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_50 = x_19;
} else {
 lean::inc(x_48);
 lean::dec(x_19);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_20);
return x_52;
}
else
{
obj* x_55; obj* x_56; 
lean::dec(x_19);
lean::inc(x_2);
x_55 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_14, x_2, x_20);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
if (lean::obj_tag(x_56) == 0)
{
obj* x_60; obj* x_63; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_1);
lean::dec(x_2);
x_60 = lean::cnstr_get(x_55, 1);
lean::inc(x_60);
lean::dec(x_55);
x_63 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 x_65 = x_56;
} else {
 lean::inc(x_63);
 lean::dec(x_56);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_63);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_60);
return x_67;
}
else
{
obj* x_69; obj* x_72; obj* x_74; obj* x_75; 
lean::dec(x_56);
x_69 = lean::cnstr_get(x_55, 1);
lean::inc(x_69);
lean::dec(x_55);
x_72 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
x_74 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_72, x_2, x_69);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
if (lean::obj_tag(x_75) == 0)
{
obj* x_79; obj* x_82; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_1);
lean::dec(x_2);
x_79 = lean::cnstr_get(x_74, 1);
lean::inc(x_79);
lean::dec(x_74);
x_82 = lean::cnstr_get(x_75, 0);
if (lean::is_exclusive(x_75)) {
 x_84 = x_75;
} else {
 lean::inc(x_82);
 lean::dec(x_75);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_82);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_79);
return x_86;
}
else
{
obj* x_88; obj* x_91; obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_75);
x_88 = lean::cnstr_get(x_74, 1);
lean::inc(x_88);
lean::dec(x_74);
x_91 = l_lean_ir_cpp_emit__apply___closed__2;
x_92 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_2);
x_94 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_91, x_92, x_1, x_2, x_88);
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
if (lean::obj_tag(x_95) == 0)
{
obj* x_98; obj* x_101; obj* x_103; obj* x_104; obj* x_105; 
lean::dec(x_2);
x_98 = lean::cnstr_get(x_94, 1);
lean::inc(x_98);
lean::dec(x_94);
x_101 = lean::cnstr_get(x_95, 0);
if (lean::is_exclusive(x_95)) {
 x_103 = x_95;
} else {
 lean::inc(x_101);
 lean::dec(x_95);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_101);
x_105 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_98);
return x_105;
}
else
{
obj* x_106; obj* x_109; obj* x_112; obj* x_113; obj* x_114; 
x_106 = lean::cnstr_get(x_94, 1);
lean::inc(x_106);
lean::dec(x_94);
x_109 = lean::cnstr_get(x_95, 0);
lean::inc(x_109);
lean::dec(x_95);
x_112 = l_option_has__repr___rarg___closed__3;
x_113 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_112, x_2, x_106);
x_114 = lean::cnstr_get(x_113, 0);
lean::inc(x_114);
if (lean::obj_tag(x_114) == 0)
{
obj* x_117; obj* x_120; obj* x_122; obj* x_123; obj* x_124; 
lean::dec(x_109);
x_117 = lean::cnstr_get(x_113, 1);
lean::inc(x_117);
lean::dec(x_113);
x_120 = lean::cnstr_get(x_114, 0);
if (lean::is_exclusive(x_114)) {
 x_122 = x_114;
} else {
 lean::inc(x_120);
 lean::dec(x_114);
 x_122 = lean::box(0);
}
if (lean::is_scalar(x_122)) {
 x_123 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_123 = x_122;
}
lean::cnstr_set(x_123, 0, x_120);
x_124 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_124, 0, x_123);
lean::cnstr_set(x_124, 1, x_117);
return x_124;
}
else
{
obj* x_125; obj* x_126; obj* x_129; obj* x_130; 
if (lean::is_exclusive(x_114)) {
 lean::cnstr_release(x_114, 0);
 x_125 = x_114;
} else {
 lean::dec(x_114);
 x_125 = lean::box(0);
}
x_126 = lean::cnstr_get(x_113, 1);
lean::inc(x_126);
lean::dec(x_113);
if (lean::is_scalar(x_125)) {
 x_129 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_129 = x_125;
}
lean::cnstr_set(x_129, 0, x_109);
x_130 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_126);
return x_130;
}
}
}
}
}
}
}
else
{
obj* x_132; obj* x_133; obj* x_135; obj* x_136; obj* x_138; obj* x_139; obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_147; 
lean::dec(x_1);
x_144 = l_lean_ir_cpp_emit__apply___closed__8;
lean::inc(x_2);
x_146 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_144, x_2, x_3);
x_147 = lean::cnstr_get(x_146, 0);
lean::inc(x_147);
if (lean::obj_tag(x_147) == 0)
{
obj* x_149; obj* x_152; obj* x_154; obj* x_155; 
x_149 = lean::cnstr_get(x_146, 1);
lean::inc(x_149);
lean::dec(x_146);
x_152 = lean::cnstr_get(x_147, 0);
if (lean::is_exclusive(x_147)) {
 x_154 = x_147;
} else {
 lean::inc(x_152);
 lean::dec(x_147);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_152);
x_141 = x_155;
x_142 = x_149;
goto lbl_143;
}
else
{
obj* x_157; obj* x_162; obj* x_163; 
lean::dec(x_147);
x_157 = lean::cnstr_get(x_146, 1);
lean::inc(x_157);
lean::dec(x_146);
lean::inc(x_2);
lean::inc(x_14);
x_162 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_14, x_2, x_157);
x_163 = lean::cnstr_get(x_162, 0);
lean::inc(x_163);
if (lean::obj_tag(x_163) == 0)
{
obj* x_165; obj* x_168; obj* x_170; obj* x_171; 
x_165 = lean::cnstr_get(x_162, 1);
lean::inc(x_165);
lean::dec(x_162);
x_168 = lean::cnstr_get(x_163, 0);
if (lean::is_exclusive(x_163)) {
 x_170 = x_163;
} else {
 lean::inc(x_168);
 lean::dec(x_163);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_168);
x_141 = x_171;
x_142 = x_165;
goto lbl_143;
}
else
{
obj* x_173; obj* x_176; obj* x_178; obj* x_179; obj* x_181; 
lean::dec(x_163);
x_173 = lean::cnstr_get(x_162, 1);
lean::inc(x_173);
lean::dec(x_162);
x_176 = l_lean_ir_cpp_emit__apply___closed__9;
lean::inc(x_2);
x_178 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_176, x_2, x_173);
x_179 = lean::cnstr_get(x_178, 0);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_178, 1);
lean::inc(x_181);
lean::dec(x_178);
x_141 = x_179;
x_142 = x_181;
goto lbl_143;
}
}
lbl_134:
{
if (lean::obj_tag(x_132) == 0)
{
obj* x_185; obj* x_187; obj* x_188; obj* x_189; 
lean::dec(x_2);
x_185 = lean::cnstr_get(x_132, 0);
if (lean::is_exclusive(x_132)) {
 x_187 = x_132;
} else {
 lean::inc(x_185);
 lean::dec(x_132);
 x_187 = lean::box(0);
}
if (lean::is_scalar(x_187)) {
 x_188 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_188 = x_187;
}
lean::cnstr_set(x_188, 0, x_185);
x_189 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_189, 0, x_188);
lean::cnstr_set(x_189, 1, x_133);
return x_189;
}
else
{
obj* x_191; obj* x_192; 
lean::dec(x_132);
x_191 = l_lean_ir_cpp_emit__apply___closed__4;
x_192 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_191, x_2, x_133);
return x_192;
}
}
lbl_137:
{
if (lean::obj_tag(x_135) == 0)
{
obj* x_193; obj* x_195; obj* x_196; 
x_193 = lean::cnstr_get(x_135, 0);
if (lean::is_exclusive(x_135)) {
 x_195 = x_135;
} else {
 lean::inc(x_193);
 lean::dec(x_135);
 x_195 = lean::box(0);
}
if (lean::is_scalar(x_195)) {
 x_196 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_196 = x_195;
}
lean::cnstr_set(x_196, 0, x_193);
x_132 = x_196;
x_133 = x_136;
goto lbl_134;
}
else
{
obj* x_198; obj* x_200; obj* x_201; 
lean::dec(x_135);
x_198 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
x_200 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_198, x_2, x_136);
x_201 = lean::cnstr_get(x_200, 0);
lean::inc(x_201);
if (lean::obj_tag(x_201) == 0)
{
obj* x_203; obj* x_206; obj* x_208; obj* x_209; 
x_203 = lean::cnstr_get(x_200, 1);
lean::inc(x_203);
lean::dec(x_200);
x_206 = lean::cnstr_get(x_201, 0);
if (lean::is_exclusive(x_201)) {
 x_208 = x_201;
} else {
 lean::inc(x_206);
 lean::dec(x_201);
 x_208 = lean::box(0);
}
if (lean::is_scalar(x_208)) {
 x_209 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_209 = x_208;
}
lean::cnstr_set(x_209, 0, x_206);
x_132 = x_209;
x_133 = x_203;
goto lbl_134;
}
else
{
obj* x_211; obj* x_214; obj* x_216; obj* x_217; 
lean::dec(x_201);
x_211 = lean::cnstr_get(x_200, 1);
lean::inc(x_211);
lean::dec(x_200);
x_214 = l_lean_ir_cpp_emit__apply___closed__5;
lean::inc(x_2);
x_216 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_214, x_2, x_211);
x_217 = lean::cnstr_get(x_216, 0);
lean::inc(x_217);
if (lean::obj_tag(x_217) == 0)
{
obj* x_219; obj* x_222; obj* x_224; obj* x_225; 
x_219 = lean::cnstr_get(x_216, 1);
lean::inc(x_219);
lean::dec(x_216);
x_222 = lean::cnstr_get(x_217, 0);
if (lean::is_exclusive(x_217)) {
 x_224 = x_217;
} else {
 lean::inc(x_222);
 lean::dec(x_217);
 x_224 = lean::box(0);
}
if (lean::is_scalar(x_224)) {
 x_225 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_225 = x_224;
}
lean::cnstr_set(x_225, 0, x_222);
x_132 = x_225;
x_133 = x_219;
goto lbl_134;
}
else
{
obj* x_226; obj* x_229; obj* x_232; obj* x_234; obj* x_235; 
x_226 = lean::cnstr_get(x_216, 1);
lean::inc(x_226);
lean::dec(x_216);
x_229 = lean::cnstr_get(x_217, 0);
lean::inc(x_229);
lean::dec(x_217);
x_232 = l_option_has__repr___rarg___closed__3;
lean::inc(x_2);
x_234 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_232, x_2, x_226);
x_235 = lean::cnstr_get(x_234, 0);
lean::inc(x_235);
if (lean::obj_tag(x_235) == 0)
{
obj* x_238; obj* x_241; obj* x_243; obj* x_244; 
lean::dec(x_229);
x_238 = lean::cnstr_get(x_234, 1);
lean::inc(x_238);
lean::dec(x_234);
x_241 = lean::cnstr_get(x_235, 0);
if (lean::is_exclusive(x_235)) {
 x_243 = x_235;
} else {
 lean::inc(x_241);
 lean::dec(x_235);
 x_243 = lean::box(0);
}
if (lean::is_scalar(x_243)) {
 x_244 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_244 = x_243;
}
lean::cnstr_set(x_244, 0, x_241);
x_132 = x_244;
x_133 = x_238;
goto lbl_134;
}
else
{
obj* x_245; obj* x_246; obj* x_249; 
if (lean::is_exclusive(x_235)) {
 lean::cnstr_release(x_235, 0);
 x_245 = x_235;
} else {
 lean::dec(x_235);
 x_245 = lean::box(0);
}
x_246 = lean::cnstr_get(x_234, 1);
lean::inc(x_246);
lean::dec(x_234);
if (lean::is_scalar(x_245)) {
 x_249 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_249 = x_245;
}
lean::cnstr_set(x_249, 0, x_229);
x_132 = x_249;
x_133 = x_246;
goto lbl_134;
}
}
}
}
}
lbl_140:
{
if (lean::obj_tag(x_138) == 0)
{
obj* x_252; obj* x_254; obj* x_255; 
lean::dec(x_8);
lean::dec(x_14);
x_252 = lean::cnstr_get(x_138, 0);
if (lean::is_exclusive(x_138)) {
 x_254 = x_138;
} else {
 lean::inc(x_252);
 lean::dec(x_138);
 x_254 = lean::box(0);
}
if (lean::is_scalar(x_254)) {
 x_255 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_255 = x_254;
}
lean::cnstr_set(x_255, 0, x_252);
x_132 = x_255;
x_133 = x_139;
goto lbl_134;
}
else
{
obj* x_257; obj* x_259; obj* x_260; 
lean::dec(x_138);
x_257 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_2);
x_259 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_257, x_2, x_139);
x_260 = lean::cnstr_get(x_259, 0);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
obj* x_264; obj* x_267; obj* x_269; obj* x_270; 
lean::dec(x_8);
lean::dec(x_14);
x_264 = lean::cnstr_get(x_259, 1);
lean::inc(x_264);
lean::dec(x_259);
x_267 = lean::cnstr_get(x_260, 0);
if (lean::is_exclusive(x_260)) {
 x_269 = x_260;
} else {
 lean::inc(x_267);
 lean::dec(x_260);
 x_269 = lean::box(0);
}
if (lean::is_scalar(x_269)) {
 x_270 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_270 = x_269;
}
lean::cnstr_set(x_270, 0, x_267);
x_132 = x_270;
x_133 = x_264;
goto lbl_134;
}
else
{
obj* x_272; obj* x_276; obj* x_277; 
lean::dec(x_260);
x_272 = lean::cnstr_get(x_259, 1);
lean::inc(x_272);
lean::dec(x_259);
lean::inc(x_2);
x_276 = l_lean_ir_cpp_emit__var(x_8, x_2, x_272);
x_277 = lean::cnstr_get(x_276, 0);
lean::inc(x_277);
if (lean::obj_tag(x_277) == 0)
{
obj* x_280; obj* x_283; obj* x_285; obj* x_286; 
lean::dec(x_14);
x_280 = lean::cnstr_get(x_276, 1);
lean::inc(x_280);
lean::dec(x_276);
x_283 = lean::cnstr_get(x_277, 0);
if (lean::is_exclusive(x_277)) {
 x_285 = x_277;
} else {
 lean::inc(x_283);
 lean::dec(x_277);
 x_285 = lean::box(0);
}
if (lean::is_scalar(x_285)) {
 x_286 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_286 = x_285;
}
lean::cnstr_set(x_286, 0, x_283);
x_135 = x_286;
x_136 = x_280;
goto lbl_137;
}
else
{
obj* x_288; obj* x_291; obj* x_293; obj* x_294; 
lean::dec(x_277);
x_288 = lean::cnstr_get(x_276, 1);
lean::inc(x_288);
lean::dec(x_276);
x_291 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
x_293 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_291, x_2, x_288);
x_294 = lean::cnstr_get(x_293, 0);
lean::inc(x_294);
if (lean::obj_tag(x_294) == 0)
{
obj* x_297; obj* x_300; obj* x_302; obj* x_303; 
lean::dec(x_14);
x_297 = lean::cnstr_get(x_293, 1);
lean::inc(x_297);
lean::dec(x_293);
x_300 = lean::cnstr_get(x_294, 0);
if (lean::is_exclusive(x_294)) {
 x_302 = x_294;
} else {
 lean::inc(x_300);
 lean::dec(x_294);
 x_302 = lean::box(0);
}
if (lean::is_scalar(x_302)) {
 x_303 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_303 = x_302;
}
lean::cnstr_set(x_303, 0, x_300);
x_135 = x_303;
x_136 = x_297;
goto lbl_137;
}
else
{
obj* x_305; obj* x_309; obj* x_310; obj* x_312; 
lean::dec(x_294);
x_305 = lean::cnstr_get(x_293, 1);
lean::inc(x_305);
lean::dec(x_293);
lean::inc(x_2);
x_309 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_14, x_2, x_305);
x_310 = lean::cnstr_get(x_309, 0);
lean::inc(x_310);
x_312 = lean::cnstr_get(x_309, 1);
lean::inc(x_312);
lean::dec(x_309);
x_135 = x_310;
x_136 = x_312;
goto lbl_137;
}
}
}
}
}
lbl_143:
{
if (lean::obj_tag(x_141) == 0)
{
obj* x_317; obj* x_319; obj* x_320; 
lean::dec(x_10);
lean::dec(x_0);
x_317 = lean::cnstr_get(x_141, 0);
if (lean::is_exclusive(x_141)) {
 x_319 = x_141;
} else {
 lean::inc(x_317);
 lean::dec(x_141);
 x_319 = lean::box(0);
}
if (lean::is_scalar(x_319)) {
 x_320 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_320 = x_319;
}
lean::cnstr_set(x_320, 0, x_317);
x_138 = x_320;
x_139 = x_142;
goto lbl_140;
}
else
{
obj* x_322; obj* x_323; obj* x_325; obj* x_326; 
lean::dec(x_141);
x_322 = l_lean_ir_cpp_emit__apply___closed__2;
x_323 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_2);
x_325 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_322, x_323, x_10, x_2, x_142);
x_326 = lean::cnstr_get(x_325, 0);
lean::inc(x_326);
if (lean::obj_tag(x_326) == 0)
{
obj* x_329; obj* x_332; obj* x_334; obj* x_335; 
lean::dec(x_0);
x_329 = lean::cnstr_get(x_325, 1);
lean::inc(x_329);
lean::dec(x_325);
x_332 = lean::cnstr_get(x_326, 0);
if (lean::is_exclusive(x_326)) {
 x_334 = x_326;
} else {
 lean::inc(x_332);
 lean::dec(x_326);
 x_334 = lean::box(0);
}
if (lean::is_scalar(x_334)) {
 x_335 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_335 = x_334;
}
lean::cnstr_set(x_335, 0, x_332);
x_138 = x_335;
x_139 = x_329;
goto lbl_140;
}
else
{
obj* x_337; obj* x_340; obj* x_342; obj* x_343; 
lean::dec(x_326);
x_337 = lean::cnstr_get(x_325, 1);
lean::inc(x_337);
lean::dec(x_325);
x_340 = l_lean_ir_cpp_emit__apply___closed__6;
lean::inc(x_2);
x_342 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_340, x_2, x_337);
x_343 = lean::cnstr_get(x_342, 0);
lean::inc(x_343);
if (lean::obj_tag(x_343) == 0)
{
obj* x_346; obj* x_349; obj* x_351; obj* x_352; 
lean::dec(x_0);
x_346 = lean::cnstr_get(x_342, 1);
lean::inc(x_346);
lean::dec(x_342);
x_349 = lean::cnstr_get(x_343, 0);
if (lean::is_exclusive(x_343)) {
 x_351 = x_343;
} else {
 lean::inc(x_349);
 lean::dec(x_343);
 x_351 = lean::box(0);
}
if (lean::is_scalar(x_351)) {
 x_352 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_352 = x_351;
}
lean::cnstr_set(x_352, 0, x_349);
x_138 = x_352;
x_139 = x_346;
goto lbl_140;
}
else
{
obj* x_354; obj* x_358; obj* x_359; 
lean::dec(x_343);
x_354 = lean::cnstr_get(x_342, 1);
lean::inc(x_354);
lean::dec(x_342);
lean::inc(x_2);
x_358 = l_lean_ir_cpp_emit__var(x_0, x_2, x_354);
x_359 = lean::cnstr_get(x_358, 0);
lean::inc(x_359);
if (lean::obj_tag(x_359) == 0)
{
obj* x_361; obj* x_364; obj* x_366; obj* x_367; 
x_361 = lean::cnstr_get(x_358, 1);
lean::inc(x_361);
lean::dec(x_358);
x_364 = lean::cnstr_get(x_359, 0);
if (lean::is_exclusive(x_359)) {
 x_366 = x_359;
} else {
 lean::inc(x_364);
 lean::dec(x_359);
 x_366 = lean::box(0);
}
if (lean::is_scalar(x_366)) {
 x_367 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_367 = x_366;
}
lean::cnstr_set(x_367, 0, x_364);
x_138 = x_367;
x_139 = x_361;
goto lbl_140;
}
else
{
obj* x_369; obj* x_372; obj* x_374; obj* x_375; obj* x_377; 
lean::dec(x_359);
x_369 = lean::cnstr_get(x_358, 1);
lean::inc(x_369);
lean::dec(x_358);
x_372 = l_lean_ir_cpp_emit__apply___closed__7;
lean::inc(x_2);
x_374 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_372, x_2, x_369);
x_375 = lean::cnstr_get(x_374, 0);
lean::inc(x_375);
x_377 = lean::cnstr_get(x_374, 1);
lean::inc(x_377);
lean::dec(x_374);
x_138 = x_375;
x_139 = x_377;
goto lbl_140;
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
obj* x_9; obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; 
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
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_9);
lean::dec(x_1);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_34 = x_25;
} else {
 lean::inc(x_32);
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
x_17 = x_29;
goto lbl_18;
}
else
{
obj* x_37; obj* x_40; obj* x_42; obj* x_43; 
lean::dec(x_25);
x_37 = lean::cnstr_get(x_24, 1);
lean::inc(x_37);
lean::dec(x_24);
x_40 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_3);
x_42 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_40, x_3, x_37);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_47; obj* x_50; obj* x_52; obj* x_53; 
lean::dec(x_9);
lean::dec(x_1);
x_47 = lean::cnstr_get(x_42, 1);
lean::inc(x_47);
lean::dec(x_42);
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
x_16 = x_53;
x_17 = x_47;
goto lbl_18;
}
else
{
obj* x_55; obj* x_60; obj* x_61; 
lean::dec(x_43);
x_55 = lean::cnstr_get(x_42, 1);
lean::inc(x_55);
lean::dec(x_42);
lean::inc(x_3);
lean::inc(x_0);
x_60 = l_lean_ir_cpp_emit__var(x_0, x_3, x_55);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
if (lean::obj_tag(x_61) == 0)
{
obj* x_64; obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_1);
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
x_19 = x_70;
x_20 = x_64;
goto lbl_21;
}
else
{
obj* x_72; obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_61);
x_72 = lean::cnstr_get(x_60, 1);
lean::inc(x_72);
lean::dec(x_60);
x_75 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_3);
x_77 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_75, x_3, x_72);
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
if (lean::obj_tag(x_78) == 0)
{
obj* x_81; obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_1);
x_81 = lean::cnstr_get(x_77, 1);
lean::inc(x_81);
lean::dec(x_77);
x_84 = lean::cnstr_get(x_78, 0);
if (lean::is_exclusive(x_78)) {
 x_86 = x_78;
} else {
 lean::inc(x_84);
 lean::dec(x_78);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_84);
x_19 = x_87;
x_20 = x_81;
goto lbl_21;
}
else
{
obj* x_89; obj* x_93; obj* x_94; obj* x_96; 
lean::dec(x_78);
x_89 = lean::cnstr_get(x_77, 1);
lean::inc(x_89);
lean::dec(x_77);
lean::inc(x_3);
x_93 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_1, x_3, x_89);
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_93, 1);
lean::inc(x_96);
lean::dec(x_93);
x_19 = x_94;
x_20 = x_96;
goto lbl_21;
}
}
}
}
lbl_18:
{
if (lean::obj_tag(x_16) == 0)
{
obj* x_103; obj* x_105; obj* x_106; obj* x_107; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
x_103 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_105 = x_16;
} else {
 lean::inc(x_103);
 lean::dec(x_16);
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
lean::cnstr_set(x_107, 1, x_17);
return x_107;
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
obj* x_111; obj* x_113; obj* x_114; 
lean::dec(x_9);
x_111 = lean::cnstr_get(x_19, 0);
if (lean::is_exclusive(x_19)) {
 x_113 = x_19;
} else {
 lean::inc(x_111);
 lean::dec(x_19);
 x_113 = lean::box(0);
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_111);
x_16 = x_114;
x_17 = x_20;
goto lbl_18;
}
else
{
obj* x_116; obj* x_118; obj* x_119; 
lean::dec(x_19);
x_116 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_3);
x_118 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_116, x_3, x_20);
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
if (lean::obj_tag(x_119) == 0)
{
obj* x_122; obj* x_125; obj* x_127; obj* x_128; 
lean::dec(x_9);
x_122 = lean::cnstr_get(x_118, 1);
lean::inc(x_122);
lean::dec(x_118);
x_125 = lean::cnstr_get(x_119, 0);
if (lean::is_exclusive(x_119)) {
 x_127 = x_119;
} else {
 lean::inc(x_125);
 lean::dec(x_119);
 x_127 = lean::box(0);
}
if (lean::is_scalar(x_127)) {
 x_128 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_128 = x_127;
}
lean::cnstr_set(x_128, 0, x_125);
x_16 = x_128;
x_17 = x_122;
goto lbl_18;
}
else
{
obj* x_130; obj* x_134; obj* x_135; 
lean::dec(x_119);
x_130 = lean::cnstr_get(x_118, 1);
lean::inc(x_130);
lean::dec(x_118);
lean::inc(x_3);
x_134 = l_lean_ir_cpp_emit__var(x_9, x_3, x_130);
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
if (lean::obj_tag(x_135) == 0)
{
obj* x_137; obj* x_140; obj* x_142; obj* x_143; 
x_137 = lean::cnstr_get(x_134, 1);
lean::inc(x_137);
lean::dec(x_134);
x_140 = lean::cnstr_get(x_135, 0);
if (lean::is_exclusive(x_135)) {
 x_142 = x_135;
} else {
 lean::inc(x_140);
 lean::dec(x_135);
 x_142 = lean::box(0);
}
if (lean::is_scalar(x_142)) {
 x_143 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_143 = x_142;
}
lean::cnstr_set(x_143, 0, x_140);
x_16 = x_143;
x_17 = x_137;
goto lbl_18;
}
else
{
obj* x_144; obj* x_147; obj* x_150; obj* x_152; obj* x_153; 
x_144 = lean::cnstr_get(x_134, 1);
lean::inc(x_144);
lean::dec(x_134);
x_147 = lean::cnstr_get(x_135, 0);
lean::inc(x_147);
lean::dec(x_135);
x_150 = l_option_has__repr___rarg___closed__3;
lean::inc(x_3);
x_152 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_150, x_3, x_144);
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
if (lean::obj_tag(x_153) == 0)
{
obj* x_156; obj* x_159; obj* x_161; obj* x_162; 
lean::dec(x_147);
x_156 = lean::cnstr_get(x_152, 1);
lean::inc(x_156);
lean::dec(x_152);
x_159 = lean::cnstr_get(x_153, 0);
if (lean::is_exclusive(x_153)) {
 x_161 = x_153;
} else {
 lean::inc(x_159);
 lean::dec(x_153);
 x_161 = lean::box(0);
}
if (lean::is_scalar(x_161)) {
 x_162 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_162 = x_161;
}
lean::cnstr_set(x_162, 0, x_159);
x_16 = x_162;
x_17 = x_156;
goto lbl_18;
}
else
{
obj* x_163; obj* x_164; obj* x_167; 
if (lean::is_exclusive(x_153)) {
 lean::cnstr_release(x_153, 0);
 x_163 = x_153;
} else {
 lean::dec(x_153);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_152, 1);
lean::inc(x_164);
lean::dec(x_152);
if (lean::is_scalar(x_163)) {
 x_167 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_167 = x_163;
}
lean::cnstr_set(x_167, 0, x_147);
x_16 = x_167;
x_17 = x_164;
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
obj* x_18; obj* x_23; obj* x_24; 
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
lean::dec(x_11);
lean::inc(x_3);
lean::inc(x_0);
x_23 = l_lean_ir_cpp_emit__var(x_0, x_3, x_4);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_31; obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_2);
x_31 = lean::cnstr_get(x_23, 1);
lean::inc(x_31);
lean::dec(x_23);
x_34 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_36 = x_24;
} else {
 lean::inc(x_34);
 lean::dec(x_24);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_31);
return x_38;
}
else
{
obj* x_40; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_24);
x_40 = lean::cnstr_get(x_23, 1);
lean::inc(x_40);
lean::dec(x_23);
x_46 = l_lean_ir_cpp_emit__closure___closed__2;
lean::inc(x_3);
x_48 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_46, x_3, x_40);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
if (lean::obj_tag(x_49) == 0)
{
obj* x_56; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_2);
x_56 = lean::cnstr_get(x_48, 1);
lean::inc(x_56);
lean::dec(x_48);
x_59 = lean::cnstr_get(x_49, 0);
if (lean::is_exclusive(x_49)) {
 x_61 = x_49;
} else {
 lean::inc(x_59);
 lean::dec(x_49);
 x_61 = lean::box(0);
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_59);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_56);
return x_63;
}
else
{
obj* x_65; obj* x_69; obj* x_70; 
lean::dec(x_49);
x_65 = lean::cnstr_get(x_48, 1);
lean::inc(x_65);
lean::dec(x_48);
lean::inc(x_3);
x_69 = l_lean_ir_cpp_fid2cpp(x_1, x_3, x_65);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_76; obj* x_79; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_2);
x_76 = lean::cnstr_get(x_69, 1);
lean::inc(x_76);
lean::dec(x_69);
x_79 = lean::cnstr_get(x_70, 0);
if (lean::is_exclusive(x_70)) {
 x_81 = x_70;
} else {
 lean::inc(x_79);
 lean::dec(x_70);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_79);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_76);
return x_83;
}
else
{
obj* x_84; obj* x_87; obj* x_90; obj* x_91; obj* x_94; obj* x_95; obj* x_96; uint8 x_97; obj* x_99; obj* x_100; obj* x_102; obj* x_103; obj* x_104; 
x_84 = lean::cnstr_get(x_69, 1);
lean::inc(x_84);
lean::dec(x_69);
x_87 = lean::cnstr_get(x_70, 0);
lean::inc(x_87);
lean::dec(x_70);
x_90 = l_lean_ir_decl_header___main(x_18);
x_91 = lean::cnstr_get(x_90, 1);
lean::inc(x_91);
lean::dec(x_90);
x_94 = lean::mk_nat_obj(0u);
x_95 = l_list_length__aux___main___rarg(x_91, x_94);
x_96 = l_lean_closure__max__args;
x_97 = lean::nat_dec_lt(x_96, x_95);
lean::inc(x_2);
x_99 = l_list_length__aux___main___rarg(x_2, x_94);
x_100 = l_lean_ir_cpp_emit__closure___closed__3;
lean::inc(x_3);
x_102 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_100, x_3, x_84);
if (x_97 == 0)
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
obj* x_117; obj* x_121; obj* x_122; obj* x_124; 
lean::dec(x_106);
x_117 = lean::cnstr_get(x_102, 1);
lean::inc(x_117);
lean::dec(x_102);
lean::inc(x_3);
x_121 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_87, x_3, x_117);
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_121, 1);
lean::inc(x_124);
lean::dec(x_121);
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
obj* x_138; obj* x_141; obj* x_142; obj* x_145; obj* x_146; obj* x_148; 
lean::dec(x_127);
x_138 = lean::cnstr_get(x_102, 1);
lean::inc(x_138);
lean::dec(x_102);
x_141 = l_lean_ir_cpp_emit__closure___closed__4;
x_142 = lean::string_append(x_141, x_87);
lean::dec(x_87);
lean::inc(x_3);
x_145 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_142, x_3, x_138);
x_146 = lean::cnstr_get(x_145, 0);
lean::inc(x_146);
x_148 = lean::cnstr_get(x_145, 1);
lean::inc(x_148);
lean::dec(x_145);
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
lean::dec(x_99);
lean::dec(x_95);
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
x_43 = x_156;
x_44 = x_104;
goto lbl_45;
}
else
{
obj* x_158; obj* x_160; obj* x_161; 
lean::dec(x_103);
x_158 = l_option_has__repr___rarg___closed__3;
lean::inc(x_3);
x_160 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_158, x_3, x_104);
x_161 = lean::cnstr_get(x_160, 0);
lean::inc(x_161);
if (lean::obj_tag(x_161) == 0)
{
obj* x_165; obj* x_168; obj* x_170; obj* x_171; 
lean::dec(x_99);
lean::dec(x_95);
x_165 = lean::cnstr_get(x_160, 1);
lean::inc(x_165);
lean::dec(x_160);
x_168 = lean::cnstr_get(x_161, 0);
if (lean::is_exclusive(x_161)) {
 x_170 = x_161;
} else {
 lean::inc(x_168);
 lean::dec(x_161);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_168);
x_43 = x_171;
x_44 = x_165;
goto lbl_45;
}
else
{
obj* x_173; obj* x_176; obj* x_178; obj* x_179; 
lean::dec(x_161);
x_173 = lean::cnstr_get(x_160, 1);
lean::inc(x_173);
lean::dec(x_160);
x_176 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_3);
x_178 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_176, x_3, x_173);
x_179 = lean::cnstr_get(x_178, 0);
lean::inc(x_179);
if (lean::obj_tag(x_179) == 0)
{
obj* x_183; obj* x_186; obj* x_188; obj* x_189; 
lean::dec(x_99);
lean::dec(x_95);
x_183 = lean::cnstr_get(x_178, 1);
lean::inc(x_183);
lean::dec(x_178);
x_186 = lean::cnstr_get(x_179, 0);
if (lean::is_exclusive(x_179)) {
 x_188 = x_179;
} else {
 lean::inc(x_186);
 lean::dec(x_179);
 x_188 = lean::box(0);
}
if (lean::is_scalar(x_188)) {
 x_189 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_189 = x_188;
}
lean::cnstr_set(x_189, 0, x_186);
x_43 = x_189;
x_44 = x_183;
goto lbl_45;
}
else
{
obj* x_191; obj* x_195; obj* x_196; 
lean::dec(x_179);
x_191 = lean::cnstr_get(x_178, 1);
lean::inc(x_191);
lean::dec(x_178);
lean::inc(x_3);
x_195 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_95, x_3, x_191);
x_196 = lean::cnstr_get(x_195, 0);
lean::inc(x_196);
if (lean::obj_tag(x_196) == 0)
{
obj* x_199; obj* x_202; obj* x_204; obj* x_205; 
lean::dec(x_99);
x_199 = lean::cnstr_get(x_195, 1);
lean::inc(x_199);
lean::dec(x_195);
x_202 = lean::cnstr_get(x_196, 0);
if (lean::is_exclusive(x_196)) {
 x_204 = x_196;
} else {
 lean::inc(x_202);
 lean::dec(x_196);
 x_204 = lean::box(0);
}
if (lean::is_scalar(x_204)) {
 x_205 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_205 = x_204;
}
lean::cnstr_set(x_205, 0, x_202);
x_43 = x_205;
x_44 = x_199;
goto lbl_45;
}
else
{
obj* x_207; obj* x_211; obj* x_212; 
lean::dec(x_196);
x_207 = lean::cnstr_get(x_195, 1);
lean::inc(x_207);
lean::dec(x_195);
lean::inc(x_3);
x_211 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_176, x_3, x_207);
x_212 = lean::cnstr_get(x_211, 0);
lean::inc(x_212);
if (lean::obj_tag(x_212) == 0)
{
obj* x_215; obj* x_218; obj* x_220; obj* x_221; 
lean::dec(x_99);
x_215 = lean::cnstr_get(x_211, 1);
lean::inc(x_215);
lean::dec(x_211);
x_218 = lean::cnstr_get(x_212, 0);
if (lean::is_exclusive(x_212)) {
 x_220 = x_212;
} else {
 lean::inc(x_218);
 lean::dec(x_212);
 x_220 = lean::box(0);
}
if (lean::is_scalar(x_220)) {
 x_221 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_221 = x_220;
}
lean::cnstr_set(x_221, 0, x_218);
x_43 = x_221;
x_44 = x_215;
goto lbl_45;
}
else
{
obj* x_223; obj* x_227; obj* x_228; obj* x_230; 
lean::dec(x_212);
x_223 = lean::cnstr_get(x_211, 1);
lean::inc(x_223);
lean::dec(x_211);
lean::inc(x_3);
x_227 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_99, x_3, x_223);
x_228 = lean::cnstr_get(x_227, 0);
lean::inc(x_228);
x_230 = lean::cnstr_get(x_227, 1);
lean::inc(x_230);
lean::dec(x_227);
x_43 = x_228;
x_44 = x_230;
goto lbl_45;
}
}
}
}
}
}
}
}
lbl_45:
{
if (lean::obj_tag(x_43) == 0)
{
obj* x_236; obj* x_238; obj* x_239; obj* x_240; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_236 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 x_238 = x_43;
} else {
 lean::inc(x_236);
 lean::dec(x_43);
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
lean::cnstr_set(x_240, 1, x_44);
return x_240;
}
else
{
obj* x_242; obj* x_244; obj* x_245; 
lean::dec(x_43);
x_242 = l_option_has__repr___rarg___closed__3;
lean::inc(x_3);
x_244 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_242, x_3, x_44);
x_245 = lean::cnstr_get(x_244, 0);
lean::inc(x_245);
if (lean::obj_tag(x_245) == 0)
{
obj* x_250; obj* x_253; obj* x_255; obj* x_256; obj* x_257; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_250 = lean::cnstr_get(x_244, 1);
lean::inc(x_250);
lean::dec(x_244);
x_253 = lean::cnstr_get(x_245, 0);
if (lean::is_exclusive(x_245)) {
 x_255 = x_245;
} else {
 lean::inc(x_253);
 lean::dec(x_245);
 x_255 = lean::box(0);
}
if (lean::is_scalar(x_255)) {
 x_256 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_256 = x_255;
}
lean::cnstr_set(x_256, 0, x_253);
x_257 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_257, 0, x_256);
lean::cnstr_set(x_257, 1, x_250);
return x_257;
}
else
{
obj* x_259; obj* x_262; obj* x_263; obj* x_264; 
lean::dec(x_245);
x_259 = lean::cnstr_get(x_244, 1);
lean::inc(x_259);
lean::dec(x_244);
x_262 = lean::mk_nat_obj(0u);
x_263 = l_list_mfoldl___main___at_lean_ir_cpp_emit__closure___spec__1(x_0, x_262, x_2, x_3, x_259);
x_264 = lean::cnstr_get(x_263, 0);
lean::inc(x_264);
if (lean::obj_tag(x_264) == 0)
{
obj* x_266; obj* x_269; obj* x_271; obj* x_272; obj* x_273; 
x_266 = lean::cnstr_get(x_263, 1);
lean::inc(x_266);
lean::dec(x_263);
x_269 = lean::cnstr_get(x_264, 0);
if (lean::is_exclusive(x_264)) {
 x_271 = x_264;
} else {
 lean::inc(x_269);
 lean::dec(x_264);
 x_271 = lean::box(0);
}
if (lean::is_scalar(x_271)) {
 x_272 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_272 = x_271;
}
lean::cnstr_set(x_272, 0, x_269);
x_273 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_273, 0, x_272);
lean::cnstr_set(x_273, 1, x_266);
return x_273;
}
else
{
obj* x_275; obj* x_278; obj* x_279; 
lean::dec(x_264);
x_275 = lean::cnstr_get(x_263, 1);
lean::inc(x_275);
lean::dec(x_263);
x_278 = l_lean_ir_match__type___closed__5;
x_279 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_279, 0, x_278);
lean::cnstr_set(x_279, 1, x_275);
return x_279;
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
obj* x_5; obj* x_7; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::inc(x_1);
x_10 = l_lean_ir_cpp_emit__var(x_5, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_14 = lean::cnstr_get(x_10, 1);
lean::inc(x_14);
lean::dec(x_10);
x_17 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_19 = x_11;
} else {
 lean::inc(x_17);
 lean::dec(x_11);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_17);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_14);
x_3 = x_21;
goto lbl_4;
}
else
{
obj* x_23; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_11);
x_23 = lean::cnstr_get(x_10, 1);
lean::inc(x_23);
lean::dec(x_10);
x_26 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_1);
x_28 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_26, x_1, x_23);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_32; obj* x_35; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_7);
x_32 = lean::cnstr_get(x_28, 1);
lean::inc(x_32);
lean::dec(x_28);
x_35 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_37 = x_29;
} else {
 lean::inc(x_35);
 lean::dec(x_29);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_35);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_32);
x_3 = x_39;
goto lbl_4;
}
else
{
obj* x_41; obj* x_45; 
lean::dec(x_29);
x_41 = lean::cnstr_get(x_28, 1);
lean::inc(x_41);
lean::dec(x_28);
lean::inc(x_1);
x_45 = l_lean_ir_cpp_emit__var(x_7, x_1, x_41);
x_3 = x_45;
goto lbl_4;
}
}
}
case 1:
{
obj* x_46; uint8 x_48; obj* x_49; obj* x_52; 
x_46 = lean::cnstr_get(x_0, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_49 = lean::cnstr_get(x_0, 1);
lean::inc(x_49);
lean::inc(x_1);
x_52 = l_lean_ir_cpp_emit__assign__lit(x_46, x_48, x_49, x_1, x_2);
x_3 = x_52;
goto lbl_4;
}
case 2:
{
obj* x_53; uint8 x_55; uint8 x_56; obj* x_57; obj* x_60; 
x_53 = lean::cnstr_get(x_0, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
x_56 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2 + 1);
x_57 = lean::cnstr_get(x_0, 1);
lean::inc(x_57);
lean::inc(x_1);
x_60 = l_lean_ir_cpp_emit__assign__unop(x_53, x_55, x_56, x_57, x_1, x_2);
x_3 = x_60;
goto lbl_4;
}
case 3:
{
obj* x_61; uint8 x_63; uint8 x_64; obj* x_65; obj* x_67; obj* x_70; 
x_61 = lean::cnstr_get(x_0, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_64 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3 + 1);
x_65 = lean::cnstr_get(x_0, 1);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_0, 2);
lean::inc(x_67);
lean::inc(x_1);
x_70 = l_lean_ir_cpp_emit__assign__binop(x_61, x_63, x_64, x_65, x_67, x_1, x_2);
x_3 = x_70;
goto lbl_4;
}
case 4:
{
uint8 x_71; obj* x_72; obj* x_75; 
x_71 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*1);
x_72 = lean::cnstr_get(x_0, 0);
lean::inc(x_72);
lean::inc(x_1);
x_75 = l_lean_ir_cpp_emit__unop(x_71, x_72, x_1, x_2);
x_3 = x_75;
goto lbl_4;
}
case 5:
{
obj* x_76; obj* x_78; obj* x_80; obj* x_82; obj* x_83; obj* x_86; obj* x_87; 
x_76 = lean::cnstr_get(x_0, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_0, 1);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_0, 2);
lean::inc(x_80);
lean::inc(x_1);
x_86 = l_lean_ir_cpp_emit__var(x_76, x_1, x_2);
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
if (lean::obj_tag(x_87) == 0)
{
obj* x_89; obj* x_92; obj* x_94; obj* x_95; 
x_89 = lean::cnstr_get(x_86, 1);
lean::inc(x_89);
lean::dec(x_86);
x_92 = lean::cnstr_get(x_87, 0);
if (lean::is_exclusive(x_87)) {
 x_94 = x_87;
} else {
 lean::inc(x_92);
 lean::dec(x_87);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_92);
x_82 = x_95;
x_83 = x_89;
goto lbl_84;
}
else
{
obj* x_97; obj* x_100; obj* x_102; obj* x_103; obj* x_105; 
lean::dec(x_87);
x_97 = lean::cnstr_get(x_86, 1);
lean::inc(x_97);
lean::dec(x_86);
x_100 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_1);
x_102 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_100, x_1, x_97);
x_103 = lean::cnstr_get(x_102, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_102, 1);
lean::inc(x_105);
lean::dec(x_102);
x_82 = x_103;
x_83 = x_105;
goto lbl_84;
}
lbl_84:
{
if (lean::obj_tag(x_82) == 0)
{
obj* x_110; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_78);
lean::dec(x_80);
x_110 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 x_112 = x_82;
} else {
 lean::inc(x_110);
 lean::dec(x_82);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_110);
x_114 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_83);
x_3 = x_114;
goto lbl_4;
}
else
{
obj* x_118; obj* x_119; obj* x_121; obj* x_124; 
lean::dec(x_82);
lean::inc(x_1);
lean::inc(x_78);
x_118 = l_lean_ir_cpp_is__const(x_78, x_1, x_83);
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_118, 1);
lean::inc(x_121);
lean::dec(x_118);
if (lean::obj_tag(x_119) == 0)
{
obj* x_128; obj* x_130; obj* x_131; obj* x_132; 
lean::dec(x_78);
lean::dec(x_80);
x_128 = lean::cnstr_get(x_119, 0);
if (lean::is_exclusive(x_119)) {
 x_130 = x_119;
} else {
 lean::inc(x_128);
 lean::dec(x_119);
 x_130 = lean::box(0);
}
if (lean::is_scalar(x_130)) {
 x_131 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_131 = x_130;
}
lean::cnstr_set(x_131, 0, x_128);
x_132 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_121);
x_3 = x_132;
goto lbl_4;
}
else
{
obj* x_133; uint8 x_136; 
x_133 = lean::cnstr_get(x_119, 0);
lean::inc(x_133);
lean::dec(x_119);
x_136 = lean::unbox(x_133);
if (x_136 == 0)
{
obj* x_137; 
x_137 = lean::box(0);
x_124 = x_137;
goto lbl_125;
}
else
{
obj* x_140; 
lean::dec(x_80);
lean::inc(x_1);
x_140 = l_lean_ir_cpp_emit__global(x_78, x_1, x_121);
x_3 = x_140;
goto lbl_4;
}
}
lbl_125:
{
obj* x_143; obj* x_144; 
lean::dec(x_124);
lean::inc(x_1);
x_143 = l_lean_ir_cpp_emit__fnid(x_78, x_1, x_121);
x_144 = lean::cnstr_get(x_143, 0);
lean::inc(x_144);
if (lean::obj_tag(x_144) == 0)
{
obj* x_147; obj* x_150; obj* x_152; obj* x_153; obj* x_154; 
lean::dec(x_80);
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
x_154 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_154, 0, x_153);
lean::cnstr_set(x_154, 1, x_147);
x_3 = x_154;
goto lbl_4;
}
else
{
obj* x_156; obj* x_159; obj* x_161; obj* x_162; 
lean::dec(x_144);
x_156 = lean::cnstr_get(x_143, 1);
lean::inc(x_156);
lean::dec(x_143);
x_159 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_161 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_159, x_1, x_156);
x_162 = lean::cnstr_get(x_161, 0);
lean::inc(x_162);
if (lean::obj_tag(x_162) == 0)
{
obj* x_165; obj* x_168; obj* x_170; obj* x_171; obj* x_172; 
lean::dec(x_80);
x_165 = lean::cnstr_get(x_161, 1);
lean::inc(x_165);
lean::dec(x_161);
x_168 = lean::cnstr_get(x_162, 0);
if (lean::is_exclusive(x_162)) {
 x_170 = x_162;
} else {
 lean::inc(x_168);
 lean::dec(x_162);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_168);
x_172 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_172, 0, x_171);
lean::cnstr_set(x_172, 1, x_165);
x_3 = x_172;
goto lbl_4;
}
else
{
obj* x_174; obj* x_177; obj* x_178; obj* x_180; obj* x_181; 
lean::dec(x_162);
x_174 = lean::cnstr_get(x_161, 1);
lean::inc(x_174);
lean::dec(x_161);
x_177 = l_lean_ir_cpp_emit__apply___closed__2;
x_178 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_1);
x_180 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_177, x_178, x_80, x_1, x_174);
x_181 = lean::cnstr_get(x_180, 0);
lean::inc(x_181);
if (lean::obj_tag(x_181) == 0)
{
obj* x_183; obj* x_186; obj* x_188; obj* x_189; obj* x_190; 
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
x_190 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_190, 0, x_189);
lean::cnstr_set(x_190, 1, x_183);
x_3 = x_190;
goto lbl_4;
}
else
{
obj* x_191; obj* x_194; obj* x_197; obj* x_199; obj* x_200; 
x_191 = lean::cnstr_get(x_180, 1);
lean::inc(x_191);
lean::dec(x_180);
x_194 = lean::cnstr_get(x_181, 0);
lean::inc(x_194);
lean::dec(x_181);
x_197 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_199 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_197, x_1, x_191);
x_200 = lean::cnstr_get(x_199, 0);
lean::inc(x_200);
if (lean::obj_tag(x_200) == 0)
{
obj* x_203; obj* x_206; obj* x_208; obj* x_209; obj* x_210; 
lean::dec(x_194);
x_203 = lean::cnstr_get(x_199, 1);
lean::inc(x_203);
lean::dec(x_199);
x_206 = lean::cnstr_get(x_200, 0);
if (lean::is_exclusive(x_200)) {
 x_208 = x_200;
} else {
 lean::inc(x_206);
 lean::dec(x_200);
 x_208 = lean::box(0);
}
if (lean::is_scalar(x_208)) {
 x_209 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_209 = x_208;
}
lean::cnstr_set(x_209, 0, x_206);
x_210 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_210, 0, x_209);
lean::cnstr_set(x_210, 1, x_203);
x_3 = x_210;
goto lbl_4;
}
else
{
obj* x_211; obj* x_212; obj* x_215; obj* x_216; 
if (lean::is_exclusive(x_200)) {
 lean::cnstr_release(x_200, 0);
 x_211 = x_200;
} else {
 lean::dec(x_200);
 x_211 = lean::box(0);
}
x_212 = lean::cnstr_get(x_199, 1);
lean::inc(x_212);
lean::dec(x_199);
if (lean::is_scalar(x_211)) {
 x_215 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_215 = x_211;
}
lean::cnstr_set(x_215, 0, x_194);
x_216 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_216, 0, x_215);
lean::cnstr_set(x_216, 1, x_212);
x_3 = x_216;
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
obj* x_217; uint16 x_219; uint16 x_220; usize x_221; obj* x_222; obj* x_223; obj* x_225; obj* x_226; obj* x_229; obj* x_230; 
x_217 = lean::cnstr_get(x_0, 0);
lean::inc(x_217);
x_219 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
x_220 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2 + 2);
x_221 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*1);
lean::inc(x_1);
x_229 = l_lean_ir_cpp_emit__var(x_217, x_1, x_2);
x_230 = lean::cnstr_get(x_229, 0);
lean::inc(x_230);
if (lean::obj_tag(x_230) == 0)
{
obj* x_232; obj* x_235; obj* x_237; obj* x_238; 
x_232 = lean::cnstr_get(x_229, 1);
lean::inc(x_232);
lean::dec(x_229);
x_235 = lean::cnstr_get(x_230, 0);
if (lean::is_exclusive(x_230)) {
 x_237 = x_230;
} else {
 lean::inc(x_235);
 lean::dec(x_230);
 x_237 = lean::box(0);
}
if (lean::is_scalar(x_237)) {
 x_238 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_238 = x_237;
}
lean::cnstr_set(x_238, 0, x_235);
x_225 = x_238;
x_226 = x_232;
goto lbl_227;
}
else
{
obj* x_240; obj* x_243; obj* x_245; obj* x_246; obj* x_248; 
lean::dec(x_230);
x_240 = lean::cnstr_get(x_229, 1);
lean::inc(x_240);
lean::dec(x_229);
x_243 = l_lean_ir_cpp_emit__instr___closed__1;
lean::inc(x_1);
x_245 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_243, x_1, x_240);
x_246 = lean::cnstr_get(x_245, 0);
lean::inc(x_246);
x_248 = lean::cnstr_get(x_245, 1);
lean::inc(x_248);
lean::dec(x_245);
x_225 = x_246;
x_226 = x_248;
goto lbl_227;
}
lbl_224:
{
if (lean::obj_tag(x_222) == 0)
{
obj* x_251; obj* x_253; obj* x_254; obj* x_255; 
x_251 = lean::cnstr_get(x_222, 0);
if (lean::is_exclusive(x_222)) {
 x_253 = x_222;
} else {
 lean::inc(x_251);
 lean::dec(x_222);
 x_253 = lean::box(0);
}
if (lean::is_scalar(x_253)) {
 x_254 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_254 = x_253;
}
lean::cnstr_set(x_254, 0, x_251);
x_255 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_255, 0, x_254);
lean::cnstr_set(x_255, 1, x_223);
x_3 = x_255;
goto lbl_4;
}
else
{
obj* x_257; obj* x_259; obj* x_260; 
lean::dec(x_222);
x_257 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_259 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_257, x_1, x_223);
x_260 = lean::cnstr_get(x_259, 0);
lean::inc(x_260);
if (lean::obj_tag(x_260) == 0)
{
obj* x_262; obj* x_265; obj* x_267; obj* x_268; obj* x_269; 
x_262 = lean::cnstr_get(x_259, 1);
lean::inc(x_262);
lean::dec(x_259);
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
x_269 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_269, 0, x_268);
lean::cnstr_set(x_269, 1, x_262);
x_3 = x_269;
goto lbl_4;
}
else
{
obj* x_271; obj* x_275; obj* x_276; 
lean::dec(x_260);
x_271 = lean::cnstr_get(x_259, 1);
lean::inc(x_271);
lean::dec(x_259);
lean::inc(x_1);
x_275 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(x_221, x_1, x_271);
x_276 = lean::cnstr_get(x_275, 0);
lean::inc(x_276);
if (lean::obj_tag(x_276) == 0)
{
obj* x_278; obj* x_281; obj* x_283; obj* x_284; obj* x_285; 
x_278 = lean::cnstr_get(x_275, 1);
lean::inc(x_278);
lean::dec(x_275);
x_281 = lean::cnstr_get(x_276, 0);
if (lean::is_exclusive(x_276)) {
 x_283 = x_276;
} else {
 lean::inc(x_281);
 lean::dec(x_276);
 x_283 = lean::box(0);
}
if (lean::is_scalar(x_283)) {
 x_284 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_284 = x_283;
}
lean::cnstr_set(x_284, 0, x_281);
x_285 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_285, 0, x_284);
lean::cnstr_set(x_285, 1, x_278);
x_3 = x_285;
goto lbl_4;
}
else
{
obj* x_286; obj* x_289; obj* x_292; obj* x_294; obj* x_295; 
x_286 = lean::cnstr_get(x_275, 1);
lean::inc(x_286);
lean::dec(x_275);
x_289 = lean::cnstr_get(x_276, 0);
lean::inc(x_289);
lean::dec(x_276);
x_292 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_294 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_292, x_1, x_286);
x_295 = lean::cnstr_get(x_294, 0);
lean::inc(x_295);
if (lean::obj_tag(x_295) == 0)
{
obj* x_298; obj* x_301; obj* x_303; obj* x_304; obj* x_305; 
lean::dec(x_289);
x_298 = lean::cnstr_get(x_294, 1);
lean::inc(x_298);
lean::dec(x_294);
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
x_305 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_305, 0, x_304);
lean::cnstr_set(x_305, 1, x_298);
x_3 = x_305;
goto lbl_4;
}
else
{
obj* x_306; obj* x_307; obj* x_310; obj* x_311; 
if (lean::is_exclusive(x_295)) {
 lean::cnstr_release(x_295, 0);
 x_306 = x_295;
} else {
 lean::dec(x_295);
 x_306 = lean::box(0);
}
x_307 = lean::cnstr_get(x_294, 1);
lean::inc(x_307);
lean::dec(x_294);
if (lean::is_scalar(x_306)) {
 x_310 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_310 = x_306;
}
lean::cnstr_set(x_310, 0, x_289);
x_311 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_311, 0, x_310);
lean::cnstr_set(x_311, 1, x_307);
x_3 = x_311;
goto lbl_4;
}
}
}
}
}
lbl_227:
{
if (lean::obj_tag(x_225) == 0)
{
obj* x_312; obj* x_314; obj* x_315; obj* x_316; 
x_312 = lean::cnstr_get(x_225, 0);
if (lean::is_exclusive(x_225)) {
 x_314 = x_225;
} else {
 lean::inc(x_312);
 lean::dec(x_225);
 x_314 = lean::box(0);
}
if (lean::is_scalar(x_314)) {
 x_315 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_315 = x_314;
}
lean::cnstr_set(x_315, 0, x_312);
x_316 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_316, 0, x_315);
lean::cnstr_set(x_316, 1, x_226);
x_3 = x_316;
goto lbl_4;
}
else
{
obj* x_318; obj* x_320; obj* x_321; 
lean::dec(x_225);
x_318 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_320 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_318, x_1, x_226);
x_321 = lean::cnstr_get(x_320, 0);
lean::inc(x_321);
if (lean::obj_tag(x_321) == 0)
{
obj* x_323; obj* x_326; obj* x_328; obj* x_329; obj* x_330; 
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
x_330 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_330, 0, x_329);
lean::cnstr_set(x_330, 1, x_323);
x_3 = x_330;
goto lbl_4;
}
else
{
obj* x_332; obj* x_336; obj* x_337; 
lean::dec(x_321);
x_332 = lean::cnstr_get(x_320, 1);
lean::inc(x_332);
lean::dec(x_320);
lean::inc(x_1);
x_336 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__2(x_219, x_1, x_332);
x_337 = lean::cnstr_get(x_336, 0);
lean::inc(x_337);
if (lean::obj_tag(x_337) == 0)
{
obj* x_339; obj* x_342; obj* x_344; obj* x_345; 
x_339 = lean::cnstr_get(x_336, 1);
lean::inc(x_339);
lean::dec(x_336);
x_342 = lean::cnstr_get(x_337, 0);
if (lean::is_exclusive(x_337)) {
 x_344 = x_337;
} else {
 lean::inc(x_342);
 lean::dec(x_337);
 x_344 = lean::box(0);
}
if (lean::is_scalar(x_344)) {
 x_345 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_345 = x_344;
}
lean::cnstr_set(x_345, 0, x_342);
x_222 = x_345;
x_223 = x_339;
goto lbl_224;
}
else
{
obj* x_347; obj* x_350; obj* x_352; obj* x_353; 
lean::dec(x_337);
x_347 = lean::cnstr_get(x_336, 1);
lean::inc(x_347);
lean::dec(x_336);
x_350 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_352 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_350, x_1, x_347);
x_353 = lean::cnstr_get(x_352, 0);
lean::inc(x_353);
if (lean::obj_tag(x_353) == 0)
{
obj* x_355; obj* x_358; obj* x_360; obj* x_361; 
x_355 = lean::cnstr_get(x_352, 1);
lean::inc(x_355);
lean::dec(x_352);
x_358 = lean::cnstr_get(x_353, 0);
if (lean::is_exclusive(x_353)) {
 x_360 = x_353;
} else {
 lean::inc(x_358);
 lean::dec(x_353);
 x_360 = lean::box(0);
}
if (lean::is_scalar(x_360)) {
 x_361 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_361 = x_360;
}
lean::cnstr_set(x_361, 0, x_358);
x_222 = x_361;
x_223 = x_355;
goto lbl_224;
}
else
{
obj* x_363; obj* x_367; obj* x_368; obj* x_370; 
lean::dec(x_353);
x_363 = lean::cnstr_get(x_352, 1);
lean::inc(x_363);
lean::dec(x_352);
lean::inc(x_1);
x_367 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_220, x_1, x_363);
x_368 = lean::cnstr_get(x_367, 0);
lean::inc(x_368);
x_370 = lean::cnstr_get(x_367, 1);
lean::inc(x_370);
lean::dec(x_367);
x_222 = x_368;
x_223 = x_370;
goto lbl_224;
}
}
}
}
}
}
case 7:
{
obj* x_373; uint16 x_375; obj* x_376; obj* x_378; obj* x_379; obj* x_381; obj* x_383; obj* x_384; 
x_373 = lean::cnstr_get(x_0, 0);
lean::inc(x_373);
x_375 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
x_376 = lean::cnstr_get(x_0, 1);
lean::inc(x_376);
x_381 = l_lean_ir_cpp_emit__instr___closed__2;
lean::inc(x_1);
x_383 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_381, x_1, x_2);
x_384 = lean::cnstr_get(x_383, 0);
lean::inc(x_384);
if (lean::obj_tag(x_384) == 0)
{
obj* x_388; obj* x_391; obj* x_393; obj* x_394; obj* x_395; 
lean::dec(x_373);
lean::dec(x_376);
x_388 = lean::cnstr_get(x_383, 1);
lean::inc(x_388);
lean::dec(x_383);
x_391 = lean::cnstr_get(x_384, 0);
if (lean::is_exclusive(x_384)) {
 x_393 = x_384;
} else {
 lean::inc(x_391);
 lean::dec(x_384);
 x_393 = lean::box(0);
}
if (lean::is_scalar(x_393)) {
 x_394 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_394 = x_393;
}
lean::cnstr_set(x_394, 0, x_391);
x_395 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_395, 0, x_394);
lean::cnstr_set(x_395, 1, x_388);
x_3 = x_395;
goto lbl_4;
}
else
{
obj* x_397; obj* x_400; obj* x_402; obj* x_403; 
lean::dec(x_384);
x_397 = lean::cnstr_get(x_383, 1);
lean::inc(x_397);
lean::dec(x_383);
x_400 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_402 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_400, x_1, x_397);
x_403 = lean::cnstr_get(x_402, 0);
lean::inc(x_403);
if (lean::obj_tag(x_403) == 0)
{
obj* x_407; obj* x_410; obj* x_412; obj* x_413; obj* x_414; 
lean::dec(x_373);
lean::dec(x_376);
x_407 = lean::cnstr_get(x_402, 1);
lean::inc(x_407);
lean::dec(x_402);
x_410 = lean::cnstr_get(x_403, 0);
if (lean::is_exclusive(x_403)) {
 x_412 = x_403;
} else {
 lean::inc(x_410);
 lean::dec(x_403);
 x_412 = lean::box(0);
}
if (lean::is_scalar(x_412)) {
 x_413 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_413 = x_412;
}
lean::cnstr_set(x_413, 0, x_410);
x_414 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_414, 0, x_413);
lean::cnstr_set(x_414, 1, x_407);
x_3 = x_414;
goto lbl_4;
}
else
{
obj* x_416; obj* x_420; obj* x_421; 
lean::dec(x_403);
x_416 = lean::cnstr_get(x_402, 1);
lean::inc(x_416);
lean::dec(x_402);
lean::inc(x_1);
x_420 = l_lean_ir_cpp_emit__var(x_373, x_1, x_416);
x_421 = lean::cnstr_get(x_420, 0);
lean::inc(x_421);
if (lean::obj_tag(x_421) == 0)
{
obj* x_423; obj* x_426; obj* x_428; obj* x_429; 
x_423 = lean::cnstr_get(x_420, 1);
lean::inc(x_423);
lean::dec(x_420);
x_426 = lean::cnstr_get(x_421, 0);
if (lean::is_exclusive(x_421)) {
 x_428 = x_421;
} else {
 lean::inc(x_426);
 lean::dec(x_421);
 x_428 = lean::box(0);
}
if (lean::is_scalar(x_428)) {
 x_429 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_429 = x_428;
}
lean::cnstr_set(x_429, 0, x_426);
x_378 = x_429;
x_379 = x_423;
goto lbl_380;
}
else
{
obj* x_431; obj* x_434; obj* x_436; obj* x_437; 
lean::dec(x_421);
x_431 = lean::cnstr_get(x_420, 1);
lean::inc(x_431);
lean::dec(x_420);
x_434 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_436 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_434, x_1, x_431);
x_437 = lean::cnstr_get(x_436, 0);
lean::inc(x_437);
if (lean::obj_tag(x_437) == 0)
{
obj* x_439; obj* x_442; obj* x_444; obj* x_445; 
x_439 = lean::cnstr_get(x_436, 1);
lean::inc(x_439);
lean::dec(x_436);
x_442 = lean::cnstr_get(x_437, 0);
if (lean::is_exclusive(x_437)) {
 x_444 = x_437;
} else {
 lean::inc(x_442);
 lean::dec(x_437);
 x_444 = lean::box(0);
}
if (lean::is_scalar(x_444)) {
 x_445 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_445 = x_444;
}
lean::cnstr_set(x_445, 0, x_442);
x_378 = x_445;
x_379 = x_439;
goto lbl_380;
}
else
{
obj* x_447; obj* x_451; obj* x_452; obj* x_454; 
lean::dec(x_437);
x_447 = lean::cnstr_get(x_436, 1);
lean::inc(x_447);
lean::dec(x_436);
lean::inc(x_1);
x_451 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_375, x_1, x_447);
x_452 = lean::cnstr_get(x_451, 0);
lean::inc(x_452);
x_454 = lean::cnstr_get(x_451, 1);
lean::inc(x_454);
lean::dec(x_451);
x_378 = x_452;
x_379 = x_454;
goto lbl_380;
}
}
}
}
lbl_380:
{
if (lean::obj_tag(x_378) == 0)
{
obj* x_458; obj* x_460; obj* x_461; obj* x_462; 
lean::dec(x_376);
x_458 = lean::cnstr_get(x_378, 0);
if (lean::is_exclusive(x_378)) {
 x_460 = x_378;
} else {
 lean::inc(x_458);
 lean::dec(x_378);
 x_460 = lean::box(0);
}
if (lean::is_scalar(x_460)) {
 x_461 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_461 = x_460;
}
lean::cnstr_set(x_461, 0, x_458);
x_462 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_462, 0, x_461);
lean::cnstr_set(x_462, 1, x_379);
x_3 = x_462;
goto lbl_4;
}
else
{
obj* x_464; obj* x_466; obj* x_467; 
lean::dec(x_378);
x_464 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_466 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_464, x_1, x_379);
x_467 = lean::cnstr_get(x_466, 0);
lean::inc(x_467);
if (lean::obj_tag(x_467) == 0)
{
obj* x_470; obj* x_473; obj* x_475; obj* x_476; obj* x_477; 
lean::dec(x_376);
x_470 = lean::cnstr_get(x_466, 1);
lean::inc(x_470);
lean::dec(x_466);
x_473 = lean::cnstr_get(x_467, 0);
if (lean::is_exclusive(x_467)) {
 x_475 = x_467;
} else {
 lean::inc(x_473);
 lean::dec(x_467);
 x_475 = lean::box(0);
}
if (lean::is_scalar(x_475)) {
 x_476 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_476 = x_475;
}
lean::cnstr_set(x_476, 0, x_473);
x_477 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_477, 0, x_476);
lean::cnstr_set(x_477, 1, x_470);
x_3 = x_477;
goto lbl_4;
}
else
{
obj* x_479; obj* x_483; obj* x_484; 
lean::dec(x_467);
x_479 = lean::cnstr_get(x_466, 1);
lean::inc(x_479);
lean::dec(x_466);
lean::inc(x_1);
x_483 = l_lean_ir_cpp_emit__var(x_376, x_1, x_479);
x_484 = lean::cnstr_get(x_483, 0);
lean::inc(x_484);
if (lean::obj_tag(x_484) == 0)
{
obj* x_486; obj* x_489; obj* x_491; obj* x_492; obj* x_493; 
x_486 = lean::cnstr_get(x_483, 1);
lean::inc(x_486);
lean::dec(x_483);
x_489 = lean::cnstr_get(x_484, 0);
if (lean::is_exclusive(x_484)) {
 x_491 = x_484;
} else {
 lean::inc(x_489);
 lean::dec(x_484);
 x_491 = lean::box(0);
}
if (lean::is_scalar(x_491)) {
 x_492 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_492 = x_491;
}
lean::cnstr_set(x_492, 0, x_489);
x_493 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_493, 0, x_492);
lean::cnstr_set(x_493, 1, x_486);
x_3 = x_493;
goto lbl_4;
}
else
{
obj* x_494; obj* x_497; obj* x_500; obj* x_502; obj* x_503; 
x_494 = lean::cnstr_get(x_483, 1);
lean::inc(x_494);
lean::dec(x_483);
x_497 = lean::cnstr_get(x_484, 0);
lean::inc(x_497);
lean::dec(x_484);
x_500 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_502 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_500, x_1, x_494);
x_503 = lean::cnstr_get(x_502, 0);
lean::inc(x_503);
if (lean::obj_tag(x_503) == 0)
{
obj* x_506; obj* x_509; obj* x_511; obj* x_512; obj* x_513; 
lean::dec(x_497);
x_506 = lean::cnstr_get(x_502, 1);
lean::inc(x_506);
lean::dec(x_502);
x_509 = lean::cnstr_get(x_503, 0);
if (lean::is_exclusive(x_503)) {
 x_511 = x_503;
} else {
 lean::inc(x_509);
 lean::dec(x_503);
 x_511 = lean::box(0);
}
if (lean::is_scalar(x_511)) {
 x_512 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_512 = x_511;
}
lean::cnstr_set(x_512, 0, x_509);
x_513 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_513, 0, x_512);
lean::cnstr_set(x_513, 1, x_506);
x_3 = x_513;
goto lbl_4;
}
else
{
obj* x_514; obj* x_515; obj* x_518; obj* x_519; 
if (lean::is_exclusive(x_503)) {
 lean::cnstr_release(x_503, 0);
 x_514 = x_503;
} else {
 lean::dec(x_503);
 x_514 = lean::box(0);
}
x_515 = lean::cnstr_get(x_502, 1);
lean::inc(x_515);
lean::dec(x_502);
if (lean::is_scalar(x_514)) {
 x_518 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_518 = x_514;
}
lean::cnstr_set(x_518, 0, x_497);
x_519 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_519, 0, x_518);
lean::cnstr_set(x_519, 1, x_515);
x_3 = x_519;
goto lbl_4;
}
}
}
}
}
}
case 8:
{
obj* x_520; obj* x_522; uint16 x_524; obj* x_525; obj* x_526; obj* x_529; obj* x_530; 
x_520 = lean::cnstr_get(x_0, 0);
lean::inc(x_520);
x_522 = lean::cnstr_get(x_0, 1);
lean::inc(x_522);
x_524 = lean::cnstr_get_scalar<uint16>(x_0, sizeof(void*)*2);
lean::inc(x_1);
x_529 = l_lean_ir_cpp_emit__var(x_520, x_1, x_2);
x_530 = lean::cnstr_get(x_529, 0);
lean::inc(x_530);
if (lean::obj_tag(x_530) == 0)
{
obj* x_532; obj* x_535; obj* x_537; obj* x_538; 
x_532 = lean::cnstr_get(x_529, 1);
lean::inc(x_532);
lean::dec(x_529);
x_535 = lean::cnstr_get(x_530, 0);
if (lean::is_exclusive(x_530)) {
 x_537 = x_530;
} else {
 lean::inc(x_535);
 lean::dec(x_530);
 x_537 = lean::box(0);
}
if (lean::is_scalar(x_537)) {
 x_538 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_538 = x_537;
}
lean::cnstr_set(x_538, 0, x_535);
x_525 = x_538;
x_526 = x_532;
goto lbl_527;
}
else
{
obj* x_540; obj* x_543; obj* x_545; obj* x_546; obj* x_548; 
lean::dec(x_530);
x_540 = lean::cnstr_get(x_529, 1);
lean::inc(x_540);
lean::dec(x_529);
x_543 = l_lean_ir_cpp_emit__instr___closed__3;
lean::inc(x_1);
x_545 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_543, x_1, x_540);
x_546 = lean::cnstr_get(x_545, 0);
lean::inc(x_546);
x_548 = lean::cnstr_get(x_545, 1);
lean::inc(x_548);
lean::dec(x_545);
x_525 = x_546;
x_526 = x_548;
goto lbl_527;
}
lbl_527:
{
if (lean::obj_tag(x_525) == 0)
{
obj* x_552; obj* x_554; obj* x_555; obj* x_556; 
lean::dec(x_522);
x_552 = lean::cnstr_get(x_525, 0);
if (lean::is_exclusive(x_525)) {
 x_554 = x_525;
} else {
 lean::inc(x_552);
 lean::dec(x_525);
 x_554 = lean::box(0);
}
if (lean::is_scalar(x_554)) {
 x_555 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_555 = x_554;
}
lean::cnstr_set(x_555, 0, x_552);
x_556 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_556, 0, x_555);
lean::cnstr_set(x_556, 1, x_526);
x_3 = x_556;
goto lbl_4;
}
else
{
obj* x_558; obj* x_560; obj* x_561; 
lean::dec(x_525);
x_558 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_560 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_558, x_1, x_526);
x_561 = lean::cnstr_get(x_560, 0);
lean::inc(x_561);
if (lean::obj_tag(x_561) == 0)
{
obj* x_564; obj* x_567; obj* x_569; obj* x_570; obj* x_571; 
lean::dec(x_522);
x_564 = lean::cnstr_get(x_560, 1);
lean::inc(x_564);
lean::dec(x_560);
x_567 = lean::cnstr_get(x_561, 0);
if (lean::is_exclusive(x_561)) {
 x_569 = x_561;
} else {
 lean::inc(x_567);
 lean::dec(x_561);
 x_569 = lean::box(0);
}
if (lean::is_scalar(x_569)) {
 x_570 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_570 = x_569;
}
lean::cnstr_set(x_570, 0, x_567);
x_571 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_571, 0, x_570);
lean::cnstr_set(x_571, 1, x_564);
x_3 = x_571;
goto lbl_4;
}
else
{
obj* x_573; obj* x_577; obj* x_578; 
lean::dec(x_561);
x_573 = lean::cnstr_get(x_560, 1);
lean::inc(x_573);
lean::dec(x_560);
lean::inc(x_1);
x_577 = l_lean_ir_cpp_emit__var(x_522, x_1, x_573);
x_578 = lean::cnstr_get(x_577, 0);
lean::inc(x_578);
if (lean::obj_tag(x_578) == 0)
{
obj* x_580; obj* x_583; obj* x_585; obj* x_586; obj* x_587; 
x_580 = lean::cnstr_get(x_577, 1);
lean::inc(x_580);
lean::dec(x_577);
x_583 = lean::cnstr_get(x_578, 0);
if (lean::is_exclusive(x_578)) {
 x_585 = x_578;
} else {
 lean::inc(x_583);
 lean::dec(x_578);
 x_585 = lean::box(0);
}
if (lean::is_scalar(x_585)) {
 x_586 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_586 = x_585;
}
lean::cnstr_set(x_586, 0, x_583);
x_587 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_587, 0, x_586);
lean::cnstr_set(x_587, 1, x_580);
x_3 = x_587;
goto lbl_4;
}
else
{
obj* x_589; obj* x_592; obj* x_594; obj* x_595; 
lean::dec(x_578);
x_589 = lean::cnstr_get(x_577, 1);
lean::inc(x_589);
lean::dec(x_577);
x_592 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_594 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_592, x_1, x_589);
x_595 = lean::cnstr_get(x_594, 0);
lean::inc(x_595);
if (lean::obj_tag(x_595) == 0)
{
obj* x_597; obj* x_600; obj* x_602; obj* x_603; obj* x_604; 
x_597 = lean::cnstr_get(x_594, 1);
lean::inc(x_597);
lean::dec(x_594);
x_600 = lean::cnstr_get(x_595, 0);
if (lean::is_exclusive(x_595)) {
 x_602 = x_595;
} else {
 lean::inc(x_600);
 lean::dec(x_595);
 x_602 = lean::box(0);
}
if (lean::is_scalar(x_602)) {
 x_603 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_603 = x_602;
}
lean::cnstr_set(x_603, 0, x_600);
x_604 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_604, 0, x_603);
lean::cnstr_set(x_604, 1, x_597);
x_3 = x_604;
goto lbl_4;
}
else
{
obj* x_606; obj* x_610; obj* x_611; 
lean::dec(x_595);
x_606 = lean::cnstr_get(x_594, 1);
lean::inc(x_606);
lean::dec(x_594);
lean::inc(x_1);
x_610 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__3(x_524, x_1, x_606);
x_611 = lean::cnstr_get(x_610, 0);
lean::inc(x_611);
if (lean::obj_tag(x_611) == 0)
{
obj* x_613; obj* x_616; obj* x_618; obj* x_619; obj* x_620; 
x_613 = lean::cnstr_get(x_610, 1);
lean::inc(x_613);
lean::dec(x_610);
x_616 = lean::cnstr_get(x_611, 0);
if (lean::is_exclusive(x_611)) {
 x_618 = x_611;
} else {
 lean::inc(x_616);
 lean::dec(x_611);
 x_618 = lean::box(0);
}
if (lean::is_scalar(x_618)) {
 x_619 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_619 = x_618;
}
lean::cnstr_set(x_619, 0, x_616);
x_620 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_620, 0, x_619);
lean::cnstr_set(x_620, 1, x_613);
x_3 = x_620;
goto lbl_4;
}
else
{
obj* x_621; obj* x_624; obj* x_627; obj* x_629; obj* x_630; 
x_621 = lean::cnstr_get(x_610, 1);
lean::inc(x_621);
lean::dec(x_610);
x_624 = lean::cnstr_get(x_611, 0);
lean::inc(x_624);
lean::dec(x_611);
x_627 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_629 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_627, x_1, x_621);
x_630 = lean::cnstr_get(x_629, 0);
lean::inc(x_630);
if (lean::obj_tag(x_630) == 0)
{
obj* x_633; obj* x_636; obj* x_638; obj* x_639; obj* x_640; 
lean::dec(x_624);
x_633 = lean::cnstr_get(x_629, 1);
lean::inc(x_633);
lean::dec(x_629);
x_636 = lean::cnstr_get(x_630, 0);
if (lean::is_exclusive(x_630)) {
 x_638 = x_630;
} else {
 lean::inc(x_636);
 lean::dec(x_630);
 x_638 = lean::box(0);
}
if (lean::is_scalar(x_638)) {
 x_639 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_639 = x_638;
}
lean::cnstr_set(x_639, 0, x_636);
x_640 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_640, 0, x_639);
lean::cnstr_set(x_640, 1, x_633);
x_3 = x_640;
goto lbl_4;
}
else
{
obj* x_641; obj* x_642; obj* x_645; obj* x_646; 
if (lean::is_exclusive(x_630)) {
 lean::cnstr_release(x_630, 0);
 x_641 = x_630;
} else {
 lean::dec(x_630);
 x_641 = lean::box(0);
}
x_642 = lean::cnstr_get(x_629, 1);
lean::inc(x_642);
lean::dec(x_629);
if (lean::is_scalar(x_641)) {
 x_645 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_645 = x_641;
}
lean::cnstr_set(x_645, 0, x_624);
x_646 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_646, 0, x_645);
lean::cnstr_set(x_646, 1, x_642);
x_3 = x_646;
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
obj* x_647; usize x_649; obj* x_650; obj* x_652; obj* x_653; obj* x_655; obj* x_657; obj* x_658; 
x_647 = lean::cnstr_get(x_0, 0);
lean::inc(x_647);
x_649 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
x_650 = lean::cnstr_get(x_0, 1);
lean::inc(x_650);
x_655 = l_lean_ir_cpp_emit__instr___closed__4;
lean::inc(x_1);
x_657 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_655, x_1, x_2);
x_658 = lean::cnstr_get(x_657, 0);
lean::inc(x_658);
if (lean::obj_tag(x_658) == 0)
{
obj* x_662; obj* x_665; obj* x_667; obj* x_668; obj* x_669; 
lean::dec(x_650);
lean::dec(x_647);
x_662 = lean::cnstr_get(x_657, 1);
lean::inc(x_662);
lean::dec(x_657);
x_665 = lean::cnstr_get(x_658, 0);
if (lean::is_exclusive(x_658)) {
 x_667 = x_658;
} else {
 lean::inc(x_665);
 lean::dec(x_658);
 x_667 = lean::box(0);
}
if (lean::is_scalar(x_667)) {
 x_668 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_668 = x_667;
}
lean::cnstr_set(x_668, 0, x_665);
x_669 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_669, 0, x_668);
lean::cnstr_set(x_669, 1, x_662);
x_3 = x_669;
goto lbl_4;
}
else
{
obj* x_671; obj* x_674; obj* x_676; obj* x_677; 
lean::dec(x_658);
x_671 = lean::cnstr_get(x_657, 1);
lean::inc(x_671);
lean::dec(x_657);
x_674 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_676 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_674, x_1, x_671);
x_677 = lean::cnstr_get(x_676, 0);
lean::inc(x_677);
if (lean::obj_tag(x_677) == 0)
{
obj* x_681; obj* x_684; obj* x_686; obj* x_687; obj* x_688; 
lean::dec(x_650);
lean::dec(x_647);
x_681 = lean::cnstr_get(x_676, 1);
lean::inc(x_681);
lean::dec(x_676);
x_684 = lean::cnstr_get(x_677, 0);
if (lean::is_exclusive(x_677)) {
 x_686 = x_677;
} else {
 lean::inc(x_684);
 lean::dec(x_677);
 x_686 = lean::box(0);
}
if (lean::is_scalar(x_686)) {
 x_687 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_687 = x_686;
}
lean::cnstr_set(x_687, 0, x_684);
x_688 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_688, 0, x_687);
lean::cnstr_set(x_688, 1, x_681);
x_3 = x_688;
goto lbl_4;
}
else
{
obj* x_690; obj* x_694; obj* x_695; 
lean::dec(x_677);
x_690 = lean::cnstr_get(x_676, 1);
lean::inc(x_690);
lean::dec(x_676);
lean::inc(x_1);
x_694 = l_lean_ir_cpp_emit__var(x_647, x_1, x_690);
x_695 = lean::cnstr_get(x_694, 0);
lean::inc(x_695);
if (lean::obj_tag(x_695) == 0)
{
obj* x_697; obj* x_700; obj* x_702; obj* x_703; 
x_697 = lean::cnstr_get(x_694, 1);
lean::inc(x_697);
lean::dec(x_694);
x_700 = lean::cnstr_get(x_695, 0);
if (lean::is_exclusive(x_695)) {
 x_702 = x_695;
} else {
 lean::inc(x_700);
 lean::dec(x_695);
 x_702 = lean::box(0);
}
if (lean::is_scalar(x_702)) {
 x_703 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_703 = x_702;
}
lean::cnstr_set(x_703, 0, x_700);
x_652 = x_703;
x_653 = x_697;
goto lbl_654;
}
else
{
obj* x_705; obj* x_708; obj* x_710; obj* x_711; 
lean::dec(x_695);
x_705 = lean::cnstr_get(x_694, 1);
lean::inc(x_705);
lean::dec(x_694);
x_708 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_710 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_708, x_1, x_705);
x_711 = lean::cnstr_get(x_710, 0);
lean::inc(x_711);
if (lean::obj_tag(x_711) == 0)
{
obj* x_713; obj* x_716; obj* x_718; obj* x_719; 
x_713 = lean::cnstr_get(x_710, 1);
lean::inc(x_713);
lean::dec(x_710);
x_716 = lean::cnstr_get(x_711, 0);
if (lean::is_exclusive(x_711)) {
 x_718 = x_711;
} else {
 lean::inc(x_716);
 lean::dec(x_711);
 x_718 = lean::box(0);
}
if (lean::is_scalar(x_718)) {
 x_719 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_719 = x_718;
}
lean::cnstr_set(x_719, 0, x_716);
x_652 = x_719;
x_653 = x_713;
goto lbl_654;
}
else
{
obj* x_721; obj* x_725; obj* x_726; obj* x_728; 
lean::dec(x_711);
x_721 = lean::cnstr_get(x_710, 1);
lean::inc(x_721);
lean::dec(x_710);
lean::inc(x_1);
x_725 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(x_649, x_1, x_721);
x_726 = lean::cnstr_get(x_725, 0);
lean::inc(x_726);
x_728 = lean::cnstr_get(x_725, 1);
lean::inc(x_728);
lean::dec(x_725);
x_652 = x_726;
x_653 = x_728;
goto lbl_654;
}
}
}
}
lbl_654:
{
if (lean::obj_tag(x_652) == 0)
{
obj* x_732; obj* x_734; obj* x_735; obj* x_736; 
lean::dec(x_650);
x_732 = lean::cnstr_get(x_652, 0);
if (lean::is_exclusive(x_652)) {
 x_734 = x_652;
} else {
 lean::inc(x_732);
 lean::dec(x_652);
 x_734 = lean::box(0);
}
if (lean::is_scalar(x_734)) {
 x_735 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_735 = x_734;
}
lean::cnstr_set(x_735, 0, x_732);
x_736 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_736, 0, x_735);
lean::cnstr_set(x_736, 1, x_653);
x_3 = x_736;
goto lbl_4;
}
else
{
obj* x_738; obj* x_740; obj* x_741; 
lean::dec(x_652);
x_738 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_740 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_738, x_1, x_653);
x_741 = lean::cnstr_get(x_740, 0);
lean::inc(x_741);
if (lean::obj_tag(x_741) == 0)
{
obj* x_744; obj* x_747; obj* x_749; obj* x_750; obj* x_751; 
lean::dec(x_650);
x_744 = lean::cnstr_get(x_740, 1);
lean::inc(x_744);
lean::dec(x_740);
x_747 = lean::cnstr_get(x_741, 0);
if (lean::is_exclusive(x_741)) {
 x_749 = x_741;
} else {
 lean::inc(x_747);
 lean::dec(x_741);
 x_749 = lean::box(0);
}
if (lean::is_scalar(x_749)) {
 x_750 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_750 = x_749;
}
lean::cnstr_set(x_750, 0, x_747);
x_751 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_751, 0, x_750);
lean::cnstr_set(x_751, 1, x_744);
x_3 = x_751;
goto lbl_4;
}
else
{
obj* x_753; obj* x_757; obj* x_758; 
lean::dec(x_741);
x_753 = lean::cnstr_get(x_740, 1);
lean::inc(x_753);
lean::dec(x_740);
lean::inc(x_1);
x_757 = l_lean_ir_cpp_emit__var(x_650, x_1, x_753);
x_758 = lean::cnstr_get(x_757, 0);
lean::inc(x_758);
if (lean::obj_tag(x_758) == 0)
{
obj* x_760; obj* x_763; obj* x_765; obj* x_766; obj* x_767; 
x_760 = lean::cnstr_get(x_757, 1);
lean::inc(x_760);
lean::dec(x_757);
x_763 = lean::cnstr_get(x_758, 0);
if (lean::is_exclusive(x_758)) {
 x_765 = x_758;
} else {
 lean::inc(x_763);
 lean::dec(x_758);
 x_765 = lean::box(0);
}
if (lean::is_scalar(x_765)) {
 x_766 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_766 = x_765;
}
lean::cnstr_set(x_766, 0, x_763);
x_767 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_767, 0, x_766);
lean::cnstr_set(x_767, 1, x_760);
x_3 = x_767;
goto lbl_4;
}
else
{
obj* x_768; obj* x_771; obj* x_774; obj* x_776; obj* x_777; 
x_768 = lean::cnstr_get(x_757, 1);
lean::inc(x_768);
lean::dec(x_757);
x_771 = lean::cnstr_get(x_758, 0);
lean::inc(x_771);
lean::dec(x_758);
x_774 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_776 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_774, x_1, x_768);
x_777 = lean::cnstr_get(x_776, 0);
lean::inc(x_777);
if (lean::obj_tag(x_777) == 0)
{
obj* x_780; obj* x_783; obj* x_785; obj* x_786; obj* x_787; 
lean::dec(x_771);
x_780 = lean::cnstr_get(x_776, 1);
lean::inc(x_780);
lean::dec(x_776);
x_783 = lean::cnstr_get(x_777, 0);
if (lean::is_exclusive(x_777)) {
 x_785 = x_777;
} else {
 lean::inc(x_783);
 lean::dec(x_777);
 x_785 = lean::box(0);
}
if (lean::is_scalar(x_785)) {
 x_786 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_786 = x_785;
}
lean::cnstr_set(x_786, 0, x_783);
x_787 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_787, 0, x_786);
lean::cnstr_set(x_787, 1, x_780);
x_3 = x_787;
goto lbl_4;
}
else
{
obj* x_788; obj* x_789; obj* x_792; obj* x_793; 
if (lean::is_exclusive(x_777)) {
 lean::cnstr_release(x_777, 0);
 x_788 = x_777;
} else {
 lean::dec(x_777);
 x_788 = lean::box(0);
}
x_789 = lean::cnstr_get(x_776, 1);
lean::inc(x_789);
lean::dec(x_776);
if (lean::is_scalar(x_788)) {
 x_792 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_792 = x_788;
}
lean::cnstr_set(x_792, 0, x_771);
x_793 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_793, 0, x_792);
lean::cnstr_set(x_793, 1, x_789);
x_3 = x_793;
goto lbl_4;
}
}
}
}
}
}
case 10:
{
obj* x_794; uint8 x_796; obj* x_797; usize x_799; obj* x_800; obj* x_801; obj* x_804; obj* x_805; 
x_794 = lean::cnstr_get(x_0, 0);
lean::inc(x_794);
x_796 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_797 = lean::cnstr_get(x_0, 1);
lean::inc(x_797);
x_799 = lean::cnstr_get_scalar<usize>(x_0, sizeof(void*)*2);
lean::inc(x_1);
x_804 = l_lean_ir_cpp_emit__var(x_794, x_1, x_2);
x_805 = lean::cnstr_get(x_804, 0);
lean::inc(x_805);
if (lean::obj_tag(x_805) == 0)
{
obj* x_807; obj* x_810; obj* x_812; obj* x_813; 
x_807 = lean::cnstr_get(x_804, 1);
lean::inc(x_807);
lean::dec(x_804);
x_810 = lean::cnstr_get(x_805, 0);
if (lean::is_exclusive(x_805)) {
 x_812 = x_805;
} else {
 lean::inc(x_810);
 lean::dec(x_805);
 x_812 = lean::box(0);
}
if (lean::is_scalar(x_812)) {
 x_813 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_813 = x_812;
}
lean::cnstr_set(x_813, 0, x_810);
x_800 = x_813;
x_801 = x_807;
goto lbl_802;
}
else
{
obj* x_815; obj* x_818; obj* x_820; obj* x_821; 
lean::dec(x_805);
x_815 = lean::cnstr_get(x_804, 1);
lean::inc(x_815);
lean::dec(x_804);
x_818 = l_lean_ir_cpp_emit__instr___closed__5;
lean::inc(x_1);
x_820 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_818, x_1, x_815);
x_821 = lean::cnstr_get(x_820, 0);
lean::inc(x_821);
if (lean::obj_tag(x_821) == 0)
{
obj* x_823; obj* x_826; obj* x_828; obj* x_829; 
x_823 = lean::cnstr_get(x_820, 1);
lean::inc(x_823);
lean::dec(x_820);
x_826 = lean::cnstr_get(x_821, 0);
if (lean::is_exclusive(x_821)) {
 x_828 = x_821;
} else {
 lean::inc(x_826);
 lean::dec(x_821);
 x_828 = lean::box(0);
}
if (lean::is_scalar(x_828)) {
 x_829 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_829 = x_828;
}
lean::cnstr_set(x_829, 0, x_826);
x_800 = x_829;
x_801 = x_823;
goto lbl_802;
}
else
{
obj* x_831; obj* x_835; obj* x_836; obj* x_838; 
lean::dec(x_821);
x_831 = lean::cnstr_get(x_820, 1);
lean::inc(x_831);
lean::dec(x_820);
lean::inc(x_1);
x_835 = l_lean_ir_cpp_emit__template__param(x_796, x_1, x_831);
x_836 = lean::cnstr_get(x_835, 0);
lean::inc(x_836);
x_838 = lean::cnstr_get(x_835, 1);
lean::inc(x_838);
lean::dec(x_835);
x_800 = x_836;
x_801 = x_838;
goto lbl_802;
}
}
lbl_802:
{
if (lean::obj_tag(x_800) == 0)
{
obj* x_842; obj* x_844; obj* x_845; obj* x_846; 
lean::dec(x_797);
x_842 = lean::cnstr_get(x_800, 0);
if (lean::is_exclusive(x_800)) {
 x_844 = x_800;
} else {
 lean::inc(x_842);
 lean::dec(x_800);
 x_844 = lean::box(0);
}
if (lean::is_scalar(x_844)) {
 x_845 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_845 = x_844;
}
lean::cnstr_set(x_845, 0, x_842);
x_846 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_846, 0, x_845);
lean::cnstr_set(x_846, 1, x_801);
x_3 = x_846;
goto lbl_4;
}
else
{
obj* x_848; obj* x_850; obj* x_851; 
lean::dec(x_800);
x_848 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_850 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_848, x_1, x_801);
x_851 = lean::cnstr_get(x_850, 0);
lean::inc(x_851);
if (lean::obj_tag(x_851) == 0)
{
obj* x_854; obj* x_857; obj* x_859; obj* x_860; obj* x_861; 
lean::dec(x_797);
x_854 = lean::cnstr_get(x_850, 1);
lean::inc(x_854);
lean::dec(x_850);
x_857 = lean::cnstr_get(x_851, 0);
if (lean::is_exclusive(x_851)) {
 x_859 = x_851;
} else {
 lean::inc(x_857);
 lean::dec(x_851);
 x_859 = lean::box(0);
}
if (lean::is_scalar(x_859)) {
 x_860 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_860 = x_859;
}
lean::cnstr_set(x_860, 0, x_857);
x_861 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_861, 0, x_860);
lean::cnstr_set(x_861, 1, x_854);
x_3 = x_861;
goto lbl_4;
}
else
{
obj* x_863; obj* x_867; obj* x_868; 
lean::dec(x_851);
x_863 = lean::cnstr_get(x_850, 1);
lean::inc(x_863);
lean::dec(x_850);
lean::inc(x_1);
x_867 = l_lean_ir_cpp_emit__var(x_797, x_1, x_863);
x_868 = lean::cnstr_get(x_867, 0);
lean::inc(x_868);
if (lean::obj_tag(x_868) == 0)
{
obj* x_870; obj* x_873; obj* x_875; obj* x_876; obj* x_877; 
x_870 = lean::cnstr_get(x_867, 1);
lean::inc(x_870);
lean::dec(x_867);
x_873 = lean::cnstr_get(x_868, 0);
if (lean::is_exclusive(x_868)) {
 x_875 = x_868;
} else {
 lean::inc(x_873);
 lean::dec(x_868);
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
lean::cnstr_set(x_877, 1, x_870);
x_3 = x_877;
goto lbl_4;
}
else
{
obj* x_879; obj* x_882; obj* x_884; obj* x_885; 
lean::dec(x_868);
x_879 = lean::cnstr_get(x_867, 1);
lean::inc(x_879);
lean::dec(x_867);
x_882 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_884 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_882, x_1, x_879);
x_885 = lean::cnstr_get(x_884, 0);
lean::inc(x_885);
if (lean::obj_tag(x_885) == 0)
{
obj* x_887; obj* x_890; obj* x_892; obj* x_893; obj* x_894; 
x_887 = lean::cnstr_get(x_884, 1);
lean::inc(x_887);
lean::dec(x_884);
x_890 = lean::cnstr_get(x_885, 0);
if (lean::is_exclusive(x_885)) {
 x_892 = x_885;
} else {
 lean::inc(x_890);
 lean::dec(x_885);
 x_892 = lean::box(0);
}
if (lean::is_scalar(x_892)) {
 x_893 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_893 = x_892;
}
lean::cnstr_set(x_893, 0, x_890);
x_894 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_894, 0, x_893);
lean::cnstr_set(x_894, 1, x_887);
x_3 = x_894;
goto lbl_4;
}
else
{
obj* x_896; obj* x_900; obj* x_901; 
lean::dec(x_885);
x_896 = lean::cnstr_get(x_884, 1);
lean::inc(x_896);
lean::dec(x_884);
lean::inc(x_1);
x_900 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__instr___spec__1(x_799, x_1, x_896);
x_901 = lean::cnstr_get(x_900, 0);
lean::inc(x_901);
if (lean::obj_tag(x_901) == 0)
{
obj* x_903; obj* x_906; obj* x_908; obj* x_909; obj* x_910; 
x_903 = lean::cnstr_get(x_900, 1);
lean::inc(x_903);
lean::dec(x_900);
x_906 = lean::cnstr_get(x_901, 0);
if (lean::is_exclusive(x_901)) {
 x_908 = x_901;
} else {
 lean::inc(x_906);
 lean::dec(x_901);
 x_908 = lean::box(0);
}
if (lean::is_scalar(x_908)) {
 x_909 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_909 = x_908;
}
lean::cnstr_set(x_909, 0, x_906);
x_910 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_910, 0, x_909);
lean::cnstr_set(x_910, 1, x_903);
x_3 = x_910;
goto lbl_4;
}
else
{
obj* x_911; obj* x_914; obj* x_917; obj* x_919; obj* x_920; 
x_911 = lean::cnstr_get(x_900, 1);
lean::inc(x_911);
lean::dec(x_900);
x_914 = lean::cnstr_get(x_901, 0);
lean::inc(x_914);
lean::dec(x_901);
x_917 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_919 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_917, x_1, x_911);
x_920 = lean::cnstr_get(x_919, 0);
lean::inc(x_920);
if (lean::obj_tag(x_920) == 0)
{
obj* x_923; obj* x_926; obj* x_928; obj* x_929; obj* x_930; 
lean::dec(x_914);
x_923 = lean::cnstr_get(x_919, 1);
lean::inc(x_923);
lean::dec(x_919);
x_926 = lean::cnstr_get(x_920, 0);
if (lean::is_exclusive(x_920)) {
 x_928 = x_920;
} else {
 lean::inc(x_926);
 lean::dec(x_920);
 x_928 = lean::box(0);
}
if (lean::is_scalar(x_928)) {
 x_929 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_929 = x_928;
}
lean::cnstr_set(x_929, 0, x_926);
x_930 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_930, 0, x_929);
lean::cnstr_set(x_930, 1, x_923);
x_3 = x_930;
goto lbl_4;
}
else
{
obj* x_931; obj* x_932; obj* x_935; obj* x_936; 
if (lean::is_exclusive(x_920)) {
 lean::cnstr_release(x_920, 0);
 x_931 = x_920;
} else {
 lean::dec(x_920);
 x_931 = lean::box(0);
}
x_932 = lean::cnstr_get(x_919, 1);
lean::inc(x_932);
lean::dec(x_919);
if (lean::is_scalar(x_931)) {
 x_935 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_935 = x_931;
}
lean::cnstr_set(x_935, 0, x_914);
x_936 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_936, 0, x_935);
lean::cnstr_set(x_936, 1, x_932);
x_3 = x_936;
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
obj* x_937; obj* x_939; obj* x_941; obj* x_944; 
x_937 = lean::cnstr_get(x_0, 0);
lean::inc(x_937);
x_939 = lean::cnstr_get(x_0, 1);
lean::inc(x_939);
x_941 = lean::cnstr_get(x_0, 2);
lean::inc(x_941);
lean::inc(x_1);
x_944 = l_lean_ir_cpp_emit__closure(x_937, x_939, x_941, x_1, x_2);
x_3 = x_944;
goto lbl_4;
}
case 12:
{
obj* x_945; obj* x_947; obj* x_950; 
x_945 = lean::cnstr_get(x_0, 0);
lean::inc(x_945);
x_947 = lean::cnstr_get(x_0, 1);
lean::inc(x_947);
lean::inc(x_1);
x_950 = l_lean_ir_cpp_emit__apply(x_945, x_947, x_1, x_2);
x_3 = x_950;
goto lbl_4;
}
case 13:
{
obj* x_951; obj* x_953; obj* x_955; obj* x_957; obj* x_958; obj* x_961; obj* x_962; 
x_951 = lean::cnstr_get(x_0, 0);
lean::inc(x_951);
x_953 = lean::cnstr_get(x_0, 1);
lean::inc(x_953);
x_955 = lean::cnstr_get(x_0, 2);
lean::inc(x_955);
lean::inc(x_1);
x_961 = l_lean_ir_cpp_emit__var(x_951, x_1, x_2);
x_962 = lean::cnstr_get(x_961, 0);
lean::inc(x_962);
if (lean::obj_tag(x_962) == 0)
{
obj* x_964; obj* x_967; obj* x_969; obj* x_970; 
x_964 = lean::cnstr_get(x_961, 1);
lean::inc(x_964);
lean::dec(x_961);
x_967 = lean::cnstr_get(x_962, 0);
if (lean::is_exclusive(x_962)) {
 x_969 = x_962;
} else {
 lean::inc(x_967);
 lean::dec(x_962);
 x_969 = lean::box(0);
}
if (lean::is_scalar(x_969)) {
 x_970 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_970 = x_969;
}
lean::cnstr_set(x_970, 0, x_967);
x_957 = x_970;
x_958 = x_964;
goto lbl_959;
}
else
{
obj* x_972; obj* x_975; obj* x_977; obj* x_978; obj* x_980; 
lean::dec(x_962);
x_972 = lean::cnstr_get(x_961, 1);
lean::inc(x_972);
lean::dec(x_961);
x_975 = l_lean_ir_cpp_emit__instr___closed__6;
lean::inc(x_1);
x_977 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_975, x_1, x_972);
x_978 = lean::cnstr_get(x_977, 0);
lean::inc(x_978);
x_980 = lean::cnstr_get(x_977, 1);
lean::inc(x_980);
lean::dec(x_977);
x_957 = x_978;
x_958 = x_980;
goto lbl_959;
}
lbl_959:
{
if (lean::obj_tag(x_957) == 0)
{
obj* x_985; obj* x_987; obj* x_988; obj* x_989; 
lean::dec(x_953);
lean::dec(x_955);
x_985 = lean::cnstr_get(x_957, 0);
if (lean::is_exclusive(x_957)) {
 x_987 = x_957;
} else {
 lean::inc(x_985);
 lean::dec(x_957);
 x_987 = lean::box(0);
}
if (lean::is_scalar(x_987)) {
 x_988 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_988 = x_987;
}
lean::cnstr_set(x_988, 0, x_985);
x_989 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_989, 0, x_988);
lean::cnstr_set(x_989, 1, x_958);
x_3 = x_989;
goto lbl_4;
}
else
{
obj* x_991; obj* x_993; obj* x_994; 
lean::dec(x_957);
x_991 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_993 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_991, x_1, x_958);
x_994 = lean::cnstr_get(x_993, 0);
lean::inc(x_994);
if (lean::obj_tag(x_994) == 0)
{
obj* x_998; obj* x_1001; obj* x_1003; obj* x_1004; obj* x_1005; 
lean::dec(x_953);
lean::dec(x_955);
x_998 = lean::cnstr_get(x_993, 1);
lean::inc(x_998);
lean::dec(x_993);
x_1001 = lean::cnstr_get(x_994, 0);
if (lean::is_exclusive(x_994)) {
 x_1003 = x_994;
} else {
 lean::inc(x_1001);
 lean::dec(x_994);
 x_1003 = lean::box(0);
}
if (lean::is_scalar(x_1003)) {
 x_1004 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1004 = x_1003;
}
lean::cnstr_set(x_1004, 0, x_1001);
x_1005 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1005, 0, x_1004);
lean::cnstr_set(x_1005, 1, x_998);
x_3 = x_1005;
goto lbl_4;
}
else
{
obj* x_1007; obj* x_1011; obj* x_1012; 
lean::dec(x_994);
x_1007 = lean::cnstr_get(x_993, 1);
lean::inc(x_1007);
lean::dec(x_993);
lean::inc(x_1);
x_1011 = l_lean_ir_cpp_emit__var(x_953, x_1, x_1007);
x_1012 = lean::cnstr_get(x_1011, 0);
lean::inc(x_1012);
if (lean::obj_tag(x_1012) == 0)
{
obj* x_1015; obj* x_1018; obj* x_1020; obj* x_1021; obj* x_1022; 
lean::dec(x_955);
x_1015 = lean::cnstr_get(x_1011, 1);
lean::inc(x_1015);
lean::dec(x_1011);
x_1018 = lean::cnstr_get(x_1012, 0);
if (lean::is_exclusive(x_1012)) {
 x_1020 = x_1012;
} else {
 lean::inc(x_1018);
 lean::dec(x_1012);
 x_1020 = lean::box(0);
}
if (lean::is_scalar(x_1020)) {
 x_1021 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1021 = x_1020;
}
lean::cnstr_set(x_1021, 0, x_1018);
x_1022 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1022, 0, x_1021);
lean::cnstr_set(x_1022, 1, x_1015);
x_3 = x_1022;
goto lbl_4;
}
else
{
obj* x_1024; obj* x_1027; obj* x_1029; obj* x_1030; 
lean::dec(x_1012);
x_1024 = lean::cnstr_get(x_1011, 1);
lean::inc(x_1024);
lean::dec(x_1011);
x_1027 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_1029 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1027, x_1, x_1024);
x_1030 = lean::cnstr_get(x_1029, 0);
lean::inc(x_1030);
if (lean::obj_tag(x_1030) == 0)
{
obj* x_1033; obj* x_1036; obj* x_1038; obj* x_1039; obj* x_1040; 
lean::dec(x_955);
x_1033 = lean::cnstr_get(x_1029, 1);
lean::inc(x_1033);
lean::dec(x_1029);
x_1036 = lean::cnstr_get(x_1030, 0);
if (lean::is_exclusive(x_1030)) {
 x_1038 = x_1030;
} else {
 lean::inc(x_1036);
 lean::dec(x_1030);
 x_1038 = lean::box(0);
}
if (lean::is_scalar(x_1038)) {
 x_1039 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1039 = x_1038;
}
lean::cnstr_set(x_1039, 0, x_1036);
x_1040 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1040, 0, x_1039);
lean::cnstr_set(x_1040, 1, x_1033);
x_3 = x_1040;
goto lbl_4;
}
else
{
obj* x_1042; obj* x_1046; obj* x_1047; 
lean::dec(x_1030);
x_1042 = lean::cnstr_get(x_1029, 1);
lean::inc(x_1042);
lean::dec(x_1029);
lean::inc(x_1);
x_1046 = l_lean_ir_cpp_emit__var(x_955, x_1, x_1042);
x_1047 = lean::cnstr_get(x_1046, 0);
lean::inc(x_1047);
if (lean::obj_tag(x_1047) == 0)
{
obj* x_1049; obj* x_1052; obj* x_1054; obj* x_1055; obj* x_1056; 
x_1049 = lean::cnstr_get(x_1046, 1);
lean::inc(x_1049);
lean::dec(x_1046);
x_1052 = lean::cnstr_get(x_1047, 0);
if (lean::is_exclusive(x_1047)) {
 x_1054 = x_1047;
} else {
 lean::inc(x_1052);
 lean::dec(x_1047);
 x_1054 = lean::box(0);
}
if (lean::is_scalar(x_1054)) {
 x_1055 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1055 = x_1054;
}
lean::cnstr_set(x_1055, 0, x_1052);
x_1056 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1056, 0, x_1055);
lean::cnstr_set(x_1056, 1, x_1049);
x_3 = x_1056;
goto lbl_4;
}
else
{
obj* x_1057; obj* x_1060; obj* x_1063; obj* x_1065; obj* x_1066; 
x_1057 = lean::cnstr_get(x_1046, 1);
lean::inc(x_1057);
lean::dec(x_1046);
x_1060 = lean::cnstr_get(x_1047, 0);
lean::inc(x_1060);
lean::dec(x_1047);
x_1063 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_1065 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1063, x_1, x_1057);
x_1066 = lean::cnstr_get(x_1065, 0);
lean::inc(x_1066);
if (lean::obj_tag(x_1066) == 0)
{
obj* x_1069; obj* x_1072; obj* x_1074; obj* x_1075; obj* x_1076; 
lean::dec(x_1060);
x_1069 = lean::cnstr_get(x_1065, 1);
lean::inc(x_1069);
lean::dec(x_1065);
x_1072 = lean::cnstr_get(x_1066, 0);
if (lean::is_exclusive(x_1066)) {
 x_1074 = x_1066;
} else {
 lean::inc(x_1072);
 lean::dec(x_1066);
 x_1074 = lean::box(0);
}
if (lean::is_scalar(x_1074)) {
 x_1075 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1075 = x_1074;
}
lean::cnstr_set(x_1075, 0, x_1072);
x_1076 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1076, 0, x_1075);
lean::cnstr_set(x_1076, 1, x_1069);
x_3 = x_1076;
goto lbl_4;
}
else
{
obj* x_1077; obj* x_1078; obj* x_1081; obj* x_1082; 
if (lean::is_exclusive(x_1066)) {
 lean::cnstr_release(x_1066, 0);
 x_1077 = x_1066;
} else {
 lean::dec(x_1066);
 x_1077 = lean::box(0);
}
x_1078 = lean::cnstr_get(x_1065, 1);
lean::inc(x_1078);
lean::dec(x_1065);
if (lean::is_scalar(x_1077)) {
 x_1081 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1081 = x_1077;
}
lean::cnstr_set(x_1081, 0, x_1060);
x_1082 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1082, 0, x_1081);
lean::cnstr_set(x_1082, 1, x_1078);
x_3 = x_1082;
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
obj* x_1083; uint8 x_1085; obj* x_1086; obj* x_1088; obj* x_1090; obj* x_1091; obj* x_1093; obj* x_1094; obj* x_1097; obj* x_1098; 
x_1083 = lean::cnstr_get(x_0, 0);
lean::inc(x_1083);
x_1085 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*3);
x_1086 = lean::cnstr_get(x_0, 1);
lean::inc(x_1086);
x_1088 = lean::cnstr_get(x_0, 2);
lean::inc(x_1088);
lean::inc(x_1);
x_1097 = l_lean_ir_cpp_emit__var(x_1083, x_1, x_2);
x_1098 = lean::cnstr_get(x_1097, 0);
lean::inc(x_1098);
if (lean::obj_tag(x_1098) == 0)
{
obj* x_1100; obj* x_1103; obj* x_1105; obj* x_1106; 
x_1100 = lean::cnstr_get(x_1097, 1);
lean::inc(x_1100);
lean::dec(x_1097);
x_1103 = lean::cnstr_get(x_1098, 0);
if (lean::is_exclusive(x_1098)) {
 x_1105 = x_1098;
} else {
 lean::inc(x_1103);
 lean::dec(x_1098);
 x_1105 = lean::box(0);
}
if (lean::is_scalar(x_1105)) {
 x_1106 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1106 = x_1105;
}
lean::cnstr_set(x_1106, 0, x_1103);
x_1093 = x_1106;
x_1094 = x_1100;
goto lbl_1095;
}
else
{
obj* x_1108; obj* x_1111; obj* x_1113; obj* x_1114; obj* x_1116; 
lean::dec(x_1098);
x_1108 = lean::cnstr_get(x_1097, 1);
lean::inc(x_1108);
lean::dec(x_1097);
x_1111 = l_lean_ir_cpp_emit__instr___closed__7;
lean::inc(x_1);
x_1113 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1111, x_1, x_1108);
x_1114 = lean::cnstr_get(x_1113, 0);
lean::inc(x_1114);
x_1116 = lean::cnstr_get(x_1113, 1);
lean::inc(x_1116);
lean::dec(x_1113);
x_1093 = x_1114;
x_1094 = x_1116;
goto lbl_1095;
}
lbl_1092:
{
if (lean::obj_tag(x_1090) == 0)
{
obj* x_1120; obj* x_1122; obj* x_1123; obj* x_1124; 
lean::dec(x_1088);
x_1120 = lean::cnstr_get(x_1090, 0);
if (lean::is_exclusive(x_1090)) {
 x_1122 = x_1090;
} else {
 lean::inc(x_1120);
 lean::dec(x_1090);
 x_1122 = lean::box(0);
}
if (lean::is_scalar(x_1122)) {
 x_1123 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1123 = x_1122;
}
lean::cnstr_set(x_1123, 0, x_1120);
x_1124 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1124, 0, x_1123);
lean::cnstr_set(x_1124, 1, x_1091);
x_3 = x_1124;
goto lbl_4;
}
else
{
obj* x_1126; obj* x_1128; obj* x_1129; 
lean::dec(x_1090);
x_1126 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_1128 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1126, x_1, x_1091);
x_1129 = lean::cnstr_get(x_1128, 0);
lean::inc(x_1129);
if (lean::obj_tag(x_1129) == 0)
{
obj* x_1132; obj* x_1135; obj* x_1137; obj* x_1138; obj* x_1139; 
lean::dec(x_1088);
x_1132 = lean::cnstr_get(x_1128, 1);
lean::inc(x_1132);
lean::dec(x_1128);
x_1135 = lean::cnstr_get(x_1129, 0);
if (lean::is_exclusive(x_1129)) {
 x_1137 = x_1129;
} else {
 lean::inc(x_1135);
 lean::dec(x_1129);
 x_1137 = lean::box(0);
}
if (lean::is_scalar(x_1137)) {
 x_1138 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1138 = x_1137;
}
lean::cnstr_set(x_1138, 0, x_1135);
x_1139 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1139, 0, x_1138);
lean::cnstr_set(x_1139, 1, x_1132);
x_3 = x_1139;
goto lbl_4;
}
else
{
obj* x_1141; obj* x_1145; obj* x_1146; 
lean::dec(x_1129);
x_1141 = lean::cnstr_get(x_1128, 1);
lean::inc(x_1141);
lean::dec(x_1128);
lean::inc(x_1);
x_1145 = l_lean_ir_cpp_emit__var(x_1088, x_1, x_1141);
x_1146 = lean::cnstr_get(x_1145, 0);
lean::inc(x_1146);
if (lean::obj_tag(x_1146) == 0)
{
obj* x_1148; obj* x_1151; obj* x_1153; obj* x_1154; obj* x_1155; 
x_1148 = lean::cnstr_get(x_1145, 1);
lean::inc(x_1148);
lean::dec(x_1145);
x_1151 = lean::cnstr_get(x_1146, 0);
if (lean::is_exclusive(x_1146)) {
 x_1153 = x_1146;
} else {
 lean::inc(x_1151);
 lean::dec(x_1146);
 x_1153 = lean::box(0);
}
if (lean::is_scalar(x_1153)) {
 x_1154 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1154 = x_1153;
}
lean::cnstr_set(x_1154, 0, x_1151);
x_1155 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1155, 0, x_1154);
lean::cnstr_set(x_1155, 1, x_1148);
x_3 = x_1155;
goto lbl_4;
}
else
{
obj* x_1156; obj* x_1159; obj* x_1162; obj* x_1164; obj* x_1165; 
x_1156 = lean::cnstr_get(x_1145, 1);
lean::inc(x_1156);
lean::dec(x_1145);
x_1159 = lean::cnstr_get(x_1146, 0);
lean::inc(x_1159);
lean::dec(x_1146);
x_1162 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_1164 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1162, x_1, x_1156);
x_1165 = lean::cnstr_get(x_1164, 0);
lean::inc(x_1165);
if (lean::obj_tag(x_1165) == 0)
{
obj* x_1168; obj* x_1171; obj* x_1173; obj* x_1174; obj* x_1175; 
lean::dec(x_1159);
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
x_1175 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1175, 0, x_1174);
lean::cnstr_set(x_1175, 1, x_1168);
x_3 = x_1175;
goto lbl_4;
}
else
{
obj* x_1176; obj* x_1177; obj* x_1180; obj* x_1181; 
if (lean::is_exclusive(x_1165)) {
 lean::cnstr_release(x_1165, 0);
 x_1176 = x_1165;
} else {
 lean::dec(x_1165);
 x_1176 = lean::box(0);
}
x_1177 = lean::cnstr_get(x_1164, 1);
lean::inc(x_1177);
lean::dec(x_1164);
if (lean::is_scalar(x_1176)) {
 x_1180 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1180 = x_1176;
}
lean::cnstr_set(x_1180, 0, x_1159);
x_1181 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1181, 0, x_1180);
lean::cnstr_set(x_1181, 1, x_1177);
x_3 = x_1181;
goto lbl_4;
}
}
}
}
}
lbl_1095:
{
if (lean::obj_tag(x_1093) == 0)
{
obj* x_1184; obj* x_1186; obj* x_1187; obj* x_1188; 
lean::dec(x_1088);
lean::dec(x_1086);
x_1184 = lean::cnstr_get(x_1093, 0);
if (lean::is_exclusive(x_1093)) {
 x_1186 = x_1093;
} else {
 lean::inc(x_1184);
 lean::dec(x_1093);
 x_1186 = lean::box(0);
}
if (lean::is_scalar(x_1186)) {
 x_1187 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1187 = x_1186;
}
lean::cnstr_set(x_1187, 0, x_1184);
x_1188 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1188, 0, x_1187);
lean::cnstr_set(x_1188, 1, x_1094);
x_3 = x_1188;
goto lbl_4;
}
else
{
obj* x_1190; obj* x_1192; obj* x_1193; 
lean::dec(x_1093);
x_1190 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_1192 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1190, x_1, x_1094);
x_1193 = lean::cnstr_get(x_1192, 0);
lean::inc(x_1193);
if (lean::obj_tag(x_1193) == 0)
{
obj* x_1197; obj* x_1200; obj* x_1202; obj* x_1203; obj* x_1204; 
lean::dec(x_1088);
lean::dec(x_1086);
x_1197 = lean::cnstr_get(x_1192, 1);
lean::inc(x_1197);
lean::dec(x_1192);
x_1200 = lean::cnstr_get(x_1193, 0);
if (lean::is_exclusive(x_1193)) {
 x_1202 = x_1193;
} else {
 lean::inc(x_1200);
 lean::dec(x_1193);
 x_1202 = lean::box(0);
}
if (lean::is_scalar(x_1202)) {
 x_1203 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1203 = x_1202;
}
lean::cnstr_set(x_1203, 0, x_1200);
x_1204 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1204, 0, x_1203);
lean::cnstr_set(x_1204, 1, x_1197);
x_3 = x_1204;
goto lbl_4;
}
else
{
obj* x_1206; obj* x_1210; obj* x_1211; 
lean::dec(x_1193);
x_1206 = lean::cnstr_get(x_1192, 1);
lean::inc(x_1206);
lean::dec(x_1192);
lean::inc(x_1);
x_1210 = l_lean_ir_cpp_emit__type__size(x_1085, x_1, x_1206);
x_1211 = lean::cnstr_get(x_1210, 0);
lean::inc(x_1211);
if (lean::obj_tag(x_1211) == 0)
{
obj* x_1214; obj* x_1217; obj* x_1219; obj* x_1220; 
lean::dec(x_1086);
x_1214 = lean::cnstr_get(x_1210, 1);
lean::inc(x_1214);
lean::dec(x_1210);
x_1217 = lean::cnstr_get(x_1211, 0);
if (lean::is_exclusive(x_1211)) {
 x_1219 = x_1211;
} else {
 lean::inc(x_1217);
 lean::dec(x_1211);
 x_1219 = lean::box(0);
}
if (lean::is_scalar(x_1219)) {
 x_1220 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1220 = x_1219;
}
lean::cnstr_set(x_1220, 0, x_1217);
x_1090 = x_1220;
x_1091 = x_1214;
goto lbl_1092;
}
else
{
obj* x_1222; obj* x_1225; obj* x_1227; obj* x_1228; 
lean::dec(x_1211);
x_1222 = lean::cnstr_get(x_1210, 1);
lean::inc(x_1222);
lean::dec(x_1210);
x_1225 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_1227 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1225, x_1, x_1222);
x_1228 = lean::cnstr_get(x_1227, 0);
lean::inc(x_1228);
if (lean::obj_tag(x_1228) == 0)
{
obj* x_1231; obj* x_1234; obj* x_1236; obj* x_1237; 
lean::dec(x_1086);
x_1231 = lean::cnstr_get(x_1227, 1);
lean::inc(x_1231);
lean::dec(x_1227);
x_1234 = lean::cnstr_get(x_1228, 0);
if (lean::is_exclusive(x_1228)) {
 x_1236 = x_1228;
} else {
 lean::inc(x_1234);
 lean::dec(x_1228);
 x_1236 = lean::box(0);
}
if (lean::is_scalar(x_1236)) {
 x_1237 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1237 = x_1236;
}
lean::cnstr_set(x_1237, 0, x_1234);
x_1090 = x_1237;
x_1091 = x_1231;
goto lbl_1092;
}
else
{
obj* x_1239; obj* x_1243; obj* x_1244; obj* x_1246; 
lean::dec(x_1228);
x_1239 = lean::cnstr_get(x_1227, 1);
lean::inc(x_1239);
lean::dec(x_1227);
lean::inc(x_1);
x_1243 = l_lean_ir_cpp_emit__var(x_1086, x_1, x_1239);
x_1244 = lean::cnstr_get(x_1243, 0);
lean::inc(x_1244);
x_1246 = lean::cnstr_get(x_1243, 1);
lean::inc(x_1246);
lean::dec(x_1243);
x_1090 = x_1244;
x_1091 = x_1246;
goto lbl_1092;
}
}
}
}
}
}
default:
{
obj* x_1249; obj* x_1251; obj* x_1253; obj* x_1255; obj* x_1256; obj* x_1258; obj* x_1260; obj* x_1262; obj* x_1265; 
x_1249 = lean::cnstr_get(x_0, 0);
lean::inc(x_1249);
x_1251 = lean::cnstr_get(x_0, 1);
lean::inc(x_1251);
x_1253 = lean::cnstr_get(x_0, 2);
lean::inc(x_1253);
x_1262 = lean::cnstr_get(x_1, 1);
lean::inc(x_1262);
lean::inc(x_1253);
x_1265 = l_rbnode_find___main___at_lean_ir_get__type___spec__2___rarg(x_1262, x_1253);
if (lean::obj_tag(x_1265) == 0)
{
obj* x_1266; 
x_1266 = lean::box(0);
x_1258 = x_1266;
goto lbl_1259;
}
else
{
obj* x_1267; uint8 x_1270; obj* x_1271; obj* x_1272; uint8 x_1273; 
x_1267 = lean::cnstr_get(x_1265, 0);
lean::inc(x_1267);
lean::dec(x_1265);
x_1270 = lean::unbox(x_1267);
x_1271 = l_lean_ir_type2id___main(x_1270);
x_1272 = l_lean_ir_valid__assign__unop__types___closed__1;
x_1273 = lean::nat_dec_eq(x_1271, x_1272);
lean::dec(x_1271);
if (x_1273 == 0)
{
obj* x_1275; 
x_1275 = lean::box(0);
x_1258 = x_1275;
goto lbl_1259;
}
else
{
obj* x_1276; 
x_1276 = lean::box(0);
x_1260 = x_1276;
goto lbl_1261;
}
}
lbl_1257:
{
if (lean::obj_tag(x_1255) == 0)
{
obj* x_1278; obj* x_1280; obj* x_1281; obj* x_1282; 
lean::dec(x_1253);
x_1278 = lean::cnstr_get(x_1255, 0);
if (lean::is_exclusive(x_1255)) {
 x_1280 = x_1255;
} else {
 lean::inc(x_1278);
 lean::dec(x_1255);
 x_1280 = lean::box(0);
}
if (lean::is_scalar(x_1280)) {
 x_1281 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1281 = x_1280;
}
lean::cnstr_set(x_1281, 0, x_1278);
x_1282 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1282, 0, x_1281);
lean::cnstr_set(x_1282, 1, x_1256);
x_3 = x_1282;
goto lbl_4;
}
else
{
obj* x_1284; obj* x_1286; obj* x_1287; 
lean::dec(x_1255);
x_1284 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_1286 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1284, x_1, x_1256);
x_1287 = lean::cnstr_get(x_1286, 0);
lean::inc(x_1287);
if (lean::obj_tag(x_1287) == 0)
{
obj* x_1290; obj* x_1293; obj* x_1295; obj* x_1296; obj* x_1297; 
lean::dec(x_1253);
x_1290 = lean::cnstr_get(x_1286, 1);
lean::inc(x_1290);
lean::dec(x_1286);
x_1293 = lean::cnstr_get(x_1287, 0);
if (lean::is_exclusive(x_1287)) {
 x_1295 = x_1287;
} else {
 lean::inc(x_1293);
 lean::dec(x_1287);
 x_1295 = lean::box(0);
}
if (lean::is_scalar(x_1295)) {
 x_1296 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1296 = x_1295;
}
lean::cnstr_set(x_1296, 0, x_1293);
x_1297 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1297, 0, x_1296);
lean::cnstr_set(x_1297, 1, x_1290);
x_3 = x_1297;
goto lbl_4;
}
else
{
obj* x_1299; obj* x_1303; obj* x_1304; 
lean::dec(x_1287);
x_1299 = lean::cnstr_get(x_1286, 1);
lean::inc(x_1299);
lean::dec(x_1286);
lean::inc(x_1);
x_1303 = l_lean_ir_cpp_emit__var(x_1253, x_1, x_1299);
x_1304 = lean::cnstr_get(x_1303, 0);
lean::inc(x_1304);
if (lean::obj_tag(x_1304) == 0)
{
obj* x_1306; obj* x_1309; obj* x_1311; obj* x_1312; obj* x_1313; 
x_1306 = lean::cnstr_get(x_1303, 1);
lean::inc(x_1306);
lean::dec(x_1303);
x_1309 = lean::cnstr_get(x_1304, 0);
if (lean::is_exclusive(x_1304)) {
 x_1311 = x_1304;
} else {
 lean::inc(x_1309);
 lean::dec(x_1304);
 x_1311 = lean::box(0);
}
if (lean::is_scalar(x_1311)) {
 x_1312 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1312 = x_1311;
}
lean::cnstr_set(x_1312, 0, x_1309);
x_1313 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1313, 0, x_1312);
lean::cnstr_set(x_1313, 1, x_1306);
x_3 = x_1313;
goto lbl_4;
}
else
{
obj* x_1314; obj* x_1317; obj* x_1320; obj* x_1322; obj* x_1323; 
x_1314 = lean::cnstr_get(x_1303, 1);
lean::inc(x_1314);
lean::dec(x_1303);
x_1317 = lean::cnstr_get(x_1304, 0);
lean::inc(x_1317);
lean::dec(x_1304);
x_1320 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_1322 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1320, x_1, x_1314);
x_1323 = lean::cnstr_get(x_1322, 0);
lean::inc(x_1323);
if (lean::obj_tag(x_1323) == 0)
{
obj* x_1326; obj* x_1329; obj* x_1331; obj* x_1332; obj* x_1333; 
lean::dec(x_1317);
x_1326 = lean::cnstr_get(x_1322, 1);
lean::inc(x_1326);
lean::dec(x_1322);
x_1329 = lean::cnstr_get(x_1323, 0);
if (lean::is_exclusive(x_1323)) {
 x_1331 = x_1323;
} else {
 lean::inc(x_1329);
 lean::dec(x_1323);
 x_1331 = lean::box(0);
}
if (lean::is_scalar(x_1331)) {
 x_1332 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1332 = x_1331;
}
lean::cnstr_set(x_1332, 0, x_1329);
x_1333 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1333, 0, x_1332);
lean::cnstr_set(x_1333, 1, x_1326);
x_3 = x_1333;
goto lbl_4;
}
else
{
obj* x_1334; obj* x_1335; obj* x_1338; obj* x_1339; 
if (lean::is_exclusive(x_1323)) {
 lean::cnstr_release(x_1323, 0);
 x_1334 = x_1323;
} else {
 lean::dec(x_1323);
 x_1334 = lean::box(0);
}
x_1335 = lean::cnstr_get(x_1322, 1);
lean::inc(x_1335);
lean::dec(x_1322);
if (lean::is_scalar(x_1334)) {
 x_1338 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_1338 = x_1334;
}
lean::cnstr_set(x_1338, 0, x_1317);
x_1339 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1339, 0, x_1338);
lean::cnstr_set(x_1339, 1, x_1335);
x_3 = x_1339;
goto lbl_4;
}
}
}
}
}
lbl_1259:
{
obj* x_1341; obj* x_1343; obj* x_1344; 
lean::dec(x_1258);
x_1341 = l_lean_ir_cpp_emit__instr___closed__8;
lean::inc(x_1);
x_1343 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1341, x_1, x_2);
x_1344 = lean::cnstr_get(x_1343, 0);
lean::inc(x_1344);
if (lean::obj_tag(x_1344) == 0)
{
obj* x_1349; obj* x_1352; obj* x_1354; obj* x_1355; obj* x_1356; 
lean::dec(x_1251);
lean::dec(x_1253);
lean::dec(x_1249);
x_1349 = lean::cnstr_get(x_1343, 1);
lean::inc(x_1349);
lean::dec(x_1343);
x_1352 = lean::cnstr_get(x_1344, 0);
if (lean::is_exclusive(x_1344)) {
 x_1354 = x_1344;
} else {
 lean::inc(x_1352);
 lean::dec(x_1344);
 x_1354 = lean::box(0);
}
if (lean::is_scalar(x_1354)) {
 x_1355 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1355 = x_1354;
}
lean::cnstr_set(x_1355, 0, x_1352);
x_1356 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1356, 0, x_1355);
lean::cnstr_set(x_1356, 1, x_1349);
x_3 = x_1356;
goto lbl_4;
}
else
{
obj* x_1358; obj* x_1361; obj* x_1363; obj* x_1364; 
lean::dec(x_1344);
x_1358 = lean::cnstr_get(x_1343, 1);
lean::inc(x_1358);
lean::dec(x_1343);
x_1361 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_1363 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1361, x_1, x_1358);
x_1364 = lean::cnstr_get(x_1363, 0);
lean::inc(x_1364);
if (lean::obj_tag(x_1364) == 0)
{
obj* x_1369; obj* x_1372; obj* x_1374; obj* x_1375; obj* x_1376; 
lean::dec(x_1251);
lean::dec(x_1253);
lean::dec(x_1249);
x_1369 = lean::cnstr_get(x_1363, 1);
lean::inc(x_1369);
lean::dec(x_1363);
x_1372 = lean::cnstr_get(x_1364, 0);
if (lean::is_exclusive(x_1364)) {
 x_1374 = x_1364;
} else {
 lean::inc(x_1372);
 lean::dec(x_1364);
 x_1374 = lean::box(0);
}
if (lean::is_scalar(x_1374)) {
 x_1375 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1375 = x_1374;
}
lean::cnstr_set(x_1375, 0, x_1372);
x_1376 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1376, 0, x_1375);
lean::cnstr_set(x_1376, 1, x_1369);
x_3 = x_1376;
goto lbl_4;
}
else
{
obj* x_1378; obj* x_1382; obj* x_1383; 
lean::dec(x_1364);
x_1378 = lean::cnstr_get(x_1363, 1);
lean::inc(x_1378);
lean::dec(x_1363);
lean::inc(x_1);
x_1382 = l_lean_ir_cpp_emit__var(x_1249, x_1, x_1378);
x_1383 = lean::cnstr_get(x_1382, 0);
lean::inc(x_1383);
if (lean::obj_tag(x_1383) == 0)
{
obj* x_1386; obj* x_1389; obj* x_1391; obj* x_1392; 
lean::dec(x_1251);
x_1386 = lean::cnstr_get(x_1382, 1);
lean::inc(x_1386);
lean::dec(x_1382);
x_1389 = lean::cnstr_get(x_1383, 0);
if (lean::is_exclusive(x_1383)) {
 x_1391 = x_1383;
} else {
 lean::inc(x_1389);
 lean::dec(x_1383);
 x_1391 = lean::box(0);
}
if (lean::is_scalar(x_1391)) {
 x_1392 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1392 = x_1391;
}
lean::cnstr_set(x_1392, 0, x_1389);
x_1255 = x_1392;
x_1256 = x_1386;
goto lbl_1257;
}
else
{
obj* x_1394; obj* x_1397; obj* x_1399; obj* x_1400; 
lean::dec(x_1383);
x_1394 = lean::cnstr_get(x_1382, 1);
lean::inc(x_1394);
lean::dec(x_1382);
x_1397 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_1399 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1397, x_1, x_1394);
x_1400 = lean::cnstr_get(x_1399, 0);
lean::inc(x_1400);
if (lean::obj_tag(x_1400) == 0)
{
obj* x_1403; obj* x_1406; obj* x_1408; obj* x_1409; 
lean::dec(x_1251);
x_1403 = lean::cnstr_get(x_1399, 1);
lean::inc(x_1403);
lean::dec(x_1399);
x_1406 = lean::cnstr_get(x_1400, 0);
if (lean::is_exclusive(x_1400)) {
 x_1408 = x_1400;
} else {
 lean::inc(x_1406);
 lean::dec(x_1400);
 x_1408 = lean::box(0);
}
if (lean::is_scalar(x_1408)) {
 x_1409 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1409 = x_1408;
}
lean::cnstr_set(x_1409, 0, x_1406);
x_1255 = x_1409;
x_1256 = x_1403;
goto lbl_1257;
}
else
{
obj* x_1411; obj* x_1415; obj* x_1416; obj* x_1418; 
lean::dec(x_1400);
x_1411 = lean::cnstr_get(x_1399, 1);
lean::inc(x_1411);
lean::dec(x_1399);
lean::inc(x_1);
x_1415 = l_lean_ir_cpp_emit__var(x_1251, x_1, x_1411);
x_1416 = lean::cnstr_get(x_1415, 0);
lean::inc(x_1416);
x_1418 = lean::cnstr_get(x_1415, 1);
lean::inc(x_1418);
lean::dec(x_1415);
x_1255 = x_1416;
x_1256 = x_1418;
goto lbl_1257;
}
}
}
}
}
lbl_1261:
{
obj* x_1422; obj* x_1424; obj* x_1425; 
lean::dec(x_1260);
x_1422 = l_lean_ir_cpp_emit__instr___closed__9;
lean::inc(x_1);
x_1424 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1422, x_1, x_2);
x_1425 = lean::cnstr_get(x_1424, 0);
lean::inc(x_1425);
if (lean::obj_tag(x_1425) == 0)
{
obj* x_1430; obj* x_1433; obj* x_1435; obj* x_1436; obj* x_1437; 
lean::dec(x_1251);
lean::dec(x_1253);
lean::dec(x_1249);
x_1430 = lean::cnstr_get(x_1424, 1);
lean::inc(x_1430);
lean::dec(x_1424);
x_1433 = lean::cnstr_get(x_1425, 0);
if (lean::is_exclusive(x_1425)) {
 x_1435 = x_1425;
} else {
 lean::inc(x_1433);
 lean::dec(x_1425);
 x_1435 = lean::box(0);
}
if (lean::is_scalar(x_1435)) {
 x_1436 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1436 = x_1435;
}
lean::cnstr_set(x_1436, 0, x_1433);
x_1437 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1437, 0, x_1436);
lean::cnstr_set(x_1437, 1, x_1430);
x_3 = x_1437;
goto lbl_4;
}
else
{
obj* x_1439; obj* x_1442; obj* x_1444; obj* x_1445; 
lean::dec(x_1425);
x_1439 = lean::cnstr_get(x_1424, 1);
lean::inc(x_1439);
lean::dec(x_1424);
x_1442 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_1444 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1442, x_1, x_1439);
x_1445 = lean::cnstr_get(x_1444, 0);
lean::inc(x_1445);
if (lean::obj_tag(x_1445) == 0)
{
obj* x_1450; obj* x_1453; obj* x_1455; obj* x_1456; obj* x_1457; 
lean::dec(x_1251);
lean::dec(x_1253);
lean::dec(x_1249);
x_1450 = lean::cnstr_get(x_1444, 1);
lean::inc(x_1450);
lean::dec(x_1444);
x_1453 = lean::cnstr_get(x_1445, 0);
if (lean::is_exclusive(x_1445)) {
 x_1455 = x_1445;
} else {
 lean::inc(x_1453);
 lean::dec(x_1445);
 x_1455 = lean::box(0);
}
if (lean::is_scalar(x_1455)) {
 x_1456 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1456 = x_1455;
}
lean::cnstr_set(x_1456, 0, x_1453);
x_1457 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1457, 0, x_1456);
lean::cnstr_set(x_1457, 1, x_1450);
x_3 = x_1457;
goto lbl_4;
}
else
{
obj* x_1459; obj* x_1463; obj* x_1464; 
lean::dec(x_1445);
x_1459 = lean::cnstr_get(x_1444, 1);
lean::inc(x_1459);
lean::dec(x_1444);
lean::inc(x_1);
x_1463 = l_lean_ir_cpp_emit__var(x_1249, x_1, x_1459);
x_1464 = lean::cnstr_get(x_1463, 0);
lean::inc(x_1464);
if (lean::obj_tag(x_1464) == 0)
{
obj* x_1467; obj* x_1470; obj* x_1472; obj* x_1473; 
lean::dec(x_1251);
x_1467 = lean::cnstr_get(x_1463, 1);
lean::inc(x_1467);
lean::dec(x_1463);
x_1470 = lean::cnstr_get(x_1464, 0);
if (lean::is_exclusive(x_1464)) {
 x_1472 = x_1464;
} else {
 lean::inc(x_1470);
 lean::dec(x_1464);
 x_1472 = lean::box(0);
}
if (lean::is_scalar(x_1472)) {
 x_1473 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1473 = x_1472;
}
lean::cnstr_set(x_1473, 0, x_1470);
x_1255 = x_1473;
x_1256 = x_1467;
goto lbl_1257;
}
else
{
obj* x_1475; obj* x_1478; obj* x_1480; obj* x_1481; 
lean::dec(x_1464);
x_1475 = lean::cnstr_get(x_1463, 1);
lean::inc(x_1475);
lean::dec(x_1463);
x_1478 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_1);
x_1480 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_1478, x_1, x_1475);
x_1481 = lean::cnstr_get(x_1480, 0);
lean::inc(x_1481);
if (lean::obj_tag(x_1481) == 0)
{
obj* x_1484; obj* x_1487; obj* x_1489; obj* x_1490; 
lean::dec(x_1251);
x_1484 = lean::cnstr_get(x_1480, 1);
lean::inc(x_1484);
lean::dec(x_1480);
x_1487 = lean::cnstr_get(x_1481, 0);
if (lean::is_exclusive(x_1481)) {
 x_1489 = x_1481;
} else {
 lean::inc(x_1487);
 lean::dec(x_1481);
 x_1489 = lean::box(0);
}
if (lean::is_scalar(x_1489)) {
 x_1490 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1490 = x_1489;
}
lean::cnstr_set(x_1490, 0, x_1487);
x_1255 = x_1490;
x_1256 = x_1484;
goto lbl_1257;
}
else
{
obj* x_1492; obj* x_1496; obj* x_1497; obj* x_1499; 
lean::dec(x_1481);
x_1492 = lean::cnstr_get(x_1480, 1);
lean::inc(x_1492);
lean::dec(x_1480);
lean::inc(x_1);
x_1496 = l_lean_ir_cpp_emit__var(x_1251, x_1, x_1492);
x_1497 = lean::cnstr_get(x_1496, 0);
lean::inc(x_1497);
x_1499 = lean::cnstr_get(x_1496, 1);
lean::inc(x_1499);
lean::dec(x_1496);
x_1255 = x_1497;
x_1256 = x_1499;
goto lbl_1257;
}
}
}
}
}
}
}
lbl_4:
{
obj* x_1502; 
x_1502 = lean::cnstr_get(x_3, 0);
lean::inc(x_1502);
if (lean::obj_tag(x_1502) == 0)
{
obj* x_1505; obj* x_1508; obj* x_1510; obj* x_1511; uint8 x_1512; obj* x_1513; obj* x_1514; obj* x_1515; obj* x_1516; obj* x_1517; obj* x_1518; obj* x_1519; obj* x_1520; obj* x_1521; obj* x_1522; obj* x_1523; obj* x_1524; obj* x_1525; 
lean::dec(x_1);
x_1505 = lean::cnstr_get(x_3, 1);
lean::inc(x_1505);
lean::dec(x_3);
x_1508 = lean::cnstr_get(x_1502, 0);
if (lean::is_exclusive(x_1502)) {
 x_1510 = x_1502;
} else {
 lean::inc(x_1508);
 lean::dec(x_1502);
 x_1510 = lean::box(0);
}
x_1511 = l_lean_ir_instr_to__format___main(x_0);
x_1512 = 0;
x_1513 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
x_1514 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1514, 0, x_1513);
lean::cnstr_set(x_1514, 1, x_1511);
lean::cnstr_set_scalar(x_1514, sizeof(void*)*2, x_1512);
x_1515 = x_1514;
x_1516 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_1517 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1517, 0, x_1515);
lean::cnstr_set(x_1517, 1, x_1516);
lean::cnstr_set_scalar(x_1517, sizeof(void*)*2, x_1512);
x_1518 = x_1517;
x_1519 = lean::box(1);
x_1520 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1520, 0, x_1518);
lean::cnstr_set(x_1520, 1, x_1519);
lean::cnstr_set_scalar(x_1520, sizeof(void*)*2, x_1512);
x_1521 = x_1520;
x_1522 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1522, 0, x_1521);
lean::cnstr_set(x_1522, 1, x_1508);
lean::cnstr_set_scalar(x_1522, sizeof(void*)*2, x_1512);
x_1523 = x_1522;
if (lean::is_scalar(x_1510)) {
 x_1524 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1524 = x_1510;
}
lean::cnstr_set(x_1524, 0, x_1523);
x_1525 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1525, 0, x_1524);
lean::cnstr_set(x_1525, 1, x_1505);
return x_1525;
}
else
{
obj* x_1527; obj* x_1530; obj* x_1531; 
lean::dec(x_1502);
x_1527 = lean::cnstr_get(x_3, 1);
lean::inc(x_1527);
lean::dec(x_3);
x_1530 = l_lean_ir_cpp_emit__eos(x_1, x_1527);
x_1531 = lean::cnstr_get(x_1530, 0);
lean::inc(x_1531);
if (lean::obj_tag(x_1531) == 0)
{
obj* x_1533; obj* x_1536; obj* x_1538; obj* x_1539; uint8 x_1540; obj* x_1541; obj* x_1542; obj* x_1543; obj* x_1544; obj* x_1545; obj* x_1546; obj* x_1547; obj* x_1548; obj* x_1549; obj* x_1550; obj* x_1551; obj* x_1552; obj* x_1553; 
x_1533 = lean::cnstr_get(x_1530, 1);
lean::inc(x_1533);
lean::dec(x_1530);
x_1536 = lean::cnstr_get(x_1531, 0);
if (lean::is_exclusive(x_1531)) {
 x_1538 = x_1531;
} else {
 lean::inc(x_1536);
 lean::dec(x_1531);
 x_1538 = lean::box(0);
}
x_1539 = l_lean_ir_instr_to__format___main(x_0);
x_1540 = 0;
x_1541 = l_lean_ir_instr_decorate__error___rarg___lambda__1___closed__1;
x_1542 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1542, 0, x_1541);
lean::cnstr_set(x_1542, 1, x_1539);
lean::cnstr_set_scalar(x_1542, sizeof(void*)*2, x_1540);
x_1543 = x_1542;
x_1544 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_1545 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1545, 0, x_1543);
lean::cnstr_set(x_1545, 1, x_1544);
lean::cnstr_set_scalar(x_1545, sizeof(void*)*2, x_1540);
x_1546 = x_1545;
x_1547 = lean::box(1);
x_1548 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1548, 0, x_1546);
lean::cnstr_set(x_1548, 1, x_1547);
lean::cnstr_set_scalar(x_1548, sizeof(void*)*2, x_1540);
x_1549 = x_1548;
x_1550 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_1550, 0, x_1549);
lean::cnstr_set(x_1550, 1, x_1536);
lean::cnstr_set_scalar(x_1550, sizeof(void*)*2, x_1540);
x_1551 = x_1550;
if (lean::is_scalar(x_1538)) {
 x_1552 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_1552 = x_1538;
}
lean::cnstr_set(x_1552, 0, x_1551);
x_1553 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1553, 0, x_1552);
lean::cnstr_set(x_1553, 1, x_1533);
return x_1553;
}
else
{
obj* x_1555; obj* x_1558; 
lean::dec(x_0);
x_1555 = lean::cnstr_get(x_1530, 1);
lean::inc(x_1555);
lean::dec(x_1530);
x_1558 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1558, 0, x_1531);
lean::cnstr_set(x_1558, 1, x_1555);
return x_1558;
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
obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
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
x_24 = lean::alloc_cnstr(0, 2, 0);
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
if (lean::is_exclusive(x_13)) {
 x_24 = x_13;
} else {
 lean::inc(x_22);
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
obj* x_29; obj* x_30; 
lean::dec(x_13);
lean::inc(x_1);
x_29 = l_lean_ir_cpp_emit__blockid(x_6, x_1, x_14);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
if (lean::obj_tag(x_30) == 0)
{
obj* x_35; obj* x_38; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
x_35 = lean::cnstr_get(x_29, 1);
lean::inc(x_35);
lean::dec(x_29);
x_38 = lean::cnstr_get(x_30, 0);
if (lean::is_exclusive(x_30)) {
 x_40 = x_30;
} else {
 lean::inc(x_38);
 lean::dec(x_30);
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
lean::cnstr_set(x_42, 1, x_35);
return x_42;
}
else
{
obj* x_44; obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_30);
x_44 = lean::cnstr_get(x_29, 1);
lean::inc(x_44);
lean::dec(x_29);
x_47 = l_lean_ir_cpp_emit__block___closed__1;
lean::inc(x_1);
x_49 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_47, x_1, x_44);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_55; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
x_55 = lean::cnstr_get(x_49, 1);
lean::inc(x_55);
lean::dec(x_49);
x_58 = lean::cnstr_get(x_50, 0);
if (lean::is_exclusive(x_50)) {
 x_60 = x_50;
} else {
 lean::inc(x_58);
 lean::dec(x_50);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_58);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_55);
return x_62;
}
else
{
obj* x_64; obj* x_67; obj* x_69; obj* x_70; 
lean::dec(x_50);
x_64 = lean::cnstr_get(x_49, 1);
lean::inc(x_64);
lean::dec(x_49);
x_67 = l_lean_format_be___main___closed__1;
lean::inc(x_1);
x_69 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_67, x_1, x_64);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_75; obj* x_78; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_8);
x_75 = lean::cnstr_get(x_69, 1);
lean::inc(x_75);
lean::dec(x_69);
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
x_82 = lean::alloc_cnstr(0, 2, 0);
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
x_88 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__block___spec__1(x_8, x_1, x_84);
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
if (lean::obj_tag(x_89) == 0)
{
obj* x_93; obj* x_96; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_10);
lean::dec(x_1);
x_93 = lean::cnstr_get(x_88, 1);
lean::inc(x_93);
lean::dec(x_88);
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
x_100 = lean::alloc_cnstr(0, 2, 0);
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
x_105 = l_lean_ir_cpp_emit__terminator(x_10, x_1, x_102);
return x_105;
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
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; uint8 x_13; obj* x_15; obj* x_16; 
x_3 = lean::cnstr_get(x_0, 2);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_13 = lean::unbox(x_3);
lean::inc(x_1);
x_15 = l_lean_ir_cpp_emit__type(x_13, x_1, x_2);
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
obj* x_26; obj* x_29; obj* x_31; obj* x_32; obj* x_34; 
lean::dec(x_16);
x_26 = lean::cnstr_get(x_15, 1);
lean::inc(x_26);
lean::dec(x_15);
x_29 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_1);
x_31 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_29, x_1, x_26);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_10 = x_32;
x_11 = x_34;
goto lbl_12;
}
lbl_12:
{
if (lean::obj_tag(x_10) == 0)
{
obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_7);
lean::dec(x_5);
lean::dec(x_1);
x_40 = lean::cnstr_get(x_10, 0);
if (lean::is_exclusive(x_10)) {
 x_42 = x_10;
} else {
 lean::inc(x_40);
 lean::dec(x_10);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_40);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_11);
return x_44;
}
else
{
obj* x_47; obj* x_48; 
lean::dec(x_10);
lean::inc(x_1);
x_47 = l_lean_ir_cpp_emit__fnid(x_5, x_1, x_11);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
obj* x_52; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_7);
lean::dec(x_1);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
lean::dec(x_47);
x_55 = lean::cnstr_get(x_48, 0);
if (lean::is_exclusive(x_48)) {
 x_57 = x_48;
} else {
 lean::inc(x_55);
 lean::dec(x_48);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_52);
return x_59;
}
else
{
obj* x_61; obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_48);
x_61 = lean::cnstr_get(x_47, 1);
lean::inc(x_61);
lean::dec(x_47);
x_64 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_66 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_64, x_1, x_61);
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_71; obj* x_74; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_7);
lean::dec(x_1);
x_71 = lean::cnstr_get(x_66, 1);
lean::inc(x_71);
lean::dec(x_66);
x_74 = lean::cnstr_get(x_67, 0);
if (lean::is_exclusive(x_67)) {
 x_76 = x_67;
} else {
 lean::inc(x_74);
 lean::dec(x_67);
 x_76 = lean::box(0);
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_74);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_71);
return x_78;
}
else
{
obj* x_80; obj* x_83; obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_67);
x_80 = lean::cnstr_get(x_66, 1);
lean::inc(x_80);
lean::dec(x_66);
x_83 = l_lean_ir_cpp_emit__header___closed__1;
x_84 = l_lean_ir_cpp_emit__template__params___closed__3;
lean::inc(x_1);
x_86 = l_lean_ir_cpp_emit__sep__aux___main___rarg(x_83, x_84, x_7, x_1, x_80);
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
if (lean::obj_tag(x_87) == 0)
{
obj* x_90; obj* x_93; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_1);
x_90 = lean::cnstr_get(x_86, 1);
lean::inc(x_90);
lean::dec(x_86);
x_93 = lean::cnstr_get(x_87, 0);
if (lean::is_exclusive(x_87)) {
 x_95 = x_87;
} else {
 lean::inc(x_93);
 lean::dec(x_87);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_93);
x_97 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_90);
return x_97;
}
else
{
obj* x_98; obj* x_101; obj* x_104; obj* x_105; obj* x_106; 
x_98 = lean::cnstr_get(x_86, 1);
lean::inc(x_98);
lean::dec(x_86);
x_101 = lean::cnstr_get(x_87, 0);
lean::inc(x_101);
lean::dec(x_87);
x_104 = l_option_has__repr___rarg___closed__3;
x_105 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_104, x_1, x_98);
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
if (lean::obj_tag(x_106) == 0)
{
obj* x_109; obj* x_112; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_101);
x_109 = lean::cnstr_get(x_105, 1);
lean::inc(x_109);
lean::dec(x_105);
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
x_116 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_109);
return x_116;
}
else
{
obj* x_117; obj* x_118; obj* x_121; obj* x_122; 
if (lean::is_exclusive(x_106)) {
 lean::cnstr_release(x_106, 0);
 x_117 = x_106;
} else {
 lean::dec(x_106);
 x_117 = lean::box(0);
}
x_118 = lean::cnstr_get(x_105, 1);
lean::inc(x_118);
lean::dec(x_105);
if (lean::is_scalar(x_117)) {
 x_121 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_121 = x_117;
}
lean::cnstr_set(x_121, 0, x_101);
x_122 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_118);
return x_122;
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
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = l_lean_ir_cpp_emit__type(x_1, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_0);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
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
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_6);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_2);
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_2, x_19);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_0);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_34 = x_25;
} else {
 lean::inc(x_32);
 lean::dec(x_25);
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
lean::cnstr_set(x_36, 1, x_29);
return x_36;
}
else
{
obj* x_38; obj* x_42; obj* x_43; 
lean::dec(x_25);
x_38 = lean::cnstr_get(x_24, 1);
lean::inc(x_38);
lean::dec(x_24);
lean::inc(x_2);
x_42 = l_lean_ir_cpp_emit__var(x_0, x_2, x_38);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_2);
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
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_46);
return x_53;
}
else
{
obj* x_55; obj* x_58; 
lean::dec(x_43);
x_55 = lean::cnstr_get(x_42, 1);
lean::inc(x_55);
lean::dec(x_42);
x_58 = l_lean_ir_cpp_emit__eos(x_2, x_55);
return x_58;
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
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_20; obj* x_21; 
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
if (lean::obj_tag(x_21) == 0)
{
obj* x_28; obj* x_31; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
lean::dec(x_15);
x_28 = lean::cnstr_get(x_20, 1);
lean::inc(x_28);
lean::dec(x_20);
x_31 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_33 = x_21;
} else {
 lean::inc(x_31);
 lean::dec(x_21);
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
lean::cnstr_set(x_35, 1, x_28);
return x_35;
}
else
{
obj* x_37; obj* x_42; uint8 x_43; 
lean::dec(x_21);
x_37 = lean::cnstr_get(x_20, 1);
lean::inc(x_37);
lean::dec(x_20);
lean::inc(x_0);
lean::inc(x_11);
x_42 = l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1(x_11, x_0);
x_43 = lean::unbox(x_42);
if (x_43 == 0)
{
uint8 x_44; obj* x_46; obj* x_47; 
x_44 = lean::unbox(x_13);
lean::inc(x_3);
x_46 = l_lean_ir_cpp_decl__local(x_11, x_44, x_3, x_37);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_52; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_15);
x_52 = lean::cnstr_get(x_46, 1);
lean::inc(x_52);
lean::dec(x_46);
x_55 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 x_57 = x_47;
} else {
 lean::inc(x_55);
 lean::dec(x_47);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_52);
return x_59;
}
else
{
obj* x_61; obj* x_64; 
lean::dec(x_47);
x_61 = lean::cnstr_get(x_46, 1);
lean::inc(x_61);
lean::dec(x_46);
x_64 = lean::box(0);
x_1 = x_15;
x_2 = x_64;
x_4 = x_61;
goto _start;
}
}
else
{
obj* x_68; 
lean::dec(x_11);
lean::dec(x_13);
x_68 = lean::box(0);
x_1 = x_15;
x_2 = x_68;
x_4 = x_37;
goto _start;
}
}
}
default:
{
obj* x_70; obj* x_72; obj* x_74; obj* x_76; obj* x_81; obj* x_82; 
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
if (lean::obj_tag(x_82) == 0)
{
obj* x_89; obj* x_92; obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_76);
lean::dec(x_74);
lean::dec(x_72);
x_89 = lean::cnstr_get(x_81, 1);
lean::inc(x_89);
lean::dec(x_81);
x_92 = lean::cnstr_get(x_82, 0);
if (lean::is_exclusive(x_82)) {
 x_94 = x_82;
} else {
 lean::inc(x_92);
 lean::dec(x_82);
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
lean::cnstr_set(x_96, 1, x_89);
return x_96;
}
else
{
obj* x_98; obj* x_103; uint8 x_104; 
lean::dec(x_82);
x_98 = lean::cnstr_get(x_81, 1);
lean::inc(x_98);
lean::dec(x_81);
lean::inc(x_0);
lean::inc(x_72);
x_103 = l_list_foldr___main___at_lean_ir_cpp_decl__locals___spec__1(x_72, x_0);
x_104 = lean::unbox(x_103);
if (x_104 == 0)
{
uint8 x_105; obj* x_107; obj* x_108; 
x_105 = lean::unbox(x_74);
lean::inc(x_3);
x_107 = l_lean_ir_cpp_decl__local(x_72, x_105, x_3, x_98);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
if (lean::obj_tag(x_108) == 0)
{
obj* x_113; obj* x_116; obj* x_118; obj* x_119; obj* x_120; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_76);
x_113 = lean::cnstr_get(x_107, 1);
lean::inc(x_113);
lean::dec(x_107);
x_116 = lean::cnstr_get(x_108, 0);
if (lean::is_exclusive(x_108)) {
 x_118 = x_108;
} else {
 lean::inc(x_116);
 lean::dec(x_108);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_116);
x_120 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_113);
return x_120;
}
else
{
obj* x_122; obj* x_125; 
lean::dec(x_108);
x_122 = lean::cnstr_get(x_107, 1);
lean::inc(x_122);
lean::dec(x_107);
x_125 = lean::box(0);
x_1 = x_76;
x_2 = x_125;
x_4 = x_122;
goto _start;
}
}
else
{
obj* x_129; 
lean::dec(x_74);
lean::dec(x_72);
x_129 = lean::box(0);
x_1 = x_76;
x_2 = x_129;
x_4 = x_98;
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
obj* x_14; uint8 x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_14 = lean::cnstr_get(x_1, 2);
lean::inc(x_14);
lean::dec(x_1);
x_17 = lean::unbox(x_14);
x_18 = l_lean_ir_type2id___main(x_17);
x_19 = l_lean_ir_valid__assign__unop__types___closed__1;
x_20 = lean::nat_dec_eq(x_18, x_19);
lean::dec(x_18);
if (x_20 == 0)
{
uint8 x_23; obj* x_24; 
lean::dec(x_2);
x_23 = 0;
x_24 = lean::box(x_23);
return x_24;
}
else
{
obj* x_25; 
x_25 = l_list_foldr___main___at_lean_ir_cpp_need__uncurry___spec__1(x_2);
return x_25;
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = l_lean_ir_cpp_emit__uncurry__header___closed__1;
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
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
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_23; obj* x_27; obj* x_28; 
lean::dec(x_6);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_lean_ir_decl_header___main(x_0);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
lean::dec(x_22);
lean::inc(x_1);
x_27 = l_lean_ir_cpp_emit__fnid(x_23, x_1, x_19);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_31; obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
x_31 = lean::cnstr_get(x_27, 1);
lean::inc(x_31);
lean::dec(x_27);
x_34 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_36 = x_28;
} else {
 lean::inc(x_34);
 lean::dec(x_28);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_34);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_31);
return x_38;
}
else
{
obj* x_40; obj* x_43; obj* x_44; 
lean::dec(x_28);
x_40 = lean::cnstr_get(x_27, 1);
lean::inc(x_40);
lean::dec(x_27);
x_43 = l_lean_ir_cpp_emit__uncurry__header___closed__2;
x_44 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_43, x_1, x_40);
return x_44;
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
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = lean::apply_2(x_0, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
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
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_6);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_list_repr__aux___main___rarg___closed__1;
lean::inc(x_2);
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_2, x_19);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_34 = x_25;
} else {
 lean::inc(x_32);
 lean::dec(x_25);
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
lean::cnstr_set(x_36, 1, x_29);
return x_36;
}
else
{
obj* x_38; obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_25);
x_38 = lean::cnstr_get(x_24, 1);
lean::inc(x_38);
lean::dec(x_24);
x_41 = l_nat_repeat__core___main___at_lean_ir_cpp_emit__uncurry___spec__3___lambda__1___closed__1;
lean::inc(x_2);
x_43 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_41, x_2, x_38);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_48; obj* x_51; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_1);
lean::dec(x_2);
x_48 = lean::cnstr_get(x_43, 1);
lean::inc(x_48);
lean::dec(x_43);
x_51 = lean::cnstr_get(x_44, 0);
if (lean::is_exclusive(x_44)) {
 x_53 = x_44;
} else {
 lean::inc(x_51);
 lean::dec(x_44);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_48);
return x_55;
}
else
{
obj* x_57; obj* x_60; obj* x_61; obj* x_64; obj* x_65; 
lean::dec(x_44);
x_57 = lean::cnstr_get(x_43, 1);
lean::inc(x_57);
lean::dec(x_43);
x_60 = lean::mk_nat_obj(1u);
x_61 = lean::nat_add(x_1, x_60);
lean::dec(x_1);
lean::inc(x_2);
x_64 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__cases___main___spec__1(x_61, x_2, x_57);
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
if (lean::obj_tag(x_65) == 0)
{
obj* x_68; obj* x_71; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_2);
x_68 = lean::cnstr_get(x_64, 1);
lean::inc(x_68);
lean::dec(x_64);
x_71 = lean::cnstr_get(x_65, 0);
if (lean::is_exclusive(x_65)) {
 x_73 = x_65;
} else {
 lean::inc(x_71);
 lean::dec(x_65);
 x_73 = lean::box(0);
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_71);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_68);
return x_75;
}
else
{
obj* x_77; obj* x_80; obj* x_81; 
lean::dec(x_65);
x_77 = lean::cnstr_get(x_64, 1);
lean::inc(x_77);
lean::dec(x_64);
x_80 = l_list_repr___main___rarg___closed__3;
x_81 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_80, x_2, x_77);
return x_81;
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_11; obj* x_12; 
lean::inc(x_1);
lean::inc(x_0);
x_11 = l_lean_ir_cpp_emit__uncurry__header(x_0, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_17; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_19 = x_12;
} else {
 lean::inc(x_17);
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
obj* x_22; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_34; 
lean::dec(x_12);
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
lean::dec(x_11);
x_25 = l_lean_ir_cpp_emit__uncurry___closed__3;
lean::inc(x_1);
x_27 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_25, x_1, x_22);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
lean::inc(x_0);
x_34 = l_lean_ir_decl_header___main(x_0);
if (lean::obj_tag(x_28) == 0)
{
obj* x_36; obj* x_38; obj* x_39; 
lean::dec(x_34);
x_36 = lean::cnstr_get(x_28, 0);
if (lean::is_exclusive(x_28)) {
 x_38 = x_28;
} else {
 lean::inc(x_36);
 lean::dec(x_28);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
x_6 = x_39;
x_7 = x_30;
goto lbl_8;
}
else
{
obj* x_41; obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_28);
x_41 = lean::cnstr_get(x_34, 0);
lean::inc(x_41);
lean::dec(x_34);
x_44 = l_lean_ir_cpp_emit__terminator___closed__1;
lean::inc(x_1);
x_46 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_44, x_1, x_30);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_50; obj* x_53; obj* x_55; obj* x_56; 
lean::dec(x_41);
x_50 = lean::cnstr_get(x_46, 1);
lean::inc(x_50);
lean::dec(x_46);
x_53 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 x_55 = x_47;
} else {
 lean::inc(x_53);
 lean::dec(x_47);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
x_6 = x_56;
x_7 = x_50;
goto lbl_8;
}
else
{
obj* x_58; obj* x_62; obj* x_63; obj* x_65; 
lean::dec(x_47);
x_58 = lean::cnstr_get(x_46, 1);
lean::inc(x_58);
lean::dec(x_46);
lean::inc(x_1);
x_62 = l_lean_ir_cpp_emit__fnid(x_41, x_1, x_58);
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
x_6 = x_63;
x_7 = x_65;
goto lbl_8;
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_69; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_1);
x_69 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_71 = x_3;
} else {
 lean::inc(x_69);
 lean::dec(x_3);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_69);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_4);
return x_73;
}
else
{
obj* x_76; obj* x_77; 
lean::dec(x_3);
lean::inc(x_1);
x_76 = l_lean_ir_cpp_emit__eos(x_1, x_4);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
if (lean::obj_tag(x_77) == 0)
{
obj* x_80; obj* x_83; obj* x_85; obj* x_86; obj* x_87; 
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
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_80);
return x_87;
}
else
{
obj* x_89; obj* x_92; obj* x_93; 
lean::dec(x_77);
x_89 = lean::cnstr_get(x_76, 1);
lean::inc(x_89);
lean::dec(x_76);
x_92 = l_lean_ir_cpp_emit__uncurry___closed__1;
x_93 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_92, x_1, x_89);
return x_93;
}
}
}
lbl_8:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_0);
x_95 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 x_97 = x_6;
} else {
 lean::inc(x_95);
 lean::dec(x_6);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
x_3 = x_98;
x_4 = x_7;
goto lbl_5;
}
else
{
obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_6);
x_100 = l_prod_has__repr___rarg___closed__1;
lean::inc(x_1);
x_102 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_100, x_1, x_7);
x_103 = lean::cnstr_get(x_102, 0);
lean::inc(x_103);
if (lean::obj_tag(x_103) == 0)
{
obj* x_106; obj* x_109; obj* x_111; obj* x_112; 
lean::dec(x_0);
x_106 = lean::cnstr_get(x_102, 1);
lean::inc(x_106);
lean::dec(x_102);
x_109 = lean::cnstr_get(x_103, 0);
if (lean::is_exclusive(x_103)) {
 x_111 = x_103;
} else {
 lean::inc(x_109);
 lean::dec(x_103);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_109);
x_3 = x_112;
x_4 = x_106;
goto lbl_5;
}
else
{
obj* x_114; obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_103);
x_114 = lean::cnstr_get(x_102, 1);
lean::inc(x_114);
lean::dec(x_102);
x_117 = l_lean_ir_cpp_emit__uncurry___closed__2;
lean::inc(x_1);
x_119 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_117, x_1, x_114);
x_120 = lean::cnstr_get(x_119, 0);
lean::inc(x_120);
if (lean::obj_tag(x_120) == 0)
{
obj* x_123; obj* x_126; obj* x_128; obj* x_129; 
lean::dec(x_0);
x_123 = lean::cnstr_get(x_119, 1);
lean::inc(x_123);
lean::dec(x_119);
x_126 = lean::cnstr_get(x_120, 0);
if (lean::is_exclusive(x_120)) {
 x_128 = x_120;
} else {
 lean::inc(x_126);
 lean::dec(x_120);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_126);
x_3 = x_129;
x_4 = x_123;
goto lbl_5;
}
else
{
obj* x_131; obj* x_135; obj* x_136; 
lean::dec(x_120);
x_131 = lean::cnstr_get(x_119, 1);
lean::inc(x_131);
lean::dec(x_119);
lean::inc(x_1);
x_135 = l_nat_mrepeat___at_lean_ir_cpp_emit__uncurry___spec__1(x_0, x_1, x_131);
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
if (lean::obj_tag(x_136) == 0)
{
obj* x_138; obj* x_141; obj* x_143; obj* x_144; 
x_138 = lean::cnstr_get(x_135, 1);
lean::inc(x_138);
lean::dec(x_135);
x_141 = lean::cnstr_get(x_136, 0);
if (lean::is_exclusive(x_136)) {
 x_143 = x_136;
} else {
 lean::inc(x_141);
 lean::dec(x_136);
 x_143 = lean::box(0);
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_141);
x_3 = x_144;
x_4 = x_138;
goto lbl_5;
}
else
{
obj* x_145; obj* x_148; obj* x_151; obj* x_153; obj* x_154; 
x_145 = lean::cnstr_get(x_135, 1);
lean::inc(x_145);
lean::dec(x_135);
x_148 = lean::cnstr_get(x_136, 0);
lean::inc(x_148);
lean::dec(x_136);
x_151 = l_option_has__repr___rarg___closed__3;
lean::inc(x_1);
x_153 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_151, x_1, x_145);
x_154 = lean::cnstr_get(x_153, 0);
lean::inc(x_154);
if (lean::obj_tag(x_154) == 0)
{
obj* x_157; obj* x_160; obj* x_162; obj* x_163; 
lean::dec(x_148);
x_157 = lean::cnstr_get(x_153, 1);
lean::inc(x_157);
lean::dec(x_153);
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
x_3 = x_163;
x_4 = x_157;
goto lbl_5;
}
else
{
obj* x_164; obj* x_165; obj* x_168; 
if (lean::is_exclusive(x_154)) {
 lean::cnstr_release(x_154, 0);
 x_164 = x_154;
} else {
 lean::dec(x_154);
 x_164 = lean::box(0);
}
x_165 = lean::cnstr_get(x_153, 1);
lean::inc(x_165);
lean::dec(x_153);
if (lean::is_scalar(x_164)) {
 x_168 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_168 = x_164;
}
lean::cnstr_set(x_168, 0, x_148);
x_3 = x_168;
x_4 = x_165;
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
obj* x_6; obj* x_8; obj* x_12; obj* x_13; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = l_lean_ir_cpp_emit__block(x_6, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
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
x_24 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_11; obj* x_13; obj* x_15; obj* x_18; uint8 x_19; uint8 x_20; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
lean::inc(x_0);
x_18 = l_lean_ir_cpp_need__uncurry(x_0);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
uint8 x_22; 
x_22 = 0;
x_20 = x_22;
goto lbl_21;
}
else
{
uint8 x_23; 
x_23 = 1;
x_20 = x_23;
goto lbl_21;
}
lbl_21:
{
obj* x_24; obj* x_25; obj* x_28; obj* x_29; 
lean::inc(x_1);
x_28 = l_lean_ir_cpp_emit__header(x_11, x_1, x_2);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_32; obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_15);
x_32 = lean::cnstr_get(x_28, 1);
lean::inc(x_32);
lean::dec(x_28);
x_35 = lean::cnstr_get(x_29, 0);
if (lean::is_exclusive(x_29)) {
 x_37 = x_29;
} else {
 lean::inc(x_35);
 lean::dec(x_29);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_35);
x_24 = x_38;
x_25 = x_32;
goto lbl_26;
}
else
{
obj* x_40; obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_29);
x_40 = lean::cnstr_get(x_28, 1);
lean::inc(x_40);
lean::dec(x_28);
x_43 = l_lean_ir_cpp_emit__case___main___closed__1;
lean::inc(x_1);
x_45 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_43, x_1, x_40);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
if (lean::obj_tag(x_46) == 0)
{
obj* x_49; obj* x_52; obj* x_54; obj* x_55; 
lean::dec(x_15);
x_49 = lean::cnstr_get(x_45, 1);
lean::inc(x_49);
lean::dec(x_45);
x_52 = lean::cnstr_get(x_46, 0);
if (lean::is_exclusive(x_46)) {
 x_54 = x_46;
} else {
 lean::inc(x_52);
 lean::dec(x_46);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_52);
x_24 = x_55;
x_25 = x_49;
goto lbl_26;
}
else
{
obj* x_57; obj* x_60; obj* x_62; obj* x_63; 
lean::dec(x_46);
x_57 = lean::cnstr_get(x_45, 1);
lean::inc(x_57);
lean::dec(x_45);
x_60 = l_lean_format_be___main___closed__1;
lean::inc(x_1);
x_62 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_60, x_1, x_57);
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
if (lean::obj_tag(x_63) == 0)
{
obj* x_66; obj* x_69; obj* x_71; obj* x_72; 
lean::dec(x_15);
x_66 = lean::cnstr_get(x_62, 1);
lean::inc(x_66);
lean::dec(x_62);
x_69 = lean::cnstr_get(x_63, 0);
if (lean::is_exclusive(x_63)) {
 x_71 = x_63;
} else {
 lean::inc(x_69);
 lean::dec(x_63);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_69);
x_24 = x_72;
x_25 = x_66;
goto lbl_26;
}
else
{
obj* x_74; obj* x_78; obj* x_79; obj* x_81; 
lean::dec(x_63);
x_74 = lean::cnstr_get(x_62, 1);
lean::inc(x_74);
lean::dec(x_62);
lean::inc(x_1);
x_78 = l_lean_ir_cpp_decl__locals(x_15, x_1, x_74);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
lean::dec(x_78);
x_24 = x_79;
x_25 = x_81;
goto lbl_26;
}
}
}
lbl_26:
{
if (lean::obj_tag(x_24) == 0)
{
obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_13);
lean::dec(x_1);
lean::dec(x_0);
x_87 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_89 = x_24;
} else {
 lean::inc(x_87);
 lean::dec(x_24);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_87);
x_5 = x_90;
x_6 = x_25;
goto lbl_7;
}
else
{
obj* x_93; obj* x_94; 
lean::dec(x_24);
lean::inc(x_1);
x_93 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__def__core___spec__1(x_13, x_1, x_25);
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
if (lean::obj_tag(x_94) == 0)
{
obj* x_98; obj* x_101; obj* x_103; obj* x_104; 
lean::dec(x_1);
lean::dec(x_0);
x_98 = lean::cnstr_get(x_93, 1);
lean::inc(x_98);
lean::dec(x_93);
x_101 = lean::cnstr_get(x_94, 0);
if (lean::is_exclusive(x_94)) {
 x_103 = x_94;
} else {
 lean::inc(x_101);
 lean::dec(x_94);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_101);
x_5 = x_104;
x_6 = x_98;
goto lbl_7;
}
else
{
obj* x_106; obj* x_109; obj* x_111; obj* x_112; 
lean::dec(x_94);
x_106 = lean::cnstr_get(x_93, 1);
lean::inc(x_106);
lean::dec(x_93);
x_109 = l_lean_ir_cpp_emit__case___main___closed__2;
lean::inc(x_1);
x_111 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_109, x_1, x_106);
x_112 = lean::cnstr_get(x_111, 0);
lean::inc(x_112);
if (lean::obj_tag(x_112) == 0)
{
obj* x_116; obj* x_119; obj* x_121; obj* x_122; 
lean::dec(x_1);
lean::dec(x_0);
x_116 = lean::cnstr_get(x_111, 1);
lean::inc(x_116);
lean::dec(x_111);
x_119 = lean::cnstr_get(x_112, 0);
if (lean::is_exclusive(x_112)) {
 x_121 = x_112;
} else {
 lean::inc(x_119);
 lean::dec(x_112);
 x_121 = lean::box(0);
}
if (lean::is_scalar(x_121)) {
 x_122 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_122 = x_121;
}
lean::cnstr_set(x_122, 0, x_119);
x_5 = x_122;
x_6 = x_116;
goto lbl_7;
}
else
{
obj* x_124; obj* x_127; obj* x_129; obj* x_130; 
lean::dec(x_112);
x_124 = lean::cnstr_get(x_111, 1);
lean::inc(x_124);
lean::dec(x_111);
x_127 = l_lean_format_be___main___closed__1;
lean::inc(x_1);
x_129 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_127, x_1, x_124);
x_130 = lean::cnstr_get(x_129, 0);
lean::inc(x_130);
if (lean::obj_tag(x_130) == 0)
{
obj* x_134; obj* x_137; obj* x_139; obj* x_140; 
lean::dec(x_1);
lean::dec(x_0);
x_134 = lean::cnstr_get(x_129, 1);
lean::inc(x_134);
lean::dec(x_129);
x_137 = lean::cnstr_get(x_130, 0);
if (lean::is_exclusive(x_130)) {
 x_139 = x_130;
} else {
 lean::inc(x_137);
 lean::dec(x_130);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_137);
x_5 = x_140;
x_6 = x_134;
goto lbl_7;
}
else
{
lean::dec(x_130);
if (x_20 == 0)
{
obj* x_144; obj* x_147; 
lean::dec(x_1);
lean::dec(x_0);
x_144 = lean::cnstr_get(x_129, 1);
lean::inc(x_144);
lean::dec(x_129);
x_147 = l_lean_ir_match__type___closed__5;
x_5 = x_147;
x_6 = x_144;
goto lbl_7;
}
else
{
obj* x_148; obj* x_151; obj* x_152; obj* x_154; 
x_148 = lean::cnstr_get(x_129, 1);
lean::inc(x_148);
lean::dec(x_129);
x_151 = l_lean_ir_cpp_emit__uncurry(x_0, x_1, x_148);
x_152 = lean::cnstr_get(x_151, 0);
lean::inc(x_152);
x_154 = lean::cnstr_get(x_151, 1);
lean::inc(x_154);
lean::dec(x_151);
x_5 = x_152;
x_6 = x_154;
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
obj* x_157; obj* x_159; obj* x_160; obj* x_163; uint8 x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; 
x_157 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_159 = x_5;
} else {
 lean::inc(x_157);
 lean::dec(x_5);
 x_159 = lean::box(0);
}
x_160 = lean::cnstr_get(x_4, 0);
lean::inc(x_160);
lean::dec(x_4);
x_163 = l_lean_to__fmt___at_lean_ir_instr_to__format___main___spec__2(x_160);
x_164 = 0;
x_165 = l_lean_ir_header_decorate__error___rarg___lambda__1___closed__1;
x_166 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_166, 0, x_165);
lean::cnstr_set(x_166, 1, x_163);
lean::cnstr_set_scalar(x_166, sizeof(void*)*2, x_164);
x_167 = x_166;
x_168 = l_lean_ir_phi_decorate__error___rarg___lambda__1___closed__2;
x_169 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_169, 0, x_167);
lean::cnstr_set(x_169, 1, x_168);
lean::cnstr_set_scalar(x_169, sizeof(void*)*2, x_164);
x_170 = x_169;
x_171 = lean::box(1);
x_172 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_172, 0, x_170);
lean::cnstr_set(x_172, 1, x_171);
lean::cnstr_set_scalar(x_172, sizeof(void*)*2, x_164);
x_173 = x_172;
x_174 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_174, 0, x_173);
lean::cnstr_set(x_174, 1, x_157);
lean::cnstr_set_scalar(x_174, sizeof(void*)*2, x_164);
x_175 = x_174;
if (lean::is_scalar(x_159)) {
 x_176 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_176 = x_159;
}
lean::cnstr_set(x_176, 0, x_175);
x_177 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_177, 0, x_176);
lean::cnstr_set(x_177, 1, x_6);
return x_177;
}
else
{
obj* x_179; 
lean::dec(x_4);
x_179 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_179, 0, x_5);
lean::cnstr_set(x_179, 1, x_6);
return x_179;
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
x_6 = lean::cnstr_get(x_0, 1);
x_8 = lean::cnstr_get(x_0, 2);
x_10 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_12 = x_0;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_0);
 x_12 = lean::box(0);
}
lean::inc(x_6);
lean::inc(x_1);
x_15 = l_lean_name_quick__lt___main(x_1, x_6);
x_16 = lean::unbox(x_15);
if (x_16 == 0)
{
obj* x_19; uint8 x_20; 
lean::inc(x_1);
lean::inc(x_6);
x_19 = l_lean_name_quick__lt___main(x_6, x_1);
x_20 = lean::unbox(x_19);
if (x_20 == 0)
{
obj* x_23; 
lean::dec(x_8);
lean::dec(x_6);
if (lean::is_scalar(x_12)) {
 x_23 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_23 = x_12;
}
lean::cnstr_set(x_23, 0, x_4);
lean::cnstr_set(x_23, 1, x_1);
lean::cnstr_set(x_23, 2, x_2);
lean::cnstr_set(x_23, 3, x_10);
return x_23;
}
else
{
obj* x_24; obj* x_25; 
x_24 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_10, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_25 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_25 = x_12;
}
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_6);
lean::cnstr_set(x_25, 2, x_8);
lean::cnstr_set(x_25, 3, x_24);
return x_25;
}
}
else
{
obj* x_26; obj* x_27; 
x_26 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_4, x_1, x_2);
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_6);
lean::cnstr_set(x_27, 2, x_8);
lean::cnstr_set(x_27, 3, x_10);
return x_27;
}
}
default:
{
obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_39; uint8 x_40; 
x_28 = lean::cnstr_get(x_0, 0);
x_30 = lean::cnstr_get(x_0, 1);
x_32 = lean::cnstr_get(x_0, 2);
x_34 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_36 = x_0;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_0);
 x_36 = lean::box(0);
}
lean::inc(x_30);
lean::inc(x_1);
x_39 = l_lean_name_quick__lt___main(x_1, x_30);
x_40 = lean::unbox(x_39);
if (x_40 == 0)
{
obj* x_43; uint8 x_44; 
lean::inc(x_1);
lean::inc(x_30);
x_43 = l_lean_name_quick__lt___main(x_30, x_1);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_47; 
lean::dec(x_30);
lean::dec(x_32);
if (lean::is_scalar(x_36)) {
 x_47 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_47 = x_36;
}
lean::cnstr_set(x_47, 0, x_28);
lean::cnstr_set(x_47, 1, x_1);
lean::cnstr_set(x_47, 2, x_2);
lean::cnstr_set(x_47, 3, x_34);
return x_47;
}
else
{
uint8 x_49; 
lean::inc(x_34);
x_49 = l_rbnode_get__color___main___rarg(x_34);
if (x_49 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_36);
x_51 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_34, x_1, x_2);
x_52 = l_rbnode_balance2__node___main___rarg(x_51, x_30, x_32, x_28);
return x_52;
}
else
{
obj* x_53; obj* x_54; 
x_53 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_34, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_54 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_54 = x_36;
}
lean::cnstr_set(x_54, 0, x_28);
lean::cnstr_set(x_54, 1, x_30);
lean::cnstr_set(x_54, 2, x_32);
lean::cnstr_set(x_54, 3, x_53);
return x_54;
}
}
}
else
{
uint8 x_56; 
lean::inc(x_28);
x_56 = l_rbnode_get__color___main___rarg(x_28);
if (x_56 == 0)
{
obj* x_58; obj* x_59; 
lean::dec(x_36);
x_58 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_28, x_1, x_2);
x_59 = l_rbnode_balance1__node___main___rarg(x_58, x_30, x_32, x_34);
return x_59;
}
else
{
obj* x_60; obj* x_61; 
x_60 = l_rbnode_ins___main___at_lean_ir_cpp_collect__used___spec__3(x_28, x_1, x_2);
if (lean::is_scalar(x_36)) {
 x_61 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_61 = x_36;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_30);
lean::cnstr_set(x_61, 2, x_32);
lean::cnstr_set(x_61, 3, x_34);
return x_61;
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
default:
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
obj* x_25; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_11);
lean::dec(x_13);
x_25 = lean::cnstr_get(x_18, 1);
lean::inc(x_25);
lean::dec(x_18);
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
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_25);
return x_32;
}
else
{
obj* x_34; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_45; 
lean::dec(x_19);
x_34 = lean::cnstr_get(x_18, 1);
lean::inc(x_34);
lean::dec(x_18);
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
obj* x_57; obj* x_59; uint8 x_60; obj* x_62; 
lean::inc(x_49);
x_57 = l_lean_ir_decl_header___main(x_49);
lean::inc(x_49);
x_59 = l_lean_ir_cpp_need__uncurry(x_49);
x_60 = lean::unbox(x_59);
lean::inc(x_3);
x_62 = l_lean_ir_cpp_emit__header(x_57, x_3, x_34);
if (x_60 == 0)
{
obj* x_64; 
lean::dec(x_49);
x_64 = lean::cnstr_get(x_62, 0);
lean::inc(x_64);
if (lean::obj_tag(x_64) == 0)
{
obj* x_66; obj* x_69; obj* x_71; obj* x_72; 
x_66 = lean::cnstr_get(x_62, 1);
lean::inc(x_66);
lean::dec(x_62);
x_69 = lean::cnstr_get(x_64, 0);
if (lean::is_exclusive(x_64)) {
 x_71 = x_64;
} else {
 lean::inc(x_69);
 lean::dec(x_64);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_69);
x_37 = x_72;
x_38 = x_66;
goto lbl_39;
}
else
{
obj* x_74; obj* x_77; obj* x_79; obj* x_80; 
lean::dec(x_64);
x_74 = lean::cnstr_get(x_62, 1);
lean::inc(x_74);
lean::dec(x_62);
x_77 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
x_79 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_77, x_3, x_74);
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
x_37 = x_88;
x_38 = x_82;
goto lbl_39;
}
else
{
obj* x_90; obj* x_93; 
lean::dec(x_80);
x_90 = lean::cnstr_get(x_79, 1);
lean::inc(x_90);
lean::dec(x_79);
x_93 = l_lean_ir_match__type___closed__5;
x_37 = x_93;
x_38 = x_90;
goto lbl_39;
}
}
}
else
{
obj* x_94; 
x_94 = lean::cnstr_get(x_62, 0);
lean::inc(x_94);
if (lean::obj_tag(x_94) == 0)
{
obj* x_97; obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_49);
x_97 = lean::cnstr_get(x_62, 1);
lean::inc(x_97);
lean::dec(x_62);
x_100 = lean::cnstr_get(x_94, 0);
if (lean::is_exclusive(x_94)) {
 x_102 = x_94;
} else {
 lean::inc(x_100);
 lean::dec(x_94);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_100);
x_37 = x_103;
x_38 = x_97;
goto lbl_39;
}
else
{
obj* x_105; obj* x_108; obj* x_110; obj* x_111; 
lean::dec(x_94);
x_105 = lean::cnstr_get(x_62, 1);
lean::inc(x_105);
lean::dec(x_62);
x_108 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
x_110 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_108, x_3, x_105);
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
if (lean::obj_tag(x_111) == 0)
{
obj* x_114; obj* x_117; obj* x_119; obj* x_120; 
lean::dec(x_49);
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
x_37 = x_120;
x_38 = x_114;
goto lbl_39;
}
else
{
obj* x_122; obj* x_126; obj* x_127; 
lean::dec(x_111);
x_122 = lean::cnstr_get(x_110, 1);
lean::inc(x_122);
lean::dec(x_110);
lean::inc(x_3);
x_126 = l_lean_ir_cpp_emit__uncurry__header(x_49, x_3, x_122);
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
x_37 = x_135;
x_38 = x_129;
goto lbl_39;
}
else
{
obj* x_137; obj* x_141; obj* x_142; obj* x_144; 
lean::dec(x_127);
x_137 = lean::cnstr_get(x_126, 1);
lean::inc(x_137);
lean::dec(x_126);
lean::inc(x_3);
x_141 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_108, x_3, x_137);
x_142 = lean::cnstr_get(x_141, 0);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_141, 1);
lean::inc(x_144);
lean::dec(x_141);
x_37 = x_142;
x_38 = x_144;
goto lbl_39;
}
}
}
}
}
else
{
obj* x_148; obj* x_150; obj* x_151; 
lean::dec(x_55);
x_148 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__2;
lean::inc(x_3);
x_150 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_148, x_3, x_34);
x_151 = lean::cnstr_get(x_150, 0);
lean::inc(x_151);
if (lean::obj_tag(x_151) == 0)
{
obj* x_154; obj* x_157; obj* x_159; obj* x_160; 
lean::dec(x_49);
x_154 = lean::cnstr_get(x_150, 1);
lean::inc(x_154);
lean::dec(x_150);
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
x_37 = x_160;
x_38 = x_154;
goto lbl_39;
}
else
{
obj* x_162; obj* x_166; obj* x_168; uint8 x_169; obj* x_171; 
lean::dec(x_151);
x_162 = lean::cnstr_get(x_150, 1);
lean::inc(x_162);
lean::dec(x_150);
lean::inc(x_49);
x_166 = l_lean_ir_decl_header___main(x_49);
lean::inc(x_49);
x_168 = l_lean_ir_cpp_need__uncurry(x_49);
x_169 = lean::unbox(x_168);
lean::inc(x_3);
x_171 = l_lean_ir_cpp_emit__header(x_166, x_3, x_162);
if (x_169 == 0)
{
obj* x_173; 
lean::dec(x_49);
x_173 = lean::cnstr_get(x_171, 0);
lean::inc(x_173);
if (lean::obj_tag(x_173) == 0)
{
obj* x_175; obj* x_178; obj* x_180; obj* x_181; 
x_175 = lean::cnstr_get(x_171, 1);
lean::inc(x_175);
lean::dec(x_171);
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
x_37 = x_181;
x_38 = x_175;
goto lbl_39;
}
else
{
obj* x_183; obj* x_186; obj* x_188; obj* x_189; 
lean::dec(x_173);
x_183 = lean::cnstr_get(x_171, 1);
lean::inc(x_183);
lean::dec(x_171);
x_186 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
x_188 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_186, x_3, x_183);
x_189 = lean::cnstr_get(x_188, 0);
lean::inc(x_189);
if (lean::obj_tag(x_189) == 0)
{
obj* x_191; obj* x_194; obj* x_196; obj* x_197; 
x_191 = lean::cnstr_get(x_188, 1);
lean::inc(x_191);
lean::dec(x_188);
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
x_37 = x_197;
x_38 = x_191;
goto lbl_39;
}
else
{
obj* x_199; obj* x_202; 
lean::dec(x_189);
x_199 = lean::cnstr_get(x_188, 1);
lean::inc(x_199);
lean::dec(x_188);
x_202 = l_lean_ir_match__type___closed__5;
x_37 = x_202;
x_38 = x_199;
goto lbl_39;
}
}
}
else
{
obj* x_203; 
x_203 = lean::cnstr_get(x_171, 0);
lean::inc(x_203);
if (lean::obj_tag(x_203) == 0)
{
obj* x_206; obj* x_209; obj* x_211; obj* x_212; 
lean::dec(x_49);
x_206 = lean::cnstr_get(x_171, 1);
lean::inc(x_206);
lean::dec(x_171);
x_209 = lean::cnstr_get(x_203, 0);
if (lean::is_exclusive(x_203)) {
 x_211 = x_203;
} else {
 lean::inc(x_209);
 lean::dec(x_203);
 x_211 = lean::box(0);
}
if (lean::is_scalar(x_211)) {
 x_212 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_212 = x_211;
}
lean::cnstr_set(x_212, 0, x_209);
x_37 = x_212;
x_38 = x_206;
goto lbl_39;
}
else
{
obj* x_214; obj* x_217; obj* x_219; obj* x_220; 
lean::dec(x_203);
x_214 = lean::cnstr_get(x_171, 1);
lean::inc(x_214);
lean::dec(x_171);
x_217 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_3);
x_219 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_217, x_3, x_214);
x_220 = lean::cnstr_get(x_219, 0);
lean::inc(x_220);
if (lean::obj_tag(x_220) == 0)
{
obj* x_223; obj* x_226; obj* x_228; obj* x_229; 
lean::dec(x_49);
x_223 = lean::cnstr_get(x_219, 1);
lean::inc(x_223);
lean::dec(x_219);
x_226 = lean::cnstr_get(x_220, 0);
if (lean::is_exclusive(x_220)) {
 x_228 = x_220;
} else {
 lean::inc(x_226);
 lean::dec(x_220);
 x_228 = lean::box(0);
}
if (lean::is_scalar(x_228)) {
 x_229 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_229 = x_228;
}
lean::cnstr_set(x_229, 0, x_226);
x_37 = x_229;
x_38 = x_223;
goto lbl_39;
}
else
{
obj* x_231; obj* x_235; obj* x_236; 
lean::dec(x_220);
x_231 = lean::cnstr_get(x_219, 1);
lean::inc(x_231);
lean::dec(x_219);
lean::inc(x_3);
x_235 = l_lean_ir_cpp_emit__uncurry__header(x_49, x_3, x_231);
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
x_37 = x_244;
x_38 = x_238;
goto lbl_39;
}
else
{
obj* x_246; obj* x_250; obj* x_251; obj* x_253; 
lean::dec(x_236);
x_246 = lean::cnstr_get(x_235, 1);
lean::inc(x_246);
lean::dec(x_235);
lean::inc(x_3);
x_250 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_217, x_3, x_246);
x_251 = lean::cnstr_get(x_250, 0);
lean::inc(x_251);
x_253 = lean::cnstr_get(x_250, 1);
lean::inc(x_253);
lean::dec(x_250);
x_37 = x_251;
x_38 = x_253;
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
obj* x_259; obj* x_261; obj* x_262; obj* x_263; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_13);
x_259 = lean::cnstr_get(x_37, 0);
if (lean::is_exclusive(x_37)) {
 x_261 = x_37;
} else {
 lean::inc(x_259);
 lean::dec(x_37);
 x_261 = lean::box(0);
}
if (lean::is_scalar(x_261)) {
 x_262 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_262 = x_261;
}
lean::cnstr_set(x_262, 0, x_259);
x_263 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_263, 0, x_262);
lean::cnstr_set(x_263, 1, x_38);
return x_263;
}
else
{
obj* x_265; 
lean::dec(x_37);
x_265 = lean::box(0);
x_1 = x_13;
x_2 = x_265;
x_4 = x_38;
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
obj* x_15; uint8 x_17; obj* x_19; obj* x_20; 
x_15 = lean::cnstr_get(x_11, 2);
lean::inc(x_15);
x_17 = lean::unbox(x_15);
lean::inc(x_1);
x_19 = l_lean_ir_cpp_emit__type(x_17, x_1, x_2);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_25; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_11);
lean::dec(x_8);
lean::dec(x_1);
x_25 = lean::cnstr_get(x_19, 1);
lean::inc(x_25);
lean::dec(x_19);
x_28 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_30 = x_20;
} else {
 lean::inc(x_28);
 lean::dec(x_20);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_25);
return x_32;
}
else
{
obj* x_34; obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_20);
x_34 = lean::cnstr_get(x_19, 1);
lean::inc(x_34);
lean::dec(x_19);
x_37 = l_lean_ir_cpp_emit__sep__aux___main___rarg___closed__1;
lean::inc(x_1);
x_39 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_37, x_1, x_34);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_45; obj* x_48; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_11);
lean::dec(x_8);
lean::dec(x_1);
x_45 = lean::cnstr_get(x_39, 1);
lean::inc(x_45);
lean::dec(x_39);
x_48 = lean::cnstr_get(x_40, 0);
if (lean::is_exclusive(x_40)) {
 x_50 = x_40;
} else {
 lean::inc(x_48);
 lean::dec(x_40);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_45);
return x_52;
}
else
{
obj* x_54; obj* x_57; obj* x_61; obj* x_62; 
lean::dec(x_40);
x_54 = lean::cnstr_get(x_39, 1);
lean::inc(x_54);
lean::dec(x_39);
x_57 = lean::cnstr_get(x_11, 0);
lean::inc(x_57);
lean::dec(x_11);
lean::inc(x_1);
x_61 = l_lean_ir_cpp_emit__global(x_57, x_1, x_54);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
obj* x_66; obj* x_69; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_8);
lean::dec(x_1);
x_66 = lean::cnstr_get(x_61, 1);
lean::inc(x_66);
lean::dec(x_61);
x_69 = lean::cnstr_get(x_62, 0);
if (lean::is_exclusive(x_62)) {
 x_71 = x_62;
} else {
 lean::inc(x_69);
 lean::dec(x_62);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_69);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_66);
return x_73;
}
else
{
obj* x_75; obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_62);
x_75 = lean::cnstr_get(x_61, 1);
lean::inc(x_75);
lean::dec(x_61);
x_78 = l_rbnode_mfold___main___at_lean_ir_cpp_emit__used__headers___spec__1___closed__1;
lean::inc(x_1);
x_80 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_78, x_1, x_75);
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
if (lean::obj_tag(x_81) == 0)
{
obj* x_85; obj* x_88; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_8);
lean::dec(x_1);
x_85 = lean::cnstr_get(x_80, 1);
lean::inc(x_85);
lean::dec(x_80);
x_88 = lean::cnstr_get(x_81, 0);
if (lean::is_exclusive(x_81)) {
 x_90 = x_81;
} else {
 lean::inc(x_88);
 lean::dec(x_81);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_88);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_85);
return x_92;
}
else
{
obj* x_94; 
lean::dec(x_81);
x_94 = lean::cnstr_get(x_80, 1);
lean::inc(x_94);
lean::dec(x_80);
x_0 = x_8;
x_2 = x_94;
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
obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_14; 
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
if (lean::obj_tag(x_14) == 0)
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_6);
lean::dec(x_8);
lean::dec(x_1);
x_19 = lean::cnstr_get(x_13, 1);
lean::inc(x_19);
lean::dec(x_13);
x_22 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_24 = x_14;
} else {
 lean::inc(x_22);
 lean::dec(x_14);
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
lean::cnstr_set(x_26, 1, x_19);
return x_26;
}
else
{
obj* x_28; obj* x_32; obj* x_33; 
lean::dec(x_14);
x_28 = lean::cnstr_get(x_13, 1);
lean::inc(x_28);
lean::dec(x_13);
lean::inc(x_1);
x_32 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_6, x_1, x_28);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_8);
lean::dec(x_1);
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
lean::dec(x_32);
x_40 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_42 = x_33;
} else {
 lean::inc(x_40);
 lean::dec(x_33);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_40);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_37);
return x_44;
}
else
{
obj* x_46; obj* x_49; obj* x_51; obj* x_52; 
lean::dec(x_33);
x_46 = lean::cnstr_get(x_32, 1);
lean::inc(x_46);
lean::dec(x_32);
x_49 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_1);
x_51 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_49, x_1, x_46);
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_56; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_8);
lean::dec(x_1);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
lean::dec(x_51);
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
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_56);
return x_63;
}
else
{
obj* x_65; 
lean::dec(x_52);
x_65 = lean::cnstr_get(x_51, 1);
lean::inc(x_65);
lean::dec(x_51);
x_0 = x_8;
x_2 = x_65;
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
obj* x_15; obj* x_20; obj* x_21; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
lean::dec(x_11);
lean::inc(x_1);
lean::inc(x_15);
x_20 = l_lean_ir_cpp_emit__global(x_15, x_1, x_2);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_26; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_15);
lean::dec(x_8);
lean::dec(x_1);
x_26 = lean::cnstr_get(x_20, 1);
lean::inc(x_26);
lean::dec(x_20);
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
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_26);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; obj* x_41; 
lean::dec(x_21);
x_35 = lean::cnstr_get(x_20, 1);
lean::inc(x_35);
lean::dec(x_20);
x_38 = l_lean_ir_cpp_emit__infix___closed__1;
lean::inc(x_1);
x_40 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_38, x_1, x_35);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_46; obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_15);
lean::dec(x_8);
lean::dec(x_1);
x_46 = lean::cnstr_get(x_40, 1);
lean::inc(x_46);
lean::dec(x_40);
x_49 = lean::cnstr_get(x_41, 0);
if (lean::is_exclusive(x_41)) {
 x_51 = x_41;
} else {
 lean::inc(x_49);
 lean::dec(x_41);
 x_51 = lean::box(0);
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_49);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_46);
return x_53;
}
else
{
obj* x_55; obj* x_59; obj* x_60; 
lean::dec(x_41);
x_55 = lean::cnstr_get(x_40, 1);
lean::inc(x_55);
lean::dec(x_40);
lean::inc(x_1);
x_59 = l_lean_ir_cpp_emit__fnid(x_15, x_1, x_55);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
if (lean::obj_tag(x_60) == 0)
{
obj* x_64; obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_8);
lean::dec(x_1);
x_64 = lean::cnstr_get(x_59, 1);
lean::inc(x_64);
lean::dec(x_59);
x_67 = lean::cnstr_get(x_60, 0);
if (lean::is_exclusive(x_60)) {
 x_69 = x_60;
} else {
 lean::inc(x_67);
 lean::dec(x_60);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_67);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_64);
return x_71;
}
else
{
obj* x_73; obj* x_76; obj* x_78; obj* x_79; 
lean::dec(x_60);
x_73 = lean::cnstr_get(x_59, 1);
lean::inc(x_73);
lean::dec(x_59);
x_76 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_1);
x_78 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_76, x_1, x_73);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
if (lean::obj_tag(x_79) == 0)
{
obj* x_83; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_8);
lean::dec(x_1);
x_83 = lean::cnstr_get(x_78, 1);
lean::inc(x_83);
lean::dec(x_78);
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
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_83);
return x_90;
}
else
{
obj* x_92; 
lean::dec(x_79);
x_92 = lean::cnstr_get(x_78, 1);
lean::inc(x_92);
lean::dec(x_78);
x_0 = x_8;
x_2 = x_92;
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = l_lean_ir_cpp_emit__initialize__proc___closed__1;
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
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
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_6);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_lean_ir_cpp_initialize__prefix;
lean::inc(x_1);
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_1, x_19);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_34 = x_25;
} else {
 lean::inc(x_32);
 lean::dec(x_25);
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
lean::cnstr_set(x_36, 1, x_29);
return x_36;
}
else
{
obj* x_38; obj* x_41; obj* x_43; obj* x_46; obj* x_47; 
lean::dec(x_25);
x_38 = lean::cnstr_get(x_24, 1);
lean::inc(x_38);
lean::dec(x_24);
x_41 = lean::cnstr_get(x_1, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_41, 0);
lean::inc(x_43);
lean::inc(x_1);
x_46 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_43, x_1, x_38);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_52; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_41);
x_52 = lean::cnstr_get(x_46, 1);
lean::inc(x_52);
lean::dec(x_46);
x_55 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 x_57 = x_47;
} else {
 lean::inc(x_55);
 lean::dec(x_47);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_52);
return x_59;
}
else
{
obj* x_61; obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_47);
x_61 = lean::cnstr_get(x_46, 1);
lean::inc(x_61);
lean::dec(x_46);
x_64 = l_lean_ir_cpp_emit__initialize__proc___closed__2;
lean::inc(x_1);
x_66 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_64, x_1, x_61);
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_72; obj* x_75; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_41);
x_72 = lean::cnstr_get(x_66, 1);
lean::inc(x_72);
lean::dec(x_66);
x_75 = lean::cnstr_get(x_67, 0);
if (lean::is_exclusive(x_67)) {
 x_77 = x_67;
} else {
 lean::inc(x_75);
 lean::dec(x_67);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_72);
return x_79;
}
else
{
obj* x_81; obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_67);
x_81 = lean::cnstr_get(x_66, 1);
lean::inc(x_81);
lean::dec(x_66);
x_84 = l_lean_ir_cpp_emit__initialize__proc___closed__3;
lean::inc(x_1);
x_86 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_84, x_1, x_81);
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
if (lean::obj_tag(x_87) == 0)
{
obj* x_92; obj* x_95; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_41);
x_92 = lean::cnstr_get(x_86, 1);
lean::inc(x_92);
lean::dec(x_86);
x_95 = lean::cnstr_get(x_87, 0);
if (lean::is_exclusive(x_87)) {
 x_97 = x_87;
} else {
 lean::inc(x_95);
 lean::dec(x_87);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_92);
return x_99;
}
else
{
obj* x_101; obj* x_104; obj* x_106; obj* x_107; 
lean::dec(x_87);
x_101 = lean::cnstr_get(x_86, 1);
lean::inc(x_101);
lean::dec(x_86);
x_104 = l_lean_ir_cpp_emit__initialize__proc___closed__4;
lean::inc(x_1);
x_106 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_104, x_1, x_101);
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
if (lean::obj_tag(x_107) == 0)
{
obj* x_112; obj* x_115; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_41);
x_112 = lean::cnstr_get(x_106, 1);
lean::inc(x_112);
lean::dec(x_106);
x_115 = lean::cnstr_get(x_107, 0);
if (lean::is_exclusive(x_107)) {
 x_117 = x_107;
} else {
 lean::inc(x_115);
 lean::dec(x_107);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_115);
x_119 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_112);
return x_119;
}
else
{
obj* x_121; obj* x_124; obj* x_128; obj* x_129; 
lean::dec(x_107);
x_121 = lean::cnstr_get(x_106, 1);
lean::inc(x_121);
lean::dec(x_106);
x_124 = lean::cnstr_get(x_41, 1);
lean::inc(x_124);
lean::dec(x_41);
lean::inc(x_1);
x_128 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1(x_124, x_1, x_121);
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
if (lean::obj_tag(x_129) == 0)
{
obj* x_133; obj* x_136; obj* x_138; obj* x_139; obj* x_140; 
lean::dec(x_1);
lean::dec(x_0);
x_133 = lean::cnstr_get(x_128, 1);
lean::inc(x_133);
lean::dec(x_128);
x_136 = lean::cnstr_get(x_129, 0);
if (lean::is_exclusive(x_129)) {
 x_138 = x_129;
} else {
 lean::inc(x_136);
 lean::dec(x_129);
 x_138 = lean::box(0);
}
if (lean::is_scalar(x_138)) {
 x_139 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_139 = x_138;
}
lean::cnstr_set(x_139, 0, x_136);
x_140 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_133);
return x_140;
}
else
{
obj* x_142; obj* x_146; obj* x_147; 
lean::dec(x_129);
x_142 = lean::cnstr_get(x_128, 1);
lean::inc(x_142);
lean::dec(x_128);
lean::inc(x_1);
x_146 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__2(x_0, x_1, x_142);
x_147 = lean::cnstr_get(x_146, 0);
lean::inc(x_147);
if (lean::obj_tag(x_147) == 0)
{
obj* x_150; obj* x_153; obj* x_155; obj* x_156; obj* x_157; 
lean::dec(x_1);
x_150 = lean::cnstr_get(x_146, 1);
lean::inc(x_150);
lean::dec(x_146);
x_153 = lean::cnstr_get(x_147, 0);
if (lean::is_exclusive(x_147)) {
 x_155 = x_147;
} else {
 lean::inc(x_153);
 lean::dec(x_147);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
x_157 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_157, 0, x_156);
lean::cnstr_set(x_157, 1, x_150);
return x_157;
}
else
{
obj* x_159; obj* x_162; obj* x_163; 
lean::dec(x_147);
x_159 = lean::cnstr_get(x_146, 1);
lean::inc(x_159);
lean::dec(x_146);
x_162 = l_lean_ir_cpp_emit__uncurry___closed__1;
x_163 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_162, x_1, x_159);
return x_163;
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
obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_14; 
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
if (lean::obj_tag(x_14) == 0)
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_6);
lean::dec(x_8);
lean::dec(x_1);
x_19 = lean::cnstr_get(x_13, 1);
lean::inc(x_19);
lean::dec(x_13);
x_22 = lean::cnstr_get(x_14, 0);
if (lean::is_exclusive(x_14)) {
 x_24 = x_14;
} else {
 lean::inc(x_22);
 lean::dec(x_14);
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
lean::cnstr_set(x_26, 1, x_19);
return x_26;
}
else
{
obj* x_28; obj* x_32; obj* x_33; 
lean::dec(x_14);
x_28 = lean::cnstr_get(x_13, 1);
lean::inc(x_28);
lean::dec(x_13);
lean::inc(x_1);
x_32 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_6, x_1, x_28);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
if (lean::obj_tag(x_33) == 0)
{
obj* x_37; obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_8);
lean::dec(x_1);
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
lean::dec(x_32);
x_40 = lean::cnstr_get(x_33, 0);
if (lean::is_exclusive(x_33)) {
 x_42 = x_33;
} else {
 lean::inc(x_40);
 lean::dec(x_33);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_40);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_37);
return x_44;
}
else
{
obj* x_46; obj* x_49; obj* x_51; obj* x_52; 
lean::dec(x_33);
x_46 = lean::cnstr_get(x_32, 1);
lean::inc(x_46);
lean::dec(x_32);
x_49 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_1);
x_51 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_49, x_1, x_46);
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
if (lean::obj_tag(x_52) == 0)
{
obj* x_56; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_8);
lean::dec(x_1);
x_56 = lean::cnstr_get(x_51, 1);
lean::inc(x_56);
lean::dec(x_51);
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
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_56);
return x_63;
}
else
{
obj* x_65; 
lean::dec(x_52);
x_65 = lean::cnstr_get(x_51, 1);
lean::inc(x_65);
lean::dec(x_51);
x_0 = x_8;
x_2 = x_65;
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
obj* x_21; uint8 x_23; obj* x_24; obj* x_25; uint8 x_26; 
x_21 = lean::cnstr_get(x_14, 2);
lean::inc(x_21);
x_23 = lean::unbox(x_21);
x_24 = l_lean_ir_type2id___main(x_23);
x_25 = l_lean_ir_valid__assign__unop__types___closed__1;
x_26 = lean::nat_dec_eq(x_24, x_25);
lean::dec(x_24);
if (x_26 == 0)
{
obj* x_29; 
lean::dec(x_14);
x_29 = l_lean_ir_match__type___closed__5;
x_11 = x_29;
x_12 = x_2;
goto lbl_13;
}
else
{
if (x_17 == 0)
{
obj* x_31; 
lean::dec(x_14);
x_31 = l_lean_ir_match__type___closed__5;
x_11 = x_31;
x_12 = x_2;
goto lbl_13;
}
else
{
obj* x_32; 
x_32 = lean::box(0);
x_15 = x_32;
goto lbl_16;
}
}
}
lbl_13:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_35; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_8);
lean::dec(x_1);
x_35 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 x_37 = x_11;
} else {
 lean::inc(x_35);
 lean::dec(x_11);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_35);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_12);
return x_39;
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
obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_15);
x_43 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__1;
lean::inc(x_1);
x_45 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_43, x_1, x_2);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
if (lean::obj_tag(x_46) == 0)
{
obj* x_49; obj* x_52; obj* x_54; obj* x_55; 
lean::dec(x_14);
x_49 = lean::cnstr_get(x_45, 1);
lean::inc(x_49);
lean::dec(x_45);
x_52 = lean::cnstr_get(x_46, 0);
if (lean::is_exclusive(x_46)) {
 x_54 = x_46;
} else {
 lean::inc(x_52);
 lean::dec(x_46);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_52);
x_11 = x_55;
x_12 = x_49;
goto lbl_13;
}
else
{
obj* x_57; obj* x_60; obj* x_65; obj* x_66; 
lean::dec(x_46);
x_57 = lean::cnstr_get(x_45, 1);
lean::inc(x_57);
lean::dec(x_45);
x_60 = lean::cnstr_get(x_14, 0);
lean::inc(x_60);
lean::dec(x_14);
lean::inc(x_1);
lean::inc(x_60);
x_65 = l_lean_ir_cpp_emit__global(x_60, x_1, x_57);
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
if (lean::obj_tag(x_66) == 0)
{
obj* x_69; obj* x_72; obj* x_74; obj* x_75; 
lean::dec(x_60);
x_69 = lean::cnstr_get(x_65, 1);
lean::inc(x_69);
lean::dec(x_65);
x_72 = lean::cnstr_get(x_66, 0);
if (lean::is_exclusive(x_66)) {
 x_74 = x_66;
} else {
 lean::inc(x_72);
 lean::dec(x_66);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_72);
x_11 = x_75;
x_12 = x_69;
goto lbl_13;
}
else
{
obj* x_77; obj* x_80; obj* x_82; obj* x_83; 
lean::dec(x_66);
x_77 = lean::cnstr_get(x_65, 1);
lean::inc(x_77);
lean::dec(x_65);
x_80 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__2;
lean::inc(x_1);
x_82 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_80, x_1, x_77);
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
if (lean::obj_tag(x_83) == 0)
{
obj* x_86; obj* x_89; obj* x_91; obj* x_92; 
lean::dec(x_60);
x_86 = lean::cnstr_get(x_82, 1);
lean::inc(x_86);
lean::dec(x_82);
x_89 = lean::cnstr_get(x_83, 0);
if (lean::is_exclusive(x_83)) {
 x_91 = x_83;
} else {
 lean::inc(x_89);
 lean::dec(x_83);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_89);
x_11 = x_92;
x_12 = x_86;
goto lbl_13;
}
else
{
obj* x_94; obj* x_98; obj* x_99; 
lean::dec(x_83);
x_94 = lean::cnstr_get(x_82, 1);
lean::inc(x_94);
lean::dec(x_82);
lean::inc(x_1);
x_98 = l_lean_ir_cpp_emit__global(x_60, x_1, x_94);
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
if (lean::obj_tag(x_99) == 0)
{
obj* x_101; obj* x_104; obj* x_106; obj* x_107; 
x_101 = lean::cnstr_get(x_98, 1);
lean::inc(x_101);
lean::dec(x_98);
x_104 = lean::cnstr_get(x_99, 0);
if (lean::is_exclusive(x_99)) {
 x_106 = x_99;
} else {
 lean::inc(x_104);
 lean::dec(x_99);
 x_106 = lean::box(0);
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_104);
x_11 = x_107;
x_12 = x_101;
goto lbl_13;
}
else
{
obj* x_109; obj* x_112; obj* x_114; obj* x_115; obj* x_117; 
lean::dec(x_99);
x_109 = lean::cnstr_get(x_98, 1);
lean::inc(x_109);
lean::dec(x_98);
x_112 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2___closed__3;
lean::inc(x_1);
x_114 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_112, x_1, x_109);
x_115 = lean::cnstr_get(x_114, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_114, 1);
lean::inc(x_117);
lean::dec(x_114);
x_11 = x_115;
x_12 = x_117;
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
obj* x_3; obj* x_5; obj* x_6; 
x_3 = l_lean_ir_cpp_emit__initialize__proc___closed__1;
lean::inc(x_1);
x_5 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_3, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
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
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_10);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; 
lean::dec(x_6);
x_19 = lean::cnstr_get(x_5, 1);
lean::inc(x_19);
lean::dec(x_5);
x_22 = l_lean_ir_cpp_finalize__prefix;
lean::inc(x_1);
x_24 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_22, x_1, x_19);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_25, 0);
if (lean::is_exclusive(x_25)) {
 x_34 = x_25;
} else {
 lean::inc(x_32);
 lean::dec(x_25);
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
lean::cnstr_set(x_36, 1, x_29);
return x_36;
}
else
{
obj* x_38; obj* x_41; obj* x_43; obj* x_46; obj* x_47; 
lean::dec(x_25);
x_38 = lean::cnstr_get(x_24, 1);
lean::inc(x_38);
lean::dec(x_24);
x_41 = lean::cnstr_get(x_1, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_41, 0);
lean::inc(x_43);
lean::inc(x_1);
x_46 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_43, x_1, x_38);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_52; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_41);
x_52 = lean::cnstr_get(x_46, 1);
lean::inc(x_52);
lean::dec(x_46);
x_55 = lean::cnstr_get(x_47, 0);
if (lean::is_exclusive(x_47)) {
 x_57 = x_47;
} else {
 lean::inc(x_55);
 lean::dec(x_47);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_52);
return x_59;
}
else
{
obj* x_61; obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_47);
x_61 = lean::cnstr_get(x_46, 1);
lean::inc(x_61);
lean::dec(x_46);
x_64 = l_lean_ir_cpp_emit__initialize__proc___closed__2;
lean::inc(x_1);
x_66 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_64, x_1, x_61);
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_72; obj* x_75; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_41);
x_72 = lean::cnstr_get(x_66, 1);
lean::inc(x_72);
lean::dec(x_66);
x_75 = lean::cnstr_get(x_67, 0);
if (lean::is_exclusive(x_67)) {
 x_77 = x_67;
} else {
 lean::inc(x_75);
 lean::dec(x_67);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_75);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_72);
return x_79;
}
else
{
obj* x_81; obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_67);
x_81 = lean::cnstr_get(x_66, 1);
lean::inc(x_81);
lean::dec(x_66);
x_84 = l_lean_ir_cpp_emit__finalize__proc___closed__1;
lean::inc(x_1);
x_86 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_84, x_1, x_81);
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
if (lean::obj_tag(x_87) == 0)
{
obj* x_92; obj* x_95; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_41);
x_92 = lean::cnstr_get(x_86, 1);
lean::inc(x_92);
lean::dec(x_86);
x_95 = lean::cnstr_get(x_87, 0);
if (lean::is_exclusive(x_87)) {
 x_97 = x_87;
} else {
 lean::inc(x_95);
 lean::dec(x_87);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_95);
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_92);
return x_99;
}
else
{
obj* x_101; obj* x_104; obj* x_106; obj* x_107; 
lean::dec(x_87);
x_101 = lean::cnstr_get(x_86, 1);
lean::inc(x_101);
lean::dec(x_86);
x_104 = l_lean_ir_cpp_emit__finalize__proc___closed__2;
lean::inc(x_1);
x_106 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_104, x_1, x_101);
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
if (lean::obj_tag(x_107) == 0)
{
obj* x_112; obj* x_115; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_41);
x_112 = lean::cnstr_get(x_106, 1);
lean::inc(x_112);
lean::dec(x_106);
x_115 = lean::cnstr_get(x_107, 0);
if (lean::is_exclusive(x_107)) {
 x_117 = x_107;
} else {
 lean::inc(x_115);
 lean::dec(x_107);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_115);
x_119 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_112);
return x_119;
}
else
{
obj* x_121; obj* x_124; obj* x_128; obj* x_129; 
lean::dec(x_107);
x_121 = lean::cnstr_get(x_106, 1);
lean::inc(x_121);
lean::dec(x_106);
x_124 = lean::cnstr_get(x_41, 1);
lean::inc(x_124);
lean::dec(x_41);
lean::inc(x_1);
x_128 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__1(x_124, x_1, x_121);
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
if (lean::obj_tag(x_129) == 0)
{
obj* x_133; obj* x_136; obj* x_138; obj* x_139; obj* x_140; 
lean::dec(x_1);
lean::dec(x_0);
x_133 = lean::cnstr_get(x_128, 1);
lean::inc(x_133);
lean::dec(x_128);
x_136 = lean::cnstr_get(x_129, 0);
if (lean::is_exclusive(x_129)) {
 x_138 = x_129;
} else {
 lean::inc(x_136);
 lean::dec(x_129);
 x_138 = lean::box(0);
}
if (lean::is_scalar(x_138)) {
 x_139 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_139 = x_138;
}
lean::cnstr_set(x_139, 0, x_136);
x_140 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_133);
return x_140;
}
else
{
obj* x_142; obj* x_146; obj* x_147; 
lean::dec(x_129);
x_142 = lean::cnstr_get(x_128, 1);
lean::inc(x_142);
lean::dec(x_128);
lean::inc(x_1);
x_146 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__finalize__proc___spec__2(x_0, x_1, x_142);
x_147 = lean::cnstr_get(x_146, 0);
lean::inc(x_147);
if (lean::obj_tag(x_147) == 0)
{
obj* x_150; obj* x_153; obj* x_155; obj* x_156; obj* x_157; 
lean::dec(x_1);
x_150 = lean::cnstr_get(x_146, 1);
lean::inc(x_150);
lean::dec(x_146);
x_153 = lean::cnstr_get(x_147, 0);
if (lean::is_exclusive(x_147)) {
 x_155 = x_147;
} else {
 lean::inc(x_153);
 lean::dec(x_147);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
x_157 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_157, 0, x_156);
lean::cnstr_set(x_157, 1, x_150);
return x_157;
}
else
{
obj* x_159; obj* x_162; obj* x_163; 
lean::dec(x_147);
x_159 = lean::cnstr_get(x_146, 1);
lean::inc(x_159);
lean::dec(x_146);
x_162 = l_lean_ir_cpp_emit__uncurry___closed__1;
x_163 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_162, x_1, x_159);
return x_163;
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
obj* x_30; obj* x_33; obj* x_34; obj* x_36; obj* x_37; uint8 x_38; obj* x_40; uint8 x_43; obj* x_44; obj* x_45; uint8 x_46; obj* x_48; uint8 x_51; 
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
x_44 = l_lean_ir_type2id___main(x_43);
x_45 = l_lean_ir_valid__assign__unop__types___closed__4;
x_46 = lean::nat_dec_eq(x_44, x_45);
lean::dec(x_44);
x_48 = lean::cnstr_get(x_2, 0);
lean::inc(x_48);
lean::dec(x_2);
if (x_46 == 0)
{
uint8 x_53; 
x_53 = 0;
x_51 = x_53;
goto lbl_52;
}
else
{
uint8 x_54; 
x_54 = 1;
x_51 = x_54;
goto lbl_52;
}
lbl_52:
{
obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_61; obj* x_62; 
if (x_38 == 0)
{
obj* x_65; obj* x_66; uint8 x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::inc(x_10);
x_65 = l_lean_ir_id_to__string___main(x_10);
x_66 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
x_67 = 0;
x_68 = l_lean_ir_cpp_emit__main__proc___closed__5;
x_69 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_66);
lean::cnstr_set_scalar(x_69, sizeof(void*)*2, x_67);
x_70 = x_69;
x_71 = l_lean_ir_cpp_emit__main__proc___closed__6;
x_72 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set(x_72, 1, x_71);
lean::cnstr_set_scalar(x_72, sizeof(void*)*2, x_67);
x_73 = x_72;
x_74 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_74, 0, x_73);
x_61 = x_74;
x_62 = x_1;
goto lbl_63;
}
else
{
if (x_51 == 0)
{
obj* x_76; obj* x_77; uint8 x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
lean::inc(x_10);
x_76 = l_lean_ir_id_to__string___main(x_10);
x_77 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_77, 0, x_76);
x_78 = 0;
x_79 = l_lean_ir_cpp_emit__main__proc___closed__5;
x_80 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_77);
lean::cnstr_set_scalar(x_80, sizeof(void*)*2, x_78);
x_81 = x_80;
x_82 = l_lean_ir_cpp_emit__main__proc___closed__7;
x_83 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set(x_83, 1, x_82);
lean::cnstr_set_scalar(x_83, sizeof(void*)*2, x_78);
x_84 = x_83;
x_85 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_85, 0, x_84);
x_61 = x_85;
x_62 = x_1;
goto lbl_63;
}
else
{
obj* x_86; 
x_86 = l_lean_ir_match__type___closed__5;
x_61 = x_86;
x_62 = x_1;
goto lbl_63;
}
}
lbl_57:
{
if (lean::obj_tag(x_55) == 0)
{
obj* x_89; obj* x_91; obj* x_92; obj* x_93; 
lean::dec(x_0);
lean::dec(x_48);
x_89 = lean::cnstr_get(x_55, 0);
if (lean::is_exclusive(x_55)) {
 x_91 = x_55;
} else {
 lean::inc(x_89);
 lean::dec(x_55);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_89);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_56);
return x_93;
}
else
{
obj* x_95; obj* x_97; obj* x_98; 
lean::dec(x_55);
x_95 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_0);
x_97 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_95, x_0, x_56);
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
if (lean::obj_tag(x_98) == 0)
{
obj* x_102; obj* x_105; obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_0);
lean::dec(x_48);
x_102 = lean::cnstr_get(x_97, 1);
lean::inc(x_102);
lean::dec(x_97);
x_105 = lean::cnstr_get(x_98, 0);
if (lean::is_exclusive(x_98)) {
 x_107 = x_98;
} else {
 lean::inc(x_105);
 lean::dec(x_98);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_105);
x_109 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_102);
return x_109;
}
else
{
obj* x_111; obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_98);
x_111 = lean::cnstr_get(x_97, 1);
lean::inc(x_111);
lean::dec(x_97);
x_114 = l_lean_ir_cpp_finalize__prefix;
lean::inc(x_0);
x_116 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_114, x_0, x_111);
x_117 = lean::cnstr_get(x_116, 0);
lean::inc(x_117);
if (lean::obj_tag(x_117) == 0)
{
obj* x_121; obj* x_124; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_0);
lean::dec(x_48);
x_121 = lean::cnstr_get(x_116, 1);
lean::inc(x_121);
lean::dec(x_116);
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
x_128 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_121);
return x_128;
}
else
{
obj* x_130; obj* x_134; obj* x_135; 
lean::dec(x_117);
x_130 = lean::cnstr_get(x_116, 1);
lean::inc(x_130);
lean::dec(x_116);
lean::inc(x_0);
x_134 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_48, x_0, x_130);
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
if (lean::obj_tag(x_135) == 0)
{
obj* x_138; obj* x_141; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_0);
x_138 = lean::cnstr_get(x_134, 1);
lean::inc(x_138);
lean::dec(x_134);
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
x_145 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_138);
return x_145;
}
else
{
obj* x_147; obj* x_151; obj* x_152; 
lean::dec(x_135);
x_147 = lean::cnstr_get(x_134, 1);
lean::inc(x_147);
lean::dec(x_134);
lean::inc(x_0);
x_151 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_95, x_0, x_147);
x_152 = lean::cnstr_get(x_151, 0);
lean::inc(x_152);
if (lean::obj_tag(x_152) == 0)
{
obj* x_155; obj* x_158; obj* x_160; obj* x_161; obj* x_162; 
lean::dec(x_0);
x_155 = lean::cnstr_get(x_151, 1);
lean::inc(x_155);
lean::dec(x_151);
x_158 = lean::cnstr_get(x_152, 0);
if (lean::is_exclusive(x_152)) {
 x_160 = x_152;
} else {
 lean::inc(x_158);
 lean::dec(x_152);
 x_160 = lean::box(0);
}
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_158);
x_162 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_162, 0, x_161);
lean::cnstr_set(x_162, 1, x_155);
return x_162;
}
else
{
obj* x_164; obj* x_167; obj* x_168; 
lean::dec(x_152);
x_164 = lean::cnstr_get(x_151, 1);
lean::inc(x_164);
lean::dec(x_151);
x_167 = l_lean_ir_cpp_emit__main__proc___closed__2;
x_168 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_167, x_0, x_164);
return x_168;
}
}
}
}
}
}
lbl_60:
{
if (lean::obj_tag(x_58) == 0)
{
obj* x_170; obj* x_172; obj* x_173; 
lean::dec(x_10);
x_170 = lean::cnstr_get(x_58, 0);
if (lean::is_exclusive(x_58)) {
 x_172 = x_58;
} else {
 lean::inc(x_170);
 lean::dec(x_58);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_170);
x_55 = x_173;
x_56 = x_59;
goto lbl_57;
}
else
{
obj* x_177; obj* x_178; 
lean::dec(x_58);
lean::inc(x_0);
lean::inc(x_48);
x_177 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_48, x_0, x_59);
x_178 = lean::cnstr_get(x_177, 0);
lean::inc(x_178);
if (lean::obj_tag(x_178) == 0)
{
obj* x_181; obj* x_184; obj* x_186; obj* x_187; 
lean::dec(x_10);
x_181 = lean::cnstr_get(x_177, 1);
lean::inc(x_181);
lean::dec(x_177);
x_184 = lean::cnstr_get(x_178, 0);
if (lean::is_exclusive(x_178)) {
 x_186 = x_178;
} else {
 lean::inc(x_184);
 lean::dec(x_178);
 x_186 = lean::box(0);
}
if (lean::is_scalar(x_186)) {
 x_187 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_187 = x_186;
}
lean::cnstr_set(x_187, 0, x_184);
x_55 = x_187;
x_56 = x_181;
goto lbl_57;
}
else
{
obj* x_189; obj* x_192; obj* x_194; obj* x_195; 
lean::dec(x_178);
x_189 = lean::cnstr_get(x_177, 1);
lean::inc(x_189);
lean::dec(x_177);
x_192 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__initialize__proc___spec__1___closed__1;
lean::inc(x_0);
x_194 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_192, x_0, x_189);
x_195 = lean::cnstr_get(x_194, 0);
lean::inc(x_195);
if (lean::obj_tag(x_195) == 0)
{
obj* x_198; obj* x_201; obj* x_203; obj* x_204; 
lean::dec(x_10);
x_198 = lean::cnstr_get(x_194, 1);
lean::inc(x_198);
lean::dec(x_194);
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
x_55 = x_204;
x_56 = x_198;
goto lbl_57;
}
else
{
obj* x_206; obj* x_209; obj* x_211; obj* x_212; 
lean::dec(x_195);
x_206 = lean::cnstr_get(x_194, 1);
lean::inc(x_206);
lean::dec(x_194);
x_209 = l_lean_ir_cpp_emit__main__proc___closed__3;
lean::inc(x_0);
x_211 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_209, x_0, x_206);
x_212 = lean::cnstr_get(x_211, 0);
lean::inc(x_212);
if (lean::obj_tag(x_212) == 0)
{
obj* x_215; obj* x_218; obj* x_220; obj* x_221; 
lean::dec(x_10);
x_215 = lean::cnstr_get(x_211, 1);
lean::inc(x_215);
lean::dec(x_211);
x_218 = lean::cnstr_get(x_212, 0);
if (lean::is_exclusive(x_212)) {
 x_220 = x_212;
} else {
 lean::inc(x_218);
 lean::dec(x_212);
 x_220 = lean::box(0);
}
if (lean::is_scalar(x_220)) {
 x_221 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_221 = x_220;
}
lean::cnstr_set(x_221, 0, x_218);
x_55 = x_221;
x_56 = x_215;
goto lbl_57;
}
else
{
obj* x_223; obj* x_227; obj* x_228; obj* x_230; 
lean::dec(x_212);
x_223 = lean::cnstr_get(x_211, 1);
lean::inc(x_223);
lean::dec(x_211);
lean::inc(x_0);
x_227 = l_lean_ir_cpp_emit__fnid(x_10, x_0, x_223);
x_228 = lean::cnstr_get(x_227, 0);
lean::inc(x_228);
x_230 = lean::cnstr_get(x_227, 1);
lean::inc(x_230);
lean::dec(x_227);
x_55 = x_228;
x_56 = x_230;
goto lbl_57;
}
}
}
}
}
lbl_63:
{
if (lean::obj_tag(x_61) == 0)
{
obj* x_233; obj* x_235; obj* x_236; 
x_233 = lean::cnstr_get(x_61, 0);
if (lean::is_exclusive(x_61)) {
 x_235 = x_61;
} else {
 lean::inc(x_233);
 lean::dec(x_61);
 x_235 = lean::box(0);
}
if (lean::is_scalar(x_235)) {
 x_236 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_236 = x_235;
}
lean::cnstr_set(x_236, 0, x_233);
x_58 = x_236;
x_59 = x_62;
goto lbl_60;
}
else
{
obj* x_238; obj* x_240; obj* x_241; 
lean::dec(x_61);
x_238 = l_lean_ir_cpp_emit__main__proc___closed__4;
lean::inc(x_0);
x_240 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_238, x_0, x_62);
x_241 = lean::cnstr_get(x_240, 0);
lean::inc(x_241);
if (lean::obj_tag(x_241) == 0)
{
obj* x_243; obj* x_246; obj* x_248; obj* x_249; 
x_243 = lean::cnstr_get(x_240, 1);
lean::inc(x_243);
lean::dec(x_240);
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
x_58 = x_249;
x_59 = x_243;
goto lbl_60;
}
else
{
obj* x_251; obj* x_254; obj* x_256; obj* x_257; obj* x_259; 
lean::dec(x_241);
x_251 = lean::cnstr_get(x_240, 1);
lean::inc(x_251);
lean::dec(x_240);
x_254 = l_lean_ir_cpp_initialize__prefix;
lean::inc(x_0);
x_256 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_254, x_0, x_251);
x_257 = lean::cnstr_get(x_256, 0);
lean::inc(x_257);
x_259 = lean::cnstr_get(x_256, 1);
lean::inc(x_259);
lean::dec(x_256);
x_58 = x_257;
x_59 = x_259;
goto lbl_60;
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
obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
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
x_24 = lean::alloc_cnstr(0, 2, 0);
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
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_14; obj* x_15; 
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
x_9 = x_23;
x_10 = x_17;
goto lbl_11;
}
else
{
obj* x_25; obj* x_28; obj* x_30; obj* x_31; 
lean::dec(x_15);
x_25 = lean::cnstr_get(x_14, 1);
lean::inc(x_25);
lean::dec(x_14);
x_28 = l_lean_ir_extract__cpp___closed__1;
lean::inc(x_8);
x_30 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_28, x_8, x_25);
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
x_9 = x_39;
x_10 = x_33;
goto lbl_11;
}
else
{
obj* x_41; obj* x_44; obj* x_46; obj* x_47; obj* x_49; 
lean::dec(x_31);
x_41 = lean::cnstr_get(x_30, 1);
lean::inc(x_41);
lean::dec(x_30);
x_44 = l_lean_ir_extract__cpp___closed__2;
lean::inc(x_8);
x_46 = l_lean_ir_cpp_emit___at_lean_ir_cpp_emit__line___spec__1(x_44, x_8, x_41);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
x_9 = x_47;
x_10 = x_49;
goto lbl_11;
}
}
lbl_11:
{
if (lean::obj_tag(x_9) == 0)
{
obj* x_55; obj* x_57; obj* x_58; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_10);
x_55 = lean::cnstr_get(x_9, 0);
if (lean::is_exclusive(x_9)) {
 x_57 = x_9;
} else {
 lean::inc(x_55);
 lean::dec(x_9);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
return x_58;
}
else
{
obj* x_62; obj* x_63; 
lean::dec(x_9);
lean::inc(x_8);
lean::inc(x_0);
x_62 = l_list_mmap_x_27___main___at_lean_ir_cpp_emit__global__var__decls___spec__1(x_0, x_8, x_10);
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
if (lean::obj_tag(x_63) == 0)
{
obj* x_68; obj* x_70; obj* x_71; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_62);
x_68 = lean::cnstr_get(x_63, 0);
if (lean::is_exclusive(x_63)) {
 x_70 = x_63;
} else {
 lean::inc(x_68);
 lean::dec(x_63);
 x_70 = lean::box(0);
}
if (lean::is_scalar(x_70)) {
 x_71 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_71 = x_70;
}
lean::cnstr_set(x_71, 0, x_68);
return x_71;
}
else
{
obj* x_73; obj* x_78; obj* x_79; 
lean::dec(x_63);
x_73 = lean::cnstr_get(x_62, 1);
lean::inc(x_73);
lean::dec(x_62);
lean::inc(x_8);
lean::inc(x_0);
x_78 = l_lean_ir_cpp_emit__initialize__proc(x_0, x_8, x_73);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
if (lean::obj_tag(x_79) == 0)
{
obj* x_84; obj* x_86; obj* x_87; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_78);
x_84 = lean::cnstr_get(x_79, 0);
if (lean::is_exclusive(x_79)) {
 x_86 = x_79;
} else {
 lean::inc(x_84);
 lean::dec(x_79);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_84);
return x_87;
}
else
{
obj* x_89; obj* x_94; obj* x_95; 
lean::dec(x_79);
x_89 = lean::cnstr_get(x_78, 1);
lean::inc(x_89);
lean::dec(x_78);
lean::inc(x_8);
lean::inc(x_0);
x_94 = l_lean_ir_cpp_emit__finalize__proc(x_0, x_8, x_89);
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
if (lean::obj_tag(x_95) == 0)
{
obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_8);
lean::dec(x_0);
lean::dec(x_94);
x_100 = lean::cnstr_get(x_95, 0);
if (lean::is_exclusive(x_95)) {
 x_102 = x_95;
} else {
 lean::inc(x_100);
 lean::dec(x_95);
 x_102 = lean::box(0);
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_100);
return x_103;
}
else
{
obj* x_105; obj* x_109; obj* x_110; 
lean::dec(x_95);
x_105 = lean::cnstr_get(x_94, 1);
lean::inc(x_105);
lean::dec(x_94);
lean::inc(x_8);
x_109 = l_list_mmap_x_27___main___at_lean_ir_extract__cpp___spec__1(x_0, x_8, x_105);
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
if (lean::obj_tag(x_110) == 0)
{
obj* x_114; obj* x_116; obj* x_117; 
lean::dec(x_8);
lean::dec(x_109);
x_114 = lean::cnstr_get(x_110, 0);
if (lean::is_exclusive(x_110)) {
 x_116 = x_110;
} else {
 lean::inc(x_114);
 lean::dec(x_110);
 x_116 = lean::box(0);
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_114);
return x_117;
}
else
{
obj* x_119; obj* x_122; obj* x_123; 
lean::dec(x_110);
x_119 = lean::cnstr_get(x_109, 1);
lean::inc(x_119);
lean::dec(x_109);
x_122 = l_lean_ir_cpp_emit__main__proc(x_8, x_119);
x_123 = lean::cnstr_get(x_122, 0);
lean::inc(x_123);
if (lean::obj_tag(x_123) == 0)
{
obj* x_126; obj* x_128; obj* x_129; 
lean::dec(x_122);
x_126 = lean::cnstr_get(x_123, 0);
if (lean::is_exclusive(x_123)) {
 x_128 = x_123;
} else {
 lean::inc(x_126);
 lean::dec(x_123);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_126);
return x_129;
}
else
{
obj* x_130; obj* x_131; obj* x_134; 
if (lean::is_exclusive(x_123)) {
 lean::cnstr_release(x_123, 0);
 x_130 = x_123;
} else {
 lean::dec(x_123);
 x_130 = lean::box(0);
}
x_131 = lean::cnstr_get(x_122, 1);
lean::inc(x_131);
lean::dec(x_122);
if (lean::is_scalar(x_130)) {
 x_134 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_134 = x_130;
}
lean::cnstr_set(x_134, 0, x_131);
return x_134;
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
