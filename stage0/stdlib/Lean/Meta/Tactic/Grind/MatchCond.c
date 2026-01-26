// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.MatchCond
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind import Init.Simproc import Lean.Meta.Tactic.Contradiction import Lean.Meta.Tactic.Grind.ProveEq import Lean.Meta.Tactic.Grind.PropagatorAttr
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3_value;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ty"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 30, 115, 12, 44, 231, 45, 94)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed(lean_object**);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0;
static const lean_string_object l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "MatchCond"};
static const lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__3_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__3_value),LEAN_SCALAR_PTR_LITERAL(109, 233, 187, 249, 156, 65, 204, 232)}};
static const lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0_value;
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__1;
lean_object* l_Lean_Meta_Grind_getRootENode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_normLitValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1_value;
static lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__0_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__1_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchCond"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__2_value;
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__3_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__3_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 170, 56, 23, 185, 62, 169, 45)}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__3_value;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "satifised"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__4 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__4_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__5;
static const lean_string_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "\nthe following equality is false"};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__6 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__6_value;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__7;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "found term that has not been internalized"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "\nwhile trying to construct a proof for `MatchCond`"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "go\?: "};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4_value;
static lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_hasSameType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_heq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getRootENode_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = ">>> "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___closed__0_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object**);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__1 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__2 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__2_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__3 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__3_value;
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__4 = (const lean_object*)&l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLevelMVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static size_t l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableLevelMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.MetavarContext"};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__0 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__0_value;
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.isLevelMVarAssignable"};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__1 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__1_value;
static const lean_string_object l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "unknown universe metavariable"};
static const lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__2 = (const lean_object*)&l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__2_value;
static lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =\?= "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__1_value;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isDefEqD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_proveEq_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_proveHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg___boxed(lean_object**);
static const lean_string_object l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__0_value;
static lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1;
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_tryToProveFalse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "proveFalse"};
static const lean_object* l_Lean_Meta_Grind_tryToProveFalse___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_tryToProveFalse___closed__0_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_tryToProveFalse___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_tryToProveFalse___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_tryToProveFalse___closed__1_value_aux_0),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_tryToProveFalse___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_tryToProveFalse___closed__1_value_aux_1),((lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(181, 170, 56, 23, 185, 62, 169, 45)}};
static const lean_ctor_object l_Lean_Meta_Grind_tryToProveFalse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_tryToProveFalse___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_tryToProveFalse___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 57, 131, 114, 246, 81, 253, 136)}};
static const lean_object* l_Lean_Meta_Grind_tryToProveFalse___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_tryToProveFalse___closed__1_value;
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_propagateMatchCondUp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "failed to construct proof for"};
static const lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_propagateMatchCondUp___closed__0_value;
static lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___closed__1;
static const lean_string_object l_Lean_Meta_Grind_propagateMatchCondUp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "visiting"};
static const lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_propagateMatchCondUp___closed__2_value;
static lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___closed__3;
lean_object* l_Lean_Meta_mkEqTrueCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
x_10 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_11 = l_Lean_Expr_isApp(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_13);
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_10);
x_15 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1));
x_16 = l_Lean_Expr_isConstOf(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec_ref(x_9);
x_17 = l_Lean_Expr_isApp(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_5);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_21 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3));
x_22 = l_Lean_Expr_isConstOf(x_20, x_21);
lean_dec_ref(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec_ref(x_19);
lean_dec_ref(x_13);
lean_dec_ref(x_5);
x_23 = lean_box(0);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_5);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_4 = x_2;
} else {
 lean_dec_ref(x_2);
 x_4 = lean_box(0);
}
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 7)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_8 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_9);
lean_dec_ref(x_5);
x_15 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_8);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_dec(x_21);
x_22 = l_Lean_Expr_hasLooseBVars(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_ctor_set(x_17, 1, x_18);
x_23 = lean_array_push(x_6, x_17);
x_10 = x_23;
goto block_14;
}
else
{
lean_free_object(x_17);
lean_dec(x_20);
lean_dec(x_18);
x_10 = x_6;
goto block_14;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l_Lean_Expr_hasLooseBVars(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_18);
x_27 = lean_array_push(x_6, x_26);
x_10 = x_27;
goto block_14;
}
else
{
lean_dec(x_24);
lean_dec(x_18);
x_10 = x_6;
goto block_14;
}
}
}
else
{
lean_dec(x_15);
x_10 = x_6;
goto block_14;
}
block_14:
{
lean_object* x_11; lean_object* x_12; 
if (lean_is_scalar(x_7)) {
 x_11 = lean_alloc_ctor(0, 2, 0);
} else {
 x_11 = x_7;
}
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_1);
if (lean_is_scalar(x_4)) {
 x_12 = lean_alloc_ctor(0, 2, 0);
} else {
 x_12 = x_4;
}
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_2 = x_12;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_3, 1);
x_30 = lean_ctor_get(x_3, 0);
lean_dec(x_30);
lean_inc(x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_29);
if (lean_is_scalar(x_4)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_4;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
lean_dec(x_3);
lean_inc(x_33);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_33);
if (lean_is_scalar(x_4)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_4;
}
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss_spec__0(x_3, x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec_ref(x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__2));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(22u);
x_4 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_cleanupAnnotations(x_1);
x_5 = l_Lean_Expr_isApp(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_7);
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_4);
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_11);
x_12 = l_Lean_Expr_appFnCleanup___redArg(x_8);
x_13 = l_Lean_Expr_isApp(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_15);
x_16 = l_Lean_Expr_appFnCleanup___redArg(x_12);
x_17 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__1));
x_18 = l_Lean_Expr_isConstOf(x_16, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_isApp(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_26; uint8_t x_27; 
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_26 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f___closed__3));
x_27 = l_Lean_Expr_isConstOf(x_21, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec_ref(x_21);
lean_dec_ref(x_15);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
x_28 = lean_box(0);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l_Lean_Expr_hasLooseBVars(x_15);
lean_dec_ref(x_15);
if (x_29 == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3;
x_31 = l_panic___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f_spec__0(x_30);
x_22 = x_31;
goto block_25;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_3, 0);
lean_inc(x_32);
lean_dec_ref(x_3);
x_22 = x_32;
goto block_25;
}
}
else
{
lean_object* x_33; 
lean_dec_ref(x_21);
lean_dec_ref(x_11);
lean_dec_ref(x_7);
lean_dec(x_3);
lean_dec_ref(x_2);
x_33 = lean_box(0);
return x_33;
}
}
block_25:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_mkApp4(x_21, x_22, x_2, x_11, x_7);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_3);
x_34 = l_Lean_Expr_hasLooseBVars(x_11);
lean_dec_ref(x_11);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_mkApp3(x_16, x_15, x_2, x_7);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
x_37 = lean_box(0);
return x_37;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_4, x_9);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget_borrowed(x_1, x_4);
x_12 = lean_box(0);
x_13 = lean_array_get_borrowed(x_12, x_2, x_4);
lean_inc(x_13);
lean_inc(x_11);
lean_inc_ref(x_6);
x_14 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f(x_6, x_11, x_13);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; size_t x_24; size_t x_25; uint8_t x_26; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_4, x_16);
lean_inc_ref(x_7);
x_18 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(x_1, x_2, x_7, x_17);
lean_dec(x_17);
x_24 = lean_ptr_addr(x_6);
x_25 = lean_ptr_addr(x_15);
x_26 = lean_usize_dec_eq(x_24, x_25);
if (x_26 == 0)
{
x_19 = x_26;
goto block_23;
}
else
{
size_t x_27; size_t x_28; uint8_t x_29; 
x_27 = lean_ptr_addr(x_7);
x_28 = lean_ptr_addr(x_18);
x_29 = lean_usize_dec_eq(x_27, x_28);
x_19 = x_29;
goto block_23;
}
block_23:
{
if (x_19 == 0)
{
lean_object* x_20; 
lean_inc(x_5);
lean_dec_ref(x_3);
x_20 = l_Lean_Expr_forallE___override(x_5, x_15, x_18, x_8);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = l_Lean_instBEqBinderInfo_beq(x_8, x_8);
if (x_21 == 0)
{
lean_object* x_22; 
lean_inc(x_5);
lean_dec_ref(x_3);
x_22 = l_Lean_Expr_forallE___override(x_5, x_15, x_18, x_8);
return x_22;
}
else
{
lean_dec_ref(x_18);
lean_dec(x_15);
return x_3;
}
}
}
}
else
{
lean_object* x_30; uint8_t x_31; size_t x_36; uint8_t x_37; 
lean_dec(x_14);
lean_inc_ref(x_7);
x_30 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(x_1, x_2, x_7, x_4);
x_36 = lean_ptr_addr(x_6);
x_37 = lean_usize_dec_eq(x_36, x_36);
if (x_37 == 0)
{
x_31 = x_37;
goto block_35;
}
else
{
size_t x_38; size_t x_39; uint8_t x_40; 
x_38 = lean_ptr_addr(x_7);
x_39 = lean_ptr_addr(x_30);
x_40 = lean_usize_dec_eq(x_38, x_39);
x_31 = x_40;
goto block_35;
}
block_35:
{
if (x_31 == 0)
{
lean_object* x_32; 
lean_inc_ref(x_6);
lean_inc(x_5);
lean_dec_ref(x_3);
x_32 = l_Lean_Expr_forallE___override(x_5, x_6, x_30, x_8);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = l_Lean_instBEqBinderInfo_beq(x_8, x_8);
if (x_33 == 0)
{
lean_object* x_34; 
lean_inc_ref(x_6);
lean_inc(x_5);
lean_dec_ref(x_3);
x_34 = l_Lean_Expr_forallE___override(x_5, x_6, x_30, x_8);
return x_34;
}
else
{
lean_dec_ref(x_30);
return x_3;
}
}
}
}
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = lean_apply_12(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, lean_box(0));
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___lam__0___boxed), 13, 7);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_6);
lean_closure_set(x_17, 2, x_7);
lean_closure_set(x_17, 3, x_8);
lean_closure_set(x_17, 4, x_9);
lean_closure_set(x_17, 5, x_10);
lean_closure_set(x_17, 6, x_11);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_17, x_5, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_2);
x_18 = lean_unbox(x_5);
x_19 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(x_1, x_17, x_3, x_4, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = 0;
x_17 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(x_1, x_15, x_2, x_3, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
lean_object* x_22; 
x_22 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_22;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
lean_inc_ref(x_9);
x_23 = lean_array_push(x_2, x_9);
x_24 = lean_box(0);
x_25 = lean_array_push(x_3, x_24);
x_26 = lean_array_push(x_4, x_9);
x_27 = lean_array_push(x_5, x_6);
x_28 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(x_7, x_8, x_22, x_23, x_25, x_26, x_27, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_28;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
lean_object* x_21; 
x_21 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_get_size(x_2);
x_20 = lean_nat_dec_lt(x_3, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_replaceLhss(x_4, x_5, x_1, x_21);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_23 = 1;
x_24 = 1;
x_25 = l_Lean_Meta_mkLambdaFVars(x_6, x_22, x_20, x_23, x_20, x_23, x_24, x_14, x_15, x_16, x_17);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_mkAppN(x_26, x_7);
x_28 = l_Lean_Meta_Sym_shareCommon___redArg(x_27, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_7);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec_ref(x_7);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_13);
lean_dec_ref(x_7);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_25, 0);
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_array_fget_borrowed(x_2, x_3);
x_42 = lean_ctor_get(x_41, 1);
if (lean_obj_tag(x_42) == 1)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_44);
x_45 = lean_infer_type(x_44, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
lean_inc(x_3);
x_47 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___boxed), 21, 9);
lean_closure_set(x_47, 0, x_3);
lean_closure_set(x_47, 1, x_4);
lean_closure_set(x_47, 2, x_5);
lean_closure_set(x_47, 3, x_6);
lean_closure_set(x_47, 4, x_7);
lean_closure_set(x_47, 5, x_44);
lean_closure_set(x_47, 6, x_43);
lean_closure_set(x_47, 7, x_1);
lean_closure_set(x_47, 8, x_2);
x_48 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___closed__1));
x_49 = lean_name_append_index_after(x_48, x_3);
x_50 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(x_49, x_46, x_47, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_45);
if (x_51 == 0)
{
return x_45;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
lean_dec(x_45);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_54);
x_55 = lean_infer_type(x_54, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
lean_inc(x_3);
x_57 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__2___boxed), 20, 8);
lean_closure_set(x_57, 0, x_3);
lean_closure_set(x_57, 1, x_4);
lean_closure_set(x_57, 2, x_5);
lean_closure_set(x_57, 3, x_6);
lean_closure_set(x_57, 4, x_7);
lean_closure_set(x_57, 5, x_54);
lean_closure_set(x_57, 6, x_1);
lean_closure_set(x_57, 7, x_2);
x_58 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1));
x_59 = lean_name_append_index_after(x_58, x_3);
x_60 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(x_59, x_56, x_57, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_60;
}
else
{
uint8_t x_61; 
lean_dec(x_54);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_61 = !lean_is_exclusive(x_55);
if (x_61 == 0)
{
return x_55;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_55, 0);
lean_inc(x_62);
lean_dec(x_55);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_1, x_23);
lean_inc_ref(x_11);
x_25 = lean_array_push(x_2, x_11);
lean_inc_ref(x_3);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_3);
x_27 = lean_array_push(x_4, x_26);
x_28 = lean_array_push(x_5, x_3);
x_29 = lean_array_push(x_28, x_11);
x_30 = lean_array_push(x_6, x_7);
x_31 = lean_array_push(x_30, x_8);
x_32 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(x_9, x_10, x_24, x_25, x_27, x_29, x_31, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_32;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
lean_object* x_23; 
x_23 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_1);
return x_23;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc_ref(x_10);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__0___boxed), 22, 10);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_10);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_4);
lean_closure_set(x_22, 5, x_5);
lean_closure_set(x_22, 6, x_6);
lean_closure_set(x_22, 7, x_7);
lean_closure_set(x_22, 8, x_8);
lean_closure_set(x_22, 9, x_9);
x_23 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___lam__1___closed__1));
x_24 = lean_name_append_index_after(x_23, x_1);
x_25 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(x_24, x_10, x_22, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_25;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
lean_object* x_19; 
x_19 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_3);
x_19 = lean_unbox(x_6);
x_20 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0_spec__0(x_1, x_2, x_18, x_4, x_5, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__3_splitter___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_18; uint8_t x_19; 
lean_inc_ref(x_1);
x_18 = l_Lean_Expr_cleanupAnnotations(x_1);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
x_23 = l_Lean_Expr_isConstOf(x_21, x_22);
lean_dec_ref(x_21);
if (x_23 == 0)
{
lean_dec_ref(x_20);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_1);
lean_inc_ref(x_20);
x_24 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss(x_20);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0;
x_27 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhssAndAbstract_go(x_20, x_24, x_25, x_26, x_26, x_26, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_27;
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_getRootENode___redArg(x_1, x_3, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*11 + 2);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_17, sizeof(void*)*11 + 1);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_20 = lean_box(x_19);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_21);
lean_dec(x_17);
x_22 = l_Lean_Expr_hasLooseBVars(x_2);
if (x_22 == 0)
{
lean_object* x_23; 
lean_free_object(x_15);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
x_23 = l_Lean_Meta_isLitValue(x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
return x_23;
}
else
{
lean_object* x_26; 
lean_dec_ref(x_23);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_26 = l_Lean_Meta_normLitValue(x_21, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_Meta_normLitValue(x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_expr_eqv(x_27, x_30);
lean_dec(x_30);
lean_dec(x_27);
if (x_31 == 0)
{
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
else
{
lean_object* x_32; 
lean_dec(x_24);
x_32 = lean_box(x_22);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_expr_eqv(x_27, x_33);
lean_dec(x_33);
lean_dec(x_27);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_24);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_24);
x_36 = lean_box(x_22);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_27);
lean_dec(x_24);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_24);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_41 = !lean_is_exclusive(x_26);
if (x_41 == 0)
{
return x_26;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_26, 0);
lean_inc(x_42);
lean_dec(x_26);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
else
{
lean_dec_ref(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
return x_23;
}
}
else
{
lean_object* x_44; 
lean_dec_ref(x_21);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_44 = lean_box(x_18);
lean_ctor_set(x_15, 0, x_44);
return x_15;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_15);
x_45 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_45);
lean_dec(x_17);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_45);
x_46 = l_Lean_Meta_isConstructorApp_x3f(x_45, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
if (lean_obj_tag(x_48) == 1)
{
lean_object* x_49; lean_object* x_50; 
lean_free_object(x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
x_50 = l_Lean_Meta_isConstructorApp_x3f(x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_53 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_53);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get(x_49, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_49, 4);
lean_inc(x_57);
lean_dec(x_49);
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
lean_dec_ref(x_53);
x_59 = lean_ctor_get(x_55, 0);
lean_inc(x_59);
lean_dec_ref(x_55);
x_60 = lean_name_eq(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_61 = lean_box(x_18);
lean_ctor_set(x_50, 0, x_61);
return x_50;
}
else
{
if (x_14 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_free_object(x_50);
x_62 = l_Lean_Expr_getAppNumArgs(x_45);
x_63 = l_Lean_Expr_getAppNumArgs(x_2);
x_64 = lean_nat_add(x_56, x_57);
lean_dec(x_57);
x_65 = lean_box(0);
x_66 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0));
x_67 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__1;
lean_inc(x_62);
x_68 = lean_mk_array(x_62, x_67);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_sub(x_62, x_69);
lean_dec(x_62);
x_71 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_45, x_68, x_70);
lean_inc(x_63);
x_72 = lean_mk_array(x_63, x_67);
x_73 = lean_nat_sub(x_63, x_69);
lean_dec(x_63);
x_74 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_72, x_73);
x_75 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(x_64, x_71, x_74, x_66, x_18, x_65, x_56, x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_74);
lean_dec_ref(x_71);
lean_dec(x_64);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_box(x_14);
lean_ctor_set(x_75, 0, x_79);
return x_75;
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec_ref(x_78);
lean_ctor_set(x_75, 0, x_80);
return x_75;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_75, 0);
lean_inc(x_81);
lean_dec(x_75);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_box(x_14);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
lean_dec_ref(x_82);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_75);
if (x_87 == 0)
{
return x_75;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_75, 0);
lean_inc(x_88);
lean_dec(x_75);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_90 = lean_box(x_18);
lean_ctor_set(x_50, 0, x_90);
return x_50;
}
}
}
else
{
lean_object* x_91; 
lean_dec(x_52);
lean_dec(x_49);
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_91 = lean_box(x_14);
lean_ctor_set(x_50, 0, x_91);
return x_50;
}
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_50, 0);
lean_inc(x_92);
lean_dec(x_50);
if (lean_obj_tag(x_92) == 1)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_93 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec_ref(x_92);
x_95 = lean_ctor_get(x_94, 0);
lean_inc_ref(x_95);
lean_dec(x_94);
x_96 = lean_ctor_get(x_49, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_49, 4);
lean_inc(x_97);
lean_dec(x_49);
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
lean_dec_ref(x_93);
x_99 = lean_ctor_get(x_95, 0);
lean_inc(x_99);
lean_dec_ref(x_95);
x_100 = lean_name_eq(x_98, x_99);
lean_dec(x_99);
lean_dec(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_101 = lean_box(x_18);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
else
{
if (x_14 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_103 = l_Lean_Expr_getAppNumArgs(x_45);
x_104 = l_Lean_Expr_getAppNumArgs(x_2);
x_105 = lean_nat_add(x_96, x_97);
lean_dec(x_97);
x_106 = lean_box(0);
x_107 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0));
x_108 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__1;
lean_inc(x_103);
x_109 = lean_mk_array(x_103, x_108);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_sub(x_103, x_110);
lean_dec(x_103);
x_112 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_45, x_109, x_111);
lean_inc(x_104);
x_113 = lean_mk_array(x_104, x_108);
x_114 = lean_nat_sub(x_104, x_110);
lean_dec(x_104);
x_115 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_113, x_114);
x_116 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(x_105, x_112, x_115, x_107, x_18, x_106, x_96, x_107, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_115);
lean_dec_ref(x_112);
lean_dec(x_105);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_box(x_14);
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(0, 1, 0);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_120);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
lean_dec_ref(x_119);
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(0, 1, 0);
} else {
 x_123 = x_118;
}
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_116, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_125 = x_116;
} else {
 lean_dec_ref(x_116);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 1, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_127 = lean_box(x_18);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_92);
lean_dec(x_49);
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_129 = lean_box(x_14);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_49);
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_131 = !lean_is_exclusive(x_50);
if (x_131 == 0)
{
return x_50;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_50, 0);
lean_inc(x_132);
lean_dec(x_50);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; 
lean_dec(x_48);
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_134 = lean_box(x_14);
lean_ctor_set(x_46, 0, x_134);
return x_46;
}
}
else
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_46, 0);
lean_inc(x_135);
lean_dec(x_46);
if (lean_obj_tag(x_135) == 1)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
x_137 = l_Lean_Meta_isConstructorApp_x3f(x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
if (lean_obj_tag(x_138) == 1)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_140 = lean_ctor_get(x_136, 0);
lean_inc_ref(x_140);
x_141 = lean_ctor_get(x_138, 0);
lean_inc(x_141);
lean_dec_ref(x_138);
x_142 = lean_ctor_get(x_141, 0);
lean_inc_ref(x_142);
lean_dec(x_141);
x_143 = lean_ctor_get(x_136, 3);
lean_inc(x_143);
x_144 = lean_ctor_get(x_136, 4);
lean_inc(x_144);
lean_dec(x_136);
x_145 = lean_ctor_get(x_140, 0);
lean_inc(x_145);
lean_dec_ref(x_140);
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
lean_dec_ref(x_142);
x_147 = lean_name_eq(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_148 = lean_box(x_18);
if (lean_is_scalar(x_139)) {
 x_149 = lean_alloc_ctor(0, 1, 0);
} else {
 x_149 = x_139;
}
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
else
{
if (x_14 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_139);
x_150 = l_Lean_Expr_getAppNumArgs(x_45);
x_151 = l_Lean_Expr_getAppNumArgs(x_2);
x_152 = lean_nat_add(x_143, x_144);
lean_dec(x_144);
x_153 = lean_box(0);
x_154 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0));
x_155 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__1;
lean_inc(x_150);
x_156 = lean_mk_array(x_150, x_155);
x_157 = lean_unsigned_to_nat(1u);
x_158 = lean_nat_sub(x_150, x_157);
lean_dec(x_150);
x_159 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_45, x_156, x_158);
lean_inc(x_151);
x_160 = lean_mk_array(x_151, x_155);
x_161 = lean_nat_sub(x_151, x_157);
lean_dec(x_151);
x_162 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_160, x_161);
x_163 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(x_152, x_159, x_162, x_154, x_18, x_153, x_143, x_154, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_162);
lean_dec_ref(x_159);
lean_dec(x_152);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_165 = x_163;
} else {
 lean_dec_ref(x_163);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
lean_dec(x_164);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_box(x_14);
if (lean_is_scalar(x_165)) {
 x_168 = lean_alloc_ctor(0, 1, 0);
} else {
 x_168 = x_165;
}
lean_ctor_set(x_168, 0, x_167);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_166, 0);
lean_inc(x_169);
lean_dec_ref(x_166);
if (lean_is_scalar(x_165)) {
 x_170 = lean_alloc_ctor(0, 1, 0);
} else {
 x_170 = x_165;
}
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_163, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_172 = x_163;
} else {
 lean_dec_ref(x_163);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 1, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_174 = lean_box(x_18);
if (lean_is_scalar(x_139)) {
 x_175 = lean_alloc_ctor(0, 1, 0);
} else {
 x_175 = x_139;
}
lean_ctor_set(x_175, 0, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_138);
lean_dec(x_136);
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_176 = lean_box(x_14);
if (lean_is_scalar(x_139)) {
 x_177 = lean_alloc_ctor(0, 1, 0);
} else {
 x_177 = x_139;
}
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_136);
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_178 = lean_ctor_get(x_137, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_179 = x_137;
} else {
 lean_dec_ref(x_137);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 1, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_135);
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_181 = lean_box(x_14);
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_181);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec_ref(x_45);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_183 = !lean_is_exclusive(x_46);
if (x_183 == 0)
{
return x_46;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_46, 0);
lean_inc(x_184);
lean_dec(x_46);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
return x_185;
}
}
}
}
else
{
lean_object* x_186; uint8_t x_187; 
x_186 = lean_ctor_get(x_15, 0);
lean_inc(x_186);
lean_dec(x_15);
x_187 = lean_ctor_get_uint8(x_186, sizeof(void*)*11 + 2);
if (x_187 == 0)
{
uint8_t x_188; 
x_188 = lean_ctor_get_uint8(x_186, sizeof(void*)*11 + 1);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_186);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_189 = lean_box(x_188);
x_190 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_190, 0, x_189);
return x_190;
}
else
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_ctor_get(x_186, 0);
lean_inc_ref(x_191);
lean_dec(x_186);
x_192 = l_Lean_Expr_hasLooseBVars(x_2);
if (x_192 == 0)
{
lean_object* x_193; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
x_193 = l_Lean_Meta_isLitValue(x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; uint8_t x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_unbox(x_194);
if (x_195 == 0)
{
lean_dec(x_194);
lean_dec_ref(x_191);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
return x_193;
}
else
{
lean_object* x_196; 
lean_dec_ref(x_193);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_196 = l_Lean_Meta_normLitValue(x_191, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec_ref(x_196);
x_198 = l_Lean_Meta_normLitValue(x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_200 = x_198;
} else {
 lean_dec_ref(x_198);
 x_200 = lean_box(0);
}
x_201 = lean_expr_eqv(x_197, x_199);
lean_dec(x_199);
lean_dec(x_197);
if (x_201 == 0)
{
lean_object* x_202; 
if (lean_is_scalar(x_200)) {
 x_202 = lean_alloc_ctor(0, 1, 0);
} else {
 x_202 = x_200;
}
lean_ctor_set(x_202, 0, x_194);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_194);
x_203 = lean_box(x_192);
if (lean_is_scalar(x_200)) {
 x_204 = lean_alloc_ctor(0, 1, 0);
} else {
 x_204 = x_200;
}
lean_ctor_set(x_204, 0, x_203);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_197);
lean_dec(x_194);
x_205 = lean_ctor_get(x_198, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_206 = x_198;
} else {
 lean_dec_ref(x_198);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_194);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_208 = lean_ctor_get(x_196, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_209 = x_196;
} else {
 lean_dec_ref(x_196);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 1, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_208);
return x_210;
}
}
}
else
{
lean_dec_ref(x_191);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
return x_193;
}
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec_ref(x_191);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_211 = lean_box(x_187);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_186, 0);
lean_inc_ref(x_213);
lean_dec(x_186);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_213);
x_214 = l_Lean_Meta_isConstructorApp_x3f(x_213, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_216 = x_214;
} else {
 lean_dec_ref(x_214);
 x_216 = lean_box(0);
}
if (lean_obj_tag(x_215) == 1)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_216);
x_217 = lean_ctor_get(x_215, 0);
lean_inc(x_217);
lean_dec_ref(x_215);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
x_218 = l_Lean_Meta_isConstructorApp_x3f(x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_220 = x_218;
} else {
 lean_dec_ref(x_218);
 x_220 = lean_box(0);
}
if (lean_obj_tag(x_219) == 1)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_221 = lean_ctor_get(x_217, 0);
lean_inc_ref(x_221);
x_222 = lean_ctor_get(x_219, 0);
lean_inc(x_222);
lean_dec_ref(x_219);
x_223 = lean_ctor_get(x_222, 0);
lean_inc_ref(x_223);
lean_dec(x_222);
x_224 = lean_ctor_get(x_217, 3);
lean_inc(x_224);
x_225 = lean_ctor_get(x_217, 4);
lean_inc(x_225);
lean_dec(x_217);
x_226 = lean_ctor_get(x_221, 0);
lean_inc(x_226);
lean_dec_ref(x_221);
x_227 = lean_ctor_get(x_223, 0);
lean_inc(x_227);
lean_dec_ref(x_223);
x_228 = lean_name_eq(x_226, x_227);
lean_dec(x_227);
lean_dec(x_226);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
lean_dec(x_225);
lean_dec(x_224);
lean_dec_ref(x_213);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_229 = lean_box(x_187);
if (lean_is_scalar(x_220)) {
 x_230 = lean_alloc_ctor(0, 1, 0);
} else {
 x_230 = x_220;
}
lean_ctor_set(x_230, 0, x_229);
return x_230;
}
else
{
if (x_14 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_220);
x_231 = l_Lean_Expr_getAppNumArgs(x_213);
x_232 = l_Lean_Expr_getAppNumArgs(x_2);
x_233 = lean_nat_add(x_224, x_225);
lean_dec(x_225);
x_234 = lean_box(0);
x_235 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__0));
x_236 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__1;
lean_inc(x_231);
x_237 = lean_mk_array(x_231, x_236);
x_238 = lean_unsigned_to_nat(1u);
x_239 = lean_nat_sub(x_231, x_238);
lean_dec(x_231);
x_240 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_213, x_237, x_239);
lean_inc(x_232);
x_241 = lean_mk_array(x_232, x_236);
x_242 = lean_nat_sub(x_232, x_238);
lean_dec(x_232);
x_243 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_241, x_242);
x_244 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(x_233, x_240, x_243, x_235, x_187, x_234, x_224, x_235, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_243);
lean_dec_ref(x_240);
lean_dec(x_233);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_246 = x_244;
} else {
 lean_dec_ref(x_244);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
lean_dec(x_245);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_box(x_14);
if (lean_is_scalar(x_246)) {
 x_249 = lean_alloc_ctor(0, 1, 0);
} else {
 x_249 = x_246;
}
lean_ctor_set(x_249, 0, x_248);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_247, 0);
lean_inc(x_250);
lean_dec_ref(x_247);
if (lean_is_scalar(x_246)) {
 x_251 = lean_alloc_ctor(0, 1, 0);
} else {
 x_251 = x_246;
}
lean_ctor_set(x_251, 0, x_250);
return x_251;
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_244, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_253 = x_244;
} else {
 lean_dec_ref(x_244);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 1, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_252);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_225);
lean_dec(x_224);
lean_dec_ref(x_213);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_255 = lean_box(x_187);
if (lean_is_scalar(x_220)) {
 x_256 = lean_alloc_ctor(0, 1, 0);
} else {
 x_256 = x_220;
}
lean_ctor_set(x_256, 0, x_255);
return x_256;
}
}
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_219);
lean_dec(x_217);
lean_dec_ref(x_213);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_257 = lean_box(x_14);
if (lean_is_scalar(x_220)) {
 x_258 = lean_alloc_ctor(0, 1, 0);
} else {
 x_258 = x_220;
}
lean_ctor_set(x_258, 0, x_257);
return x_258;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_217);
lean_dec_ref(x_213);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_259 = lean_ctor_get(x_218, 0);
lean_inc(x_259);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_260 = x_218;
} else {
 lean_dec_ref(x_218);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 1, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_259);
return x_261;
}
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_215);
lean_dec_ref(x_213);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_262 = lean_box(x_14);
if (lean_is_scalar(x_216)) {
 x_263 = lean_alloc_ctor(0, 1, 0);
} else {
 x_263 = x_216;
}
lean_ctor_set(x_263, 0, x_262);
return x_263;
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec_ref(x_213);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_264 = lean_ctor_get(x_214, 0);
lean_inc(x_264);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_265 = x_214;
} else {
 lean_dec_ref(x_214);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 1, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_264);
return x_266;
}
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
x_267 = !lean_is_exclusive(x_15);
if (x_267 == 0)
{
return x_15;
}
else
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_15, 0);
lean_inc(x_268);
lean_dec(x_15);
x_269 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_269, 0, x_268);
return x_269;
}
}
}
else
{
uint8_t x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_270 = 0;
x_271 = lean_box(x_270);
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_271);
return x_272;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_7, x_1);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_7);
lean_dec_ref(x_4);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_8);
x_22 = l_Lean_instInhabitedExpr;
x_23 = lean_array_get_borrowed(x_22, x_2, x_7);
x_24 = lean_array_get_borrowed(x_22, x_3, x_7);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_24);
lean_inc(x_23);
x_25 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(x_23, x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_25);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_7, x_29);
lean_dec(x_7);
lean_inc_ref(x_4);
{
lean_object* _tmp_6 = x_30;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_7);
lean_dec_ref(x_4);
x_32 = lean_box(x_5);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
lean_ctor_set(x_25, 0, x_34);
return x_25;
}
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_7, x_37);
lean_dec(x_7);
lean_inc_ref(x_4);
{
lean_object* _tmp_6 = x_38;
lean_object* _tmp_7 = x_4;
x_7 = _tmp_6;
x_8 = _tmp_7;
}
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_7);
lean_dec_ref(x_4);
x_40 = lean_box(x_5);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_6);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_7);
lean_dec_ref(x_4);
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_25, 0);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_5);
x_21 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(x_1, x_2, x_3, x_4, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_23; 
x_23 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
return x_23;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
uint8_t x_23; lean_object* x_24; 
x_23 = lean_unbox(x_5);
x_24 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse_spec__0(x_1, x_2, x_3, x_4, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_1);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_1, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0;
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0;
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0;
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0;
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__1));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_16 = x_3;
} else {
 lean_dec_ref(x_3);
 x_16 = lean_box(0);
}
if (lean_obj_tag(x_15) == 7)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 1);
x_24 = lean_ctor_get(x_15, 2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_23);
x_25 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_inc_ref(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_inc(x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_24);
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_30 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__3));
x_31 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_30, x_12);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_17 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_34);
x_35 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__5;
lean_inc_ref(x_15);
x_36 = l_Lean_indentExpr(x_15);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__7;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_inc_ref(x_23);
x_40 = l_Lean_indentExpr(x_23);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_30, x_41, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_42) == 0)
{
lean_dec_ref(x_42);
x_17 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_43; 
lean_dec(x_16);
lean_dec_ref(x_15);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
return x_34;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_34, 0);
lean_inc(x_47);
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_49 = !lean_is_exclusive(x_31);
if (x_49 == 0)
{
return x_31;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
lean_dec(x_31);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_25);
if (x_52 == 0)
{
return x_25;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_25, 0);
lean_inc(x_53);
lean_dec(x_25);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_2);
lean_ctor_set(x_55, 1, x_15);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_box(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_16 = x_3;
} else {
 lean_dec_ref(x_3);
 x_16 = lean_box(0);
}
if (lean_obj_tag(x_15) == 7)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 1);
x_24 = lean_ctor_get(x_15, 2);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc_ref(x_23);
x_25 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_inc_ref(x_24);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_inc(x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_24);
x_29 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3(x_1, x_2, x_28, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_30 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__3));
x_31 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_30, x_12);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_17 = lean_box(0);
goto block_22;
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Meta_Grind_updateLastTag(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_34);
x_35 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__5;
lean_inc_ref(x_15);
x_36 = l_Lean_indentExpr(x_15);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__7;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_inc_ref(x_23);
x_40 = l_Lean_indentExpr(x_23);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_30, x_41, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_42) == 0)
{
lean_dec_ref(x_42);
x_17 = lean_box(0);
goto block_22;
}
else
{
uint8_t x_43; 
lean_dec(x_16);
lean_dec_ref(x_15);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
return x_34;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_34, 0);
lean_inc(x_47);
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_49 = !lean_is_exclusive(x_31);
if (x_49 == 0)
{
return x_31;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
lean_dec(x_31);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_25);
if (x_52 == 0)
{
return x_25;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_25, 0);
lean_inc(x_53);
lean_dec(x_25);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_2);
lean_ctor_set(x_55, 1, x_15);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_box(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_1);
x_16 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___redArg(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_20; uint8_t x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_15 = x_13;
} else {
 lean_dec_ref(x_13);
 x_15 = lean_box(0);
}
x_20 = l_Lean_Expr_cleanupAnnotations(x_14);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
goto block_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
lean_dec_ref(x_23);
if (x_25 == 0)
{
lean_dec_ref(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
x_28 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___redArg(x_25, x_26, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; lean_object* x_33; 
x_32 = 0;
x_33 = lean_box(x_32);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec_ref(x_31);
lean_ctor_set(x_28, 0, x_34);
return x_28;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
lean_dec_ref(x_36);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_28);
if (x_42 == 0)
{
return x_28;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_28, 0);
lean_inc(x_43);
lean_dec(x_28);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
}
block_19:
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_box(x_16);
if (lean_is_scalar(x_15)) {
 x_18 = lean_alloc_ctor(0, 1, 0);
} else {
 x_18 = x_15;
}
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_45 = !lean_is_exclusive(x_13);
if (x_45 == 0)
{
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_13, 0);
lean_inc(x_46);
lean_dec(x_13);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_1, x_2, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_21; 
x_21 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___redArg(x_1, x_2, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_1);
x_22 = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = lean_apply_13(x_1, x_8, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11, x_12, x_13, lean_box(0));
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___lam__0___boxed), 14, 7);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_5);
lean_closure_set(x_16, 2, x_6);
lean_closure_set(x_16, 3, x_7);
lean_closure_set(x_16, 4, x_8);
lean_closure_set(x_16, 5, x_9);
lean_closure_set(x_16, 6, x_10);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), x_1, x_16, x_3, x_4, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_3);
x_17 = lean_unbox(x_4);
x_18 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_1, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_4);
x_18 = lean_unbox(x_5);
x_19 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1(x_1, x_2, x_3, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_2);
x_18 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_600; lean_object* x_601; 
x_600 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__3));
x_601 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_600, x_11);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; uint8_t x_603; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
lean_dec_ref(x_601);
x_603 = lean_unbox(x_602);
lean_dec(x_602);
if (x_603 == 0)
{
x_366 = x_3;
x_367 = x_4;
x_368 = x_5;
x_369 = x_6;
x_370 = x_7;
x_371 = x_8;
x_372 = x_9;
x_373 = x_10;
x_374 = x_11;
x_375 = x_12;
x_376 = lean_box(0);
goto block_599;
}
else
{
lean_object* x_604; 
x_604 = l_Lean_Meta_Grind_updateLastTag(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_604) == 0)
{
lean_object* x_605; 
lean_dec_ref(x_604);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
x_605 = lean_infer_type(x_2, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
lean_dec_ref(x_605);
x_607 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5;
x_608 = l_Lean_MessageData_ofExpr(x_606);
x_609 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_609, 0, x_607);
lean_ctor_set(x_609, 1, x_608);
x_610 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_600, x_609, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_610) == 0)
{
lean_dec_ref(x_610);
x_366 = x_3;
x_367 = x_4;
x_368 = x_5;
x_369 = x_6;
x_370 = x_7;
x_371 = x_8;
x_372 = x_9;
x_373 = x_10;
x_374 = x_11;
x_375 = x_12;
x_376 = lean_box(0);
goto block_599;
}
else
{
uint8_t x_611; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_611 = !lean_is_exclusive(x_610);
if (x_611 == 0)
{
return x_610;
}
else
{
lean_object* x_612; lean_object* x_613; 
x_612 = lean_ctor_get(x_610, 0);
lean_inc(x_612);
lean_dec(x_610);
x_613 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_613, 0, x_612);
return x_613;
}
}
}
else
{
uint8_t x_614; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_614 = !lean_is_exclusive(x_605);
if (x_614 == 0)
{
return x_605;
}
else
{
lean_object* x_615; lean_object* x_616; 
x_615 = lean_ctor_get(x_605, 0);
lean_inc(x_615);
lean_dec(x_605);
x_616 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_616, 0, x_615);
return x_616;
}
}
}
else
{
uint8_t x_617; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_617 = !lean_is_exclusive(x_604);
if (x_617 == 0)
{
return x_604;
}
else
{
lean_object* x_618; lean_object* x_619; 
x_618 = lean_ctor_get(x_604, 0);
lean_inc(x_618);
lean_dec(x_604);
x_619 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_619, 0, x_618);
return x_619;
}
}
}
}
else
{
uint8_t x_620; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_620 = !lean_is_exclusive(x_601);
if (x_620 == 0)
{
return x_601;
}
else
{
lean_object* x_621; lean_object* x_622; 
x_621 = lean_ctor_get(x_601, 0);
lean_inc(x_621);
lean_dec(x_601);
x_622 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_622, 0, x_621);
return x_622;
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_277:
{
if (x_20 == 0)
{
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_19);
lean_dec_ref(x_1);
if (x_21 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; 
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc_ref(x_23);
x_38 = l_Lean_Meta_normLitValue(x_23, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc_ref(x_22);
x_40 = l_Lean_Meta_normLitValue(x_22, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_expr_eqv(x_39, x_42);
lean_dec(x_42);
lean_dec(x_39);
if (x_43 == 0)
{
lean_object* x_44; 
lean_free_object(x_40);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_44 = l_Lean_Meta_mkEq(x_23, x_22, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l_Lean_mkNot(x_45);
x_47 = l_Lean_Meta_mkDecideProof(x_46, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = l_Lean_Expr_app___override(x_49, x_24);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
x_53 = l_Lean_Expr_app___override(x_52, x_24);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_24);
x_56 = !lean_is_exclusive(x_47);
if (x_56 == 0)
{
return x_47;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_47, 0);
lean_inc(x_57);
lean_dec(x_47);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_24);
x_59 = !lean_is_exclusive(x_44);
if (x_59 == 0)
{
return x_44;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_44, 0);
lean_inc(x_60);
lean_dec(x_44);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
x_62 = lean_box(0);
lean_ctor_set(x_40, 0, x_62);
return x_40;
}
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_40, 0);
lean_inc(x_63);
lean_dec(x_40);
x_64 = lean_expr_eqv(x_39, x_63);
lean_dec(x_63);
lean_dec(x_39);
if (x_64 == 0)
{
lean_object* x_65; 
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_65 = l_Lean_Meta_mkEq(x_23, x_22, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = l_Lean_mkNot(x_66);
x_68 = l_Lean_Meta_mkDecideProof(x_67, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = l_Lean_Expr_app___override(x_69, x_24);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(0, 1, 0);
} else {
 x_73 = x_70;
}
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_24);
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_24);
x_77 = lean_ctor_get(x_65, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_78 = x_65;
} else {
 lean_dec_ref(x_65);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_39);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
x_82 = !lean_is_exclusive(x_40);
if (x_82 == 0)
{
return x_40;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_40, 0);
lean_inc(x_83);
lean_dec(x_40);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
x_85 = !lean_is_exclusive(x_38);
if (x_85 == 0)
{
return x_38;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_38, 0);
lean_inc(x_86);
lean_dec(x_38);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
}
}
}
else
{
lean_object* x_88; 
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_88 = l_Lean_Meta_isConstructorApp_x3f(x_23, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_88, 0);
if (lean_obj_tag(x_90) == 1)
{
lean_object* x_91; lean_object* x_92; 
lean_free_object(x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_92 = l_Lean_Meta_isConstructorApp_x3f(x_22, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_92, 0);
if (lean_obj_tag(x_94) == 1)
{
uint8_t x_95; 
lean_free_object(x_92);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_97 = l_Lean_Meta_mkNoConfusion(x_19, x_24, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_91, 0);
lean_inc_ref(x_98);
lean_dec(x_91);
x_99 = lean_ctor_get(x_96, 0);
lean_inc_ref(x_99);
lean_dec(x_96);
x_100 = !lean_is_exclusive(x_97);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = lean_ctor_get(x_97, 0);
x_102 = lean_ctor_get(x_98, 0);
lean_inc(x_102);
lean_dec_ref(x_98);
x_103 = lean_ctor_get(x_99, 0);
lean_inc(x_103);
lean_dec_ref(x_99);
x_104 = lean_name_eq(x_102, x_103);
lean_dec(x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
lean_ctor_set(x_94, 0, x_101);
lean_ctor_set(x_97, 0, x_94);
return x_97;
}
else
{
lean_object* x_105; 
lean_free_object(x_97);
lean_free_object(x_94);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_101);
x_105 = lean_infer_type(x_101, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_107 = l_Lean_Meta_whnfD(x_106, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_107, 0);
if (lean_obj_tag(x_109) == 7)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
lean_free_object(x_107);
x_110 = lean_ctor_get(x_109, 1);
lean_inc_ref(x_110);
lean_dec_ref(x_109);
x_111 = lean_box(x_18);
x_112 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 16, 3);
lean_closure_set(x_112, 0, x_1);
lean_closure_set(x_112, 1, x_111);
lean_closure_set(x_112, 2, x_101);
x_113 = 0;
x_114 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_110, x_112, x_113, x_113, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_114;
}
else
{
lean_object* x_115; 
lean_dec(x_109);
lean_dec(x_101);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_115 = lean_box(0);
lean_ctor_set(x_107, 0, x_115);
return x_107;
}
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_107, 0);
lean_inc(x_116);
lean_dec(x_107);
if (lean_obj_tag(x_116) == 7)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc_ref(x_117);
lean_dec_ref(x_116);
x_118 = lean_box(x_18);
x_119 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 16, 3);
lean_closure_set(x_119, 0, x_1);
lean_closure_set(x_119, 1, x_118);
lean_closure_set(x_119, 2, x_101);
x_120 = 0;
x_121 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_117, x_119, x_120, x_120, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_116);
lean_dec(x_101);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_101);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_124 = !lean_is_exclusive(x_107);
if (x_124 == 0)
{
return x_107;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_107, 0);
lean_inc(x_125);
lean_dec(x_107);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_101);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_127 = !lean_is_exclusive(x_105);
if (x_127 == 0)
{
return x_105;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_105, 0);
lean_inc(x_128);
lean_dec(x_105);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_97, 0);
lean_inc(x_130);
lean_dec(x_97);
x_131 = lean_ctor_get(x_98, 0);
lean_inc(x_131);
lean_dec_ref(x_98);
x_132 = lean_ctor_get(x_99, 0);
lean_inc(x_132);
lean_dec_ref(x_99);
x_133 = lean_name_eq(x_131, x_132);
lean_dec(x_132);
lean_dec(x_131);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
lean_ctor_set(x_94, 0, x_130);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_94);
return x_134;
}
else
{
lean_object* x_135; 
lean_free_object(x_94);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_130);
x_135 = lean_infer_type(x_130, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_137 = l_Lean_Meta_whnfD(x_136, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
if (lean_obj_tag(x_138) == 7)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; 
lean_dec(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc_ref(x_140);
lean_dec_ref(x_138);
x_141 = lean_box(x_18);
x_142 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 16, 3);
lean_closure_set(x_142, 0, x_1);
lean_closure_set(x_142, 1, x_141);
lean_closure_set(x_142, 2, x_130);
x_143 = 0;
x_144 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_140, x_142, x_143, x_143, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_138);
lean_dec(x_130);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_145 = lean_box(0);
if (lean_is_scalar(x_139)) {
 x_146 = lean_alloc_ctor(0, 1, 0);
} else {
 x_146 = x_139;
}
lean_ctor_set(x_146, 0, x_145);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_130);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_147 = lean_ctor_get(x_137, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_148 = x_137;
} else {
 lean_dec_ref(x_137);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 1, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_130);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_150 = lean_ctor_get(x_135, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_151 = x_135;
} else {
 lean_dec_ref(x_135);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_150);
return x_152;
}
}
}
}
else
{
uint8_t x_153; 
lean_free_object(x_94);
lean_dec(x_96);
lean_dec(x_91);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_153 = !lean_is_exclusive(x_97);
if (x_153 == 0)
{
return x_97;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_97, 0);
lean_inc(x_154);
lean_dec(x_97);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_94, 0);
lean_inc(x_156);
lean_dec(x_94);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_157 = l_Lean_Meta_mkNoConfusion(x_19, x_24, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_158 = lean_ctor_get(x_91, 0);
lean_inc_ref(x_158);
lean_dec(x_91);
x_159 = lean_ctor_get(x_156, 0);
lean_inc_ref(x_159);
lean_dec(x_156);
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 x_161 = x_157;
} else {
 lean_dec_ref(x_157);
 x_161 = lean_box(0);
}
x_162 = lean_ctor_get(x_158, 0);
lean_inc(x_162);
lean_dec_ref(x_158);
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
lean_dec_ref(x_159);
x_164 = lean_name_eq(x_162, x_163);
lean_dec(x_163);
lean_dec(x_162);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_160);
if (lean_is_scalar(x_161)) {
 x_166 = lean_alloc_ctor(0, 1, 0);
} else {
 x_166 = x_161;
}
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
else
{
lean_object* x_167; 
lean_dec(x_161);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_160);
x_167 = lean_infer_type(x_160, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_169 = l_Lean_Meta_whnfD(x_168, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
if (lean_obj_tag(x_170) == 7)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; 
lean_dec(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc_ref(x_172);
lean_dec_ref(x_170);
x_173 = lean_box(x_18);
x_174 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 16, 3);
lean_closure_set(x_174, 0, x_1);
lean_closure_set(x_174, 1, x_173);
lean_closure_set(x_174, 2, x_160);
x_175 = 0;
x_176 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_172, x_174, x_175, x_175, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_170);
lean_dec(x_160);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_177 = lean_box(0);
if (lean_is_scalar(x_171)) {
 x_178 = lean_alloc_ctor(0, 1, 0);
} else {
 x_178 = x_171;
}
lean_ctor_set(x_178, 0, x_177);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_160);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_179 = lean_ctor_get(x_169, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_180 = x_169;
} else {
 lean_dec_ref(x_169);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_160);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_182 = lean_ctor_get(x_167, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_183 = x_167;
} else {
 lean_dec_ref(x_167);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_182);
return x_184;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_156);
lean_dec(x_91);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_185 = lean_ctor_get(x_157, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 x_186 = x_157;
} else {
 lean_dec_ref(x_157);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 1, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_185);
return x_187;
}
}
}
else
{
lean_object* x_188; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_188 = lean_box(0);
lean_ctor_set(x_92, 0, x_188);
return x_92;
}
}
else
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_92, 0);
lean_inc(x_189);
lean_dec(x_92);
if (lean_obj_tag(x_189) == 1)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_191 = x_189;
} else {
 lean_dec_ref(x_189);
 x_191 = lean_box(0);
}
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_192 = l_Lean_Meta_mkNoConfusion(x_19, x_24, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_193 = lean_ctor_get(x_91, 0);
lean_inc_ref(x_193);
lean_dec(x_91);
x_194 = lean_ctor_get(x_190, 0);
lean_inc_ref(x_194);
lean_dec(x_190);
x_195 = lean_ctor_get(x_192, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_196 = x_192;
} else {
 lean_dec_ref(x_192);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_193, 0);
lean_inc(x_197);
lean_dec_ref(x_193);
x_198 = lean_ctor_get(x_194, 0);
lean_inc(x_198);
lean_dec_ref(x_194);
x_199 = lean_name_eq(x_197, x_198);
lean_dec(x_198);
lean_dec(x_197);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
if (lean_is_scalar(x_191)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_191;
}
lean_ctor_set(x_200, 0, x_195);
if (lean_is_scalar(x_196)) {
 x_201 = lean_alloc_ctor(0, 1, 0);
} else {
 x_201 = x_196;
}
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
else
{
lean_object* x_202; 
lean_dec(x_196);
lean_dec(x_191);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_195);
x_202 = lean_infer_type(x_195, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
lean_dec_ref(x_202);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_204 = l_Lean_Meta_whnfD(x_203, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
if (lean_obj_tag(x_205) == 7)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; 
lean_dec(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc_ref(x_207);
lean_dec_ref(x_205);
x_208 = lean_box(x_18);
x_209 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 16, 3);
lean_closure_set(x_209, 0, x_1);
lean_closure_set(x_209, 1, x_208);
lean_closure_set(x_209, 2, x_195);
x_210 = 0;
x_211 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_207, x_209, x_210, x_210, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_205);
lean_dec(x_195);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_212 = lean_box(0);
if (lean_is_scalar(x_206)) {
 x_213 = lean_alloc_ctor(0, 1, 0);
} else {
 x_213 = x_206;
}
lean_ctor_set(x_213, 0, x_212);
return x_213;
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_195);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_214 = lean_ctor_get(x_204, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_215 = x_204;
} else {
 lean_dec_ref(x_204);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 1, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_214);
return x_216;
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_195);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_217 = lean_ctor_get(x_202, 0);
lean_inc(x_217);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 x_218 = x_202;
} else {
 lean_dec_ref(x_202);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 1, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_217);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_91);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_220 = lean_ctor_get(x_192, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_221 = x_192;
} else {
 lean_dec_ref(x_192);
 x_221 = lean_box(0);
}
if (lean_is_scalar(x_221)) {
 x_222 = lean_alloc_ctor(1, 1, 0);
} else {
 x_222 = x_221;
}
lean_ctor_set(x_222, 0, x_220);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; 
lean_dec(x_189);
lean_dec(x_91);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_223 = lean_box(0);
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_223);
return x_224;
}
}
}
else
{
uint8_t x_225; 
lean_dec(x_91);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_225 = !lean_is_exclusive(x_92);
if (x_225 == 0)
{
return x_92;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_ctor_get(x_92, 0);
lean_inc(x_226);
lean_dec(x_92);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
}
}
else
{
lean_object* x_228; 
lean_dec(x_90);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_228 = lean_box(0);
lean_ctor_set(x_88, 0, x_228);
return x_88;
}
}
else
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_88, 0);
lean_inc(x_229);
lean_dec(x_88);
if (lean_obj_tag(x_229) == 1)
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
lean_dec_ref(x_229);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_231 = l_Lean_Meta_isConstructorApp_x3f(x_22, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
if (lean_obj_tag(x_232) == 1)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_233);
x_234 = lean_ctor_get(x_232, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_236 = l_Lean_Meta_mkNoConfusion(x_19, x_24, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_237 = lean_ctor_get(x_230, 0);
lean_inc_ref(x_237);
lean_dec(x_230);
x_238 = lean_ctor_get(x_234, 0);
lean_inc_ref(x_238);
lean_dec(x_234);
x_239 = lean_ctor_get(x_236, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 x_240 = x_236;
} else {
 lean_dec_ref(x_236);
 x_240 = lean_box(0);
}
x_241 = lean_ctor_get(x_237, 0);
lean_inc(x_241);
lean_dec_ref(x_237);
x_242 = lean_ctor_get(x_238, 0);
lean_inc(x_242);
lean_dec_ref(x_238);
x_243 = lean_name_eq(x_241, x_242);
lean_dec(x_242);
lean_dec(x_241);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
if (lean_is_scalar(x_235)) {
 x_244 = lean_alloc_ctor(1, 1, 0);
} else {
 x_244 = x_235;
}
lean_ctor_set(x_244, 0, x_239);
if (lean_is_scalar(x_240)) {
 x_245 = lean_alloc_ctor(0, 1, 0);
} else {
 x_245 = x_240;
}
lean_ctor_set(x_245, 0, x_244);
return x_245;
}
else
{
lean_object* x_246; 
lean_dec(x_240);
lean_dec(x_235);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
lean_inc(x_239);
x_246 = lean_infer_type(x_239, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
lean_dec_ref(x_246);
lean_inc(x_34);
lean_inc_ref(x_33);
lean_inc(x_32);
lean_inc_ref(x_31);
x_248 = l_Lean_Meta_whnfD(x_247, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 x_250 = x_248;
} else {
 lean_dec_ref(x_248);
 x_250 = lean_box(0);
}
if (lean_obj_tag(x_249) == 7)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; 
lean_dec(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc_ref(x_251);
lean_dec_ref(x_249);
x_252 = lean_box(x_18);
x_253 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___boxed), 16, 3);
lean_closure_set(x_253, 0, x_1);
lean_closure_set(x_253, 1, x_252);
lean_closure_set(x_253, 2, x_239);
x_254 = 0;
x_255 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_251, x_253, x_254, x_254, x_25, x_26, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_249);
lean_dec(x_239);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_256 = lean_box(0);
if (lean_is_scalar(x_250)) {
 x_257 = lean_alloc_ctor(0, 1, 0);
} else {
 x_257 = x_250;
}
lean_ctor_set(x_257, 0, x_256);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_239);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_258 = lean_ctor_get(x_248, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 x_259 = x_248;
} else {
 lean_dec_ref(x_248);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 1, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_258);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_239);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_261 = lean_ctor_get(x_246, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 x_262 = x_246;
} else {
 lean_dec_ref(x_246);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 1, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_261);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_230);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_1);
x_264 = lean_ctor_get(x_236, 0);
lean_inc(x_264);
if (lean_is_exclusive(x_236)) {
 lean_ctor_release(x_236, 0);
 x_265 = x_236;
} else {
 lean_dec_ref(x_236);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 1, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_264);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_232);
lean_dec(x_230);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_267 = lean_box(0);
if (lean_is_scalar(x_233)) {
 x_268 = lean_alloc_ctor(0, 1, 0);
} else {
 x_268 = x_233;
}
lean_ctor_set(x_268, 0, x_267);
return x_268;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_230);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_269 = lean_ctor_get(x_231, 0);
lean_inc(x_269);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_270 = x_231;
} else {
 lean_dec_ref(x_231);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 1, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_269);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; 
lean_dec(x_229);
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_272 = lean_box(0);
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_272);
return x_273;
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_32);
lean_dec_ref(x_31);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_1);
x_274 = !lean_is_exclusive(x_88);
if (x_274 == 0)
{
return x_88;
}
else
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_88, 0);
lean_inc(x_275);
lean_dec(x_88);
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_275);
return x_276;
}
}
}
}
block_365:
{
lean_object* x_294; uint8_t x_295; uint8_t x_296; lean_object* x_297; 
x_294 = lean_ctor_get(x_289, 0);
lean_inc_ref(x_294);
x_295 = lean_ctor_get_uint8(x_289, sizeof(void*)*11 + 1);
x_296 = lean_ctor_get_uint8(x_289, sizeof(void*)*11 + 2);
lean_dec_ref(x_289);
lean_inc(x_281);
lean_inc_ref(x_283);
lean_inc(x_287);
lean_inc_ref(x_291);
lean_inc_ref(x_286);
lean_inc_ref(x_294);
x_297 = l_Lean_Meta_Grind_hasSameType(x_294, x_286, x_291, x_287, x_283, x_281);
if (lean_obj_tag(x_297) == 0)
{
uint8_t x_298; 
x_298 = !lean_is_exclusive(x_297);
if (x_298 == 0)
{
lean_object* x_299; uint8_t x_300; 
x_299 = lean_ctor_get(x_297, 0);
x_300 = lean_unbox(x_299);
if (x_300 == 0)
{
lean_object* x_301; 
lean_dec(x_299);
lean_dec_ref(x_294);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_290);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_301 = lean_box(0);
lean_ctor_set(x_297, 0, x_301);
return x_297;
}
else
{
lean_free_object(x_297);
if (x_293 == 0)
{
lean_object* x_302; 
lean_inc(x_281);
lean_inc_ref(x_283);
lean_inc(x_287);
lean_inc_ref(x_291);
lean_inc(x_278);
lean_inc_ref(x_279);
lean_inc(x_284);
lean_inc_ref(x_288);
lean_inc(x_282);
lean_inc(x_292);
lean_inc_ref(x_294);
x_302 = lean_grind_mk_eq_proof(x_294, x_290, x_292, x_282, x_288, x_284, x_279, x_278, x_291, x_287, x_283, x_281);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
lean_dec_ref(x_302);
lean_inc(x_281);
lean_inc_ref(x_283);
lean_inc(x_287);
lean_inc_ref(x_291);
x_304 = l_Lean_Meta_mkEqTrans(x_303, x_2, x_291, x_287, x_283, x_281);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; uint8_t x_306; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
lean_dec_ref(x_304);
x_306 = lean_unbox(x_299);
lean_dec(x_299);
x_18 = x_306;
x_19 = x_285;
x_20 = x_296;
x_21 = x_295;
x_22 = x_286;
x_23 = x_294;
x_24 = x_305;
x_25 = x_292;
x_26 = x_282;
x_27 = x_288;
x_28 = x_284;
x_29 = x_279;
x_30 = x_278;
x_31 = x_291;
x_32 = x_287;
x_33 = x_283;
x_34 = x_281;
x_35 = lean_box(0);
goto block_277;
}
else
{
uint8_t x_307; 
lean_dec(x_299);
lean_dec_ref(x_294);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_1);
x_307 = !lean_is_exclusive(x_304);
if (x_307 == 0)
{
return x_304;
}
else
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_304, 0);
lean_inc(x_308);
lean_dec(x_304);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_308);
return x_309;
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_299);
lean_dec_ref(x_294);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_310 = !lean_is_exclusive(x_302);
if (x_310 == 0)
{
return x_302;
}
else
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_302, 0);
lean_inc(x_311);
lean_dec(x_302);
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_311);
return x_312;
}
}
}
else
{
lean_object* x_313; 
lean_inc(x_281);
lean_inc_ref(x_283);
lean_inc(x_287);
lean_inc_ref(x_291);
lean_inc(x_278);
lean_inc_ref(x_279);
lean_inc(x_284);
lean_inc_ref(x_288);
lean_inc(x_282);
lean_inc(x_292);
lean_inc_ref(x_294);
x_313 = lean_grind_mk_heq_proof(x_294, x_290, x_292, x_282, x_288, x_284, x_279, x_278, x_291, x_287, x_283, x_281);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
lean_dec_ref(x_313);
lean_inc(x_281);
lean_inc_ref(x_283);
lean_inc(x_287);
lean_inc_ref(x_291);
x_315 = l_Lean_Meta_mkHEqTrans(x_314, x_2, x_291, x_287, x_283, x_281);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; uint8_t x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec_ref(x_315);
x_317 = 0;
lean_inc(x_281);
lean_inc_ref(x_283);
lean_inc(x_287);
lean_inc_ref(x_291);
x_318 = l_Lean_Meta_mkEqOfHEq(x_316, x_317, x_291, x_287, x_283, x_281);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; uint8_t x_320; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
lean_dec_ref(x_318);
x_320 = lean_unbox(x_299);
lean_dec(x_299);
x_18 = x_320;
x_19 = x_285;
x_20 = x_296;
x_21 = x_295;
x_22 = x_286;
x_23 = x_294;
x_24 = x_319;
x_25 = x_292;
x_26 = x_282;
x_27 = x_288;
x_28 = x_284;
x_29 = x_279;
x_30 = x_278;
x_31 = x_291;
x_32 = x_287;
x_33 = x_283;
x_34 = x_281;
x_35 = lean_box(0);
goto block_277;
}
else
{
uint8_t x_321; 
lean_dec(x_299);
lean_dec_ref(x_294);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_1);
x_321 = !lean_is_exclusive(x_318);
if (x_321 == 0)
{
return x_318;
}
else
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_318, 0);
lean_inc(x_322);
lean_dec(x_318);
x_323 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_323, 0, x_322);
return x_323;
}
}
}
else
{
uint8_t x_324; 
lean_dec(x_299);
lean_dec_ref(x_294);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_1);
x_324 = !lean_is_exclusive(x_315);
if (x_324 == 0)
{
return x_315;
}
else
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_ctor_get(x_315, 0);
lean_inc(x_325);
lean_dec(x_315);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
return x_326;
}
}
}
else
{
uint8_t x_327; 
lean_dec(x_299);
lean_dec_ref(x_294);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_327 = !lean_is_exclusive(x_313);
if (x_327 == 0)
{
return x_313;
}
else
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_313, 0);
lean_inc(x_328);
lean_dec(x_313);
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_328);
return x_329;
}
}
}
}
}
else
{
lean_object* x_330; uint8_t x_331; 
x_330 = lean_ctor_get(x_297, 0);
lean_inc(x_330);
lean_dec(x_297);
x_331 = lean_unbox(x_330);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; 
lean_dec(x_330);
lean_dec_ref(x_294);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_290);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_332 = lean_box(0);
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_332);
return x_333;
}
else
{
if (x_293 == 0)
{
lean_object* x_334; 
lean_inc(x_281);
lean_inc_ref(x_283);
lean_inc(x_287);
lean_inc_ref(x_291);
lean_inc(x_278);
lean_inc_ref(x_279);
lean_inc(x_284);
lean_inc_ref(x_288);
lean_inc(x_282);
lean_inc(x_292);
lean_inc_ref(x_294);
x_334 = lean_grind_mk_eq_proof(x_294, x_290, x_292, x_282, x_288, x_284, x_279, x_278, x_291, x_287, x_283, x_281);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
lean_dec_ref(x_334);
lean_inc(x_281);
lean_inc_ref(x_283);
lean_inc(x_287);
lean_inc_ref(x_291);
x_336 = l_Lean_Meta_mkEqTrans(x_335, x_2, x_291, x_287, x_283, x_281);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; uint8_t x_338; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
lean_dec_ref(x_336);
x_338 = lean_unbox(x_330);
lean_dec(x_330);
x_18 = x_338;
x_19 = x_285;
x_20 = x_296;
x_21 = x_295;
x_22 = x_286;
x_23 = x_294;
x_24 = x_337;
x_25 = x_292;
x_26 = x_282;
x_27 = x_288;
x_28 = x_284;
x_29 = x_279;
x_30 = x_278;
x_31 = x_291;
x_32 = x_287;
x_33 = x_283;
x_34 = x_281;
x_35 = lean_box(0);
goto block_277;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_330);
lean_dec_ref(x_294);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_1);
x_339 = lean_ctor_get(x_336, 0);
lean_inc(x_339);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_340 = x_336;
} else {
 lean_dec_ref(x_336);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 1, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_339);
return x_341;
}
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_330);
lean_dec_ref(x_294);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_342 = lean_ctor_get(x_334, 0);
lean_inc(x_342);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 x_343 = x_334;
} else {
 lean_dec_ref(x_334);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 1, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_342);
return x_344;
}
}
else
{
lean_object* x_345; 
lean_inc(x_281);
lean_inc_ref(x_283);
lean_inc(x_287);
lean_inc_ref(x_291);
lean_inc(x_278);
lean_inc_ref(x_279);
lean_inc(x_284);
lean_inc_ref(x_288);
lean_inc(x_282);
lean_inc(x_292);
lean_inc_ref(x_294);
x_345 = lean_grind_mk_heq_proof(x_294, x_290, x_292, x_282, x_288, x_284, x_279, x_278, x_291, x_287, x_283, x_281);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
lean_dec_ref(x_345);
lean_inc(x_281);
lean_inc_ref(x_283);
lean_inc(x_287);
lean_inc_ref(x_291);
x_347 = l_Lean_Meta_mkHEqTrans(x_346, x_2, x_291, x_287, x_283, x_281);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; uint8_t x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
lean_dec_ref(x_347);
x_349 = 0;
lean_inc(x_281);
lean_inc_ref(x_283);
lean_inc(x_287);
lean_inc_ref(x_291);
x_350 = l_Lean_Meta_mkEqOfHEq(x_348, x_349, x_291, x_287, x_283, x_281);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; uint8_t x_352; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
lean_dec_ref(x_350);
x_352 = lean_unbox(x_330);
lean_dec(x_330);
x_18 = x_352;
x_19 = x_285;
x_20 = x_296;
x_21 = x_295;
x_22 = x_286;
x_23 = x_294;
x_24 = x_351;
x_25 = x_292;
x_26 = x_282;
x_27 = x_288;
x_28 = x_284;
x_29 = x_279;
x_30 = x_278;
x_31 = x_291;
x_32 = x_287;
x_33 = x_283;
x_34 = x_281;
x_35 = lean_box(0);
goto block_277;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_330);
lean_dec_ref(x_294);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_1);
x_353 = lean_ctor_get(x_350, 0);
lean_inc(x_353);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 x_354 = x_350;
} else {
 lean_dec_ref(x_350);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 1, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_353);
return x_355;
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_330);
lean_dec_ref(x_294);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_1);
x_356 = lean_ctor_get(x_347, 0);
lean_inc(x_356);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 x_357 = x_347;
} else {
 lean_dec_ref(x_347);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 1, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_356);
return x_358;
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_330);
lean_dec_ref(x_294);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_359 = lean_ctor_get(x_345, 0);
lean_inc(x_359);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 x_360 = x_345;
} else {
 lean_dec_ref(x_345);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 1, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_359);
return x_361;
}
}
}
}
}
else
{
uint8_t x_362; 
lean_dec_ref(x_294);
lean_dec(x_292);
lean_dec_ref(x_291);
lean_dec_ref(x_290);
lean_dec_ref(x_288);
lean_dec(x_287);
lean_dec_ref(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec_ref(x_283);
lean_dec(x_282);
lean_dec(x_281);
lean_dec_ref(x_279);
lean_dec(x_278);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_362 = !lean_is_exclusive(x_297);
if (x_362 == 0)
{
return x_297;
}
else
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_297, 0);
lean_inc(x_363);
lean_dec(x_297);
x_364 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_364, 0, x_363);
return x_364;
}
}
}
block_599:
{
lean_object* x_377; 
lean_inc(x_375);
lean_inc_ref(x_374);
lean_inc(x_373);
lean_inc_ref(x_372);
lean_inc_ref(x_2);
x_377 = lean_infer_type(x_2, x_372, x_373, x_374, x_375);
if (lean_obj_tag(x_377) == 0)
{
uint8_t x_378; 
x_378 = !lean_is_exclusive(x_377);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_377, 0);
x_380 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_379);
if (lean_obj_tag(x_380) == 1)
{
lean_object* x_381; uint8_t x_382; 
lean_free_object(x_377);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
lean_dec_ref(x_380);
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; uint8_t x_384; 
x_383 = lean_ctor_get(x_381, 1);
x_384 = !lean_is_exclusive(x_383);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_385 = lean_ctor_get(x_381, 0);
x_386 = lean_ctor_get(x_383, 0);
x_387 = lean_ctor_get(x_383, 1);
x_388 = lean_st_ref_get(x_366);
x_389 = !lean_is_exclusive(x_388);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_388, 1);
x_391 = lean_ctor_get(x_388, 0);
lean_dec(x_391);
x_392 = l_Lean_MVarId_getType(x_390, x_372, x_373, x_374, x_375);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
lean_dec_ref(x_392);
x_394 = l_Lean_Meta_Sym_shareCommon___redArg(x_386, x_371);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
lean_dec_ref(x_394);
x_396 = l_Lean_Meta_Grind_getRootENode_x3f___redArg(x_395, x_366);
if (lean_obj_tag(x_396) == 0)
{
lean_object* x_397; 
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
lean_dec_ref(x_396);
if (lean_obj_tag(x_397) == 1)
{
lean_free_object(x_388);
lean_free_object(x_383);
lean_free_object(x_381);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_398; uint8_t x_399; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
lean_dec_ref(x_397);
x_399 = 0;
x_278 = x_371;
x_279 = x_370;
x_280 = lean_box(0);
x_281 = x_375;
x_282 = x_367;
x_283 = x_374;
x_284 = x_369;
x_285 = x_393;
x_286 = x_387;
x_287 = x_373;
x_288 = x_368;
x_289 = x_398;
x_290 = x_395;
x_291 = x_372;
x_292 = x_366;
x_293 = x_399;
goto block_365;
}
else
{
lean_object* x_400; uint8_t x_401; 
lean_dec_ref(x_385);
x_400 = lean_ctor_get(x_397, 0);
lean_inc(x_400);
lean_dec_ref(x_397);
x_401 = 1;
x_278 = x_371;
x_279 = x_370;
x_280 = lean_box(0);
x_281 = x_375;
x_282 = x_367;
x_283 = x_374;
x_284 = x_369;
x_285 = x_393;
x_286 = x_387;
x_287 = x_373;
x_288 = x_368;
x_289 = x_400;
x_290 = x_395;
x_291 = x_372;
x_292 = x_366;
x_293 = x_401;
goto block_365;
}
}
else
{
lean_object* x_402; 
lean_dec(x_397);
lean_dec(x_393);
lean_dec(x_387);
lean_dec(x_385);
lean_dec(x_366);
lean_dec_ref(x_2);
x_402 = l_Lean_Meta_Grind_getConfig___redArg(x_368);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; uint8_t x_404; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
lean_dec_ref(x_402);
x_404 = lean_ctor_get_uint8(x_403, sizeof(void*)*10 + 14);
lean_dec(x_403);
if (x_404 == 0)
{
lean_dec(x_395);
lean_free_object(x_388);
lean_free_object(x_383);
lean_free_object(x_381);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_1);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_405 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1;
x_406 = l_Lean_indentExpr(x_395);
lean_ctor_set_tag(x_388, 7);
lean_ctor_set(x_388, 1, x_406);
lean_ctor_set(x_388, 0, x_405);
x_407 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3;
lean_ctor_set_tag(x_383, 7);
lean_ctor_set(x_383, 1, x_407);
lean_ctor_set(x_383, 0, x_388);
x_408 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_381, 7);
lean_ctor_set(x_381, 1, x_408);
lean_ctor_set(x_381, 0, x_383);
x_409 = l_Lean_Meta_Grind_reportIssue(x_381, x_367, x_368, x_369, x_370, x_371, x_372, x_373, x_374, x_375);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
if (lean_obj_tag(x_409) == 0)
{
lean_dec_ref(x_409);
x_14 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_410; 
x_410 = !lean_is_exclusive(x_409);
if (x_410 == 0)
{
return x_409;
}
else
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_409, 0);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_412, 0, x_411);
return x_412;
}
}
}
}
else
{
uint8_t x_413; 
lean_dec(x_395);
lean_free_object(x_388);
lean_free_object(x_383);
lean_free_object(x_381);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_1);
x_413 = !lean_is_exclusive(x_402);
if (x_413 == 0)
{
return x_402;
}
else
{
lean_object* x_414; lean_object* x_415; 
x_414 = lean_ctor_get(x_402, 0);
lean_inc(x_414);
lean_dec(x_402);
x_415 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_415, 0, x_414);
return x_415;
}
}
}
}
else
{
uint8_t x_416; 
lean_dec(x_395);
lean_dec(x_393);
lean_free_object(x_388);
lean_free_object(x_383);
lean_dec(x_387);
lean_free_object(x_381);
lean_dec(x_385);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_416 = !lean_is_exclusive(x_396);
if (x_416 == 0)
{
return x_396;
}
else
{
lean_object* x_417; lean_object* x_418; 
x_417 = lean_ctor_get(x_396, 0);
lean_inc(x_417);
lean_dec(x_396);
x_418 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_418, 0, x_417);
return x_418;
}
}
}
else
{
uint8_t x_419; 
lean_dec(x_393);
lean_free_object(x_388);
lean_free_object(x_383);
lean_dec(x_387);
lean_free_object(x_381);
lean_dec(x_385);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_419 = !lean_is_exclusive(x_394);
if (x_419 == 0)
{
return x_394;
}
else
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_ctor_get(x_394, 0);
lean_inc(x_420);
lean_dec(x_394);
x_421 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_421, 0, x_420);
return x_421;
}
}
}
else
{
uint8_t x_422; 
lean_free_object(x_388);
lean_free_object(x_383);
lean_dec(x_387);
lean_dec(x_386);
lean_free_object(x_381);
lean_dec(x_385);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_422 = !lean_is_exclusive(x_392);
if (x_422 == 0)
{
return x_392;
}
else
{
lean_object* x_423; lean_object* x_424; 
x_423 = lean_ctor_get(x_392, 0);
lean_inc(x_423);
lean_dec(x_392);
x_424 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_424, 0, x_423);
return x_424;
}
}
}
else
{
lean_object* x_425; lean_object* x_426; 
x_425 = lean_ctor_get(x_388, 1);
lean_inc(x_425);
lean_dec(x_388);
x_426 = l_Lean_MVarId_getType(x_425, x_372, x_373, x_374, x_375);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
lean_dec_ref(x_426);
x_428 = l_Lean_Meta_Sym_shareCommon___redArg(x_386, x_371);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
lean_dec_ref(x_428);
x_430 = l_Lean_Meta_Grind_getRootENode_x3f___redArg(x_429, x_366);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
lean_dec_ref(x_430);
if (lean_obj_tag(x_431) == 1)
{
lean_free_object(x_383);
lean_free_object(x_381);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_432; uint8_t x_433; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
lean_dec_ref(x_431);
x_433 = 0;
x_278 = x_371;
x_279 = x_370;
x_280 = lean_box(0);
x_281 = x_375;
x_282 = x_367;
x_283 = x_374;
x_284 = x_369;
x_285 = x_427;
x_286 = x_387;
x_287 = x_373;
x_288 = x_368;
x_289 = x_432;
x_290 = x_429;
x_291 = x_372;
x_292 = x_366;
x_293 = x_433;
goto block_365;
}
else
{
lean_object* x_434; uint8_t x_435; 
lean_dec_ref(x_385);
x_434 = lean_ctor_get(x_431, 0);
lean_inc(x_434);
lean_dec_ref(x_431);
x_435 = 1;
x_278 = x_371;
x_279 = x_370;
x_280 = lean_box(0);
x_281 = x_375;
x_282 = x_367;
x_283 = x_374;
x_284 = x_369;
x_285 = x_427;
x_286 = x_387;
x_287 = x_373;
x_288 = x_368;
x_289 = x_434;
x_290 = x_429;
x_291 = x_372;
x_292 = x_366;
x_293 = x_435;
goto block_365;
}
}
else
{
lean_object* x_436; 
lean_dec(x_431);
lean_dec(x_427);
lean_dec(x_387);
lean_dec(x_385);
lean_dec(x_366);
lean_dec_ref(x_2);
x_436 = l_Lean_Meta_Grind_getConfig___redArg(x_368);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; uint8_t x_438; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
lean_dec_ref(x_436);
x_438 = lean_ctor_get_uint8(x_437, sizeof(void*)*10 + 14);
lean_dec(x_437);
if (x_438 == 0)
{
lean_dec(x_429);
lean_free_object(x_383);
lean_free_object(x_381);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_1);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_439 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1;
x_440 = l_Lean_indentExpr(x_429);
x_441 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
x_442 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3;
lean_ctor_set_tag(x_383, 7);
lean_ctor_set(x_383, 1, x_442);
lean_ctor_set(x_383, 0, x_441);
x_443 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_381, 7);
lean_ctor_set(x_381, 1, x_443);
lean_ctor_set(x_381, 0, x_383);
x_444 = l_Lean_Meta_Grind_reportIssue(x_381, x_367, x_368, x_369, x_370, x_371, x_372, x_373, x_374, x_375);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
if (lean_obj_tag(x_444) == 0)
{
lean_dec_ref(x_444);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 x_446 = x_444;
} else {
 lean_dec_ref(x_444);
 x_446 = lean_box(0);
}
if (lean_is_scalar(x_446)) {
 x_447 = lean_alloc_ctor(1, 1, 0);
} else {
 x_447 = x_446;
}
lean_ctor_set(x_447, 0, x_445);
return x_447;
}
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_429);
lean_free_object(x_383);
lean_free_object(x_381);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_1);
x_448 = lean_ctor_get(x_436, 0);
lean_inc(x_448);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 x_449 = x_436;
} else {
 lean_dec_ref(x_436);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_449)) {
 x_450 = lean_alloc_ctor(1, 1, 0);
} else {
 x_450 = x_449;
}
lean_ctor_set(x_450, 0, x_448);
return x_450;
}
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_429);
lean_dec(x_427);
lean_free_object(x_383);
lean_dec(x_387);
lean_free_object(x_381);
lean_dec(x_385);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_451 = lean_ctor_get(x_430, 0);
lean_inc(x_451);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 x_452 = x_430;
} else {
 lean_dec_ref(x_430);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 1, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_451);
return x_453;
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_427);
lean_free_object(x_383);
lean_dec(x_387);
lean_free_object(x_381);
lean_dec(x_385);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_454 = lean_ctor_get(x_428, 0);
lean_inc(x_454);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 x_455 = x_428;
} else {
 lean_dec_ref(x_428);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(1, 1, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_454);
return x_456;
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_free_object(x_383);
lean_dec(x_387);
lean_dec(x_386);
lean_free_object(x_381);
lean_dec(x_385);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_457 = lean_ctor_get(x_426, 0);
lean_inc(x_457);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 x_458 = x_426;
} else {
 lean_dec_ref(x_426);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(1, 1, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_457);
return x_459;
}
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_460 = lean_ctor_get(x_381, 0);
x_461 = lean_ctor_get(x_383, 0);
x_462 = lean_ctor_get(x_383, 1);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_383);
x_463 = lean_st_ref_get(x_366);
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_465 = x_463;
} else {
 lean_dec_ref(x_463);
 x_465 = lean_box(0);
}
x_466 = l_Lean_MVarId_getType(x_464, x_372, x_373, x_374, x_375);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
lean_dec_ref(x_466);
x_468 = l_Lean_Meta_Sym_shareCommon___redArg(x_461, x_371);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
lean_dec_ref(x_468);
x_470 = l_Lean_Meta_Grind_getRootENode_x3f___redArg(x_469, x_366);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
lean_dec_ref(x_470);
if (lean_obj_tag(x_471) == 1)
{
lean_dec(x_465);
lean_free_object(x_381);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_472; uint8_t x_473; 
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
lean_dec_ref(x_471);
x_473 = 0;
x_278 = x_371;
x_279 = x_370;
x_280 = lean_box(0);
x_281 = x_375;
x_282 = x_367;
x_283 = x_374;
x_284 = x_369;
x_285 = x_467;
x_286 = x_462;
x_287 = x_373;
x_288 = x_368;
x_289 = x_472;
x_290 = x_469;
x_291 = x_372;
x_292 = x_366;
x_293 = x_473;
goto block_365;
}
else
{
lean_object* x_474; uint8_t x_475; 
lean_dec_ref(x_460);
x_474 = lean_ctor_get(x_471, 0);
lean_inc(x_474);
lean_dec_ref(x_471);
x_475 = 1;
x_278 = x_371;
x_279 = x_370;
x_280 = lean_box(0);
x_281 = x_375;
x_282 = x_367;
x_283 = x_374;
x_284 = x_369;
x_285 = x_467;
x_286 = x_462;
x_287 = x_373;
x_288 = x_368;
x_289 = x_474;
x_290 = x_469;
x_291 = x_372;
x_292 = x_366;
x_293 = x_475;
goto block_365;
}
}
else
{
lean_object* x_476; 
lean_dec(x_471);
lean_dec(x_467);
lean_dec(x_462);
lean_dec(x_460);
lean_dec(x_366);
lean_dec_ref(x_2);
x_476 = l_Lean_Meta_Grind_getConfig___redArg(x_368);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; uint8_t x_478; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
lean_dec_ref(x_476);
x_478 = lean_ctor_get_uint8(x_477, sizeof(void*)*10 + 14);
lean_dec(x_477);
if (x_478 == 0)
{
lean_dec(x_469);
lean_dec(x_465);
lean_free_object(x_381);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_1);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_479 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1;
x_480 = l_Lean_indentExpr(x_469);
if (lean_is_scalar(x_465)) {
 x_481 = lean_alloc_ctor(7, 2, 0);
} else {
 x_481 = x_465;
 lean_ctor_set_tag(x_481, 7);
}
lean_ctor_set(x_481, 0, x_479);
lean_ctor_set(x_481, 1, x_480);
x_482 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3;
x_483 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_482);
x_484 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_381, 7);
lean_ctor_set(x_381, 1, x_484);
lean_ctor_set(x_381, 0, x_483);
x_485 = l_Lean_Meta_Grind_reportIssue(x_381, x_367, x_368, x_369, x_370, x_371, x_372, x_373, x_374, x_375);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
if (lean_obj_tag(x_485) == 0)
{
lean_dec_ref(x_485);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 x_487 = x_485;
} else {
 lean_dec_ref(x_485);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(1, 1, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_486);
return x_488;
}
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
lean_dec(x_469);
lean_dec(x_465);
lean_free_object(x_381);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_1);
x_489 = lean_ctor_get(x_476, 0);
lean_inc(x_489);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 x_490 = x_476;
} else {
 lean_dec_ref(x_476);
 x_490 = lean_box(0);
}
if (lean_is_scalar(x_490)) {
 x_491 = lean_alloc_ctor(1, 1, 0);
} else {
 x_491 = x_490;
}
lean_ctor_set(x_491, 0, x_489);
return x_491;
}
}
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_469);
lean_dec(x_467);
lean_dec(x_465);
lean_dec(x_462);
lean_free_object(x_381);
lean_dec(x_460);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_492 = lean_ctor_get(x_470, 0);
lean_inc(x_492);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 x_493 = x_470;
} else {
 lean_dec_ref(x_470);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(1, 1, 0);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_492);
return x_494;
}
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_dec(x_467);
lean_dec(x_465);
lean_dec(x_462);
lean_free_object(x_381);
lean_dec(x_460);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_495 = lean_ctor_get(x_468, 0);
lean_inc(x_495);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 x_496 = x_468;
} else {
 lean_dec_ref(x_468);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(1, 1, 0);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_495);
return x_497;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_465);
lean_dec(x_462);
lean_dec(x_461);
lean_free_object(x_381);
lean_dec(x_460);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_498 = lean_ctor_get(x_466, 0);
lean_inc(x_498);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 x_499 = x_466;
} else {
 lean_dec_ref(x_466);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 1, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_498);
return x_500;
}
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_501 = lean_ctor_get(x_381, 1);
x_502 = lean_ctor_get(x_381, 0);
lean_inc(x_501);
lean_inc(x_502);
lean_dec(x_381);
x_503 = lean_ctor_get(x_501, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_501, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_505 = x_501;
} else {
 lean_dec_ref(x_501);
 x_505 = lean_box(0);
}
x_506 = lean_st_ref_get(x_366);
x_507 = lean_ctor_get(x_506, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_506)) {
 lean_ctor_release(x_506, 0);
 lean_ctor_release(x_506, 1);
 x_508 = x_506;
} else {
 lean_dec_ref(x_506);
 x_508 = lean_box(0);
}
x_509 = l_Lean_MVarId_getType(x_507, x_372, x_373, x_374, x_375);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; 
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
lean_dec_ref(x_509);
x_511 = l_Lean_Meta_Sym_shareCommon___redArg(x_503, x_371);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
lean_dec_ref(x_511);
x_513 = l_Lean_Meta_Grind_getRootENode_x3f___redArg(x_512, x_366);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
lean_dec_ref(x_513);
if (lean_obj_tag(x_514) == 1)
{
lean_dec(x_508);
lean_dec(x_505);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_515; uint8_t x_516; 
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
lean_dec_ref(x_514);
x_516 = 0;
x_278 = x_371;
x_279 = x_370;
x_280 = lean_box(0);
x_281 = x_375;
x_282 = x_367;
x_283 = x_374;
x_284 = x_369;
x_285 = x_510;
x_286 = x_504;
x_287 = x_373;
x_288 = x_368;
x_289 = x_515;
x_290 = x_512;
x_291 = x_372;
x_292 = x_366;
x_293 = x_516;
goto block_365;
}
else
{
lean_object* x_517; uint8_t x_518; 
lean_dec_ref(x_502);
x_517 = lean_ctor_get(x_514, 0);
lean_inc(x_517);
lean_dec_ref(x_514);
x_518 = 1;
x_278 = x_371;
x_279 = x_370;
x_280 = lean_box(0);
x_281 = x_375;
x_282 = x_367;
x_283 = x_374;
x_284 = x_369;
x_285 = x_510;
x_286 = x_504;
x_287 = x_373;
x_288 = x_368;
x_289 = x_517;
x_290 = x_512;
x_291 = x_372;
x_292 = x_366;
x_293 = x_518;
goto block_365;
}
}
else
{
lean_object* x_519; 
lean_dec(x_514);
lean_dec(x_510);
lean_dec(x_504);
lean_dec(x_502);
lean_dec(x_366);
lean_dec_ref(x_2);
x_519 = l_Lean_Meta_Grind_getConfig___redArg(x_368);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; uint8_t x_521; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
lean_dec_ref(x_519);
x_521 = lean_ctor_get_uint8(x_520, sizeof(void*)*10 + 14);
lean_dec(x_520);
if (x_521 == 0)
{
lean_dec(x_512);
lean_dec(x_508);
lean_dec(x_505);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_1);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_522 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1;
x_523 = l_Lean_indentExpr(x_512);
if (lean_is_scalar(x_508)) {
 x_524 = lean_alloc_ctor(7, 2, 0);
} else {
 x_524 = x_508;
 lean_ctor_set_tag(x_524, 7);
}
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_523);
x_525 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3;
if (lean_is_scalar(x_505)) {
 x_526 = lean_alloc_ctor(7, 2, 0);
} else {
 x_526 = x_505;
 lean_ctor_set_tag(x_526, 7);
}
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_525);
x_527 = l_Lean_indentExpr(x_1);
x_528 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_528, 0, x_526);
lean_ctor_set(x_528, 1, x_527);
x_529 = l_Lean_Meta_Grind_reportIssue(x_528, x_367, x_368, x_369, x_370, x_371, x_372, x_373, x_374, x_375);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
if (lean_obj_tag(x_529) == 0)
{
lean_dec_ref(x_529);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 x_531 = x_529;
} else {
 lean_dec_ref(x_529);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 1, 0);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_530);
return x_532;
}
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_512);
lean_dec(x_508);
lean_dec(x_505);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_1);
x_533 = lean_ctor_get(x_519, 0);
lean_inc(x_533);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 x_534 = x_519;
} else {
 lean_dec_ref(x_519);
 x_534 = lean_box(0);
}
if (lean_is_scalar(x_534)) {
 x_535 = lean_alloc_ctor(1, 1, 0);
} else {
 x_535 = x_534;
}
lean_ctor_set(x_535, 0, x_533);
return x_535;
}
}
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_512);
lean_dec(x_510);
lean_dec(x_508);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_502);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_536 = lean_ctor_get(x_513, 0);
lean_inc(x_536);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 x_537 = x_513;
} else {
 lean_dec_ref(x_513);
 x_537 = lean_box(0);
}
if (lean_is_scalar(x_537)) {
 x_538 = lean_alloc_ctor(1, 1, 0);
} else {
 x_538 = x_537;
}
lean_ctor_set(x_538, 0, x_536);
return x_538;
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_510);
lean_dec(x_508);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_502);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_539 = lean_ctor_get(x_511, 0);
lean_inc(x_539);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 x_540 = x_511;
} else {
 lean_dec_ref(x_511);
 x_540 = lean_box(0);
}
if (lean_is_scalar(x_540)) {
 x_541 = lean_alloc_ctor(1, 1, 0);
} else {
 x_541 = x_540;
}
lean_ctor_set(x_541, 0, x_539);
return x_541;
}
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
lean_dec(x_508);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_503);
lean_dec(x_502);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_542 = lean_ctor_get(x_509, 0);
lean_inc(x_542);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 x_543 = x_509;
} else {
 lean_dec_ref(x_509);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(1, 1, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_542);
return x_544;
}
}
}
else
{
lean_object* x_545; 
lean_dec(x_380);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_545 = lean_box(0);
lean_ctor_set(x_377, 0, x_545);
return x_377;
}
}
else
{
lean_object* x_546; lean_object* x_547; 
x_546 = lean_ctor_get(x_377, 0);
lean_inc(x_546);
lean_dec(x_377);
x_547 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_546);
if (lean_obj_tag(x_547) == 1)
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
lean_dec_ref(x_547);
x_549 = lean_ctor_get(x_548, 1);
lean_inc(x_549);
x_550 = lean_ctor_get(x_548, 0);
lean_inc(x_550);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 x_551 = x_548;
} else {
 lean_dec_ref(x_548);
 x_551 = lean_box(0);
}
x_552 = lean_ctor_get(x_549, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_549, 1);
lean_inc(x_553);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_554 = x_549;
} else {
 lean_dec_ref(x_549);
 x_554 = lean_box(0);
}
x_555 = lean_st_ref_get(x_366);
x_556 = lean_ctor_get(x_555, 1);
lean_inc(x_556);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 lean_ctor_release(x_555, 1);
 x_557 = x_555;
} else {
 lean_dec_ref(x_555);
 x_557 = lean_box(0);
}
x_558 = l_Lean_MVarId_getType(x_556, x_372, x_373, x_374, x_375);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; lean_object* x_560; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
lean_dec_ref(x_558);
x_560 = l_Lean_Meta_Sym_shareCommon___redArg(x_552, x_371);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
lean_dec_ref(x_560);
x_562 = l_Lean_Meta_Grind_getRootENode_x3f___redArg(x_561, x_366);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
lean_dec_ref(x_562);
if (lean_obj_tag(x_563) == 1)
{
lean_dec(x_557);
lean_dec(x_554);
lean_dec(x_551);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_564; uint8_t x_565; 
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
lean_dec_ref(x_563);
x_565 = 0;
x_278 = x_371;
x_279 = x_370;
x_280 = lean_box(0);
x_281 = x_375;
x_282 = x_367;
x_283 = x_374;
x_284 = x_369;
x_285 = x_559;
x_286 = x_553;
x_287 = x_373;
x_288 = x_368;
x_289 = x_564;
x_290 = x_561;
x_291 = x_372;
x_292 = x_366;
x_293 = x_565;
goto block_365;
}
else
{
lean_object* x_566; uint8_t x_567; 
lean_dec_ref(x_550);
x_566 = lean_ctor_get(x_563, 0);
lean_inc(x_566);
lean_dec_ref(x_563);
x_567 = 1;
x_278 = x_371;
x_279 = x_370;
x_280 = lean_box(0);
x_281 = x_375;
x_282 = x_367;
x_283 = x_374;
x_284 = x_369;
x_285 = x_559;
x_286 = x_553;
x_287 = x_373;
x_288 = x_368;
x_289 = x_566;
x_290 = x_561;
x_291 = x_372;
x_292 = x_366;
x_293 = x_567;
goto block_365;
}
}
else
{
lean_object* x_568; 
lean_dec(x_563);
lean_dec(x_559);
lean_dec(x_553);
lean_dec(x_550);
lean_dec(x_366);
lean_dec_ref(x_2);
x_568 = l_Lean_Meta_Grind_getConfig___redArg(x_368);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; uint8_t x_570; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
lean_dec_ref(x_568);
x_570 = lean_ctor_get_uint8(x_569, sizeof(void*)*10 + 14);
lean_dec(x_569);
if (x_570 == 0)
{
lean_dec(x_561);
lean_dec(x_557);
lean_dec(x_554);
lean_dec(x_551);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_1);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_571 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1;
x_572 = l_Lean_indentExpr(x_561);
if (lean_is_scalar(x_557)) {
 x_573 = lean_alloc_ctor(7, 2, 0);
} else {
 x_573 = x_557;
 lean_ctor_set_tag(x_573, 7);
}
lean_ctor_set(x_573, 0, x_571);
lean_ctor_set(x_573, 1, x_572);
x_574 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3;
if (lean_is_scalar(x_554)) {
 x_575 = lean_alloc_ctor(7, 2, 0);
} else {
 x_575 = x_554;
 lean_ctor_set_tag(x_575, 7);
}
lean_ctor_set(x_575, 0, x_573);
lean_ctor_set(x_575, 1, x_574);
x_576 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_551)) {
 x_577 = lean_alloc_ctor(7, 2, 0);
} else {
 x_577 = x_551;
 lean_ctor_set_tag(x_577, 7);
}
lean_ctor_set(x_577, 0, x_575);
lean_ctor_set(x_577, 1, x_576);
x_578 = l_Lean_Meta_Grind_reportIssue(x_577, x_367, x_368, x_369, x_370, x_371, x_372, x_373, x_374, x_375);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
if (lean_obj_tag(x_578) == 0)
{
lean_dec_ref(x_578);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 x_580 = x_578;
} else {
 lean_dec_ref(x_578);
 x_580 = lean_box(0);
}
if (lean_is_scalar(x_580)) {
 x_581 = lean_alloc_ctor(1, 1, 0);
} else {
 x_581 = x_580;
}
lean_ctor_set(x_581, 0, x_579);
return x_581;
}
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
lean_dec(x_561);
lean_dec(x_557);
lean_dec(x_554);
lean_dec(x_551);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec_ref(x_1);
x_582 = lean_ctor_get(x_568, 0);
lean_inc(x_582);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 x_583 = x_568;
} else {
 lean_dec_ref(x_568);
 x_583 = lean_box(0);
}
if (lean_is_scalar(x_583)) {
 x_584 = lean_alloc_ctor(1, 1, 0);
} else {
 x_584 = x_583;
}
lean_ctor_set(x_584, 0, x_582);
return x_584;
}
}
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_561);
lean_dec(x_559);
lean_dec(x_557);
lean_dec(x_554);
lean_dec(x_553);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_585 = lean_ctor_get(x_562, 0);
lean_inc(x_585);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 x_586 = x_562;
} else {
 lean_dec_ref(x_562);
 x_586 = lean_box(0);
}
if (lean_is_scalar(x_586)) {
 x_587 = lean_alloc_ctor(1, 1, 0);
} else {
 x_587 = x_586;
}
lean_ctor_set(x_587, 0, x_585);
return x_587;
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_559);
lean_dec(x_557);
lean_dec(x_554);
lean_dec(x_553);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_588 = lean_ctor_get(x_560, 0);
lean_inc(x_588);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 x_589 = x_560;
} else {
 lean_dec_ref(x_560);
 x_589 = lean_box(0);
}
if (lean_is_scalar(x_589)) {
 x_590 = lean_alloc_ctor(1, 1, 0);
} else {
 x_590 = x_589;
}
lean_ctor_set(x_590, 0, x_588);
return x_590;
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
lean_dec(x_557);
lean_dec(x_554);
lean_dec(x_553);
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_591 = lean_ctor_get(x_558, 0);
lean_inc(x_591);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 x_592 = x_558;
} else {
 lean_dec_ref(x_558);
 x_592 = lean_box(0);
}
if (lean_is_scalar(x_592)) {
 x_593 = lean_alloc_ctor(1, 1, 0);
} else {
 x_593 = x_592;
}
lean_ctor_set(x_593, 0, x_591);
return x_593;
}
}
else
{
lean_object* x_594; lean_object* x_595; 
lean_dec(x_547);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_594 = lean_box(0);
x_595 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_595, 0, x_594);
return x_595;
}
}
}
else
{
uint8_t x_596; 
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_370);
lean_dec(x_369);
lean_dec_ref(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_596 = !lean_is_exclusive(x_377);
if (x_596 == 0)
{
return x_377;
}
else
{
lean_object* x_597; lean_object* x_598; 
x_597 = lean_ctor_get(x_377, 0);
lean_inc(x_597);
lean_dec(x_377);
x_598 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_598, 0, x_597);
return x_598;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_9, x_8);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_10);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_10);
x_24 = lean_array_uget(x_7, x_9);
lean_inc(x_20);
lean_inc_ref(x_19);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc_ref(x_1);
x_25 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(x_1, x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = 0;
x_30 = 1;
x_31 = l_Lean_Meta_mkLambdaFVars(x_2, x_28, x_29, x_3, x_29, x_3, x_30, x_17, x_18, x_19, x_20);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_Lean_Expr_app___override(x_4, x_33);
lean_ctor_set(x_26, 0, x_34);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_5);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lean_Expr_app___override(x_4, x_37);
lean_ctor_set(x_26, 0, x_38);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_26);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_5);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_free_object(x_26);
lean_dec_ref(x_4);
x_42 = !lean_is_exclusive(x_31);
if (x_42 == 0)
{
return x_31;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
lean_dec(x_31);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_26, 0);
lean_inc(x_45);
lean_dec(x_26);
x_46 = 0;
x_47 = 1;
x_48 = l_Lean_Meta_mkLambdaFVars(x_2, x_45, x_46, x_3, x_46, x_3, x_47, x_17, x_18, x_19, x_20);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = l_Lean_Expr_app___override(x_4, x_49);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_5);
if (lean_is_scalar(x_50)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_50;
}
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_4);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_57 = x_48;
} else {
 lean_dec_ref(x_48);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
}
}
else
{
size_t x_59; size_t x_60; 
lean_dec(x_26);
x_59 = 1;
x_60 = lean_usize_add(x_9, x_59);
lean_inc_ref(x_6);
{
size_t _tmp_8 = x_60;
lean_object* _tmp_9 = x_6;
x_9 = _tmp_8;
x_10 = _tmp_9;
}
goto _start;
}
}
else
{
uint8_t x_62; 
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_62 = !lean_is_exclusive(x_25);
if (x_62 == 0)
{
return x_25;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_25, 0);
lean_inc(x_63);
lean_dec(x_25);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_17 = lean_box(0);
x_18 = lean_box(0);
x_19 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
x_20 = lean_array_size(x_4);
x_21 = 0;
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(x_1, x_4, x_2, x_3, x_18, x_19, x_4, x_20, x_21, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_ctor_set(x_22, 0, x_17);
return x_22;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_17);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_22);
if (x_32 == 0)
{
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_22, 0);
lean_inc(x_33);
lean_dec(x_22);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_22 = lean_unbox(x_3);
x_23 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_24 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__0(x_1, x_2, x_22, x_4, x_5, x_6, x_7, x_23, x_24, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec_ref(x_7);
lean_dec_ref(x_2);
return x_25;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_21; lean_object* x_22; uint8_t x_27; 
x_27 = lean_usize_dec_lt(x_8, x_7);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_9);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_76; 
lean_dec_ref(x_9);
x_29 = lean_array_uget(x_6, x_8);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_29);
x_76 = lean_infer_type(x_29, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_77);
x_78 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(x_77, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_dec(x_77);
lean_dec(x_29);
lean_inc_ref(x_5);
x_21 = x_5;
x_22 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__3));
x_82 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_81, x_18);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_dec(x_77);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_30 = x_10;
x_31 = x_11;
x_32 = x_12;
x_33 = x_13;
x_34 = x_14;
x_35 = x_15;
x_36 = x_16;
x_37 = x_17;
x_38 = x_18;
x_39 = x_19;
x_40 = lean_box(0);
goto block_75;
}
else
{
lean_object* x_85; 
x_85 = l_Lean_Meta_Grind_updateLastTag(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_85);
x_86 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___closed__1;
x_87 = l_Lean_MessageData_ofExpr(x_77);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_81, x_88, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_89) == 0)
{
lean_dec_ref(x_89);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_30 = x_10;
x_31 = x_11;
x_32 = x_12;
x_33 = x_13;
x_34 = x_14;
x_35 = x_15;
x_36 = x_16;
x_37 = x_17;
x_38 = x_18;
x_39 = x_19;
x_40 = lean_box(0);
goto block_75;
}
else
{
uint8_t x_90; 
lean_dec(x_29);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_77);
lean_dec(x_29);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_93 = !lean_is_exclusive(x_85);
if (x_93 == 0)
{
return x_85;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_85, 0);
lean_inc(x_94);
lean_dec(x_85);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_77);
lean_dec(x_29);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_96 = !lean_is_exclusive(x_82);
if (x_96 == 0)
{
return x_82;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_82, 0);
lean_inc(x_97);
lean_dec(x_82);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_77);
lean_dec(x_29);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_99 = !lean_is_exclusive(x_78);
if (x_99 == 0)
{
return x_78;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
lean_dec(x_78);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_29);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_102 = !lean_is_exclusive(x_76);
if (x_102 == 0)
{
return x_76;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_76, 0);
lean_inc(x_103);
lean_dec(x_76);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
block_75:
{
lean_object* x_41; 
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc_ref(x_1);
x_41 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(x_1, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
if (lean_obj_tag(x_42) == 1)
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = 0;
x_46 = 1;
x_47 = l_Lean_Meta_mkLambdaFVars(x_2, x_44, x_45, x_3, x_45, x_3, x_46, x_36, x_37, x_38, x_39);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
lean_ctor_set(x_42, 0, x_49);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_42);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_4);
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
lean_ctor_set(x_42, 0, x_52);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_42);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_4);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_free_object(x_42);
x_56 = !lean_is_exclusive(x_47);
if (x_56 == 0)
{
return x_47;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_47, 0);
lean_inc(x_57);
lean_dec(x_47);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_42, 0);
lean_inc(x_59);
lean_dec(x_42);
x_60 = 0;
x_61 = 1;
x_62 = l_Lean_Meta_mkLambdaFVars(x_2, x_59, x_60, x_3, x_60, x_3, x_61, x_36, x_37, x_38, x_39);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_63);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_4);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
}
}
else
{
lean_dec(x_42);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_inc_ref(x_5);
x_21 = x_5;
x_22 = lean_box(0);
goto block_26;
}
}
else
{
uint8_t x_72; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_41);
if (x_72 == 0)
{
return x_41;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_41, 0);
lean_inc(x_73);
lean_dec(x_41);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
block_26:
{
size_t x_23; size_t x_24; 
x_23 = 1;
x_24 = lean_usize_add(x_8, x_23);
x_8 = x_24;
x_9 = x_21;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_unbox(x_3);
x_22 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_23 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0(x_1, x_2, x_21, x_4, x_5, x_6, x_22, x_23, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_24;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_21; lean_object* x_22; uint8_t x_27; 
x_27 = lean_usize_dec_lt(x_8, x_7);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_9);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_76; 
lean_dec_ref(x_9);
x_29 = lean_array_uget(x_6, x_8);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_29);
x_76 = lean_infer_type(x_29, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_77);
x_78 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp(x_77, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_dec(x_77);
lean_dec(x_29);
lean_inc_ref(x_5);
x_21 = x_5;
x_22 = lean_box(0);
goto block_26;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__3));
x_82 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_81, x_18);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_dec(x_77);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_30 = x_10;
x_31 = x_11;
x_32 = x_12;
x_33 = x_13;
x_34 = x_14;
x_35 = x_15;
x_36 = x_16;
x_37 = x_17;
x_38 = x_18;
x_39 = x_19;
x_40 = lean_box(0);
goto block_75;
}
else
{
lean_object* x_85; 
x_85 = l_Lean_Meta_Grind_updateLastTag(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_85);
x_86 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___closed__1;
x_87 = l_Lean_MessageData_ofExpr(x_77);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_81, x_88, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_89) == 0)
{
lean_dec_ref(x_89);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_30 = x_10;
x_31 = x_11;
x_32 = x_12;
x_33 = x_13;
x_34 = x_14;
x_35 = x_15;
x_36 = x_16;
x_37 = x_17;
x_38 = x_18;
x_39 = x_19;
x_40 = lean_box(0);
goto block_75;
}
else
{
uint8_t x_90; 
lean_dec(x_29);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
return x_89;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_77);
lean_dec(x_29);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_93 = !lean_is_exclusive(x_85);
if (x_93 == 0)
{
return x_85;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_85, 0);
lean_inc(x_94);
lean_dec(x_85);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_77);
lean_dec(x_29);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_96 = !lean_is_exclusive(x_82);
if (x_96 == 0)
{
return x_82;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_82, 0);
lean_inc(x_97);
lean_dec(x_82);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_77);
lean_dec(x_29);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_99 = !lean_is_exclusive(x_78);
if (x_99 == 0)
{
return x_78;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_78, 0);
lean_inc(x_100);
lean_dec(x_78);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_29);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_102 = !lean_is_exclusive(x_76);
if (x_102 == 0)
{
return x_76;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_76, 0);
lean_inc(x_103);
lean_dec(x_76);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
block_75:
{
lean_object* x_41; 
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc_ref(x_1);
x_41 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f(x_1, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
if (lean_obj_tag(x_42) == 1)
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = 0;
x_46 = 1;
x_47 = l_Lean_Meta_mkLambdaFVars(x_2, x_44, x_45, x_3, x_45, x_3, x_46, x_36, x_37, x_38, x_39);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
lean_ctor_set(x_42, 0, x_49);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_42);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_4);
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
lean_ctor_set(x_42, 0, x_52);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_42);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_4);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_free_object(x_42);
x_56 = !lean_is_exclusive(x_47);
if (x_56 == 0)
{
return x_47;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_47, 0);
lean_inc(x_57);
lean_dec(x_47);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_42, 0);
lean_inc(x_59);
lean_dec(x_42);
x_60 = 0;
x_61 = 1;
x_62 = l_Lean_Meta_mkLambdaFVars(x_2, x_59, x_60, x_3, x_60, x_3, x_61, x_36, x_37, x_38, x_39);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_63);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_4);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(0, 1, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_62, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
}
}
else
{
lean_dec(x_42);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_inc_ref(x_5);
x_21 = x_5;
x_22 = lean_box(0);
goto block_26;
}
}
else
{
uint8_t x_72; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_72 = !lean_is_exclusive(x_41);
if (x_72 == 0)
{
return x_41;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_41, 0);
lean_inc(x_73);
lean_dec(x_41);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
}
}
}
block_26:
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = 1;
x_24 = lean_usize_add(x_8, x_23);
x_25 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_24, x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___redArg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_unbox(x_3);
x_22 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_23 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_24 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___redArg(x_1, x_2, x_21, x_4, x_5, x_6, x_22, x_23, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_24;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___lam__0___closed__0));
x_19 = lean_array_size(x_3);
x_20 = 0;
x_21 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___redArg(x_1, x_3, x_2, x_17, x_18, x_3, x_19, x_20, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_ctor_set(x_21, 0, x_16);
return x_21;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_16);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_21, 0);
lean_inc(x_32);
lean_dec(x_21);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
x_17 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc_ref(x_1);
x_13 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_15 = x_13;
} else {
 lean_dec_ref(x_13);
 x_15 = lean_box(0);
}
x_19 = l_Lean_Expr_cleanupAnnotations(x_14);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_21);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_23 = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
x_24 = l_Lean_Expr_isConstOf(x_22, x_23);
lean_dec_ref(x_22);
if (x_24 == 0)
{
lean_dec_ref(x_21);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_18;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
lean_dec(x_15);
x_25 = lean_box(x_24);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___lam__0___boxed), 15, 2);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_25);
x_27 = 0;
x_28 = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f_spec__1___redArg(x_21, x_26, x_27, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_28;
}
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
if (lean_is_scalar(x_15)) {
 x_17 = lean_alloc_ctor(0, 1, 0);
} else {
 x_17 = x_15;
}
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, size_t x_13, size_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25) {
_start:
{
lean_object* x_27; 
x_27 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
return x_27;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
_start:
{
uint8_t x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_27 = lean_unbox(x_3);
x_28 = lean_unbox_usize(x_13);
lean_dec(x_13);
x_29 = lean_unbox_usize(x_14);
lean_dec(x_14);
x_30 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0(x_1, x_2, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_28, x_29, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_30;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc_ref(x_1);
x_13 = l_Lean_Meta_Grind_getRootENode___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_17 = lean_ctor_get_uint8(x_15, sizeof(void*)*11 + 1);
if (x_17 == 0)
{
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_18; 
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_18);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_13);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_19);
lean_dec(x_15);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_19);
x_20 = l_Lean_Meta_isConstructorApp_x3f(x_19, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 4);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Expr_getAppNumArgs(x_19);
x_27 = lean_nat_add(x_24, x_25);
lean_dec(x_25);
x_28 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__1;
lean_inc(x_26);
x_29 = lean_mk_array(x_26, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_26, x_30);
lean_dec(x_26);
lean_inc_ref(x_19);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_19, x_29, x_31);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(x_27, x_16, x_24, x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_27);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_38, 1);
x_40 = lean_unbox(x_39);
if (x_40 == 0)
{
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_19);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_free_object(x_36);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Lean_Expr_getAppFn(x_19);
lean_dec_ref(x_19);
x_43 = l_Lean_mkAppN(x_42, x_41);
lean_dec(x_41);
x_44 = l_Lean_Meta_Sym_shareCommon___redArg(x_43, x_7);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_ctor_get(x_45, 1);
x_47 = lean_unbox(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_45);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_19);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec(x_45);
x_50 = l_Lean_Expr_getAppFn(x_19);
lean_dec_ref(x_19);
x_51 = l_Lean_mkAppN(x_50, x_49);
lean_dec(x_49);
x_52 = l_Lean_Meta_Sym_shareCommon___redArg(x_51, x_7);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec_ref(x_19);
x_53 = !lean_is_exclusive(x_36);
if (x_53 == 0)
{
return x_36;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_36, 0);
lean_inc(x_54);
lean_dec(x_36);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_20, 0);
lean_inc(x_56);
lean_dec(x_20);
if (lean_obj_tag(x_56) == 1)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_ctor_get(x_57, 3);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 4);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Expr_getAppNumArgs(x_19);
x_61 = lean_nat_add(x_58, x_59);
lean_dec(x_59);
x_62 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__1;
lean_inc(x_60);
x_63 = lean_mk_array(x_60, x_62);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_sub(x_60, x_64);
lean_dec(x_60);
lean_inc_ref(x_19);
x_66 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_19, x_63, x_65);
x_67 = 0;
x_68 = lean_box(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(x_61, x_16, x_58, x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_61);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_71, 1);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_71);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_19);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_72);
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
lean_dec(x_71);
x_77 = l_Lean_Expr_getAppFn(x_19);
lean_dec_ref(x_19);
x_78 = l_Lean_mkAppN(x_77, x_76);
lean_dec(x_76);
x_79 = l_Lean_Meta_Sym_shareCommon___redArg(x_78, x_7);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec_ref(x_19);
x_80 = lean_ctor_get(x_70, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_81 = x_70;
} else {
 lean_dec_ref(x_70);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
}
else
{
lean_object* x_83; 
lean_dec(x_56);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_19);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec_ref(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_84 = !lean_is_exclusive(x_20);
if (x_84 == 0)
{
return x_20;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_20, 0);
lean_inc(x_85);
lean_dec(x_20);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
}
else
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_13, 0);
lean_inc(x_87);
lean_dec(x_13);
x_88 = lean_ctor_get_uint8(x_87, sizeof(void*)*11 + 2);
if (x_88 == 0)
{
uint8_t x_89; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_89 = lean_ctor_get_uint8(x_87, sizeof(void*)*11 + 1);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_87);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_1);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_1);
x_91 = lean_ctor_get(x_87, 0);
lean_inc_ref(x_91);
lean_dec(x_87);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec_ref(x_1);
x_93 = lean_ctor_get(x_87, 0);
lean_inc_ref(x_93);
lean_dec(x_87);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_93);
x_94 = l_Lean_Meta_isConstructorApp_x3f(x_93, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_96 = x_94;
} else {
 lean_dec_ref(x_94);
 x_96 = lean_box(0);
}
if (lean_obj_tag(x_95) == 1)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_96);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
lean_dec_ref(x_95);
x_98 = lean_ctor_get(x_97, 3);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 4);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Expr_getAppNumArgs(x_93);
x_101 = lean_nat_add(x_98, x_99);
lean_dec(x_99);
x_102 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__1;
lean_inc(x_100);
x_103 = lean_mk_array(x_100, x_102);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_sub(x_100, x_104);
lean_dec(x_100);
lean_inc_ref(x_93);
x_106 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_93, x_103, x_105);
x_107 = 0;
x_108 = lean_box(x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(x_101, x_88, x_98, x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_101);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_111, 1);
x_114 = lean_unbox(x_113);
if (x_114 == 0)
{
lean_object* x_115; 
lean_dec(x_111);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 1, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_93);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_112);
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
lean_dec(x_111);
x_117 = l_Lean_Expr_getAppFn(x_93);
lean_dec_ref(x_93);
x_118 = l_Lean_mkAppN(x_117, x_116);
lean_dec(x_116);
x_119 = l_Lean_Meta_Sym_shareCommon___redArg(x_118, x_7);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec_ref(x_93);
x_120 = lean_ctor_get(x_110, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_121 = x_110;
} else {
 lean_dec_ref(x_110);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
else
{
lean_object* x_123; 
lean_dec(x_95);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
if (lean_is_scalar(x_96)) {
 x_123 = lean_alloc_ctor(0, 1, 0);
} else {
 x_123 = x_96;
}
lean_ctor_set(x_123, 0, x_93);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec_ref(x_93);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
x_124 = lean_ctor_get(x_94, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_125 = x_94;
} else {
 lean_dec_ref(x_94);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 1, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_124);
return x_126;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_127 = !lean_is_exclusive(x_13);
if (x_127 == 0)
{
return x_13;
}
else
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_13, 0);
lean_inc(x_128);
lean_dec(x_13);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_lt(x_3, x_1);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
x_21 = l_Lean_instInhabitedExpr;
x_22 = lean_array_get_borrowed(x_21, x_19, x_3);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_22);
x_23 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_30 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_22, x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_20);
x_31 = lean_array_set(x_19, x_3, x_24);
x_32 = lean_box(x_2);
lean_ctor_set(x_4, 1, x_32);
lean_ctor_set(x_4, 0, x_31);
x_25 = x_4;
goto block_29;
}
else
{
lean_dec(x_24);
x_25 = x_4;
goto block_29;
}
block_29:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
lean_dec(x_3);
x_3 = x_27;
x_4 = x_25;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_4);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_38 = l_Lean_instInhabitedExpr;
x_39 = lean_array_get_borrowed(x_38, x_36, x_3);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_39);
x_40 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_47; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_47 = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(x_39, x_41);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_37);
x_48 = lean_array_set(x_36, x_3, x_41);
x_49 = lean_box(x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_42 = x_50;
goto block_46;
}
else
{
lean_object* x_51; 
lean_dec(x_41);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_37);
x_42 = x_51;
goto block_46;
}
block_46:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_3, x_43);
lean_dec(x_3);
x_3 = x_44;
x_4 = x_42;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_52 = lean_ctor_get(x_40, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_53 = x_40;
} else {
 lean_dec_ref(x_40);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
x_17 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_19; 
x_19 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___redArg(x_1, x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_2);
x_20 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go_spec__0(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(x_1, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = lean_apply_11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___lam__0___boxed), 12, 7);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_5);
lean_closure_set(x_14, 4, x_6);
lean_closure_set(x_14, 5, x_7);
lean_closure_set(x_14, 6, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), x_2, x_14, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
x_15 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
x_16 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
lean_inc_ref(x_5);
x_6 = l_Lean_MetavarContext_getDecl(x_5, x_1);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__0;
x_14 = l_ReaderT_instMonad___redArg(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 2);
x_21 = lean_ctor_get(x_16, 3);
x_22 = lean_ctor_get(x_16, 4);
x_23 = lean_ctor_get(x_16, 1);
lean_dec(x_23);
x_24 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__1));
x_25 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__2));
lean_inc_ref(x_19);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_26, 0, x_19);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_27, 0, x_19);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_29, 0, x_22);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_30, 0, x_21);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_31, 0, x_20);
lean_ctor_set(x_16, 4, x_29);
lean_ctor_set(x_16, 3, x_30);
lean_ctor_set(x_16, 2, x_31);
lean_ctor_set(x_16, 1, x_24);
lean_ctor_set(x_16, 0, x_28);
lean_ctor_set(x_14, 1, x_25);
x_32 = l_ReaderT_instMonad___redArg(x_14);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_37 = lean_ctor_get(x_34, 0);
x_38 = lean_ctor_get(x_34, 2);
x_39 = lean_ctor_get(x_34, 3);
x_40 = lean_ctor_get(x_34, 4);
x_41 = lean_ctor_get(x_34, 1);
lean_dec(x_41);
x_42 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__3));
x_43 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__4));
lean_inc_ref(x_37);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_44, 0, x_37);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_37);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_47, 0, x_40);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_48, 0, x_39);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_49, 0, x_38);
lean_ctor_set(x_34, 4, x_47);
lean_ctor_set(x_34, 3, x_48);
lean_ctor_set(x_34, 2, x_49);
lean_ctor_set(x_34, 1, x_42);
lean_ctor_set(x_34, 0, x_46);
lean_ctor_set(x_32, 1, x_43);
x_50 = l_ReaderT_instMonad___redArg(x_32);
x_51 = l_ReaderT_instMonad___redArg(x_50);
x_52 = l_ReaderT_instMonad___redArg(x_51);
x_53 = l_ReaderT_instMonad___redArg(x_52);
x_54 = l_ReaderT_instMonad___redArg(x_53);
x_55 = l_ReaderT_instMonad___redArg(x_54);
x_56 = 0;
x_57 = lean_box(x_56);
x_58 = l_instInhabitedOfMonad___redArg(x_55, x_57);
x_59 = lean_panic_fn(x_58, x_1);
x_60 = lean_apply_11(x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_61 = lean_ctor_get(x_34, 0);
x_62 = lean_ctor_get(x_34, 2);
x_63 = lean_ctor_get(x_34, 3);
x_64 = lean_ctor_get(x_34, 4);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_34);
x_65 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__3));
x_66 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__4));
lean_inc_ref(x_61);
x_67 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_67, 0, x_61);
x_68 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_68, 0, x_61);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_70, 0, x_64);
x_71 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_71, 0, x_63);
x_72 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_72, 0, x_62);
x_73 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_73, 0, x_69);
lean_ctor_set(x_73, 1, x_65);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_71);
lean_ctor_set(x_73, 4, x_70);
lean_ctor_set(x_32, 1, x_66);
lean_ctor_set(x_32, 0, x_73);
x_74 = l_ReaderT_instMonad___redArg(x_32);
x_75 = l_ReaderT_instMonad___redArg(x_74);
x_76 = l_ReaderT_instMonad___redArg(x_75);
x_77 = l_ReaderT_instMonad___redArg(x_76);
x_78 = l_ReaderT_instMonad___redArg(x_77);
x_79 = l_ReaderT_instMonad___redArg(x_78);
x_80 = 0;
x_81 = lean_box(x_80);
x_82 = l_instInhabitedOfMonad___redArg(x_79, x_81);
x_83 = lean_panic_fn(x_82, x_1);
x_84 = lean_apply_11(x_83, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_85 = lean_ctor_get(x_32, 0);
lean_inc(x_85);
lean_dec(x_32);
x_86 = lean_ctor_get(x_85, 0);
lean_inc_ref(x_86);
x_87 = lean_ctor_get(x_85, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_85, 4);
lean_inc(x_89);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 lean_ctor_release(x_85, 2);
 lean_ctor_release(x_85, 3);
 lean_ctor_release(x_85, 4);
 x_90 = x_85;
} else {
 lean_dec_ref(x_85);
 x_90 = lean_box(0);
}
x_91 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__3));
x_92 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__4));
lean_inc_ref(x_86);
x_93 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_93, 0, x_86);
x_94 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_94, 0, x_86);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_96, 0, x_89);
x_97 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_97, 0, x_88);
x_98 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_98, 0, x_87);
if (lean_is_scalar(x_90)) {
 x_99 = lean_alloc_ctor(0, 5, 0);
} else {
 x_99 = x_90;
}
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_99, 1, x_91);
lean_ctor_set(x_99, 2, x_98);
lean_ctor_set(x_99, 3, x_97);
lean_ctor_set(x_99, 4, x_96);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_92);
x_101 = l_ReaderT_instMonad___redArg(x_100);
x_102 = l_ReaderT_instMonad___redArg(x_101);
x_103 = l_ReaderT_instMonad___redArg(x_102);
x_104 = l_ReaderT_instMonad___redArg(x_103);
x_105 = l_ReaderT_instMonad___redArg(x_104);
x_106 = l_ReaderT_instMonad___redArg(x_105);
x_107 = 0;
x_108 = lean_box(x_107);
x_109 = l_instInhabitedOfMonad___redArg(x_106, x_108);
x_110 = lean_panic_fn(x_109, x_1);
x_111 = lean_apply_11(x_110, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_112 = lean_ctor_get(x_16, 0);
x_113 = lean_ctor_get(x_16, 2);
x_114 = lean_ctor_get(x_16, 3);
x_115 = lean_ctor_get(x_16, 4);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_16);
x_116 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__1));
x_117 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__2));
lean_inc_ref(x_112);
x_118 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_118, 0, x_112);
x_119 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_119, 0, x_112);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_121, 0, x_115);
x_122 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_122, 0, x_114);
x_123 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_123, 0, x_113);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_116);
lean_ctor_set(x_124, 2, x_123);
lean_ctor_set(x_124, 3, x_122);
lean_ctor_set(x_124, 4, x_121);
lean_ctor_set(x_14, 1, x_117);
lean_ctor_set(x_14, 0, x_124);
x_125 = l_ReaderT_instMonad___redArg(x_14);
x_126 = lean_ctor_get(x_125, 0);
lean_inc_ref(x_126);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_127 = x_125;
} else {
 lean_dec_ref(x_125);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_126, 0);
lean_inc_ref(x_128);
x_129 = lean_ctor_get(x_126, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_126, 3);
lean_inc(x_130);
x_131 = lean_ctor_get(x_126, 4);
lean_inc(x_131);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 lean_ctor_release(x_126, 2);
 lean_ctor_release(x_126, 3);
 lean_ctor_release(x_126, 4);
 x_132 = x_126;
} else {
 lean_dec_ref(x_126);
 x_132 = lean_box(0);
}
x_133 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__3));
x_134 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__4));
lean_inc_ref(x_128);
x_135 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_135, 0, x_128);
x_136 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_136, 0, x_128);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_138, 0, x_131);
x_139 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_139, 0, x_130);
x_140 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_140, 0, x_129);
if (lean_is_scalar(x_132)) {
 x_141 = lean_alloc_ctor(0, 5, 0);
} else {
 x_141 = x_132;
}
lean_ctor_set(x_141, 0, x_137);
lean_ctor_set(x_141, 1, x_133);
lean_ctor_set(x_141, 2, x_140);
lean_ctor_set(x_141, 3, x_139);
lean_ctor_set(x_141, 4, x_138);
if (lean_is_scalar(x_127)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_127;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_134);
x_143 = l_ReaderT_instMonad___redArg(x_142);
x_144 = l_ReaderT_instMonad___redArg(x_143);
x_145 = l_ReaderT_instMonad___redArg(x_144);
x_146 = l_ReaderT_instMonad___redArg(x_145);
x_147 = l_ReaderT_instMonad___redArg(x_146);
x_148 = l_ReaderT_instMonad___redArg(x_147);
x_149 = 0;
x_150 = lean_box(x_149);
x_151 = l_instInhabitedOfMonad___redArg(x_148, x_150);
x_152 = lean_panic_fn(x_151, x_1);
x_153 = lean_apply_11(x_152, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_154 = lean_ctor_get(x_14, 0);
lean_inc(x_154);
lean_dec(x_14);
x_155 = lean_ctor_get(x_154, 0);
lean_inc_ref(x_155);
x_156 = lean_ctor_get(x_154, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 3);
lean_inc(x_157);
x_158 = lean_ctor_get(x_154, 4);
lean_inc(x_158);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 lean_ctor_release(x_154, 2);
 lean_ctor_release(x_154, 3);
 lean_ctor_release(x_154, 4);
 x_159 = x_154;
} else {
 lean_dec_ref(x_154);
 x_159 = lean_box(0);
}
x_160 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__1));
x_161 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__2));
lean_inc_ref(x_155);
x_162 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_162, 0, x_155);
x_163 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_163, 0, x_155);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_165, 0, x_158);
x_166 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_166, 0, x_157);
x_167 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_167, 0, x_156);
if (lean_is_scalar(x_159)) {
 x_168 = lean_alloc_ctor(0, 5, 0);
} else {
 x_168 = x_159;
}
lean_ctor_set(x_168, 0, x_164);
lean_ctor_set(x_168, 1, x_160);
lean_ctor_set(x_168, 2, x_167);
lean_ctor_set(x_168, 3, x_166);
lean_ctor_set(x_168, 4, x_165);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_161);
x_170 = l_ReaderT_instMonad___redArg(x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc_ref(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_171, 0);
lean_inc_ref(x_173);
x_174 = lean_ctor_get(x_171, 2);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 3);
lean_inc(x_175);
x_176 = lean_ctor_get(x_171, 4);
lean_inc(x_176);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 lean_ctor_release(x_171, 3);
 lean_ctor_release(x_171, 4);
 x_177 = x_171;
} else {
 lean_dec_ref(x_171);
 x_177 = lean_box(0);
}
x_178 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__3));
x_179 = ((lean_object*)(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__4));
lean_inc_ref(x_173);
x_180 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_180, 0, x_173);
x_181 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_181, 0, x_173);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_183, 0, x_176);
x_184 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_184, 0, x_175);
x_185 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_185, 0, x_174);
if (lean_is_scalar(x_177)) {
 x_186 = lean_alloc_ctor(0, 5, 0);
} else {
 x_186 = x_177;
}
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_178);
lean_ctor_set(x_186, 2, x_185);
lean_ctor_set(x_186, 3, x_184);
lean_ctor_set(x_186, 4, x_183);
if (lean_is_scalar(x_172)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_172;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_179);
x_188 = l_ReaderT_instMonad___redArg(x_187);
x_189 = l_ReaderT_instMonad___redArg(x_188);
x_190 = l_ReaderT_instMonad___redArg(x_189);
x_191 = l_ReaderT_instMonad___redArg(x_190);
x_192 = l_ReaderT_instMonad___redArg(x_191);
x_193 = l_ReaderT_instMonad___redArg(x_192);
x_194 = 0;
x_195 = lean_box(x_194);
x_196 = l_instInhabitedOfMonad___redArg(x_193, x_195);
x_197 = lean_panic_fn(x_196, x_1);
x_198 = lean_apply_11(x_197, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, lean_box(0));
return x_198;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = l_Lean_instBEqLevelMVarId_beq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_instBEqLevelMVarId_beq(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Lean_instBEqLevelMVarId_beq(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_instHashableLevelMVarId_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__2));
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(443u);
x_4 = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__1));
x_5 = ((lean_object*)(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_st_ref_get(x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 3);
lean_inc_ref(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7___redArg(x_16, x_1);
if (lean_obj_tag(x_17) == 1)
{
uint8_t x_18; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_nat_dec_le(x_15, x_19);
lean_dec(x_19);
lean_dec(x_15);
x_21 = lean_box(x_20);
lean_ctor_set_tag(x_17, 0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_nat_dec_le(x_15, x_22);
lean_dec(x_22);
lean_dec(x_15);
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_15);
x_26 = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__3;
x_27 = l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_22; lean_object* x_23; 
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = l_Lean_Level_hasMVar(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
x_1 = x_31;
goto _start;
}
}
case 2:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
x_22 = x_36;
x_23 = x_37;
goto block_30;
}
case 3:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_22 = x_38;
x_23 = x_39;
goto block_30;
}
case 5:
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_41;
}
default: 
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = 0;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
block_21:
{
if (x_15 == 0)
{
uint8_t x_17; 
lean_dec_ref(x_14);
x_17 = l_Lean_Level_hasMVar(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
x_1 = x_13;
goto _start;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
block_30:
{
uint8_t x_24; 
x_24 = l_Lean_Level_hasMVar(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_13 = x_23;
x_14 = x_26;
x_15 = x_24;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_27; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
x_13 = x_23;
x_14 = x_27;
x_15 = x_29;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_18);
x_1 = x_17;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_22; lean_object* x_23; 
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
x_32 = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___redArg(x_31, x_9);
lean_dec(x_9);
return x_32;
}
case 3:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = l_Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_34;
}
case 4:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_1, 1);
x_36 = l_List_anyM___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__5(x_35, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_36;
}
case 5:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; uint8_t x_47; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
x_47 = l_Lean_Expr_hasMVar(x_37);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_39 = x_49;
x_40 = x_47;
x_41 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_50; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_50 = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
x_39 = x_50;
x_40 = x_52;
x_41 = lean_box(0);
goto block_46;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
}
block_46:
{
if (x_40 == 0)
{
uint8_t x_42; 
lean_dec_ref(x_39);
x_42 = l_Lean_Expr_hasMVar(x_38);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
x_1 = x_38;
goto _start;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_39;
}
}
}
case 6:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_1, 1);
x_54 = lean_ctor_get(x_1, 2);
x_22 = x_53;
x_23 = x_54;
goto block_30;
}
case 7:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_1, 1);
x_56 = lean_ctor_get(x_1, 2);
x_22 = x_55;
x_23 = x_56;
goto block_30;
}
case 8:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_68; uint8_t x_69; lean_object* x_70; uint8_t x_78; 
x_57 = lean_ctor_get(x_1, 1);
x_58 = lean_ctor_get(x_1, 2);
x_59 = lean_ctor_get(x_1, 3);
x_78 = l_Lean_Expr_hasMVar(x_57);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_box(x_78);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_68 = x_80;
x_69 = x_78;
x_70 = lean_box(0);
goto block_77;
}
else
{
lean_object* x_81; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_81 = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
x_68 = x_81;
x_69 = x_83;
x_70 = lean_box(0);
goto block_77;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_81;
}
}
block_67:
{
if (x_61 == 0)
{
uint8_t x_63; 
lean_dec_ref(x_60);
x_63 = l_Lean_Expr_hasMVar(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_box(x_63);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
x_1 = x_59;
goto _start;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_60;
}
}
block_77:
{
if (x_69 == 0)
{
uint8_t x_71; 
lean_dec_ref(x_68);
x_71 = l_Lean_Expr_hasMVar(x_58);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_60 = x_73;
x_61 = x_71;
x_62 = lean_box(0);
goto block_67;
}
else
{
lean_object* x_74; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_74 = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
x_60 = x_74;
x_61 = x_76;
x_62 = lean_box(0);
goto block_67;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_74;
}
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_68;
}
}
}
case 10:
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_1, 1);
x_85 = l_Lean_Expr_hasMVar(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
else
{
x_1 = x_84;
goto _start;
}
}
case 11:
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_1, 2);
x_90 = l_Lean_Expr_hasMVar(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = lean_box(x_90);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
else
{
x_1 = x_89;
goto _start;
}
}
default: 
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_94 = 0;
x_95 = lean_box(x_94);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
block_21:
{
if (x_15 == 0)
{
uint8_t x_17; 
lean_dec_ref(x_14);
x_17 = l_Lean_Expr_hasMVar(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
x_1 = x_13;
goto _start;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
block_30:
{
uint8_t x_24; 
x_24 = l_Lean_Expr_hasMVar(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_13 = x_23;
x_14 = x_26;
x_15 = x_24;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_27; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
x_13 = x_23;
x_14 = x_27;
x_15 = x_29;
x_16 = lean_box(0);
goto block_21;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_5, x_4);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_6);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_27 = x_6;
} else {
 lean_dec_ref(x_6);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_26, 2);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
if (lean_is_scalar(x_27)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_27;
}
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_26);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
uint8_t x_34; 
lean_inc(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_35 = lean_ctor_get(x_26, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_26, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_26, 0);
lean_dec(x_37);
x_38 = lean_array_fget(x_28, x_29);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_29, x_39);
lean_dec(x_29);
lean_ctor_set(x_26, 1, x_40);
x_41 = lean_unbox(x_38);
lean_dec(x_38);
if (x_41 == 0)
{
lean_object* x_42; 
lean_inc(x_1);
if (lean_is_scalar(x_27)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_27;
}
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_26);
x_18 = x_42;
x_19 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_71; 
x_43 = lean_array_uget(x_3, x_5);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_43);
x_71 = lean_infer_type(x_43, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_73);
if (lean_obj_tag(x_74) == 1)
{
lean_object* x_75; uint8_t x_76; 
lean_free_object(x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_75, 1);
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_81 = x_77;
} else {
 lean_dec_ref(x_77);
 x_81 = lean_box(0);
}
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_79);
x_82 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(x_79, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_132; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_inc(x_2);
x_132 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_2, x_15);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_free_object(x_75);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_84 = x_7;
x_85 = x_8;
x_86 = x_9;
x_87 = x_10;
x_88 = x_11;
x_89 = x_12;
x_90 = x_13;
x_91 = x_14;
x_92 = x_15;
x_93 = x_16;
x_94 = lean_box(0);
goto block_131;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_inc(x_83);
x_135 = l_Lean_MessageData_ofExpr(x_83);
x_136 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__2;
lean_ctor_set_tag(x_75, 7);
lean_ctor_set(x_75, 1, x_136);
lean_ctor_set(x_75, 0, x_135);
lean_inc(x_80);
x_137 = l_Lean_MessageData_ofExpr(x_80);
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_75);
lean_ctor_set(x_138, 1, x_137);
lean_inc(x_2);
x_139 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_2, x_138, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_139) == 0)
{
lean_dec_ref(x_139);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_84 = x_7;
x_85 = x_8;
x_86 = x_9;
x_87 = x_10;
x_88 = x_11;
x_89 = x_12;
x_90 = x_13;
x_91 = x_14;
x_92 = x_15;
x_93 = x_16;
x_94 = lean_box(0);
goto block_131;
}
else
{
uint8_t x_140; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
return x_139;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_free_object(x_75);
lean_dec(x_78);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_132);
if (x_143 == 0)
{
return x_132;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_132, 0);
lean_inc(x_144);
lean_dec(x_132);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
return x_145;
}
}
block_131:
{
lean_object* x_95; 
lean_inc(x_93);
lean_inc_ref(x_92);
lean_inc(x_91);
lean_inc_ref(x_90);
lean_inc(x_83);
x_95 = l_Lean_Meta_isDefEqD(x_83, x_80, x_90, x_91, x_92, x_93);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_99 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_81)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_81;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_26);
lean_ctor_set(x_95, 0, x_100);
return x_95;
}
else
{
lean_free_object(x_95);
lean_dec(x_81);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_101; lean_object* x_102; 
x_101 = 0;
lean_inc(x_93);
lean_inc_ref(x_92);
lean_inc(x_91);
lean_inc_ref(x_90);
x_102 = l_Lean_Meta_Grind_proveEq_x3f(x_79, x_83, x_101, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
x_44 = x_103;
x_45 = x_90;
x_46 = x_91;
x_47 = x_92;
x_48 = x_93;
x_49 = lean_box(0);
goto block_70;
}
else
{
uint8_t x_104; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
return x_102;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; 
lean_dec_ref(x_78);
lean_inc(x_93);
lean_inc_ref(x_92);
lean_inc(x_91);
lean_inc_ref(x_90);
x_107 = l_Lean_Meta_Grind_proveHEq_x3f(x_79, x_83, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_44 = x_108;
x_45 = x_90;
x_46 = x_91;
x_47 = x_92;
x_48 = x_93;
x_49 = lean_box(0);
goto block_70;
}
else
{
uint8_t x_109; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_107);
if (x_109 == 0)
{
return x_107;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
}
}
else
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_95, 0);
lean_inc(x_112);
lean_dec(x_95);
x_113 = lean_unbox(x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_114 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_81)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_81;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_26);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
else
{
lean_dec(x_81);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_117; lean_object* x_118; 
x_117 = 0;
lean_inc(x_93);
lean_inc_ref(x_92);
lean_inc(x_91);
lean_inc_ref(x_90);
x_118 = l_Lean_Meta_Grind_proveEq_x3f(x_79, x_83, x_117, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_44 = x_119;
x_45 = x_90;
x_46 = x_91;
x_47 = x_92;
x_48 = x_93;
x_49 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
else
{
lean_object* x_123; 
lean_dec_ref(x_78);
lean_inc(x_93);
lean_inc_ref(x_92);
lean_inc(x_91);
lean_inc_ref(x_90);
x_123 = l_Lean_Meta_Grind_proveHEq_x3f(x_79, x_83, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_44 = x_124;
x_45 = x_90;
x_46 = x_91;
x_47 = x_92;
x_48 = x_93;
x_49 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_95);
if (x_128 == 0)
{
return x_95;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_95, 0);
lean_inc(x_129);
lean_dec(x_95);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_free_object(x_75);
lean_dec(x_78);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_82);
if (x_146 == 0)
{
return x_82;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_82, 0);
lean_inc(x_147);
lean_dec(x_82);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_149 = lean_ctor_get(x_75, 1);
x_150 = lean_ctor_get(x_75, 0);
lean_inc(x_149);
lean_inc(x_150);
lean_dec(x_75);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_151);
x_154 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(x_151, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_189; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec_ref(x_154);
lean_inc(x_2);
x_189 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_2, x_15);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec_ref(x_189);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_156 = x_7;
x_157 = x_8;
x_158 = x_9;
x_159 = x_10;
x_160 = x_11;
x_161 = x_12;
x_162 = x_13;
x_163 = x_14;
x_164 = x_15;
x_165 = x_16;
x_166 = lean_box(0);
goto block_188;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_inc(x_155);
x_192 = l_Lean_MessageData_ofExpr(x_155);
x_193 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__2;
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
lean_inc(x_152);
x_195 = l_Lean_MessageData_ofExpr(x_152);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
lean_inc(x_2);
x_197 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_2, x_196, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_197) == 0)
{
lean_dec_ref(x_197);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_156 = x_7;
x_157 = x_8;
x_158 = x_9;
x_159 = x_10;
x_160 = x_11;
x_161 = x_12;
x_162 = x_13;
x_163 = x_14;
x_164 = x_15;
x_165 = x_16;
x_166 = lean_box(0);
goto block_188;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_198);
return x_200;
}
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_201 = lean_ctor_get(x_189, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_202 = x_189;
} else {
 lean_dec_ref(x_189);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 1, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_201);
return x_203;
}
block_188:
{
lean_object* x_167; 
lean_inc(x_165);
lean_inc_ref(x_164);
lean_inc(x_163);
lean_inc_ref(x_162);
lean_inc(x_155);
x_167 = l_Lean_Meta_isDefEqD(x_155, x_152, x_162, x_163, x_164, x_165);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = lean_unbox(x_168);
lean_dec(x_168);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_171 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_153)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_153;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_26);
if (lean_is_scalar(x_169)) {
 x_173 = lean_alloc_ctor(0, 1, 0);
} else {
 x_173 = x_169;
}
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
else
{
lean_dec(x_169);
lean_dec(x_153);
if (lean_obj_tag(x_150) == 0)
{
uint8_t x_174; lean_object* x_175; 
x_174 = 0;
lean_inc(x_165);
lean_inc_ref(x_164);
lean_inc(x_163);
lean_inc_ref(x_162);
x_175 = l_Lean_Meta_Grind_proveEq_x3f(x_151, x_155, x_174, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164, x_165);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_44 = x_176;
x_45 = x_162;
x_46 = x_163;
x_47 = x_164;
x_48 = x_165;
x_49 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 1, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_177);
return x_179;
}
}
else
{
lean_object* x_180; 
lean_dec_ref(x_150);
lean_inc(x_165);
lean_inc_ref(x_164);
lean_inc(x_163);
lean_inc_ref(x_162);
x_180 = l_Lean_Meta_Grind_proveHEq_x3f(x_151, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164, x_165);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
x_44 = x_181;
x_45 = x_162;
x_46 = x_163;
x_47 = x_164;
x_48 = x_165;
x_49 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_182);
return x_184;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_185 = lean_ctor_get(x_167, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_186 = x_167;
} else {
 lean_dec_ref(x_167);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 1, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_185);
return x_187;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_204 = lean_ctor_get(x_154, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 x_205 = x_154;
} else {
 lean_dec_ref(x_154);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 1, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_204);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_74);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_207 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_26);
lean_ctor_set(x_71, 0, x_208);
return x_71;
}
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_71, 0);
lean_inc(x_209);
lean_dec(x_71);
x_210 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_209);
if (lean_obj_tag(x_210) == 1)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_214 = x_211;
} else {
 lean_dec_ref(x_211);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_212, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_217 = x_212;
} else {
 lean_dec_ref(x_212);
 x_217 = lean_box(0);
}
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_215);
x_218 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(x_215, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_253; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
lean_inc(x_2);
x_253 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_2, x_15);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = lean_unbox(x_254);
lean_dec(x_254);
if (x_255 == 0)
{
lean_dec(x_214);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_220 = x_7;
x_221 = x_8;
x_222 = x_9;
x_223 = x_10;
x_224 = x_11;
x_225 = x_12;
x_226 = x_13;
x_227 = x_14;
x_228 = x_15;
x_229 = x_16;
x_230 = lean_box(0);
goto block_252;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_inc(x_219);
x_256 = l_Lean_MessageData_ofExpr(x_219);
x_257 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__2;
if (lean_is_scalar(x_214)) {
 x_258 = lean_alloc_ctor(7, 2, 0);
} else {
 x_258 = x_214;
 lean_ctor_set_tag(x_258, 7);
}
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
lean_inc(x_216);
x_259 = l_Lean_MessageData_ofExpr(x_216);
x_260 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
lean_inc(x_2);
x_261 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_2, x_260, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_261) == 0)
{
lean_dec_ref(x_261);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_220 = x_7;
x_221 = x_8;
x_222 = x_9;
x_223 = x_10;
x_224 = x_11;
x_225 = x_12;
x_226 = x_13;
x_227 = x_14;
x_228 = x_15;
x_229 = x_16;
x_230 = lean_box(0);
goto block_252;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_263 = x_261;
} else {
 lean_dec_ref(x_261);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 1, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_262);
return x_264;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_265 = lean_ctor_get(x_253, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_266 = x_253;
} else {
 lean_dec_ref(x_253);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 1, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_265);
return x_267;
}
block_252:
{
lean_object* x_231; 
lean_inc(x_229);
lean_inc_ref(x_228);
lean_inc(x_227);
lean_inc_ref(x_226);
lean_inc(x_219);
x_231 = l_Lean_Meta_isDefEqD(x_219, x_216, x_226, x_227, x_228, x_229);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
x_234 = lean_unbox(x_232);
lean_dec(x_232);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec_ref(x_226);
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_235 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_217)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_217;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_26);
if (lean_is_scalar(x_233)) {
 x_237 = lean_alloc_ctor(0, 1, 0);
} else {
 x_237 = x_233;
}
lean_ctor_set(x_237, 0, x_236);
return x_237;
}
else
{
lean_dec(x_233);
lean_dec(x_217);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_238; lean_object* x_239; 
x_238 = 0;
lean_inc(x_229);
lean_inc_ref(x_228);
lean_inc(x_227);
lean_inc_ref(x_226);
x_239 = l_Lean_Meta_Grind_proveEq_x3f(x_215, x_219, x_238, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec_ref(x_239);
x_44 = x_240;
x_45 = x_226;
x_46 = x_227;
x_47 = x_228;
x_48 = x_229;
x_49 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec_ref(x_226);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_241 = lean_ctor_get(x_239, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_242 = x_239;
} else {
 lean_dec_ref(x_239);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 1, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_241);
return x_243;
}
}
else
{
lean_object* x_244; 
lean_dec_ref(x_213);
lean_inc(x_229);
lean_inc_ref(x_228);
lean_inc(x_227);
lean_inc_ref(x_226);
x_244 = l_Lean_Meta_Grind_proveHEq_x3f(x_215, x_219, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec_ref(x_244);
x_44 = x_245;
x_45 = x_226;
x_46 = x_227;
x_47 = x_228;
x_48 = x_229;
x_49 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec_ref(x_226);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_246 = lean_ctor_get(x_244, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 1, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_246);
return x_248;
}
}
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec_ref(x_226);
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_249 = lean_ctor_get(x_231, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_250 = x_231;
} else {
 lean_dec_ref(x_231);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 1, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_249);
return x_251;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_268 = lean_ctor_get(x_218, 0);
lean_inc(x_268);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_269 = x_218;
} else {
 lean_dec_ref(x_218);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 1, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_268);
return x_270;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_210);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_271 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_26);
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_272);
return x_273;
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_274 = !lean_is_exclusive(x_71);
if (x_274 == 0)
{
return x_71;
}
else
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_71, 0);
lean_inc(x_275);
lean_dec(x_71);
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_275);
return x_276;
}
}
block_70:
{
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
lean_dec_ref(x_44);
x_51 = l_Lean_Meta_isExprDefEq(x_43, x_50, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_55 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_27)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_27;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_26);
lean_ctor_set(x_51, 0, x_56);
return x_51;
}
else
{
lean_object* x_57; 
lean_free_object(x_51);
lean_inc(x_1);
if (lean_is_scalar(x_27)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_27;
}
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_26);
x_18 = x_57;
x_19 = lean_box(0);
goto block_23;
}
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_60 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_27)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_27;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_26);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
else
{
lean_object* x_63; 
lean_inc(x_1);
if (lean_is_scalar(x_27)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_27;
}
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_26);
x_18 = x_63;
x_19 = lean_box(0);
goto block_23;
}
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_51);
if (x_64 == 0)
{
return x_51;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_51, 0);
lean_inc(x_65);
lean_dec(x_51);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_67 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_27)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_27;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_26);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
lean_dec(x_26);
x_277 = lean_array_fget(x_28, x_29);
x_278 = lean_unsigned_to_nat(1u);
x_279 = lean_nat_add(x_29, x_278);
lean_dec(x_29);
x_280 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_280, 0, x_28);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set(x_280, 2, x_30);
x_281 = lean_unbox(x_277);
lean_dec(x_277);
if (x_281 == 0)
{
lean_object* x_282; 
lean_inc(x_1);
if (lean_is_scalar(x_27)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_27;
}
lean_ctor_set(x_282, 0, x_1);
lean_ctor_set(x_282, 1, x_280);
x_18 = x_282;
x_19 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_306; 
x_283 = lean_array_uget(x_3, x_5);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_283);
x_306 = lean_infer_type(x_283, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 x_308 = x_306;
} else {
 lean_dec_ref(x_306);
 x_308 = lean_box(0);
}
x_309 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_307);
if (lean_obj_tag(x_309) == 1)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_308);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
lean_dec_ref(x_309);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 0);
lean_inc(x_312);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_313 = x_310;
} else {
 lean_dec_ref(x_310);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_311, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_311, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_316 = x_311;
} else {
 lean_dec_ref(x_311);
 x_316 = lean_box(0);
}
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_314);
x_317 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(x_314, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_352; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
lean_dec_ref(x_317);
lean_inc(x_2);
x_352 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_2, x_15);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; uint8_t x_354; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
lean_dec_ref(x_352);
x_354 = lean_unbox(x_353);
lean_dec(x_353);
if (x_354 == 0)
{
lean_dec(x_313);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_319 = x_7;
x_320 = x_8;
x_321 = x_9;
x_322 = x_10;
x_323 = x_11;
x_324 = x_12;
x_325 = x_13;
x_326 = x_14;
x_327 = x_15;
x_328 = x_16;
x_329 = lean_box(0);
goto block_351;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_inc(x_318);
x_355 = l_Lean_MessageData_ofExpr(x_318);
x_356 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__2;
if (lean_is_scalar(x_313)) {
 x_357 = lean_alloc_ctor(7, 2, 0);
} else {
 x_357 = x_313;
 lean_ctor_set_tag(x_357, 7);
}
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
lean_inc(x_315);
x_358 = l_Lean_MessageData_ofExpr(x_315);
x_359 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
lean_inc(x_2);
x_360 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_2, x_359, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_360) == 0)
{
lean_dec_ref(x_360);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_319 = x_7;
x_320 = x_8;
x_321 = x_9;
x_322 = x_10;
x_323 = x_11;
x_324 = x_12;
x_325 = x_13;
x_326 = x_14;
x_327 = x_15;
x_328 = x_16;
x_329 = lean_box(0);
goto block_351;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_318);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_312);
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 x_362 = x_360;
} else {
 lean_dec_ref(x_360);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 1, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_361);
return x_363;
}
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_318);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_364 = lean_ctor_get(x_352, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 x_365 = x_352;
} else {
 lean_dec_ref(x_352);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 1, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_364);
return x_366;
}
block_351:
{
lean_object* x_330; 
lean_inc(x_328);
lean_inc_ref(x_327);
lean_inc(x_326);
lean_inc_ref(x_325);
lean_inc(x_318);
x_330 = l_Lean_Meta_isDefEqD(x_318, x_315, x_325, x_326, x_327, x_328);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 x_332 = x_330;
} else {
 lean_dec_ref(x_330);
 x_332 = lean_box(0);
}
x_333 = lean_unbox(x_331);
lean_dec(x_331);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_314);
lean_dec(x_312);
lean_dec(x_283);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_334 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_316)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_316;
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_280);
if (lean_is_scalar(x_332)) {
 x_336 = lean_alloc_ctor(0, 1, 0);
} else {
 x_336 = x_332;
}
lean_ctor_set(x_336, 0, x_335);
return x_336;
}
else
{
lean_dec(x_332);
lean_dec(x_316);
if (lean_obj_tag(x_312) == 0)
{
uint8_t x_337; lean_object* x_338; 
x_337 = 0;
lean_inc(x_328);
lean_inc_ref(x_327);
lean_inc(x_326);
lean_inc_ref(x_325);
x_338 = l_Lean_Meta_Grind_proveEq_x3f(x_314, x_318, x_337, x_319, x_320, x_321, x_322, x_323, x_324, x_325, x_326, x_327, x_328);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
x_284 = x_339;
x_285 = x_325;
x_286 = x_326;
x_287 = x_327;
x_288 = x_328;
x_289 = lean_box(0);
goto block_305;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_340 = lean_ctor_get(x_338, 0);
lean_inc(x_340);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_341 = x_338;
} else {
 lean_dec_ref(x_338);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 1, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_340);
return x_342;
}
}
else
{
lean_object* x_343; 
lean_dec_ref(x_312);
lean_inc(x_328);
lean_inc_ref(x_327);
lean_inc(x_326);
lean_inc_ref(x_325);
x_343 = l_Lean_Meta_Grind_proveHEq_x3f(x_314, x_318, x_319, x_320, x_321, x_322, x_323, x_324, x_325, x_326, x_327, x_328);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
lean_dec_ref(x_343);
x_284 = x_344;
x_285 = x_325;
x_286 = x_326;
x_287 = x_327;
x_288 = x_328;
x_289 = lean_box(0);
goto block_305;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 x_346 = x_343;
} else {
 lean_dec_ref(x_343);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 1, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_345);
return x_347;
}
}
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_316);
lean_dec(x_314);
lean_dec(x_312);
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_348 = lean_ctor_get(x_330, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 x_349 = x_330;
} else {
 lean_dec_ref(x_330);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 1, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_348);
return x_350;
}
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_367 = lean_ctor_get(x_317, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 x_368 = x_317;
} else {
 lean_dec_ref(x_317);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(1, 1, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_367);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_309);
lean_dec(x_283);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_370 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_280);
if (lean_is_scalar(x_308)) {
 x_372 = lean_alloc_ctor(0, 1, 0);
} else {
 x_372 = x_308;
}
lean_ctor_set(x_372, 0, x_371);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_373 = lean_ctor_get(x_306, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 x_374 = x_306;
} else {
 lean_dec_ref(x_306);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 1, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_373);
return x_375;
}
block_305:
{
if (lean_obj_tag(x_284) == 1)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_284, 0);
lean_inc(x_290);
lean_dec_ref(x_284);
x_291 = l_Lean_Meta_isExprDefEq(x_283, x_290, x_285, x_286, x_287, x_288);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_293 = x_291;
} else {
 lean_dec_ref(x_291);
 x_293 = lean_box(0);
}
x_294 = lean_unbox(x_292);
lean_dec(x_292);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_295 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_27)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_27;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_280);
if (lean_is_scalar(x_293)) {
 x_297 = lean_alloc_ctor(0, 1, 0);
} else {
 x_297 = x_293;
}
lean_ctor_set(x_297, 0, x_296);
return x_297;
}
else
{
lean_object* x_298; 
lean_dec(x_293);
lean_inc(x_1);
if (lean_is_scalar(x_27)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_27;
}
lean_ctor_set(x_298, 0, x_1);
lean_ctor_set(x_298, 1, x_280);
x_18 = x_298;
x_19 = lean_box(0);
goto block_23;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_299 = lean_ctor_get(x_291, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_300 = x_291;
} else {
 lean_dec_ref(x_291);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_299);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_288);
lean_dec_ref(x_287);
lean_dec(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_302 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_27)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_27;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_280);
x_304 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_304, 0, x_303);
return x_304;
}
}
}
}
}
}
block_23:
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_5 = x_21;
x_6 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_3);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_18; lean_object* x_19; uint8_t x_24; 
x_24 = lean_usize_dec_lt(x_5, x_4);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_6);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_27 = x_6;
} else {
 lean_dec_ref(x_6);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_26, 2);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
if (lean_is_scalar(x_27)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_27;
}
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_26);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
uint8_t x_34; 
lean_inc(x_30);
lean_inc(x_29);
lean_inc_ref(x_28);
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_35 = lean_ctor_get(x_26, 2);
lean_dec(x_35);
x_36 = lean_ctor_get(x_26, 1);
lean_dec(x_36);
x_37 = lean_ctor_get(x_26, 0);
lean_dec(x_37);
x_38 = lean_array_fget(x_28, x_29);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_29, x_39);
lean_dec(x_29);
lean_ctor_set(x_26, 1, x_40);
x_41 = lean_unbox(x_38);
lean_dec(x_38);
if (x_41 == 0)
{
lean_object* x_42; 
lean_inc(x_1);
if (lean_is_scalar(x_27)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_27;
}
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_26);
x_18 = x_42;
x_19 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_71; 
x_43 = lean_array_uget(x_3, x_5);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_43);
x_71 = lean_infer_type(x_43, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_73);
if (lean_obj_tag(x_74) == 1)
{
lean_object* x_75; uint8_t x_76; 
lean_free_object(x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_75, 1);
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_81 = x_77;
} else {
 lean_dec_ref(x_77);
 x_81 = lean_box(0);
}
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_79);
x_82 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(x_79, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_132; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_inc(x_2);
x_132 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_2, x_15);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_free_object(x_75);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_84 = x_7;
x_85 = x_8;
x_86 = x_9;
x_87 = x_10;
x_88 = x_11;
x_89 = x_12;
x_90 = x_13;
x_91 = x_14;
x_92 = x_15;
x_93 = x_16;
x_94 = lean_box(0);
goto block_131;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_inc(x_83);
x_135 = l_Lean_MessageData_ofExpr(x_83);
x_136 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__2;
lean_ctor_set_tag(x_75, 7);
lean_ctor_set(x_75, 1, x_136);
lean_ctor_set(x_75, 0, x_135);
lean_inc(x_80);
x_137 = l_Lean_MessageData_ofExpr(x_80);
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_75);
lean_ctor_set(x_138, 1, x_137);
lean_inc(x_2);
x_139 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_2, x_138, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_139) == 0)
{
lean_dec_ref(x_139);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_84 = x_7;
x_85 = x_8;
x_86 = x_9;
x_87 = x_10;
x_88 = x_11;
x_89 = x_12;
x_90 = x_13;
x_91 = x_14;
x_92 = x_15;
x_93 = x_16;
x_94 = lean_box(0);
goto block_131;
}
else
{
uint8_t x_140; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
return x_139;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_free_object(x_75);
lean_dec(x_78);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_132);
if (x_143 == 0)
{
return x_132;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_132, 0);
lean_inc(x_144);
lean_dec(x_132);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
return x_145;
}
}
block_131:
{
lean_object* x_95; 
lean_inc(x_93);
lean_inc_ref(x_92);
lean_inc(x_91);
lean_inc_ref(x_90);
lean_inc(x_83);
x_95 = l_Lean_Meta_isDefEqD(x_83, x_80, x_90, x_91, x_92, x_93);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_99 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_81)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_81;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_26);
lean_ctor_set(x_95, 0, x_100);
return x_95;
}
else
{
lean_free_object(x_95);
lean_dec(x_81);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_101; lean_object* x_102; 
x_101 = 0;
lean_inc(x_93);
lean_inc_ref(x_92);
lean_inc(x_91);
lean_inc_ref(x_90);
x_102 = l_Lean_Meta_Grind_proveEq_x3f(x_79, x_83, x_101, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
x_44 = x_103;
x_45 = x_90;
x_46 = x_91;
x_47 = x_92;
x_48 = x_93;
x_49 = lean_box(0);
goto block_70;
}
else
{
uint8_t x_104; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
return x_102;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; 
lean_dec_ref(x_78);
lean_inc(x_93);
lean_inc_ref(x_92);
lean_inc(x_91);
lean_inc_ref(x_90);
x_107 = l_Lean_Meta_Grind_proveHEq_x3f(x_79, x_83, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_44 = x_108;
x_45 = x_90;
x_46 = x_91;
x_47 = x_92;
x_48 = x_93;
x_49 = lean_box(0);
goto block_70;
}
else
{
uint8_t x_109; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_107);
if (x_109 == 0)
{
return x_107;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
}
}
else
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_95, 0);
lean_inc(x_112);
lean_dec(x_95);
x_113 = lean_unbox(x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_114 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_81)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_81;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_26);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
else
{
lean_dec(x_81);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_117; lean_object* x_118; 
x_117 = 0;
lean_inc(x_93);
lean_inc_ref(x_92);
lean_inc(x_91);
lean_inc_ref(x_90);
x_118 = l_Lean_Meta_Grind_proveEq_x3f(x_79, x_83, x_117, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_44 = x_119;
x_45 = x_90;
x_46 = x_91;
x_47 = x_92;
x_48 = x_93;
x_49 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
else
{
lean_object* x_123; 
lean_dec_ref(x_78);
lean_inc(x_93);
lean_inc_ref(x_92);
lean_inc(x_91);
lean_inc_ref(x_90);
x_123 = l_Lean_Meta_Grind_proveHEq_x3f(x_79, x_83, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_44 = x_124;
x_45 = x_90;
x_46 = x_91;
x_47 = x_92;
x_48 = x_93;
x_49 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_93);
lean_dec_ref(x_92);
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_95);
if (x_128 == 0)
{
return x_95;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_95, 0);
lean_inc(x_129);
lean_dec(x_95);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_free_object(x_75);
lean_dec(x_78);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_82);
if (x_146 == 0)
{
return x_82;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_82, 0);
lean_inc(x_147);
lean_dec(x_82);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_149 = lean_ctor_get(x_75, 1);
x_150 = lean_ctor_get(x_75, 0);
lean_inc(x_149);
lean_inc(x_150);
lean_dec(x_75);
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_149, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_153 = x_149;
} else {
 lean_dec_ref(x_149);
 x_153 = lean_box(0);
}
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_151);
x_154 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(x_151, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_189; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec_ref(x_154);
lean_inc(x_2);
x_189 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_2, x_15);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_dec_ref(x_189);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_156 = x_7;
x_157 = x_8;
x_158 = x_9;
x_159 = x_10;
x_160 = x_11;
x_161 = x_12;
x_162 = x_13;
x_163 = x_14;
x_164 = x_15;
x_165 = x_16;
x_166 = lean_box(0);
goto block_188;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_inc(x_155);
x_192 = l_Lean_MessageData_ofExpr(x_155);
x_193 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__2;
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
lean_inc(x_152);
x_195 = l_Lean_MessageData_ofExpr(x_152);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
lean_inc(x_2);
x_197 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_2, x_196, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_197) == 0)
{
lean_dec_ref(x_197);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_156 = x_7;
x_157 = x_8;
x_158 = x_9;
x_159 = x_10;
x_160 = x_11;
x_161 = x_12;
x_162 = x_13;
x_163 = x_14;
x_164 = x_15;
x_165 = x_16;
x_166 = lean_box(0);
goto block_188;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_198);
return x_200;
}
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_201 = lean_ctor_get(x_189, 0);
lean_inc(x_201);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 x_202 = x_189;
} else {
 lean_dec_ref(x_189);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 1, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_201);
return x_203;
}
block_188:
{
lean_object* x_167; 
lean_inc(x_165);
lean_inc_ref(x_164);
lean_inc(x_163);
lean_inc_ref(x_162);
lean_inc(x_155);
x_167 = l_Lean_Meta_isDefEqD(x_155, x_152, x_162, x_163, x_164, x_165);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = lean_unbox(x_168);
lean_dec(x_168);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_171 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_153)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_153;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_26);
if (lean_is_scalar(x_169)) {
 x_173 = lean_alloc_ctor(0, 1, 0);
} else {
 x_173 = x_169;
}
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
else
{
lean_dec(x_169);
lean_dec(x_153);
if (lean_obj_tag(x_150) == 0)
{
uint8_t x_174; lean_object* x_175; 
x_174 = 0;
lean_inc(x_165);
lean_inc_ref(x_164);
lean_inc(x_163);
lean_inc_ref(x_162);
x_175 = l_Lean_Meta_Grind_proveEq_x3f(x_151, x_155, x_174, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164, x_165);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_44 = x_176;
x_45 = x_162;
x_46 = x_163;
x_47 = x_164;
x_48 = x_165;
x_49 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 1, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_177);
return x_179;
}
}
else
{
lean_object* x_180; 
lean_dec_ref(x_150);
lean_inc(x_165);
lean_inc_ref(x_164);
lean_inc(x_163);
lean_inc_ref(x_162);
x_180 = l_Lean_Meta_Grind_proveHEq_x3f(x_151, x_155, x_156, x_157, x_158, x_159, x_160, x_161, x_162, x_163, x_164, x_165);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec_ref(x_180);
x_44 = x_181;
x_45 = x_162;
x_46 = x_163;
x_47 = x_164;
x_48 = x_165;
x_49 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_ctor_get(x_180, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_182);
return x_184;
}
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec_ref(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_185 = lean_ctor_get(x_167, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_186 = x_167;
} else {
 lean_dec_ref(x_167);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 1, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_185);
return x_187;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_204 = lean_ctor_get(x_154, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 x_205 = x_154;
} else {
 lean_dec_ref(x_154);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 1, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_204);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_74);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_207 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_26);
lean_ctor_set(x_71, 0, x_208);
return x_71;
}
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_71, 0);
lean_inc(x_209);
lean_dec(x_71);
x_210 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_209);
if (lean_obj_tag(x_210) == 1)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_214 = x_211;
} else {
 lean_dec_ref(x_211);
 x_214 = lean_box(0);
}
x_215 = lean_ctor_get(x_212, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_217 = x_212;
} else {
 lean_dec_ref(x_212);
 x_217 = lean_box(0);
}
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_215);
x_218 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(x_215, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_253; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
lean_inc(x_2);
x_253 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_2, x_15);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = lean_unbox(x_254);
lean_dec(x_254);
if (x_255 == 0)
{
lean_dec(x_214);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_220 = x_7;
x_221 = x_8;
x_222 = x_9;
x_223 = x_10;
x_224 = x_11;
x_225 = x_12;
x_226 = x_13;
x_227 = x_14;
x_228 = x_15;
x_229 = x_16;
x_230 = lean_box(0);
goto block_252;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_inc(x_219);
x_256 = l_Lean_MessageData_ofExpr(x_219);
x_257 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__2;
if (lean_is_scalar(x_214)) {
 x_258 = lean_alloc_ctor(7, 2, 0);
} else {
 x_258 = x_214;
 lean_ctor_set_tag(x_258, 7);
}
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
lean_inc(x_216);
x_259 = l_Lean_MessageData_ofExpr(x_216);
x_260 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
lean_inc(x_2);
x_261 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_2, x_260, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_261) == 0)
{
lean_dec_ref(x_261);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_220 = x_7;
x_221 = x_8;
x_222 = x_9;
x_223 = x_10;
x_224 = x_11;
x_225 = x_12;
x_226 = x_13;
x_227 = x_14;
x_228 = x_15;
x_229 = x_16;
x_230 = lean_box(0);
goto block_252;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_263 = x_261;
} else {
 lean_dec_ref(x_261);
 x_263 = lean_box(0);
}
if (lean_is_scalar(x_263)) {
 x_264 = lean_alloc_ctor(1, 1, 0);
} else {
 x_264 = x_263;
}
lean_ctor_set(x_264, 0, x_262);
return x_264;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_265 = lean_ctor_get(x_253, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_266 = x_253;
} else {
 lean_dec_ref(x_253);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 1, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_265);
return x_267;
}
block_252:
{
lean_object* x_231; 
lean_inc(x_229);
lean_inc_ref(x_228);
lean_inc(x_227);
lean_inc_ref(x_226);
lean_inc(x_219);
x_231 = l_Lean_Meta_isDefEqD(x_219, x_216, x_226, x_227, x_228, x_229);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
x_234 = lean_unbox(x_232);
lean_dec(x_232);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec_ref(x_226);
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_235 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_217)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_217;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_26);
if (lean_is_scalar(x_233)) {
 x_237 = lean_alloc_ctor(0, 1, 0);
} else {
 x_237 = x_233;
}
lean_ctor_set(x_237, 0, x_236);
return x_237;
}
else
{
lean_dec(x_233);
lean_dec(x_217);
if (lean_obj_tag(x_213) == 0)
{
uint8_t x_238; lean_object* x_239; 
x_238 = 0;
lean_inc(x_229);
lean_inc_ref(x_228);
lean_inc(x_227);
lean_inc_ref(x_226);
x_239 = l_Lean_Meta_Grind_proveEq_x3f(x_215, x_219, x_238, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec_ref(x_239);
x_44 = x_240;
x_45 = x_226;
x_46 = x_227;
x_47 = x_228;
x_48 = x_229;
x_49 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec_ref(x_226);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_241 = lean_ctor_get(x_239, 0);
lean_inc(x_241);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 x_242 = x_239;
} else {
 lean_dec_ref(x_239);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 1, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_241);
return x_243;
}
}
else
{
lean_object* x_244; 
lean_dec_ref(x_213);
lean_inc(x_229);
lean_inc_ref(x_228);
lean_inc(x_227);
lean_inc_ref(x_226);
x_244 = l_Lean_Meta_Grind_proveHEq_x3f(x_215, x_219, x_220, x_221, x_222, x_223, x_224, x_225, x_226, x_227, x_228, x_229);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec_ref(x_244);
x_44 = x_245;
x_45 = x_226;
x_46 = x_227;
x_47 = x_228;
x_48 = x_229;
x_49 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec_ref(x_226);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_246 = lean_ctor_get(x_244, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 1, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_246);
return x_248;
}
}
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec_ref(x_226);
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_249 = lean_ctor_get(x_231, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 x_250 = x_231;
} else {
 lean_dec_ref(x_231);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 1, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_249);
return x_251;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_268 = lean_ctor_get(x_218, 0);
lean_inc(x_268);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_269 = x_218;
} else {
 lean_dec_ref(x_218);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 1, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_268);
return x_270;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_210);
lean_dec(x_43);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_271 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_26);
x_273 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_273, 0, x_272);
return x_273;
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_43);
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_274 = !lean_is_exclusive(x_71);
if (x_274 == 0)
{
return x_71;
}
else
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_71, 0);
lean_inc(x_275);
lean_dec(x_71);
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_275);
return x_276;
}
}
block_70:
{
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
lean_dec_ref(x_44);
x_51 = l_Lean_Meta_isExprDefEq(x_43, x_50, x_45, x_46, x_47, x_48);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_55 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_27)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_27;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_26);
lean_ctor_set(x_51, 0, x_56);
return x_51;
}
else
{
lean_object* x_57; 
lean_free_object(x_51);
lean_inc(x_1);
if (lean_is_scalar(x_27)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_27;
}
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_26);
x_18 = x_57;
x_19 = lean_box(0);
goto block_23;
}
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_60 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_27)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_27;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_26);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
else
{
lean_object* x_63; 
lean_inc(x_1);
if (lean_is_scalar(x_27)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_27;
}
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_26);
x_18 = x_63;
x_19 = lean_box(0);
goto block_23;
}
}
}
else
{
uint8_t x_64; 
lean_dec_ref(x_26);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_51);
if (x_64 == 0)
{
return x_51;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_51, 0);
lean_inc(x_65);
lean_dec(x_51);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec(x_46);
lean_dec_ref(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_67 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_27)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_27;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_26);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
lean_dec(x_26);
x_277 = lean_array_fget(x_28, x_29);
x_278 = lean_unsigned_to_nat(1u);
x_279 = lean_nat_add(x_29, x_278);
lean_dec(x_29);
x_280 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_280, 0, x_28);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set(x_280, 2, x_30);
x_281 = lean_unbox(x_277);
lean_dec(x_277);
if (x_281 == 0)
{
lean_object* x_282; 
lean_inc(x_1);
if (lean_is_scalar(x_27)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_27;
}
lean_ctor_set(x_282, 0, x_1);
lean_ctor_set(x_282, 1, x_280);
x_18 = x_282;
x_19 = lean_box(0);
goto block_23;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_306; 
x_283 = lean_array_uget(x_3, x_5);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_283);
x_306 = lean_infer_type(x_283, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 x_308 = x_306;
} else {
 lean_dec_ref(x_306);
 x_308 = lean_box(0);
}
x_309 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isEqHEq_x3f(x_307);
if (lean_obj_tag(x_309) == 1)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_308);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
lean_dec_ref(x_309);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 0);
lean_inc(x_312);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 x_313 = x_310;
} else {
 lean_dec_ref(x_310);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_311, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_311, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_316 = x_311;
} else {
 lean_dec_ref(x_311);
 x_316 = lean_box(0);
}
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_314);
x_317 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_tryToProveFalse_go(x_314, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_352; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
lean_dec_ref(x_317);
lean_inc(x_2);
x_352 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_2, x_15);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; uint8_t x_354; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
lean_dec_ref(x_352);
x_354 = lean_unbox(x_353);
lean_dec(x_353);
if (x_354 == 0)
{
lean_dec(x_313);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_319 = x_7;
x_320 = x_8;
x_321 = x_9;
x_322 = x_10;
x_323 = x_11;
x_324 = x_12;
x_325 = x_13;
x_326 = x_14;
x_327 = x_15;
x_328 = x_16;
x_329 = lean_box(0);
goto block_351;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_inc(x_318);
x_355 = l_Lean_MessageData_ofExpr(x_318);
x_356 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__2;
if (lean_is_scalar(x_313)) {
 x_357 = lean_alloc_ctor(7, 2, 0);
} else {
 x_357 = x_313;
 lean_ctor_set_tag(x_357, 7);
}
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
lean_inc(x_315);
x_358 = l_Lean_MessageData_ofExpr(x_315);
x_359 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
lean_inc(x_2);
x_360 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_2, x_359, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_360) == 0)
{
lean_dec_ref(x_360);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_319 = x_7;
x_320 = x_8;
x_321 = x_9;
x_322 = x_10;
x_323 = x_11;
x_324 = x_12;
x_325 = x_13;
x_326 = x_14;
x_327 = x_15;
x_328 = x_16;
x_329 = lean_box(0);
goto block_351;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_318);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_312);
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 x_362 = x_360;
} else {
 lean_dec_ref(x_360);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(1, 1, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_361);
return x_363;
}
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_318);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_364 = lean_ctor_get(x_352, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 x_365 = x_352;
} else {
 lean_dec_ref(x_352);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 1, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_364);
return x_366;
}
block_351:
{
lean_object* x_330; 
lean_inc(x_328);
lean_inc_ref(x_327);
lean_inc(x_326);
lean_inc_ref(x_325);
lean_inc(x_318);
x_330 = l_Lean_Meta_isDefEqD(x_318, x_315, x_325, x_326, x_327, x_328);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 x_332 = x_330;
} else {
 lean_dec_ref(x_330);
 x_332 = lean_box(0);
}
x_333 = lean_unbox(x_331);
lean_dec(x_331);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_314);
lean_dec(x_312);
lean_dec(x_283);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_334 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_316)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_316;
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_280);
if (lean_is_scalar(x_332)) {
 x_336 = lean_alloc_ctor(0, 1, 0);
} else {
 x_336 = x_332;
}
lean_ctor_set(x_336, 0, x_335);
return x_336;
}
else
{
lean_dec(x_332);
lean_dec(x_316);
if (lean_obj_tag(x_312) == 0)
{
uint8_t x_337; lean_object* x_338; 
x_337 = 0;
lean_inc(x_328);
lean_inc_ref(x_327);
lean_inc(x_326);
lean_inc_ref(x_325);
x_338 = l_Lean_Meta_Grind_proveEq_x3f(x_314, x_318, x_337, x_319, x_320, x_321, x_322, x_323, x_324, x_325, x_326, x_327, x_328);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
x_284 = x_339;
x_285 = x_325;
x_286 = x_326;
x_287 = x_327;
x_288 = x_328;
x_289 = lean_box(0);
goto block_305;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_340 = lean_ctor_get(x_338, 0);
lean_inc(x_340);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_341 = x_338;
} else {
 lean_dec_ref(x_338);
 x_341 = lean_box(0);
}
if (lean_is_scalar(x_341)) {
 x_342 = lean_alloc_ctor(1, 1, 0);
} else {
 x_342 = x_341;
}
lean_ctor_set(x_342, 0, x_340);
return x_342;
}
}
else
{
lean_object* x_343; 
lean_dec_ref(x_312);
lean_inc(x_328);
lean_inc_ref(x_327);
lean_inc(x_326);
lean_inc_ref(x_325);
x_343 = l_Lean_Meta_Grind_proveHEq_x3f(x_314, x_318, x_319, x_320, x_321, x_322, x_323, x_324, x_325, x_326, x_327, x_328);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
lean_dec_ref(x_343);
x_284 = x_344;
x_285 = x_325;
x_286 = x_326;
x_287 = x_327;
x_288 = x_328;
x_289 = lean_box(0);
goto block_305;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_345 = lean_ctor_get(x_343, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 x_346 = x_343;
} else {
 lean_dec_ref(x_343);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 1, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_345);
return x_347;
}
}
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_328);
lean_dec_ref(x_327);
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec(x_324);
lean_dec_ref(x_323);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_316);
lean_dec(x_314);
lean_dec(x_312);
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_348 = lean_ctor_get(x_330, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 x_349 = x_330;
} else {
 lean_dec_ref(x_330);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 1, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_348);
return x_350;
}
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_367 = lean_ctor_get(x_317, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 x_368 = x_317;
} else {
 lean_dec_ref(x_317);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(1, 1, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_367);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_309);
lean_dec(x_283);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_370 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_280);
if (lean_is_scalar(x_308)) {
 x_372 = lean_alloc_ctor(0, 1, 0);
} else {
 x_372 = x_308;
}
lean_ctor_set(x_372, 0, x_371);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_283);
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_373 = lean_ctor_get(x_306, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 x_374 = x_306;
} else {
 lean_dec_ref(x_306);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 1, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_373);
return x_375;
}
block_305:
{
if (lean_obj_tag(x_284) == 1)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_284, 0);
lean_inc(x_290);
lean_dec_ref(x_284);
x_291 = l_Lean_Meta_isExprDefEq(x_283, x_290, x_285, x_286, x_287, x_288);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_293 = x_291;
} else {
 lean_dec_ref(x_291);
 x_293 = lean_box(0);
}
x_294 = lean_unbox(x_292);
lean_dec(x_292);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_295 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_27)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_27;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_280);
if (lean_is_scalar(x_293)) {
 x_297 = lean_alloc_ctor(0, 1, 0);
} else {
 x_297 = x_293;
}
lean_ctor_set(x_297, 0, x_296);
return x_297;
}
else
{
lean_object* x_298; 
lean_dec(x_293);
lean_inc(x_1);
if (lean_is_scalar(x_27)) {
 x_298 = lean_alloc_ctor(0, 2, 0);
} else {
 x_298 = x_27;
}
lean_ctor_set(x_298, 0, x_1);
lean_ctor_set(x_298, 1, x_280);
x_18 = x_298;
x_19 = lean_box(0);
goto block_23;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec_ref(x_280);
lean_dec(x_27);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_299 = lean_ctor_get(x_291, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_300 = x_291;
} else {
 lean_dec_ref(x_291);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_299);
return x_301;
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_288);
lean_dec_ref(x_287);
lean_dec(x_286);
lean_dec_ref(x_285);
lean_dec(x_284);
lean_dec(x_283);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_302 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__0));
if (lean_is_scalar(x_27)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_27;
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_280);
x_304 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_304, 0, x_303);
return x_304;
}
}
}
}
}
}
block_23:
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 1;
x_21 = lean_usize_add(x_5, x_20);
x_22 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0(x_1, x_2, x_3, x_4, x_21, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(x_1, x_2, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec_ref(x_3);
return x_20;
}
}
static lean_object* _init_l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_forallMetaTelescope(x_1, x_2, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_dec(x_20);
x_21 = l_Lean_Meta_mkGenDiseqMask(x_1);
lean_dec_ref(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_21);
x_24 = l_Array_toSubarray___redArg(x_21, x_22, x_23);
x_25 = lean_box(0);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_25);
x_26 = lean_array_size(x_19);
x_27 = 0;
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_28 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(x_25, x_3, x_19, x_26, x_27, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_dec(x_33);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_34; 
lean_free_object(x_28);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_34 = l_Lean_Meta_Grind_mkEqTrueProof(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_45; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = l_Lean_Meta_mkOfEqTrueCore(x_4, x_35);
x_37 = l_Lean_mkAppN(x_36, x_19);
lean_dec(x_19);
x_38 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(x_37, x_12);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_40 = x_38;
} else {
 lean_dec_ref(x_38);
 x_40 = lean_box(0);
}
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_45 = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_free_object(x_45);
lean_inc(x_3);
x_49 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_3, x_13);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_free_object(x_30);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_41 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_52; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_39);
x_52 = lean_infer_type(x_39, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
lean_inc(x_39);
x_54 = l_Lean_MessageData_ofExpr(x_39);
x_55 = l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1;
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_55);
lean_ctor_set(x_30, 0, x_54);
x_56 = l_Lean_MessageData_ofExpr(x_53);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_30);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_3, x_57, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_58) == 0)
{
lean_dec_ref(x_58);
x_41 = lean_box(0);
goto block_44;
}
else
{
uint8_t x_59; 
lean_dec(x_40);
lean_dec(x_39);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_30);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_52);
if (x_62 == 0)
{
return x_52;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_52, 0);
lean_inc(x_63);
lean_dec(x_52);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
else
{
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_30);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
lean_ctor_set(x_45, 0, x_25);
return x_45;
}
}
else
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_45, 0);
lean_inc(x_65);
lean_dec(x_45);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_inc(x_3);
x_67 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_3, x_13);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_free_object(x_30);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_41 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_70; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_39);
x_70 = lean_infer_type(x_39, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
lean_inc(x_39);
x_72 = l_Lean_MessageData_ofExpr(x_39);
x_73 = l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1;
lean_ctor_set_tag(x_30, 7);
lean_ctor_set(x_30, 1, x_73);
lean_ctor_set(x_30, 0, x_72);
x_74 = l_Lean_MessageData_ofExpr(x_71);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_30);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_3, x_75, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_76) == 0)
{
lean_dec_ref(x_76);
x_41 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_40);
lean_dec(x_39);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_30);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_80 = lean_ctor_get(x_70, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_81 = x_70;
} else {
 lean_dec_ref(x_70);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; 
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_30);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_25);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_30);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_45);
if (x_84 == 0)
{
return x_45;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_45, 0);
lean_inc(x_85);
lean_dec(x_45);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
block_44:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
if (lean_is_scalar(x_40)) {
 x_43 = lean_alloc_ctor(0, 1, 0);
} else {
 x_43 = x_40;
}
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
else
{
uint8_t x_87; 
lean_free_object(x_30);
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_87 = !lean_is_exclusive(x_34);
if (x_87 == 0)
{
return x_34;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_34, 0);
lean_inc(x_88);
lean_dec(x_34);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; 
lean_free_object(x_30);
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_90 = lean_ctor_get(x_32, 0);
lean_inc(x_90);
lean_dec_ref(x_32);
lean_ctor_set(x_28, 0, x_90);
return x_28;
}
}
else
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_30, 0);
lean_inc(x_91);
lean_dec(x_30);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
lean_free_object(x_28);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_92 = l_Lean_Meta_Grind_mkEqTrueProof(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_103; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
x_94 = l_Lean_Meta_mkOfEqTrueCore(x_4, x_93);
x_95 = l_Lean_mkAppN(x_94, x_19);
lean_dec(x_19);
x_96 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(x_95, x_12);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_103 = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(x_97, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
x_106 = lean_unbox(x_104);
lean_dec(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_105);
lean_inc(x_3);
x_107 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_3, x_13);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_99 = lean_box(0);
goto block_102;
}
else
{
lean_object* x_110; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_97);
x_110 = lean_infer_type(x_97, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
lean_inc(x_97);
x_112 = l_Lean_MessageData_ofExpr(x_97);
x_113 = l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1;
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_MessageData_ofExpr(x_111);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_3, x_116, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_117) == 0)
{
lean_dec_ref(x_117);
x_99 = lean_box(0);
goto block_102;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_98);
lean_dec(x_97);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 1, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_121 = lean_ctor_get(x_110, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_122 = x_110;
} else {
 lean_dec_ref(x_110);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_121);
return x_123;
}
}
}
else
{
lean_object* x_124; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
if (lean_is_scalar(x_105)) {
 x_124 = lean_alloc_ctor(0, 1, 0);
} else {
 x_124 = x_105;
}
lean_ctor_set(x_124, 0, x_25);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_125 = lean_ctor_get(x_103, 0);
lean_inc(x_125);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_126 = x_103;
} else {
 lean_dec_ref(x_103);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_125);
return x_127;
}
block_102:
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_97);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(0, 1, 0);
} else {
 x_101 = x_98;
}
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_128 = lean_ctor_get(x_92, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 x_129 = x_92;
} else {
 lean_dec_ref(x_92);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 1, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_128);
return x_130;
}
}
else
{
lean_object* x_131; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_131 = lean_ctor_get(x_91, 0);
lean_inc(x_131);
lean_dec_ref(x_91);
lean_ctor_set(x_28, 0, x_131);
return x_28;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_28, 0);
lean_inc(x_132);
lean_dec(x_28);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_134 = x_132;
} else {
 lean_dec_ref(x_132);
 x_134 = lean_box(0);
}
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_135; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_135 = l_Lean_Meta_Grind_mkEqTrueProof(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_146; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
x_137 = l_Lean_Meta_mkOfEqTrueCore(x_4, x_136);
x_138 = l_Lean_mkAppN(x_137, x_19);
lean_dec(x_19);
x_139 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(x_138, x_12);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 x_141 = x_139;
} else {
 lean_dec_ref(x_139);
 x_141 = lean_box(0);
}
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_146 = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(x_140, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
x_149 = lean_unbox(x_147);
lean_dec(x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
lean_dec(x_148);
lean_inc(x_3);
x_150 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_3, x_13);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_dec(x_134);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_142 = lean_box(0);
goto block_145;
}
else
{
lean_object* x_153; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_140);
x_153 = lean_infer_type(x_140, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
lean_inc(x_140);
x_155 = l_Lean_MessageData_ofExpr(x_140);
x_156 = l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1;
if (lean_is_scalar(x_134)) {
 x_157 = lean_alloc_ctor(7, 2, 0);
} else {
 x_157 = x_134;
 lean_ctor_set_tag(x_157, 7);
}
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_MessageData_ofExpr(x_154);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_3, x_159, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_160) == 0)
{
lean_dec_ref(x_160);
x_142 = lean_box(0);
goto block_145;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_141);
lean_dec(x_140);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_161);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_134);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_164 = lean_ctor_get(x_153, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_165 = x_153;
} else {
 lean_dec_ref(x_153);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_164);
return x_166;
}
}
}
else
{
lean_object* x_167; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_134);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
if (lean_is_scalar(x_148)) {
 x_167 = lean_alloc_ctor(0, 1, 0);
} else {
 x_167 = x_148;
}
lean_ctor_set(x_167, 0, x_25);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_134);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_168 = lean_ctor_get(x_146, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_169 = x_146;
} else {
 lean_dec_ref(x_146);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 1, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_168);
return x_170;
}
block_145:
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_140);
if (lean_is_scalar(x_141)) {
 x_144 = lean_alloc_ctor(0, 1, 0);
} else {
 x_144 = x_141;
}
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_134);
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_171 = lean_ctor_get(x_135, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_172 = x_135;
} else {
 lean_dec_ref(x_135);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 1, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_134);
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_174 = lean_ctor_get(x_133, 0);
lean_inc(x_174);
lean_dec_ref(x_133);
x_175 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_175, 0, x_174);
return x_175;
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_176 = !lean_is_exclusive(x_28);
if (x_176 == 0)
{
return x_28;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_28, 0);
lean_inc(x_177);
lean_dec(x_28);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; size_t x_186; size_t x_187; lean_object* x_188; 
x_179 = lean_ctor_get(x_17, 0);
lean_inc(x_179);
lean_dec(x_17);
x_180 = l_Lean_Meta_mkGenDiseqMask(x_1);
lean_dec_ref(x_1);
x_181 = lean_unsigned_to_nat(0u);
x_182 = lean_array_get_size(x_180);
x_183 = l_Array_toSubarray___redArg(x_180, x_181, x_182);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = lean_array_size(x_179);
x_187 = 0;
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_188 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(x_184, x_3, x_179, x_186, x_187, x_185, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_189, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_192 = x_189;
} else {
 lean_dec_ref(x_189);
 x_192 = lean_box(0);
}
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_193; 
lean_dec(x_190);
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_193 = l_Lean_Meta_Grind_mkEqTrueProof(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_204; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec_ref(x_193);
x_195 = l_Lean_Meta_mkOfEqTrueCore(x_4, x_194);
x_196 = l_Lean_mkAppN(x_195, x_179);
lean_dec(x_179);
x_197 = l_Lean_instantiateMVars___at___00Lean_Meta_Grind_tryToProveFalse_spec__1___redArg(x_196, x_12);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 x_199 = x_197;
} else {
 lean_dec_ref(x_197);
 x_199 = lean_box(0);
}
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
x_204 = l_Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2(x_198, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_206 = x_204;
} else {
 lean_dec_ref(x_204);
 x_206 = lean_box(0);
}
x_207 = lean_unbox(x_205);
lean_dec(x_205);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_dec(x_206);
lean_inc(x_3);
x_208 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_3, x_13);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_dec_ref(x_208);
x_210 = lean_unbox(x_209);
lean_dec(x_209);
if (x_210 == 0)
{
lean_dec(x_192);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_200 = lean_box(0);
goto block_203;
}
else
{
lean_object* x_211; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_198);
x_211 = lean_infer_type(x_198, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec_ref(x_211);
lean_inc(x_198);
x_213 = l_Lean_MessageData_ofExpr(x_198);
x_214 = l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1;
if (lean_is_scalar(x_192)) {
 x_215 = lean_alloc_ctor(7, 2, 0);
} else {
 x_215 = x_192;
 lean_ctor_set_tag(x_215, 7);
}
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_216 = l_Lean_MessageData_ofExpr(x_212);
x_217 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_218 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_3, x_217, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
if (lean_obj_tag(x_218) == 0)
{
lean_dec_ref(x_218);
x_200 = lean_box(0);
goto block_203;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_199);
lean_dec(x_198);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_220 = x_218;
} else {
 lean_dec_ref(x_218);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 1, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_219);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_192);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_222 = lean_ctor_get(x_211, 0);
lean_inc(x_222);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 x_223 = x_211;
} else {
 lean_dec_ref(x_211);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_222);
return x_224;
}
}
}
else
{
lean_object* x_225; 
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_192);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
if (lean_is_scalar(x_206)) {
 x_225 = lean_alloc_ctor(0, 1, 0);
} else {
 x_225 = x_206;
}
lean_ctor_set(x_225, 0, x_184);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_192);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_3);
x_226 = lean_ctor_get(x_204, 0);
lean_inc(x_226);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_227 = x_204;
} else {
 lean_dec_ref(x_204);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 1, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_226);
return x_228;
}
block_203:
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_201, 0, x_198);
if (lean_is_scalar(x_199)) {
 x_202 = lean_alloc_ctor(0, 1, 0);
} else {
 x_202 = x_199;
}
lean_ctor_set(x_202, 0, x_201);
return x_202;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_192);
lean_dec(x_179);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_229 = lean_ctor_get(x_193, 0);
lean_inc(x_229);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 x_230 = x_193;
} else {
 lean_dec_ref(x_193);
 x_230 = lean_box(0);
}
if (lean_is_scalar(x_230)) {
 x_231 = lean_alloc_ctor(1, 1, 0);
} else {
 x_231 = x_230;
}
lean_ctor_set(x_231, 0, x_229);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_192);
lean_dec(x_179);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_232 = lean_ctor_get(x_191, 0);
lean_inc(x_232);
lean_dec_ref(x_191);
if (lean_is_scalar(x_190)) {
 x_233 = lean_alloc_ctor(0, 1, 0);
} else {
 x_233 = x_190;
}
lean_ctor_set(x_233, 0, x_232);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_179);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_234 = lean_ctor_get(x_188, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_235 = x_188;
} else {
 lean_dec_ref(x_188);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 1, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_234);
return x_236;
}
}
}
else
{
uint8_t x_237; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_237 = !lean_is_exclusive(x_16);
if (x_237 == 0)
{
return x_16;
}
else
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_16, 0);
lean_inc(x_238);
lean_dec(x_16);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_238);
return x_239;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_2);
x_17 = l_Lean_Meta_Grind_tryToProveFalse___lam__0(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_17 = ((lean_object*)(l_Lean_Meta_Grind_tryToProveFalse___closed__1));
x_59 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_17, x_10);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
x_27 = x_11;
x_28 = lean_box(0);
goto block_58;
}
else
{
lean_object* x_62; 
x_62 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_62);
lean_inc_ref(x_1);
x_63 = l_Lean_MessageData_ofExpr(x_1);
x_64 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_17, x_63, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_64) == 0)
{
lean_dec_ref(x_64);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
x_27 = x_11;
x_28 = lean_box(0);
goto block_58;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_64;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_62;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_58:
{
lean_object* x_29; 
lean_inc_ref(x_1);
x_29 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_Expr_cleanupAnnotations(x_30);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec_ref(x_31);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_33);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_35 = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
x_36 = l_Lean_Expr_isConstOf(x_34, x_35);
lean_dec_ref(x_34);
if (x_36 == 0)
{
lean_dec_ref(x_33);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_tryToProveFalse___lam__0___boxed), 15, 4);
lean_closure_set(x_39, 0, x_33);
lean_closure_set(x_39, 1, x_38);
lean_closure_set(x_39, 2, x_17);
lean_closure_set(x_39, 3, x_1);
x_40 = 0;
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_41 = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_Grind_tryToProveFalse_spec__3___redArg(x_39, x_40, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; 
lean_free_object(x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = l_Lean_Meta_Grind_closeGoal(x_44, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec(x_43);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_46 = lean_box(0);
lean_ctor_set(x_41, 0, x_46);
return x_41;
}
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_41, 0);
lean_inc(x_47);
lean_dec(x_41);
if (lean_obj_tag(x_47) == 1)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l_Lean_Meta_Grind_closeGoal(x_48, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
return x_41;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_41, 0);
lean_inc(x_53);
lean_dec(x_41);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_1);
x_55 = !lean_is_exclusive(x_29);
if (x_55 == 0)
{
return x_29;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_29, 0);
lean_inc(x_56);
lean_dec(x_29);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_tryToProveFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_tryToProveFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, size_t x_12, size_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24) {
_start:
{
lean_object* x_26; 
x_26 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___redArg(x_1, x_2, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
return x_26;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
_start:
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_27 = lean_unbox_usize(x_13);
lean_dec(x_13);
x_28 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_26, x_27, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___redArg(x_1, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_isAssignable___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9_spec__11___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9_spec__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Meta_Grind_propagateMatchCondUp___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_29 = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__3));
x_128 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_29, x_10);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
x_30 = x_2;
x_31 = x_3;
x_32 = x_4;
x_33 = x_5;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = lean_box(0);
goto block_127;
}
else
{
lean_object* x_131; 
x_131 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec_ref(x_131);
x_132 = l_Lean_Meta_Grind_propagateMatchCondUp___closed__3;
lean_inc_ref(x_1);
x_133 = l_Lean_indentExpr(x_1);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_29, x_134, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_135) == 0)
{
lean_dec_ref(x_135);
x_30 = x_2;
x_31 = x_3;
x_32 = x_4;
x_33 = x_5;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_10;
x_39 = x_11;
x_40 = lean_box(0);
goto block_127;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_135;
}
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_131;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
lean_inc_ref(x_1);
x_26 = l_Lean_Meta_mkEqTrueCore(x_1, x_17);
x_27 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_26, x_18, x_19, x_20, x_21, x_22, x_23, x_24);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
return x_27;
}
block_127:
{
lean_object* x_41; 
lean_inc_ref(x_1);
x_41 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_30, x_34, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc_ref(x_1);
x_44 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(x_1, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
x_48 = lean_box(0);
lean_ctor_set(x_44, 0, x_48);
return x_44;
}
else
{
lean_object* x_49; 
lean_free_object(x_44);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc(x_35);
lean_inc_ref(x_34);
lean_inc(x_33);
lean_inc_ref(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc_ref(x_1);
x_49 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(x_1, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_29, x_38);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
x_17 = x_51;
x_18 = x_30;
x_19 = x_32;
x_20 = x_34;
x_21 = x_36;
x_22 = x_37;
x_23 = x_38;
x_24 = x_39;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_55; 
x_55 = l_Lean_Meta_Grind_updateLastTag(x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
lean_dec_ref(x_55);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc(x_51);
x_56 = lean_infer_type(x_51, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = l_Lean_MessageData_ofExpr(x_57);
x_59 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_29, x_58, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_59) == 0)
{
lean_dec_ref(x_59);
x_17 = x_51;
x_18 = x_30;
x_19 = x_32;
x_20 = x_34;
x_21 = x_36;
x_22 = x_37;
x_23 = x_38;
x_24 = x_39;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_dec(x_51);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec_ref(x_1);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_51);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_56);
if (x_60 == 0)
{
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
else
{
lean_dec(x_51);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec_ref(x_1);
return x_55;
}
}
}
else
{
lean_object* x_63; 
lean_dec(x_50);
lean_dec(x_30);
x_63 = l_Lean_Meta_Grind_getConfig___redArg(x_32);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*10 + 14);
lean_dec(x_64);
if (x_65 == 0)
{
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = l_Lean_Meta_Grind_propagateMatchCondUp___closed__1;
x_67 = l_Lean_indentExpr(x_1);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_Grind_reportIssue(x_68, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_69) == 0)
{
lean_dec_ref(x_69);
x_13 = lean_box(0);
goto block_16;
}
else
{
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec_ref(x_1);
x_70 = !lean_is_exclusive(x_63);
if (x_70 == 0)
{
return x_63;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
lean_dec(x_63);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_49);
if (x_73 == 0)
{
return x_49;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_49, 0);
lean_inc(x_74);
lean_dec(x_49);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_44, 0);
lean_inc(x_76);
lean_dec(x_44);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
else
{
lean_object* x_80; 
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc(x_35);
lean_inc_ref(x_34);
lean_inc(x_33);
lean_inc_ref(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc_ref(x_1);
x_80 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f(x_1, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__0___redArg(x_29, x_38);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
x_17 = x_82;
x_18 = x_30;
x_19 = x_32;
x_20 = x_34;
x_21 = x_36;
x_22 = x_37;
x_23 = x_38;
x_24 = x_39;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_86; 
x_86 = l_Lean_Meta_Grind_updateLastTag(x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
lean_dec_ref(x_86);
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc(x_82);
x_87 = lean_infer_type(x_82, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = l_Lean_MessageData_ofExpr(x_88);
x_90 = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg(x_29, x_89, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_90) == 0)
{
lean_dec_ref(x_90);
x_17 = x_82;
x_18 = x_30;
x_19 = x_32;
x_20 = x_34;
x_21 = x_36;
x_22 = x_37;
x_23 = x_38;
x_24 = x_39;
x_25 = lean_box(0);
goto block_28;
}
else
{
lean_dec(x_82);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec_ref(x_1);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_82);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec_ref(x_1);
x_91 = lean_ctor_get(x_87, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_92 = x_87;
} else {
 lean_dec_ref(x_87);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_91);
return x_93;
}
}
else
{
lean_dec(x_82);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_34);
lean_dec_ref(x_32);
lean_dec(x_30);
lean_dec_ref(x_1);
return x_86;
}
}
}
else
{
lean_object* x_94; 
lean_dec(x_81);
lean_dec(x_30);
x_94 = l_Lean_Meta_Grind_getConfig___redArg(x_32);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_96 = lean_ctor_get_uint8(x_95, sizeof(void*)*10 + 14);
lean_dec(x_95);
if (x_96 == 0)
{
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec_ref(x_1);
x_13 = lean_box(0);
goto block_16;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = l_Lean_Meta_Grind_propagateMatchCondUp___closed__1;
x_98 = l_Lean_indentExpr(x_1);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Meta_Grind_reportIssue(x_99, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_100) == 0)
{
lean_dec_ref(x_100);
x_13 = lean_box(0);
goto block_16;
}
else
{
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec_ref(x_1);
x_101 = lean_ctor_get(x_94, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_102 = x_94;
} else {
 lean_dec_ref(x_94);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_101);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
x_104 = lean_ctor_get(x_80, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_105 = x_80;
} else {
 lean_dec_ref(x_80);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_104);
return x_106;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
x_107 = !lean_is_exclusive(x_44);
if (x_107 == 0)
{
return x_44;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_44, 0);
lean_inc(x_108);
lean_dec(x_44);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; 
lean_inc(x_39);
lean_inc_ref(x_38);
lean_inc(x_37);
lean_inc_ref(x_36);
lean_inc_ref(x_1);
x_110 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(x_1, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_unbox(x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; 
lean_free_object(x_110);
x_114 = l_Lean_Meta_Grind_tryToProveFalse(x_1, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
return x_114;
}
else
{
lean_object* x_115; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
x_115 = lean_box(0);
lean_ctor_set(x_110, 0, x_115);
return x_110;
}
}
else
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
lean_dec(x_110);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = l_Lean_Meta_Grind_tryToProveFalse(x_1, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37, x_38, x_39);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
x_121 = !lean_is_exclusive(x_110);
if (x_121 == 0)
{
return x_110;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_110, 0);
lean_inc(x_122);
lean_dec(x_110);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec_ref(x_1);
x_124 = !lean_is_exclusive(x_41);
if (x_124 == 0)
{
return x_41;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_41, 0);
lean_inc(x_125);
lean_dec(x_41);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateMatchCondUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondUp___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc_ref(x_1);
x_13 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; 
lean_free_object(x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_18 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_free_object(x_18);
x_22 = l_Lean_Meta_Grind_tryToProveFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_23 = lean_box(0);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Meta_Grind_tryToProveFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_13, 0);
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
lean_object* x_36; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
x_36 = l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_unbox(x_37);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_38);
x_40 = l_Lean_Meta_Grind_tryToProveFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_41 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_38;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_46 = !lean_is_exclusive(x_13);
if (x_46 == 0)
{
return x_13;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_13, 0);
lean_inc(x_47);
lean_dec(x_13);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_propagateMatchCondDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__4));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateMatchCondDown___boxed), 12, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_ProveEq(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_ProveEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_collectMatchCondLhss___closed__0);
l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_replaceLhs_x3f___closed__3);
l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0 = _init_l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_collectMatchCondLhssAndAbstract___closed__0);
l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isMatchCondFalseHyp_isFalse___closed__1);
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__0();
l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2 = _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__1___redArg___closed__2);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__5 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__5();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__5);
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__7 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__7();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_isSatisfied_spec__2_spec__3___closed__7);
l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__3);
l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_go_x3f___closed__5);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___closed__1 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_MatchCond_0__Lean_Meta_Grind_mkMatchCondProof_x3f_spec__0_spec__0___closed__1);
l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__0 = _init_l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__0();
lean_mark_persistent(l_panic___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__8___closed__0);
l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg___closed__0 = _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg___closed__0();
l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6_spec__7_spec__9___redArg___closed__1();
l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__3 = _init_l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__3();
lean_mark_persistent(l_Lean_isLevelMVarAssignable___at___00Lean_hasAssignableLevelMVar___at___00Lean_hasAssignableMVar___at___00Lean_Meta_Grind_tryToProveFalse_spec__2_spec__4_spec__6___closed__3);
l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__2 = _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__2();
lean_mark_persistent(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_tryToProveFalse_spec__0_spec__0___closed__2);
l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1 = _init_l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_tryToProveFalse___lam__0___closed__1);
l_Lean_Meta_Grind_propagateMatchCondUp___closed__1 = _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateMatchCondUp___closed__1);
l_Lean_Meta_Grind_propagateMatchCondUp___closed__3 = _init_l_Lean_Meta_Grind_propagateMatchCondUp___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateMatchCondUp___closed__3);
if (builtin) {res = l_Lean_Meta_Grind_propagateMatchCondUp___regBuiltin_Lean_Meta_Grind_propagateMatchCondUp_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_1804808425____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Grind_propagateMatchCondDown___regBuiltin_Lean_Meta_Grind_propagateMatchCondDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_MatchCond_2992396906____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
