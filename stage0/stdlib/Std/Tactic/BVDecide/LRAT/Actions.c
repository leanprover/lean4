// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Actions
// Imports: public import Std.Sat.CNF
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
lean_object* l_Nat_decEq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instReprNat___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Array_instRepr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_instToStringArray___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_instToStringProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Array_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Bool_repr___boxed(lean_object*, lean_object*);
lean_object* l_Prod_repr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addEmpty_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addEmpty_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addRup_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addRup_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addRat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addRat_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_del_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_del_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(lean_object*, lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___closed__0;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0_value;
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0_value)} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__1_value;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprNat___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Std.Tactic.BVDecide.LRAT.Action.addEmpty"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__1_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__1_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__2_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__3_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Tactic.BVDecide.LRAT.Action.addRup"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__6_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__6_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__7 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__7_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__8 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__8_value;
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instRepr___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0_value)} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__9 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__9_value;
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Bool_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__10 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__10_value;
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprTupleOfRepr___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__10_value)} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__11 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__11_value;
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprTupleOfRepr___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__9_value)} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__12 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__12_value;
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Prod_repr___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0_value),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__12_value)} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__13 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__13_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.Tactic.BVDecide.LRAT.Action.addRat"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__14 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__14_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__14_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__15 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__15_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__15_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__16 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__16_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Std.Tactic.BVDecide.LRAT.Action.del"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__17 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__17_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__17_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__18 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__18_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__18_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__19 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Nat_reprFast, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "addEmpty (id: "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__1_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ") (hints: "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "#"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "addRup "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__5 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__5_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " (id : "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__6 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__6_value;
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringArray___redArg___lam__0, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0_value)} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__7 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__7_value;
static const lean_closure_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToStringProd___redArg___lam__0, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0_value),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__7_value)} };
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__8 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__8_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "addRat "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__9 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__9_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " (id: "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__10 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__10_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = ") (pivot: "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__11 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__11_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__12 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__12_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__13 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__13_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ") (rup hints: "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__14 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__14_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = ") (rat hints: "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__15 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__15_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__16 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__16_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__17 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__17_value;
static const lean_string_object l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "del "};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__18 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__18_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instToStringAction___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instToStringAction(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___redArg___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___redArg(v_x_6_);
lean_dec_ref(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx(lean_object* v_00_u03b2_8_, lean_object* v_00_u03b1_9_, lean_object* v_x_10_){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___redArg(v_x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___boxed(lean_object* v_00_u03b2_12_, lean_object* v_00_u03b1_13_, lean_object* v_x_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx(v_00_u03b2_12_, v_00_u03b1_13_, v_x_14_);
lean_dec_ref(v_x_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(lean_object* v_t_16_, lean_object* v_k_17_){
_start:
{
switch(lean_obj_tag(v_t_16_))
{
case 0:
{
lean_object* v_id_18_; lean_object* v_rupHints_19_; lean_object* v___x_20_; 
v_id_18_ = lean_ctor_get(v_t_16_, 0);
lean_inc(v_id_18_);
v_rupHints_19_ = lean_ctor_get(v_t_16_, 1);
lean_inc_ref(v_rupHints_19_);
lean_dec_ref(v_t_16_);
v___x_20_ = lean_apply_2(v_k_17_, v_id_18_, v_rupHints_19_);
return v___x_20_;
}
case 1:
{
lean_object* v_id_21_; lean_object* v_c_22_; lean_object* v_rupHints_23_; lean_object* v___x_24_; 
v_id_21_ = lean_ctor_get(v_t_16_, 0);
lean_inc(v_id_21_);
v_c_22_ = lean_ctor_get(v_t_16_, 1);
lean_inc(v_c_22_);
v_rupHints_23_ = lean_ctor_get(v_t_16_, 2);
lean_inc_ref(v_rupHints_23_);
lean_dec_ref(v_t_16_);
v___x_24_ = lean_apply_3(v_k_17_, v_id_21_, v_c_22_, v_rupHints_23_);
return v___x_24_;
}
case 2:
{
lean_object* v_id_25_; lean_object* v_c_26_; lean_object* v_pivot_27_; lean_object* v_rupHints_28_; lean_object* v_ratHints_29_; lean_object* v___x_30_; 
v_id_25_ = lean_ctor_get(v_t_16_, 0);
lean_inc(v_id_25_);
v_c_26_ = lean_ctor_get(v_t_16_, 1);
lean_inc(v_c_26_);
v_pivot_27_ = lean_ctor_get(v_t_16_, 2);
lean_inc_ref(v_pivot_27_);
v_rupHints_28_ = lean_ctor_get(v_t_16_, 3);
lean_inc_ref(v_rupHints_28_);
v_ratHints_29_ = lean_ctor_get(v_t_16_, 4);
lean_inc_ref(v_ratHints_29_);
lean_dec_ref(v_t_16_);
v___x_30_ = lean_apply_5(v_k_17_, v_id_25_, v_c_26_, v_pivot_27_, v_rupHints_28_, v_ratHints_29_);
return v___x_30_;
}
default: 
{
lean_object* v_ids_31_; lean_object* v___x_32_; 
v_ids_31_ = lean_ctor_get(v_t_16_, 0);
lean_inc_ref(v_ids_31_);
lean_dec_ref(v_t_16_);
v___x_32_ = lean_apply_1(v_k_17_, v_ids_31_);
return v___x_32_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorElim(lean_object* v_00_u03b2_33_, lean_object* v_00_u03b1_34_, lean_object* v_motive_35_, lean_object* v_ctorIdx_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_k_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_37_, v_k_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___boxed(lean_object* v_00_u03b2_41_, lean_object* v_00_u03b1_42_, lean_object* v_motive_43_, lean_object* v_ctorIdx_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_k_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim(v_00_u03b2_41_, v_00_u03b1_42_, v_motive_43_, v_ctorIdx_44_, v_t_45_, v_h_46_, v_k_47_);
lean_dec(v_ctorIdx_44_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addEmpty_elim___redArg(lean_object* v_t_49_, lean_object* v_addEmpty_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_49_, v_addEmpty_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addEmpty_elim(lean_object* v_00_u03b2_52_, lean_object* v_00_u03b1_53_, lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_addEmpty_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_55_, v_addEmpty_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addRup_elim___redArg(lean_object* v_t_59_, lean_object* v_addRup_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_59_, v_addRup_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addRup_elim(lean_object* v_00_u03b2_62_, lean_object* v_00_u03b1_63_, lean_object* v_motive_64_, lean_object* v_t_65_, lean_object* v_h_66_, lean_object* v_addRup_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_65_, v_addRup_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addRat_elim___redArg(lean_object* v_t_69_, lean_object* v_addRat_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_69_, v_addRat_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addRat_elim(lean_object* v_00_u03b2_72_, lean_object* v_00_u03b1_73_, lean_object* v_motive_74_, lean_object* v_t_75_, lean_object* v_h_76_, lean_object* v_addRat_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_75_, v_addRat_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_del_elim___redArg(lean_object* v_t_79_, lean_object* v_del_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_79_, v_del_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_del_elim(lean_object* v_00_u03b2_82_, lean_object* v_00_u03b1_83_, lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_del_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_85_, v_del_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(lean_object* v_00_u03b2_94_, lean_object* v_00_u03b1_95_){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__1));
return v___x_96_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___closed__0(void){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(lean_box(0), lean_box(0));
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction(lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___closed__0, &l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___closed__0);
return v___x_100_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0(lean_object* v___f_101_, lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
lean_object* v_fst_104_; lean_object* v_snd_105_; lean_object* v_fst_106_; lean_object* v_snd_107_; uint8_t v___x_108_; 
v_fst_104_ = lean_ctor_get(v_x_102_, 0);
v_snd_105_ = lean_ctor_get(v_x_102_, 1);
v_fst_106_ = lean_ctor_get(v_x_103_, 0);
v_snd_107_ = lean_ctor_get(v_x_103_, 1);
v___x_108_ = lean_nat_dec_eq(v_fst_104_, v_fst_106_);
if (v___x_108_ == 0)
{
lean_dec_ref(v___f_101_);
return v___x_108_;
}
else
{
lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_109_ = lean_array_get_size(v_snd_105_);
v___x_110_ = lean_array_get_size(v_snd_107_);
v___x_111_ = lean_nat_dec_eq(v___x_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_dec_ref(v___f_101_);
return v___x_111_;
}
else
{
uint8_t v___x_112_; 
v___x_112_ = l_Array_isEqvAux___redArg(v_snd_105_, v_snd_107_, v___f_101_, v___x_109_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0___boxed(lean_object* v___f_113_, lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0(v___f_113_, v_x_114_, v_x_115_);
lean_dec_ref(v_x_115_);
lean_dec_ref(v_x_114_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(lean_object* v_inst_121_, lean_object* v_inst_122_, lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
switch(lean_obj_tag(v_x_123_))
{
case 0:
{
lean_dec_ref(v_inst_122_);
lean_dec_ref(v_inst_121_);
if (lean_obj_tag(v_x_124_) == 0)
{
lean_object* v_id_125_; lean_object* v_rupHints_126_; lean_object* v_id_127_; lean_object* v_rupHints_128_; uint8_t v___x_129_; 
v_id_125_ = lean_ctor_get(v_x_123_, 0);
lean_inc(v_id_125_);
v_rupHints_126_ = lean_ctor_get(v_x_123_, 1);
lean_inc_ref(v_rupHints_126_);
lean_dec_ref(v_x_123_);
v_id_127_ = lean_ctor_get(v_x_124_, 0);
lean_inc(v_id_127_);
v_rupHints_128_ = lean_ctor_get(v_x_124_, 1);
lean_inc_ref(v_rupHints_128_);
lean_dec_ref(v_x_124_);
v___x_129_ = lean_nat_dec_eq(v_id_125_, v_id_127_);
lean_dec(v_id_127_);
lean_dec(v_id_125_);
if (v___x_129_ == 0)
{
lean_dec_ref(v_rupHints_128_);
lean_dec_ref(v_rupHints_126_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_130_ = lean_array_get_size(v_rupHints_126_);
v___x_131_ = lean_array_get_size(v_rupHints_128_);
v___x_132_ = lean_nat_dec_eq(v___x_130_, v___x_131_);
if (v___x_132_ == 0)
{
lean_dec_ref(v_rupHints_128_);
lean_dec_ref(v_rupHints_126_);
return v___x_132_;
}
else
{
lean_object* v___f_133_; uint8_t v___x_134_; 
v___f_133_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0));
v___x_134_ = l_Array_isEqvAux___redArg(v_rupHints_126_, v_rupHints_128_, v___f_133_, v___x_130_);
lean_dec_ref(v_rupHints_128_);
lean_dec_ref(v_rupHints_126_);
return v___x_134_;
}
}
}
else
{
uint8_t v___x_135_; 
lean_dec_ref(v_x_123_);
lean_dec_ref(v_x_124_);
v___x_135_ = 0;
return v___x_135_;
}
}
case 1:
{
lean_dec_ref(v_inst_122_);
if (lean_obj_tag(v_x_124_) == 1)
{
lean_object* v_id_136_; lean_object* v_c_137_; lean_object* v_rupHints_138_; lean_object* v_id_139_; lean_object* v_c_140_; lean_object* v_rupHints_141_; uint8_t v___x_142_; 
v_id_136_ = lean_ctor_get(v_x_123_, 0);
lean_inc(v_id_136_);
v_c_137_ = lean_ctor_get(v_x_123_, 1);
lean_inc(v_c_137_);
v_rupHints_138_ = lean_ctor_get(v_x_123_, 2);
lean_inc_ref(v_rupHints_138_);
lean_dec_ref(v_x_123_);
v_id_139_ = lean_ctor_get(v_x_124_, 0);
lean_inc(v_id_139_);
v_c_140_ = lean_ctor_get(v_x_124_, 1);
lean_inc(v_c_140_);
v_rupHints_141_ = lean_ctor_get(v_x_124_, 2);
lean_inc_ref(v_rupHints_141_);
lean_dec_ref(v_x_124_);
v___x_142_ = lean_nat_dec_eq(v_id_136_, v_id_139_);
lean_dec(v_id_139_);
lean_dec(v_id_136_);
if (v___x_142_ == 0)
{
lean_dec_ref(v_rupHints_141_);
lean_dec(v_c_140_);
lean_dec_ref(v_rupHints_138_);
lean_dec(v_c_137_);
lean_dec_ref(v_inst_121_);
return v___x_142_;
}
else
{
lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_143_ = lean_apply_2(v_inst_121_, v_c_137_, v_c_140_);
v___x_144_ = lean_unbox(v___x_143_);
if (v___x_144_ == 0)
{
uint8_t v___x_145_; 
lean_dec_ref(v_rupHints_141_);
lean_dec_ref(v_rupHints_138_);
v___x_145_ = lean_unbox(v___x_143_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v___x_146_ = lean_array_get_size(v_rupHints_138_);
v___x_147_ = lean_array_get_size(v_rupHints_141_);
v___x_148_ = lean_nat_dec_eq(v___x_146_, v___x_147_);
if (v___x_148_ == 0)
{
lean_dec_ref(v_rupHints_141_);
lean_dec_ref(v_rupHints_138_);
return v___x_148_;
}
else
{
lean_object* v___f_149_; uint8_t v___x_150_; 
v___f_149_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0));
v___x_150_ = l_Array_isEqvAux___redArg(v_rupHints_138_, v_rupHints_141_, v___f_149_, v___x_146_);
lean_dec_ref(v_rupHints_141_);
lean_dec_ref(v_rupHints_138_);
return v___x_150_;
}
}
}
}
else
{
uint8_t v___x_151_; 
lean_dec_ref(v_x_123_);
lean_dec_ref(v_x_124_);
lean_dec_ref(v_inst_121_);
v___x_151_ = 0;
return v___x_151_;
}
}
case 2:
{
if (lean_obj_tag(v_x_124_) == 2)
{
lean_object* v_id_152_; lean_object* v_c_153_; lean_object* v_pivot_154_; lean_object* v_rupHints_155_; lean_object* v_ratHints_156_; lean_object* v_id_157_; lean_object* v_c_158_; lean_object* v_pivot_159_; lean_object* v_rupHints_160_; lean_object* v_ratHints_161_; uint8_t v___x_162_; 
v_id_152_ = lean_ctor_get(v_x_123_, 0);
lean_inc(v_id_152_);
v_c_153_ = lean_ctor_get(v_x_123_, 1);
lean_inc(v_c_153_);
v_pivot_154_ = lean_ctor_get(v_x_123_, 2);
lean_inc_ref(v_pivot_154_);
v_rupHints_155_ = lean_ctor_get(v_x_123_, 3);
lean_inc_ref(v_rupHints_155_);
v_ratHints_156_ = lean_ctor_get(v_x_123_, 4);
lean_inc_ref(v_ratHints_156_);
lean_dec_ref(v_x_123_);
v_id_157_ = lean_ctor_get(v_x_124_, 0);
lean_inc(v_id_157_);
v_c_158_ = lean_ctor_get(v_x_124_, 1);
lean_inc(v_c_158_);
v_pivot_159_ = lean_ctor_get(v_x_124_, 2);
lean_inc_ref(v_pivot_159_);
v_rupHints_160_ = lean_ctor_get(v_x_124_, 3);
lean_inc_ref(v_rupHints_160_);
v_ratHints_161_ = lean_ctor_get(v_x_124_, 4);
lean_inc_ref(v_ratHints_161_);
lean_dec_ref(v_x_124_);
v___x_162_ = lean_nat_dec_eq(v_id_152_, v_id_157_);
lean_dec(v_id_157_);
lean_dec(v_id_152_);
if (v___x_162_ == 0)
{
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_rupHints_160_);
lean_dec_ref(v_pivot_159_);
lean_dec(v_c_158_);
lean_dec_ref(v_ratHints_156_);
lean_dec_ref(v_rupHints_155_);
lean_dec_ref(v_pivot_154_);
lean_dec(v_c_153_);
lean_dec_ref(v_inst_122_);
lean_dec_ref(v_inst_121_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_163_ = lean_apply_2(v_inst_121_, v_c_153_, v_c_158_);
v___x_164_ = lean_unbox(v___x_163_);
if (v___x_164_ == 0)
{
uint8_t v___x_165_; 
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_rupHints_160_);
lean_dec_ref(v_pivot_159_);
lean_dec_ref(v_ratHints_156_);
lean_dec_ref(v_rupHints_155_);
lean_dec_ref(v_pivot_154_);
lean_dec_ref(v_inst_122_);
v___x_165_ = lean_unbox(v___x_163_);
return v___x_165_;
}
else
{
lean_object* v_fst_166_; lean_object* v_snd_167_; lean_object* v_fst_168_; lean_object* v_snd_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v_fst_166_ = lean_ctor_get(v_pivot_154_, 0);
lean_inc(v_fst_166_);
v_snd_167_ = lean_ctor_get(v_pivot_154_, 1);
lean_inc(v_snd_167_);
lean_dec_ref(v_pivot_154_);
v_fst_168_ = lean_ctor_get(v_pivot_159_, 0);
lean_inc(v_fst_168_);
v_snd_169_ = lean_ctor_get(v_pivot_159_, 1);
lean_inc(v_snd_169_);
lean_dec_ref(v_pivot_159_);
v___x_170_ = lean_apply_2(v_inst_122_, v_fst_166_, v_fst_168_);
v___x_171_ = lean_unbox(v___x_170_);
if (v___x_171_ == 0)
{
uint8_t v___x_172_; 
lean_dec(v_snd_169_);
lean_dec(v_snd_167_);
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_rupHints_160_);
lean_dec_ref(v_ratHints_156_);
lean_dec_ref(v_rupHints_155_);
v___x_172_ = lean_unbox(v___x_170_);
return v___x_172_;
}
else
{
lean_object* v___f_173_; lean_object* v___f_174_; uint8_t v___x_184_; 
v___f_173_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0));
v___f_174_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__1));
v___x_184_ = lean_unbox(v_snd_167_);
if (v___x_184_ == 0)
{
uint8_t v___x_185_; 
v___x_185_ = lean_unbox(v_snd_169_);
lean_dec(v_snd_169_);
if (v___x_185_ == 0)
{
lean_dec(v_snd_167_);
goto v___jp_175_;
}
else
{
uint8_t v___x_186_; 
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_rupHints_160_);
lean_dec_ref(v_ratHints_156_);
lean_dec_ref(v_rupHints_155_);
v___x_186_ = lean_unbox(v_snd_167_);
lean_dec(v_snd_167_);
return v___x_186_;
}
}
else
{
uint8_t v___x_187_; 
lean_dec(v_snd_167_);
v___x_187_ = lean_unbox(v_snd_169_);
if (v___x_187_ == 0)
{
uint8_t v___x_188_; 
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_rupHints_160_);
lean_dec_ref(v_ratHints_156_);
lean_dec_ref(v_rupHints_155_);
v___x_188_ = lean_unbox(v_snd_169_);
lean_dec(v_snd_169_);
return v___x_188_;
}
else
{
lean_dec(v_snd_169_);
goto v___jp_175_;
}
}
v___jp_175_:
{
lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_176_ = lean_array_get_size(v_rupHints_155_);
v___x_177_ = lean_array_get_size(v_rupHints_160_);
v___x_178_ = lean_nat_dec_eq(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_rupHints_160_);
lean_dec_ref(v_ratHints_156_);
lean_dec_ref(v_rupHints_155_);
return v___x_178_;
}
else
{
uint8_t v___x_179_; 
v___x_179_ = l_Array_isEqvAux___redArg(v_rupHints_155_, v_rupHints_160_, v___f_173_, v___x_176_);
lean_dec_ref(v_rupHints_160_);
lean_dec_ref(v_rupHints_155_);
if (v___x_179_ == 0)
{
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_ratHints_156_);
return v___x_179_;
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; 
v___x_180_ = lean_array_get_size(v_ratHints_156_);
v___x_181_ = lean_array_get_size(v_ratHints_161_);
v___x_182_ = lean_nat_dec_eq(v___x_180_, v___x_181_);
if (v___x_182_ == 0)
{
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_ratHints_156_);
return v___x_182_;
}
else
{
uint8_t v___x_183_; 
v___x_183_ = l_Array_isEqvAux___redArg(v_ratHints_156_, v_ratHints_161_, v___f_174_, v___x_180_);
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_ratHints_156_);
return v___x_183_;
}
}
}
}
}
}
}
}
else
{
uint8_t v___x_189_; 
lean_dec_ref(v_x_123_);
lean_dec_ref(v_x_124_);
lean_dec_ref(v_inst_122_);
lean_dec_ref(v_inst_121_);
v___x_189_ = 0;
return v___x_189_;
}
}
default: 
{
lean_dec_ref(v_inst_122_);
lean_dec_ref(v_inst_121_);
if (lean_obj_tag(v_x_124_) == 3)
{
lean_object* v_ids_190_; lean_object* v_ids_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_ids_190_ = lean_ctor_get(v_x_123_, 0);
lean_inc_ref(v_ids_190_);
lean_dec_ref(v_x_123_);
v_ids_191_ = lean_ctor_get(v_x_124_, 0);
lean_inc_ref(v_ids_191_);
lean_dec_ref(v_x_124_);
v___x_192_ = lean_array_get_size(v_ids_190_);
v___x_193_ = lean_array_get_size(v_ids_191_);
v___x_194_ = lean_nat_dec_eq(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_dec_ref(v_ids_191_);
lean_dec_ref(v_ids_190_);
return v___x_194_;
}
else
{
lean_object* v___f_195_; uint8_t v___x_196_; 
v___f_195_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0));
v___x_196_ = l_Array_isEqvAux___redArg(v_ids_190_, v_ids_191_, v___f_195_, v___x_192_);
lean_dec_ref(v_ids_191_);
lean_dec_ref(v_ids_190_);
return v___x_196_;
}
}
else
{
uint8_t v___x_197_; 
lean_dec_ref(v_x_123_);
lean_dec_ref(v_x_124_);
v___x_197_ = 0;
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___boxed(lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(v_inst_198_, v_inst_199_, v_x_200_, v_x_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq(lean_object* v_00_u03b2_204_, lean_object* v_00_u03b1_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
uint8_t v___x_210_; 
v___x_210_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(v_inst_206_, v_inst_207_, v_x_208_, v_x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed(lean_object* v_00_u03b2_211_, lean_object* v_00_u03b1_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
uint8_t v_res_217_; lean_object* v_r_218_; 
v_res_217_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq(v_00_u03b2_211_, v_00_u03b1_212_, v_inst_213_, v_inst_214_, v_x_215_, v_x_216_);
v_r_218_ = lean_box(v_res_217_);
return v_r_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction___redArg(lean_object* v_inst_219_, lean_object* v_inst_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed), 6, 4);
lean_closure_set(v___x_221_, 0, lean_box(0));
lean_closure_set(v___x_221_, 1, lean_box(0));
lean_closure_set(v___x_221_, 2, v_inst_219_);
lean_closure_set(v___x_221_, 3, v_inst_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction(lean_object* v_00_u03b2_222_, lean_object* v_00_u03b1_223_, lean_object* v_inst_224_, lean_object* v_inst_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed), 6, 4);
lean_closure_set(v___x_226_, 0, lean_box(0));
lean_closure_set(v___x_226_, 1, lean_box(0));
lean_closure_set(v___x_226_, 2, v_inst_224_);
lean_closure_set(v___x_226_, 3, v_inst_225_);
return v___x_226_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = lean_unsigned_to_nat(2u);
v___x_235_ = lean_nat_to_int(v___x_234_);
return v___x_235_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = lean_unsigned_to_nat(1u);
v___x_237_ = lean_nat_to_int(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_x_268_, lean_object* v_prec_269_){
_start:
{
lean_object* v___f_270_; 
v___f_270_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0));
switch(lean_obj_tag(v_x_268_))
{
case 0:
{
lean_object* v_id_271_; lean_object* v_rupHints_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_296_; 
lean_dec_ref(v_inst_267_);
lean_dec_ref(v_inst_266_);
v_id_271_ = lean_ctor_get(v_x_268_, 0);
v_rupHints_272_ = lean_ctor_get(v_x_268_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_x_268_);
if (v_isSharedCheck_296_ == 0)
{
v___x_274_ = v_x_268_;
v_isShared_275_ = v_isSharedCheck_296_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_rupHints_272_);
lean_inc(v_id_271_);
lean_dec(v_x_268_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_296_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___y_277_; lean_object* v___x_292_; uint8_t v___x_293_; 
v___x_292_ = lean_unsigned_to_nat(1024u);
v___x_293_ = lean_nat_dec_le(v___x_292_, v_prec_269_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; 
v___x_294_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_277_ = v___x_294_;
goto v___jp_276_;
}
else
{
lean_object* v___x_295_; 
v___x_295_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_277_ = v___x_295_;
goto v___jp_276_;
}
v___jp_276_:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
v___x_278_ = lean_box(1);
v___x_279_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__3));
v___x_280_ = l_Nat_reprFast(v_id_271_);
v___x_281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
if (v_isShared_275_ == 0)
{
lean_ctor_set_tag(v___x_274_, 5);
lean_ctor_set(v___x_274_, 1, v___x_281_);
lean_ctor_set(v___x_274_, 0, v___x_279_);
v___x_283_ = v___x_274_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_279_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v___x_281_);
v___x_283_ = v_reuseFailAlloc_291_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_284_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_278_);
v___x_285_ = l_Array_repr___redArg(v___f_270_, v_rupHints_272_);
v___x_286_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_284_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
lean_inc(v___y_277_);
v___x_287_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_287_, 0, v___y_277_);
lean_ctor_set(v___x_287_, 1, v___x_286_);
v___x_288_ = 0;
v___x_289_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_289_, 0, v___x_287_);
lean_ctor_set_uint8(v___x_289_, sizeof(void*)*1, v___x_288_);
v___x_290_ = l_Repr_addAppParen(v___x_289_, v_prec_269_);
return v___x_290_;
}
}
}
}
case 1:
{
lean_object* v_id_297_; lean_object* v_c_298_; lean_object* v_rupHints_299_; lean_object* v___y_301_; lean_object* v___x_318_; uint8_t v___x_319_; 
lean_dec_ref(v_inst_267_);
v_id_297_ = lean_ctor_get(v_x_268_, 0);
lean_inc(v_id_297_);
v_c_298_ = lean_ctor_get(v_x_268_, 1);
lean_inc(v_c_298_);
v_rupHints_299_ = lean_ctor_get(v_x_268_, 2);
lean_inc_ref(v_rupHints_299_);
lean_dec_ref(v_x_268_);
v___x_318_ = lean_unsigned_to_nat(1024u);
v___x_319_ = lean_nat_dec_le(v___x_318_, v_prec_269_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
v___x_320_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_301_ = v___x_320_;
goto v___jp_300_;
}
else
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_301_ = v___x_321_;
goto v___jp_300_;
}
v___jp_300_:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_302_ = lean_box(1);
v___x_303_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__8));
v___x_304_ = l_Nat_reprFast(v_id_297_);
v___x_305_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
v___x_306_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_303_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_302_);
v___x_308_ = lean_unsigned_to_nat(1024u);
v___x_309_ = lean_apply_2(v_inst_266_, v_c_298_, v___x_308_);
v___x_310_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_310_, 0, v___x_307_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_302_);
v___x_312_ = l_Array_repr___redArg(v___f_270_, v_rupHints_299_);
v___x_313_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
lean_inc(v___y_301_);
v___x_314_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_314_, 0, v___y_301_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = 0;
v___x_316_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*1, v___x_315_);
v___x_317_ = l_Repr_addAppParen(v___x_316_, v_prec_269_);
return v___x_317_;
}
}
case 2:
{
lean_object* v_id_322_; lean_object* v_c_323_; lean_object* v_pivot_324_; lean_object* v_rupHints_325_; lean_object* v_ratHints_326_; lean_object* v___f_327_; lean_object* v___x_328_; lean_object* v___y_330_; lean_object* v___x_353_; uint8_t v___x_354_; 
v_id_322_ = lean_ctor_get(v_x_268_, 0);
lean_inc(v_id_322_);
v_c_323_ = lean_ctor_get(v_x_268_, 1);
lean_inc(v_c_323_);
v_pivot_324_ = lean_ctor_get(v_x_268_, 2);
lean_inc_ref(v_pivot_324_);
v_rupHints_325_ = lean_ctor_get(v_x_268_, 3);
lean_inc_ref(v_rupHints_325_);
v_ratHints_326_ = lean_ctor_get(v_x_268_, 4);
lean_inc_ref(v_ratHints_326_);
lean_dec_ref(v_x_268_);
v___f_327_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__11));
v___x_328_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__13));
v___x_353_ = lean_unsigned_to_nat(1024u);
v___x_354_ = lean_nat_dec_le(v___x_353_, v_prec_269_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; 
v___x_355_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_330_ = v___x_355_;
goto v___jp_329_;
}
else
{
lean_object* v___x_356_; 
v___x_356_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_330_ = v___x_356_;
goto v___jp_329_;
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_331_ = lean_box(1);
v___x_332_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__16));
v___x_333_ = l_Nat_reprFast(v_id_322_);
v___x_334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
v___x_335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_332_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
v___x_336_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_331_);
v___x_337_ = lean_unsigned_to_nat(1024u);
v___x_338_ = lean_apply_2(v_inst_266_, v_c_323_, v___x_337_);
v___x_339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_336_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_331_);
v___x_341_ = l_Prod_repr___redArg(v_inst_267_, v___f_327_, v_pivot_324_);
v___x_342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_331_);
v___x_344_ = l_Array_repr___redArg(v___f_270_, v_rupHints_325_);
v___x_345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_331_);
v___x_347_ = l_Array_repr___redArg(v___x_328_, v_ratHints_326_);
v___x_348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
lean_inc(v___y_330_);
v___x_349_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_349_, 0, v___y_330_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = 0;
v___x_351_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_351_, 0, v___x_349_);
lean_ctor_set_uint8(v___x_351_, sizeof(void*)*1, v___x_350_);
v___x_352_ = l_Repr_addAppParen(v___x_351_, v_prec_269_);
return v___x_352_;
}
}
default: 
{
lean_object* v_ids_357_; lean_object* v___y_359_; lean_object* v___x_367_; uint8_t v___x_368_; 
lean_dec_ref(v_inst_267_);
lean_dec_ref(v_inst_266_);
v_ids_357_ = lean_ctor_get(v_x_268_, 0);
lean_inc_ref(v_ids_357_);
lean_dec_ref(v_x_268_);
v___x_367_ = lean_unsigned_to_nat(1024u);
v___x_368_ = lean_nat_dec_le(v___x_367_, v_prec_269_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; 
v___x_369_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_359_ = v___x_369_;
goto v___jp_358_;
}
else
{
lean_object* v___x_370_; 
v___x_370_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_359_ = v___x_370_;
goto v___jp_358_;
}
v___jp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; uint8_t v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_360_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__19));
v___x_361_ = l_Array_repr___redArg(v___f_270_, v_ids_357_);
v___x_362_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_360_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
lean_inc(v___y_359_);
v___x_363_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_363_, 0, v___y_359_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = 0;
v___x_365_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*1, v___x_364_);
v___x_366_ = l_Repr_addAppParen(v___x_365_, v_prec_269_);
return v___x_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___boxed(lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_x_373_, lean_object* v_prec_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(v_inst_371_, v_inst_372_, v_x_373_, v_prec_374_);
lean_dec(v_prec_374_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr(lean_object* v_00_u03b2_376_, lean_object* v_00_u03b1_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_x_380_, lean_object* v_prec_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(v_inst_378_, v_inst_379_, v_x_380_, v_prec_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed(lean_object* v_00_u03b2_383_, lean_object* v_00_u03b1_384_, lean_object* v_inst_385_, lean_object* v_inst_386_, lean_object* v_x_387_, lean_object* v_prec_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr(v_00_u03b2_383_, v_00_u03b1_384_, v_inst_385_, v_inst_386_, v_x_387_, v_prec_388_);
lean_dec(v_prec_388_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction___redArg(lean_object* v_inst_390_, lean_object* v_inst_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed), 6, 4);
lean_closure_set(v___x_392_, 0, lean_box(0));
lean_closure_set(v___x_392_, 1, lean_box(0));
lean_closure_set(v___x_392_, 2, v_inst_390_);
lean_closure_set(v___x_392_, 3, v_inst_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction(lean_object* v_00_u03b2_393_, lean_object* v_00_u03b1_394_, lean_object* v_inst_395_, lean_object* v_inst_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed), 6, 4);
lean_closure_set(v___x_397_, 0, lean_box(0));
lean_closure_set(v___x_397_, 1, lean_box(0));
lean_closure_set(v___x_397_, 2, v_inst_395_);
lean_closure_set(v___x_397_, 3, v_inst_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg(lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_x_422_){
_start:
{
lean_object* v___f_423_; 
v___f_423_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0));
switch(lean_obj_tag(v_x_422_))
{
case 0:
{
lean_object* v_id_424_; lean_object* v_rupHints_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec_ref(v_inst_421_);
lean_dec_ref(v_inst_420_);
v_id_424_ = lean_ctor_get(v_x_422_, 0);
lean_inc(v_id_424_);
v_rupHints_425_ = lean_ctor_get(v_x_422_, 1);
lean_inc_ref(v_rupHints_425_);
lean_dec_ref(v_x_422_);
v___x_426_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__1));
v___x_427_ = l_Nat_reprFast(v_id_424_);
v___x_428_ = lean_string_append(v___x_426_, v___x_427_);
lean_dec_ref(v___x_427_);
v___x_429_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2));
v___x_430_ = lean_string_append(v___x_428_, v___x_429_);
v___x_431_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_432_ = lean_array_to_list(v_rupHints_425_);
v___x_433_ = l_List_toString___redArg(v___f_423_, v___x_432_);
v___x_434_ = lean_string_append(v___x_431_, v___x_433_);
lean_dec_ref(v___x_433_);
v___x_435_ = lean_string_append(v___x_430_, v___x_434_);
lean_dec_ref(v___x_434_);
v___x_436_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4));
v___x_437_ = lean_string_append(v___x_435_, v___x_436_);
return v___x_437_;
}
case 1:
{
lean_object* v_id_438_; lean_object* v_c_439_; lean_object* v_rupHints_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec_ref(v_inst_421_);
v_id_438_ = lean_ctor_get(v_x_422_, 0);
lean_inc(v_id_438_);
v_c_439_ = lean_ctor_get(v_x_422_, 1);
lean_inc(v_c_439_);
v_rupHints_440_ = lean_ctor_get(v_x_422_, 2);
lean_inc_ref(v_rupHints_440_);
lean_dec_ref(v_x_422_);
v___x_441_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__5));
v___x_442_ = lean_apply_1(v_inst_420_, v_c_439_);
v___x_443_ = lean_string_append(v___x_441_, v___x_442_);
lean_dec_ref(v___x_442_);
v___x_444_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__6));
v___x_445_ = lean_string_append(v___x_443_, v___x_444_);
v___x_446_ = l_Nat_reprFast(v_id_438_);
v___x_447_ = lean_string_append(v___x_445_, v___x_446_);
lean_dec_ref(v___x_446_);
v___x_448_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2));
v___x_449_ = lean_string_append(v___x_447_, v___x_448_);
v___x_450_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_451_ = lean_array_to_list(v_rupHints_440_);
v___x_452_ = l_List_toString___redArg(v___f_423_, v___x_451_);
v___x_453_ = lean_string_append(v___x_450_, v___x_452_);
lean_dec_ref(v___x_452_);
v___x_454_ = lean_string_append(v___x_449_, v___x_453_);
lean_dec_ref(v___x_453_);
v___x_455_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4));
v___x_456_ = lean_string_append(v___x_454_, v___x_455_);
return v___x_456_;
}
case 2:
{
lean_object* v_pivot_457_; lean_object* v_id_458_; lean_object* v_c_459_; lean_object* v_rupHints_460_; lean_object* v_ratHints_461_; lean_object* v_fst_462_; lean_object* v_snd_463_; lean_object* v___f_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___y_480_; uint8_t v___x_499_; 
v_pivot_457_ = lean_ctor_get(v_x_422_, 2);
lean_inc_ref(v_pivot_457_);
v_id_458_ = lean_ctor_get(v_x_422_, 0);
lean_inc(v_id_458_);
v_c_459_ = lean_ctor_get(v_x_422_, 1);
lean_inc(v_c_459_);
v_rupHints_460_ = lean_ctor_get(v_x_422_, 3);
lean_inc_ref(v_rupHints_460_);
v_ratHints_461_ = lean_ctor_get(v_x_422_, 4);
lean_inc_ref(v_ratHints_461_);
lean_dec_ref(v_x_422_);
v_fst_462_ = lean_ctor_get(v_pivot_457_, 0);
lean_inc(v_fst_462_);
v_snd_463_ = lean_ctor_get(v_pivot_457_, 1);
lean_inc(v_snd_463_);
lean_dec_ref(v_pivot_457_);
v___f_464_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__8));
v___x_465_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__9));
v___x_466_ = lean_apply_1(v_inst_420_, v_c_459_);
v___x_467_ = lean_string_append(v___x_465_, v___x_466_);
lean_dec_ref(v___x_466_);
v___x_468_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__10));
v___x_469_ = lean_string_append(v___x_467_, v___x_468_);
v___x_470_ = l_Nat_reprFast(v_id_458_);
v___x_471_ = lean_string_append(v___x_469_, v___x_470_);
lean_dec_ref(v___x_470_);
v___x_472_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__11));
v___x_473_ = lean_string_append(v___x_471_, v___x_472_);
v___x_474_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__12));
v___x_475_ = lean_apply_1(v_inst_421_, v_fst_462_);
v___x_476_ = lean_string_append(v___x_474_, v___x_475_);
lean_dec_ref(v___x_475_);
v___x_477_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__13));
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
v___x_499_ = lean_unbox(v_snd_463_);
lean_dec(v_snd_463_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
v___x_500_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__16));
v___y_480_ = v___x_500_;
goto v___jp_479_;
}
else
{
lean_object* v___x_501_; 
v___x_501_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__17));
v___y_480_ = v___x_501_;
goto v___jp_479_;
}
v___jp_479_:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_481_ = lean_string_append(v___x_478_, v___y_480_);
v___x_482_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4));
v___x_483_ = lean_string_append(v___x_481_, v___x_482_);
v___x_484_ = lean_string_append(v___x_473_, v___x_483_);
lean_dec_ref(v___x_483_);
v___x_485_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__14));
v___x_486_ = lean_string_append(v___x_484_, v___x_485_);
v___x_487_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_488_ = lean_array_to_list(v_rupHints_460_);
v___x_489_ = l_List_toString___redArg(v___f_423_, v___x_488_);
v___x_490_ = lean_string_append(v___x_487_, v___x_489_);
lean_dec_ref(v___x_489_);
v___x_491_ = lean_string_append(v___x_486_, v___x_490_);
lean_dec_ref(v___x_490_);
v___x_492_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__15));
v___x_493_ = lean_string_append(v___x_491_, v___x_492_);
v___x_494_ = lean_array_to_list(v_ratHints_461_);
v___x_495_ = l_List_toString___redArg(v___f_464_, v___x_494_);
v___x_496_ = lean_string_append(v___x_487_, v___x_495_);
lean_dec_ref(v___x_495_);
v___x_497_ = lean_string_append(v___x_493_, v___x_496_);
lean_dec_ref(v___x_496_);
v___x_498_ = lean_string_append(v___x_497_, v___x_482_);
return v___x_498_;
}
}
default: 
{
lean_object* v_ids_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec_ref(v_inst_421_);
lean_dec_ref(v_inst_420_);
v_ids_502_ = lean_ctor_get(v_x_422_, 0);
lean_inc_ref(v_ids_502_);
lean_dec_ref(v_x_422_);
v___x_503_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__18));
v___x_504_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_505_ = lean_array_to_list(v_ids_502_);
v___x_506_ = l_List_toString___redArg(v___f_423_, v___x_505_);
v___x_507_ = lean_string_append(v___x_504_, v___x_506_);
lean_dec_ref(v___x_506_);
v___x_508_ = lean_string_append(v___x_503_, v___x_507_);
lean_dec_ref(v___x_507_);
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString(lean_object* v_00_u03b2_509_, lean_object* v_00_u03b1_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_x_513_){
_start:
{
lean_object* v___x_514_; 
v___x_514_ = l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg(v_inst_511_, v_inst_512_, v_x_513_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instToStringAction___redArg(lean_object* v_inst_515_, lean_object* v_inst_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Action_toString), 5, 4);
lean_closure_set(v___x_517_, 0, lean_box(0));
lean_closure_set(v___x_517_, 1, lean_box(0));
lean_closure_set(v___x_517_, 2, v_inst_515_);
lean_closure_set(v___x_517_, 3, v_inst_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instToStringAction(lean_object* v_00_u03b2_518_, lean_object* v_00_u03b1_519_, lean_object* v_inst_520_, lean_object* v_inst_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Action_toString), 5, 4);
lean_closure_set(v___x_522_, 0, lean_box(0));
lean_closure_set(v___x_522_, 1, lean_box(0));
lean_closure_set(v___x_522_, 2, v_inst_520_);
lean_closure_set(v___x_522_, 3, v_inst_521_);
return v___x_522_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_CNF(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin);
}
#ifdef __cplusplus
}
#endif
