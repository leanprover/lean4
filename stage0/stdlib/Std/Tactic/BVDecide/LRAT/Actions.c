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
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___closed__0_value;
static const lean_ctor_object l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___closed__0_value)}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___closed__1 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg();
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___redArg();
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___redArg___boxed(lean_object*);
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
lean_dec_ref_known(v_t_16_, 2);
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
lean_dec_ref_known(v_t_16_, 3);
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
lean_dec_ref_known(v_t_16_, 5);
v___x_30_ = lean_apply_5(v_k_17_, v_id_25_, v_c_26_, v_pivot_27_, v_rupHints_28_, v_ratHints_29_);
return v___x_30_;
}
default: 
{
lean_object* v_ids_31_; lean_object* v___x_32_; 
v_ids_31_ = lean_ctor_get(v_t_16_, 0);
lean_inc_ref(v_ids_31_);
lean_dec_ref_known(v_t_16_, 1);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg(){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___closed__1));
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___boxed(lean_object* v___dummy_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg();
return v_res_97_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0(void){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg();
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(lean_object* v_00_u03b2_99_, lean_object* v_00_u03b1_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0, &l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___redArg(){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0, &l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___redArg___boxed(lean_object* v___dummy_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___redArg();
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction(lean_object* v_a_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0, &l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0);
return v___x_108_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0(lean_object* v___f_109_, lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
lean_object* v_fst_112_; lean_object* v_snd_113_; lean_object* v_fst_114_; lean_object* v_snd_115_; uint8_t v___x_116_; 
v_fst_112_ = lean_ctor_get(v_x_110_, 0);
v_snd_113_ = lean_ctor_get(v_x_110_, 1);
v_fst_114_ = lean_ctor_get(v_x_111_, 0);
v_snd_115_ = lean_ctor_get(v_x_111_, 1);
v___x_116_ = lean_nat_dec_eq(v_fst_112_, v_fst_114_);
if (v___x_116_ == 0)
{
lean_dec_ref(v___f_109_);
return v___x_116_;
}
else
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = lean_array_get_size(v_snd_113_);
v___x_118_ = lean_array_get_size(v_snd_115_);
v___x_119_ = lean_nat_dec_eq(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_dec_ref(v___f_109_);
return v___x_119_;
}
else
{
uint8_t v___x_120_; 
v___x_120_ = l_Array_isEqvAux___redArg(v_snd_113_, v_snd_115_, v___f_109_, v___x_117_);
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0___boxed(lean_object* v___f_121_, lean_object* v_x_122_, lean_object* v_x_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0(v___f_121_, v_x_122_, v_x_123_);
lean_dec_ref(v_x_123_);
lean_dec_ref(v_x_122_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
switch(lean_obj_tag(v_x_131_))
{
case 0:
{
lean_dec_ref(v_inst_130_);
lean_dec_ref(v_inst_129_);
if (lean_obj_tag(v_x_132_) == 0)
{
lean_object* v_id_133_; lean_object* v_rupHints_134_; lean_object* v_id_135_; lean_object* v_rupHints_136_; uint8_t v___x_137_; 
v_id_133_ = lean_ctor_get(v_x_131_, 0);
lean_inc(v_id_133_);
v_rupHints_134_ = lean_ctor_get(v_x_131_, 1);
lean_inc_ref(v_rupHints_134_);
lean_dec_ref_known(v_x_131_, 2);
v_id_135_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_id_135_);
v_rupHints_136_ = lean_ctor_get(v_x_132_, 1);
lean_inc_ref(v_rupHints_136_);
lean_dec_ref_known(v_x_132_, 2);
v___x_137_ = lean_nat_dec_eq(v_id_133_, v_id_135_);
lean_dec(v_id_135_);
lean_dec(v_id_133_);
if (v___x_137_ == 0)
{
lean_dec_ref(v_rupHints_136_);
lean_dec_ref(v_rupHints_134_);
return v___x_137_;
}
else
{
lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_138_ = lean_array_get_size(v_rupHints_134_);
v___x_139_ = lean_array_get_size(v_rupHints_136_);
v___x_140_ = lean_nat_dec_eq(v___x_138_, v___x_139_);
if (v___x_140_ == 0)
{
lean_dec_ref(v_rupHints_136_);
lean_dec_ref(v_rupHints_134_);
return v___x_140_;
}
else
{
lean_object* v___f_141_; uint8_t v___x_142_; 
v___f_141_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0));
v___x_142_ = l_Array_isEqvAux___redArg(v_rupHints_134_, v_rupHints_136_, v___f_141_, v___x_138_);
lean_dec_ref(v_rupHints_136_);
lean_dec_ref(v_rupHints_134_);
return v___x_142_;
}
}
}
else
{
uint8_t v___x_143_; 
lean_dec_ref_known(v_x_131_, 2);
lean_dec_ref(v_x_132_);
v___x_143_ = 0;
return v___x_143_;
}
}
case 1:
{
lean_dec_ref(v_inst_130_);
if (lean_obj_tag(v_x_132_) == 1)
{
lean_object* v_id_144_; lean_object* v_c_145_; lean_object* v_rupHints_146_; lean_object* v_id_147_; lean_object* v_c_148_; lean_object* v_rupHints_149_; uint8_t v___x_150_; 
v_id_144_ = lean_ctor_get(v_x_131_, 0);
lean_inc(v_id_144_);
v_c_145_ = lean_ctor_get(v_x_131_, 1);
lean_inc(v_c_145_);
v_rupHints_146_ = lean_ctor_get(v_x_131_, 2);
lean_inc_ref(v_rupHints_146_);
lean_dec_ref_known(v_x_131_, 3);
v_id_147_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_id_147_);
v_c_148_ = lean_ctor_get(v_x_132_, 1);
lean_inc(v_c_148_);
v_rupHints_149_ = lean_ctor_get(v_x_132_, 2);
lean_inc_ref(v_rupHints_149_);
lean_dec_ref_known(v_x_132_, 3);
v___x_150_ = lean_nat_dec_eq(v_id_144_, v_id_147_);
lean_dec(v_id_147_);
lean_dec(v_id_144_);
if (v___x_150_ == 0)
{
lean_dec_ref(v_rupHints_149_);
lean_dec(v_c_148_);
lean_dec_ref(v_rupHints_146_);
lean_dec(v_c_145_);
lean_dec_ref(v_inst_129_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = lean_apply_2(v_inst_129_, v_c_145_, v_c_148_);
v___x_152_ = lean_unbox(v___x_151_);
if (v___x_152_ == 0)
{
uint8_t v___x_153_; 
lean_dec_ref(v_rupHints_149_);
lean_dec_ref(v_rupHints_146_);
v___x_153_ = lean_unbox(v___x_151_);
return v___x_153_;
}
else
{
lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_154_ = lean_array_get_size(v_rupHints_146_);
v___x_155_ = lean_array_get_size(v_rupHints_149_);
v___x_156_ = lean_nat_dec_eq(v___x_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_dec_ref(v_rupHints_149_);
lean_dec_ref(v_rupHints_146_);
return v___x_156_;
}
else
{
lean_object* v___f_157_; uint8_t v___x_158_; 
v___f_157_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0));
v___x_158_ = l_Array_isEqvAux___redArg(v_rupHints_146_, v_rupHints_149_, v___f_157_, v___x_154_);
lean_dec_ref(v_rupHints_149_);
lean_dec_ref(v_rupHints_146_);
return v___x_158_;
}
}
}
}
else
{
uint8_t v___x_159_; 
lean_dec_ref_known(v_x_131_, 3);
lean_dec_ref(v_x_132_);
lean_dec_ref(v_inst_129_);
v___x_159_ = 0;
return v___x_159_;
}
}
case 2:
{
if (lean_obj_tag(v_x_132_) == 2)
{
lean_object* v_id_160_; lean_object* v_c_161_; lean_object* v_pivot_162_; lean_object* v_rupHints_163_; lean_object* v_ratHints_164_; lean_object* v_id_165_; lean_object* v_c_166_; lean_object* v_pivot_167_; lean_object* v_rupHints_168_; lean_object* v_ratHints_169_; uint8_t v___x_170_; 
v_id_160_ = lean_ctor_get(v_x_131_, 0);
lean_inc(v_id_160_);
v_c_161_ = lean_ctor_get(v_x_131_, 1);
lean_inc(v_c_161_);
v_pivot_162_ = lean_ctor_get(v_x_131_, 2);
lean_inc_ref(v_pivot_162_);
v_rupHints_163_ = lean_ctor_get(v_x_131_, 3);
lean_inc_ref(v_rupHints_163_);
v_ratHints_164_ = lean_ctor_get(v_x_131_, 4);
lean_inc_ref(v_ratHints_164_);
lean_dec_ref_known(v_x_131_, 5);
v_id_165_ = lean_ctor_get(v_x_132_, 0);
lean_inc(v_id_165_);
v_c_166_ = lean_ctor_get(v_x_132_, 1);
lean_inc(v_c_166_);
v_pivot_167_ = lean_ctor_get(v_x_132_, 2);
lean_inc_ref(v_pivot_167_);
v_rupHints_168_ = lean_ctor_get(v_x_132_, 3);
lean_inc_ref(v_rupHints_168_);
v_ratHints_169_ = lean_ctor_get(v_x_132_, 4);
lean_inc_ref(v_ratHints_169_);
lean_dec_ref_known(v_x_132_, 5);
v___x_170_ = lean_nat_dec_eq(v_id_160_, v_id_165_);
lean_dec(v_id_165_);
lean_dec(v_id_160_);
if (v___x_170_ == 0)
{
lean_dec_ref(v_ratHints_169_);
lean_dec_ref(v_rupHints_168_);
lean_dec_ref(v_pivot_167_);
lean_dec(v_c_166_);
lean_dec_ref(v_ratHints_164_);
lean_dec_ref(v_rupHints_163_);
lean_dec_ref(v_pivot_162_);
lean_dec(v_c_161_);
lean_dec_ref(v_inst_130_);
lean_dec_ref(v_inst_129_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_apply_2(v_inst_129_, v_c_161_, v_c_166_);
v___x_172_ = lean_unbox(v___x_171_);
if (v___x_172_ == 0)
{
uint8_t v___x_173_; 
lean_dec_ref(v_ratHints_169_);
lean_dec_ref(v_rupHints_168_);
lean_dec_ref(v_pivot_167_);
lean_dec_ref(v_ratHints_164_);
lean_dec_ref(v_rupHints_163_);
lean_dec_ref(v_pivot_162_);
lean_dec_ref(v_inst_130_);
v___x_173_ = lean_unbox(v___x_171_);
return v___x_173_;
}
else
{
lean_object* v_fst_174_; lean_object* v_snd_175_; lean_object* v_fst_176_; lean_object* v_snd_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_fst_174_ = lean_ctor_get(v_pivot_162_, 0);
lean_inc(v_fst_174_);
v_snd_175_ = lean_ctor_get(v_pivot_162_, 1);
lean_inc(v_snd_175_);
lean_dec_ref(v_pivot_162_);
v_fst_176_ = lean_ctor_get(v_pivot_167_, 0);
lean_inc(v_fst_176_);
v_snd_177_ = lean_ctor_get(v_pivot_167_, 1);
lean_inc(v_snd_177_);
lean_dec_ref(v_pivot_167_);
v___x_178_ = lean_apply_2(v_inst_130_, v_fst_174_, v_fst_176_);
v___x_179_ = lean_unbox(v___x_178_);
if (v___x_179_ == 0)
{
uint8_t v___x_180_; 
lean_dec(v_snd_177_);
lean_dec(v_snd_175_);
lean_dec_ref(v_ratHints_169_);
lean_dec_ref(v_rupHints_168_);
lean_dec_ref(v_ratHints_164_);
lean_dec_ref(v_rupHints_163_);
v___x_180_ = lean_unbox(v___x_178_);
return v___x_180_;
}
else
{
lean_object* v___f_181_; lean_object* v___f_182_; uint8_t v___x_192_; 
v___f_181_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0));
v___f_182_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__1));
v___x_192_ = lean_unbox(v_snd_177_);
if (v___x_192_ == 0)
{
uint8_t v___x_193_; 
v___x_193_ = lean_unbox(v_snd_175_);
lean_dec(v_snd_175_);
if (v___x_193_ == 0)
{
lean_dec(v_snd_177_);
goto v___jp_183_;
}
else
{
uint8_t v___x_194_; 
lean_dec_ref(v_ratHints_169_);
lean_dec_ref(v_rupHints_168_);
lean_dec_ref(v_ratHints_164_);
lean_dec_ref(v_rupHints_163_);
v___x_194_ = lean_unbox(v_snd_177_);
lean_dec(v_snd_177_);
return v___x_194_;
}
}
else
{
uint8_t v___x_195_; 
lean_dec(v_snd_177_);
v___x_195_ = lean_unbox(v_snd_175_);
if (v___x_195_ == 0)
{
uint8_t v___x_196_; 
lean_dec_ref(v_ratHints_169_);
lean_dec_ref(v_rupHints_168_);
lean_dec_ref(v_ratHints_164_);
lean_dec_ref(v_rupHints_163_);
v___x_196_ = lean_unbox(v_snd_175_);
lean_dec(v_snd_175_);
return v___x_196_;
}
else
{
lean_dec(v_snd_175_);
goto v___jp_183_;
}
}
v___jp_183_:
{
lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_184_ = lean_array_get_size(v_rupHints_163_);
v___x_185_ = lean_array_get_size(v_rupHints_168_);
v___x_186_ = lean_nat_dec_eq(v___x_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_dec_ref(v_ratHints_169_);
lean_dec_ref(v_rupHints_168_);
lean_dec_ref(v_ratHints_164_);
lean_dec_ref(v_rupHints_163_);
return v___x_186_;
}
else
{
uint8_t v___x_187_; 
v___x_187_ = l_Array_isEqvAux___redArg(v_rupHints_163_, v_rupHints_168_, v___f_181_, v___x_184_);
lean_dec_ref(v_rupHints_168_);
lean_dec_ref(v_rupHints_163_);
if (v___x_187_ == 0)
{
lean_dec_ref(v_ratHints_169_);
lean_dec_ref(v_ratHints_164_);
return v___x_187_;
}
else
{
lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_188_ = lean_array_get_size(v_ratHints_164_);
v___x_189_ = lean_array_get_size(v_ratHints_169_);
v___x_190_ = lean_nat_dec_eq(v___x_188_, v___x_189_);
if (v___x_190_ == 0)
{
lean_dec_ref(v_ratHints_169_);
lean_dec_ref(v_ratHints_164_);
return v___x_190_;
}
else
{
uint8_t v___x_191_; 
v___x_191_ = l_Array_isEqvAux___redArg(v_ratHints_164_, v_ratHints_169_, v___f_182_, v___x_188_);
lean_dec_ref(v_ratHints_169_);
lean_dec_ref(v_ratHints_164_);
return v___x_191_;
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
uint8_t v___x_197_; 
lean_dec_ref_known(v_x_131_, 5);
lean_dec_ref(v_x_132_);
lean_dec_ref(v_inst_130_);
lean_dec_ref(v_inst_129_);
v___x_197_ = 0;
return v___x_197_;
}
}
default: 
{
lean_dec_ref(v_inst_130_);
lean_dec_ref(v_inst_129_);
if (lean_obj_tag(v_x_132_) == 3)
{
lean_object* v_ids_198_; lean_object* v_ids_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_ids_198_ = lean_ctor_get(v_x_131_, 0);
lean_inc_ref(v_ids_198_);
lean_dec_ref_known(v_x_131_, 1);
v_ids_199_ = lean_ctor_get(v_x_132_, 0);
lean_inc_ref(v_ids_199_);
lean_dec_ref_known(v_x_132_, 1);
v___x_200_ = lean_array_get_size(v_ids_198_);
v___x_201_ = lean_array_get_size(v_ids_199_);
v___x_202_ = lean_nat_dec_eq(v___x_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_dec_ref(v_ids_199_);
lean_dec_ref(v_ids_198_);
return v___x_202_;
}
else
{
lean_object* v___f_203_; uint8_t v___x_204_; 
v___f_203_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0));
v___x_204_ = l_Array_isEqvAux___redArg(v_ids_198_, v_ids_199_, v___f_203_, v___x_200_);
lean_dec_ref(v_ids_199_);
lean_dec_ref(v_ids_198_);
return v___x_204_;
}
}
else
{
uint8_t v___x_205_; 
lean_dec_ref_known(v_x_131_, 1);
lean_dec_ref(v_x_132_);
v___x_205_ = 0;
return v___x_205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___boxed(lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
uint8_t v_res_210_; lean_object* v_r_211_; 
v_res_210_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(v_inst_206_, v_inst_207_, v_x_208_, v_x_209_);
v_r_211_ = lean_box(v_res_210_);
return v_r_211_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq(lean_object* v_00_u03b2_212_, lean_object* v_00_u03b1_213_, lean_object* v_inst_214_, lean_object* v_inst_215_, lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
uint8_t v___x_218_; 
v___x_218_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(v_inst_214_, v_inst_215_, v_x_216_, v_x_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed(lean_object* v_00_u03b2_219_, lean_object* v_00_u03b1_220_, lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq(v_00_u03b2_219_, v_00_u03b1_220_, v_inst_221_, v_inst_222_, v_x_223_, v_x_224_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction___redArg(lean_object* v_inst_227_, lean_object* v_inst_228_){
_start:
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed), 6, 4);
lean_closure_set(v___x_229_, 0, lean_box(0));
lean_closure_set(v___x_229_, 1, lean_box(0));
lean_closure_set(v___x_229_, 2, v_inst_227_);
lean_closure_set(v___x_229_, 3, v_inst_228_);
return v___x_229_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction(lean_object* v_00_u03b2_230_, lean_object* v_00_u03b1_231_, lean_object* v_inst_232_, lean_object* v_inst_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed), 6, 4);
lean_closure_set(v___x_234_, 0, lean_box(0));
lean_closure_set(v___x_234_, 1, lean_box(0));
lean_closure_set(v___x_234_, 2, v_inst_232_);
lean_closure_set(v___x_234_, 3, v_inst_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_unsigned_to_nat(2u);
v___x_243_ = lean_nat_to_int(v___x_242_);
return v___x_243_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = lean_nat_to_int(v___x_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_x_276_, lean_object* v_prec_277_){
_start:
{
lean_object* v___f_278_; 
v___f_278_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0));
switch(lean_obj_tag(v_x_276_))
{
case 0:
{
lean_object* v_id_279_; lean_object* v_rupHints_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_304_; 
lean_dec_ref(v_inst_275_);
lean_dec_ref(v_inst_274_);
v_id_279_ = lean_ctor_get(v_x_276_, 0);
v_rupHints_280_ = lean_ctor_get(v_x_276_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_x_276_);
if (v_isSharedCheck_304_ == 0)
{
v___x_282_ = v_x_276_;
v_isShared_283_ = v_isSharedCheck_304_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_rupHints_280_);
lean_inc(v_id_279_);
lean_dec(v_x_276_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_304_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v___y_285_; lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(1024u);
v___x_301_ = lean_nat_dec_le(v___x_300_, v_prec_277_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_285_ = v___x_302_;
goto v___jp_284_;
}
else
{
lean_object* v___x_303_; 
v___x_303_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_285_ = v___x_303_;
goto v___jp_284_;
}
v___jp_284_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_286_ = lean_box(1);
v___x_287_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__3));
v___x_288_ = l_Nat_reprFast(v_id_279_);
v___x_289_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
if (v_isShared_283_ == 0)
{
lean_ctor_set_tag(v___x_282_, 5);
lean_ctor_set(v___x_282_, 1, v___x_289_);
lean_ctor_set(v___x_282_, 0, v___x_287_);
v___x_291_ = v___x_282_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v___x_289_);
v___x_291_ = v_reuseFailAlloc_299_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_292_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
lean_ctor_set(v___x_292_, 1, v___x_286_);
v___x_293_ = l_Array_repr___redArg(v___f_278_, v_rupHints_280_);
v___x_294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
lean_inc(v___y_285_);
v___x_295_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_295_, 0, v___y_285_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = 0;
v___x_297_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_297_, 0, v___x_295_);
lean_ctor_set_uint8(v___x_297_, sizeof(void*)*1, v___x_296_);
v___x_298_ = l_Repr_addAppParen(v___x_297_, v_prec_277_);
return v___x_298_;
}
}
}
}
case 1:
{
lean_object* v_id_305_; lean_object* v_c_306_; lean_object* v_rupHints_307_; lean_object* v___y_309_; lean_object* v___x_326_; uint8_t v___x_327_; 
lean_dec_ref(v_inst_275_);
v_id_305_ = lean_ctor_get(v_x_276_, 0);
lean_inc(v_id_305_);
v_c_306_ = lean_ctor_get(v_x_276_, 1);
lean_inc(v_c_306_);
v_rupHints_307_ = lean_ctor_get(v_x_276_, 2);
lean_inc_ref(v_rupHints_307_);
lean_dec_ref_known(v_x_276_, 3);
v___x_326_ = lean_unsigned_to_nat(1024u);
v___x_327_ = lean_nat_dec_le(v___x_326_, v_prec_277_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; 
v___x_328_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_309_ = v___x_328_;
goto v___jp_308_;
}
else
{
lean_object* v___x_329_; 
v___x_329_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_309_ = v___x_329_;
goto v___jp_308_;
}
v___jp_308_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_310_ = lean_box(1);
v___x_311_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__8));
v___x_312_ = l_Nat_reprFast(v_id_305_);
v___x_313_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
v___x_314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_311_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_310_);
v___x_316_ = lean_unsigned_to_nat(1024u);
v___x_317_ = lean_apply_2(v_inst_274_, v_c_306_, v___x_316_);
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_315_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_310_);
v___x_320_ = l_Array_repr___redArg(v___f_278_, v_rupHints_307_);
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
lean_inc(v___y_309_);
v___x_322_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_322_, 0, v___y_309_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = 0;
v___x_324_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*1, v___x_323_);
v___x_325_ = l_Repr_addAppParen(v___x_324_, v_prec_277_);
return v___x_325_;
}
}
case 2:
{
lean_object* v_id_330_; lean_object* v_c_331_; lean_object* v_pivot_332_; lean_object* v_rupHints_333_; lean_object* v_ratHints_334_; lean_object* v___f_335_; lean_object* v___x_336_; lean_object* v___y_338_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_id_330_ = lean_ctor_get(v_x_276_, 0);
lean_inc(v_id_330_);
v_c_331_ = lean_ctor_get(v_x_276_, 1);
lean_inc(v_c_331_);
v_pivot_332_ = lean_ctor_get(v_x_276_, 2);
lean_inc_ref(v_pivot_332_);
v_rupHints_333_ = lean_ctor_get(v_x_276_, 3);
lean_inc_ref(v_rupHints_333_);
v_ratHints_334_ = lean_ctor_get(v_x_276_, 4);
lean_inc_ref(v_ratHints_334_);
lean_dec_ref_known(v_x_276_, 5);
v___f_335_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__11));
v___x_336_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__13));
v___x_361_ = lean_unsigned_to_nat(1024u);
v___x_362_ = lean_nat_dec_le(v___x_361_, v_prec_277_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; 
v___x_363_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_338_ = v___x_363_;
goto v___jp_337_;
}
else
{
lean_object* v___x_364_; 
v___x_364_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_338_ = v___x_364_;
goto v___jp_337_;
}
v___jp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_339_ = lean_box(1);
v___x_340_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__16));
v___x_341_ = l_Nat_reprFast(v_id_330_);
v___x_342_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
v___x_343_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_340_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___x_339_);
v___x_345_ = lean_unsigned_to_nat(1024u);
v___x_346_ = lean_apply_2(v_inst_274_, v_c_331_, v___x_345_);
v___x_347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_344_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_339_);
v___x_349_ = l_Prod_repr___redArg(v_inst_275_, v___f_335_, v_pivot_332_);
v___x_350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_339_);
v___x_352_ = l_Array_repr___redArg(v___f_278_, v_rupHints_333_);
v___x_353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_339_);
v___x_355_ = l_Array_repr___redArg(v___x_336_, v_ratHints_334_);
v___x_356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
lean_inc(v___y_338_);
v___x_357_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_357_, 0, v___y_338_);
lean_ctor_set(v___x_357_, 1, v___x_356_);
v___x_358_ = 0;
v___x_359_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_359_, 0, v___x_357_);
lean_ctor_set_uint8(v___x_359_, sizeof(void*)*1, v___x_358_);
v___x_360_ = l_Repr_addAppParen(v___x_359_, v_prec_277_);
return v___x_360_;
}
}
default: 
{
lean_object* v_ids_365_; lean_object* v___y_367_; lean_object* v___x_375_; uint8_t v___x_376_; 
lean_dec_ref(v_inst_275_);
lean_dec_ref(v_inst_274_);
v_ids_365_ = lean_ctor_get(v_x_276_, 0);
lean_inc_ref(v_ids_365_);
lean_dec_ref_known(v_x_276_, 1);
v___x_375_ = lean_unsigned_to_nat(1024u);
v___x_376_ = lean_nat_dec_le(v___x_375_, v_prec_277_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; 
v___x_377_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_367_ = v___x_377_;
goto v___jp_366_;
}
else
{
lean_object* v___x_378_; 
v___x_378_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_367_ = v___x_378_;
goto v___jp_366_;
}
v___jp_366_:
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_368_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__19));
v___x_369_ = l_Array_repr___redArg(v___f_278_, v_ids_365_);
v___x_370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
lean_inc(v___y_367_);
v___x_371_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_371_, 0, v___y_367_);
lean_ctor_set(v___x_371_, 1, v___x_370_);
v___x_372_ = 0;
v___x_373_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_373_, 0, v___x_371_);
lean_ctor_set_uint8(v___x_373_, sizeof(void*)*1, v___x_372_);
v___x_374_ = l_Repr_addAppParen(v___x_373_, v_prec_277_);
return v___x_374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___boxed(lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_x_381_, lean_object* v_prec_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(v_inst_379_, v_inst_380_, v_x_381_, v_prec_382_);
lean_dec(v_prec_382_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr(lean_object* v_00_u03b2_384_, lean_object* v_00_u03b1_385_, lean_object* v_inst_386_, lean_object* v_inst_387_, lean_object* v_x_388_, lean_object* v_prec_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(v_inst_386_, v_inst_387_, v_x_388_, v_prec_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed(lean_object* v_00_u03b2_391_, lean_object* v_00_u03b1_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_x_395_, lean_object* v_prec_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr(v_00_u03b2_391_, v_00_u03b1_392_, v_inst_393_, v_inst_394_, v_x_395_, v_prec_396_);
lean_dec(v_prec_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction___redArg(lean_object* v_inst_398_, lean_object* v_inst_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed), 6, 4);
lean_closure_set(v___x_400_, 0, lean_box(0));
lean_closure_set(v___x_400_, 1, lean_box(0));
lean_closure_set(v___x_400_, 2, v_inst_398_);
lean_closure_set(v___x_400_, 3, v_inst_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction(lean_object* v_00_u03b2_401_, lean_object* v_00_u03b1_402_, lean_object* v_inst_403_, lean_object* v_inst_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed), 6, 4);
lean_closure_set(v___x_405_, 0, lean_box(0));
lean_closure_set(v___x_405_, 1, lean_box(0));
lean_closure_set(v___x_405_, 2, v_inst_403_);
lean_closure_set(v___x_405_, 3, v_inst_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg(lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_x_430_){
_start:
{
lean_object* v___f_431_; 
v___f_431_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0));
switch(lean_obj_tag(v_x_430_))
{
case 0:
{
lean_object* v_id_432_; lean_object* v_rupHints_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec_ref(v_inst_429_);
lean_dec_ref(v_inst_428_);
v_id_432_ = lean_ctor_get(v_x_430_, 0);
lean_inc(v_id_432_);
v_rupHints_433_ = lean_ctor_get(v_x_430_, 1);
lean_inc_ref(v_rupHints_433_);
lean_dec_ref_known(v_x_430_, 2);
v___x_434_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__1));
v___x_435_ = l_Nat_reprFast(v_id_432_);
v___x_436_ = lean_string_append(v___x_434_, v___x_435_);
lean_dec_ref(v___x_435_);
v___x_437_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2));
v___x_438_ = lean_string_append(v___x_436_, v___x_437_);
v___x_439_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_440_ = lean_array_to_list(v_rupHints_433_);
v___x_441_ = l_List_toString___redArg(v___f_431_, v___x_440_);
v___x_442_ = lean_string_append(v___x_439_, v___x_441_);
lean_dec_ref(v___x_441_);
v___x_443_ = lean_string_append(v___x_438_, v___x_442_);
lean_dec_ref(v___x_442_);
v___x_444_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4));
v___x_445_ = lean_string_append(v___x_443_, v___x_444_);
return v___x_445_;
}
case 1:
{
lean_object* v_id_446_; lean_object* v_c_447_; lean_object* v_rupHints_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec_ref(v_inst_429_);
v_id_446_ = lean_ctor_get(v_x_430_, 0);
lean_inc(v_id_446_);
v_c_447_ = lean_ctor_get(v_x_430_, 1);
lean_inc(v_c_447_);
v_rupHints_448_ = lean_ctor_get(v_x_430_, 2);
lean_inc_ref(v_rupHints_448_);
lean_dec_ref_known(v_x_430_, 3);
v___x_449_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__5));
v___x_450_ = lean_apply_1(v_inst_428_, v_c_447_);
v___x_451_ = lean_string_append(v___x_449_, v___x_450_);
lean_dec_ref(v___x_450_);
v___x_452_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__6));
v___x_453_ = lean_string_append(v___x_451_, v___x_452_);
v___x_454_ = l_Nat_reprFast(v_id_446_);
v___x_455_ = lean_string_append(v___x_453_, v___x_454_);
lean_dec_ref(v___x_454_);
v___x_456_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2));
v___x_457_ = lean_string_append(v___x_455_, v___x_456_);
v___x_458_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_459_ = lean_array_to_list(v_rupHints_448_);
v___x_460_ = l_List_toString___redArg(v___f_431_, v___x_459_);
v___x_461_ = lean_string_append(v___x_458_, v___x_460_);
lean_dec_ref(v___x_460_);
v___x_462_ = lean_string_append(v___x_457_, v___x_461_);
lean_dec_ref(v___x_461_);
v___x_463_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4));
v___x_464_ = lean_string_append(v___x_462_, v___x_463_);
return v___x_464_;
}
case 2:
{
lean_object* v_pivot_465_; lean_object* v_id_466_; lean_object* v_c_467_; lean_object* v_rupHints_468_; lean_object* v_ratHints_469_; lean_object* v_fst_470_; lean_object* v_snd_471_; lean_object* v___f_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___y_488_; uint8_t v___x_507_; 
v_pivot_465_ = lean_ctor_get(v_x_430_, 2);
lean_inc_ref(v_pivot_465_);
v_id_466_ = lean_ctor_get(v_x_430_, 0);
lean_inc(v_id_466_);
v_c_467_ = lean_ctor_get(v_x_430_, 1);
lean_inc(v_c_467_);
v_rupHints_468_ = lean_ctor_get(v_x_430_, 3);
lean_inc_ref(v_rupHints_468_);
v_ratHints_469_ = lean_ctor_get(v_x_430_, 4);
lean_inc_ref(v_ratHints_469_);
lean_dec_ref_known(v_x_430_, 5);
v_fst_470_ = lean_ctor_get(v_pivot_465_, 0);
lean_inc(v_fst_470_);
v_snd_471_ = lean_ctor_get(v_pivot_465_, 1);
lean_inc(v_snd_471_);
lean_dec_ref(v_pivot_465_);
v___f_472_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__8));
v___x_473_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__9));
v___x_474_ = lean_apply_1(v_inst_428_, v_c_467_);
v___x_475_ = lean_string_append(v___x_473_, v___x_474_);
lean_dec_ref(v___x_474_);
v___x_476_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__10));
v___x_477_ = lean_string_append(v___x_475_, v___x_476_);
v___x_478_ = l_Nat_reprFast(v_id_466_);
v___x_479_ = lean_string_append(v___x_477_, v___x_478_);
lean_dec_ref(v___x_478_);
v___x_480_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__11));
v___x_481_ = lean_string_append(v___x_479_, v___x_480_);
v___x_482_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__12));
v___x_483_ = lean_apply_1(v_inst_429_, v_fst_470_);
v___x_484_ = lean_string_append(v___x_482_, v___x_483_);
lean_dec_ref(v___x_483_);
v___x_485_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__13));
v___x_486_ = lean_string_append(v___x_484_, v___x_485_);
v___x_507_ = lean_unbox(v_snd_471_);
lean_dec(v_snd_471_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
v___x_508_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__16));
v___y_488_ = v___x_508_;
goto v___jp_487_;
}
else
{
lean_object* v___x_509_; 
v___x_509_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__17));
v___y_488_ = v___x_509_;
goto v___jp_487_;
}
v___jp_487_:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_489_ = lean_string_append(v___x_486_, v___y_488_);
v___x_490_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4));
v___x_491_ = lean_string_append(v___x_489_, v___x_490_);
v___x_492_ = lean_string_append(v___x_481_, v___x_491_);
lean_dec_ref(v___x_491_);
v___x_493_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__14));
v___x_494_ = lean_string_append(v___x_492_, v___x_493_);
v___x_495_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_496_ = lean_array_to_list(v_rupHints_468_);
v___x_497_ = l_List_toString___redArg(v___f_431_, v___x_496_);
v___x_498_ = lean_string_append(v___x_495_, v___x_497_);
lean_dec_ref(v___x_497_);
v___x_499_ = lean_string_append(v___x_494_, v___x_498_);
lean_dec_ref(v___x_498_);
v___x_500_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__15));
v___x_501_ = lean_string_append(v___x_499_, v___x_500_);
v___x_502_ = lean_array_to_list(v_ratHints_469_);
v___x_503_ = l_List_toString___redArg(v___f_472_, v___x_502_);
v___x_504_ = lean_string_append(v___x_495_, v___x_503_);
lean_dec_ref(v___x_503_);
v___x_505_ = lean_string_append(v___x_501_, v___x_504_);
lean_dec_ref(v___x_504_);
v___x_506_ = lean_string_append(v___x_505_, v___x_490_);
return v___x_506_;
}
}
default: 
{
lean_object* v_ids_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec_ref(v_inst_429_);
lean_dec_ref(v_inst_428_);
v_ids_510_ = lean_ctor_get(v_x_430_, 0);
lean_inc_ref(v_ids_510_);
lean_dec_ref_known(v_x_430_, 1);
v___x_511_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__18));
v___x_512_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_513_ = lean_array_to_list(v_ids_510_);
v___x_514_ = l_List_toString___redArg(v___f_431_, v___x_513_);
v___x_515_ = lean_string_append(v___x_512_, v___x_514_);
lean_dec_ref(v___x_514_);
v___x_516_ = lean_string_append(v___x_511_, v___x_515_);
lean_dec_ref(v___x_515_);
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString(lean_object* v_00_u03b2_517_, lean_object* v_00_u03b1_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_x_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg(v_inst_519_, v_inst_520_, v_x_521_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instToStringAction___redArg(lean_object* v_inst_523_, lean_object* v_inst_524_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Action_toString), 5, 4);
lean_closure_set(v___x_525_, 0, lean_box(0));
lean_closure_set(v___x_525_, 1, lean_box(0));
lean_closure_set(v___x_525_, 2, v_inst_523_);
lean_closure_set(v___x_525_, 3, v_inst_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instToStringAction(lean_object* v_00_u03b2_526_, lean_object* v_00_u03b1_527_, lean_object* v_inst_528_, lean_object* v_inst_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Action_toString), 5, 4);
lean_closure_set(v___x_530_, 0, lean_box(0));
lean_closure_set(v___x_530_, 1, lean_box(0));
lean_closure_set(v___x_530_, 2, v_inst_528_);
lean_closure_set(v___x_530_, 3, v_inst_529_);
return v___x_530_;
}
}
lean_object* runtime_initialize_Std_Sat_CNF(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
