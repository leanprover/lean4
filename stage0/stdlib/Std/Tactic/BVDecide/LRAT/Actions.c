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
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___impl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___impl___redArg(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___impl(lean_object* v_00_u03b2_5_, lean_object* v_00_u03b1_6_, lean_object* v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_obj_tag_nat(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___impl___boxed(lean_object* v_00_u03b2_9_, lean_object* v_00_u03b1_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorIdx___impl(v_00_u03b2_9_, v_00_u03b1_10_, v_x_11_);
lean_dec_ref(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(lean_object* v_t_13_, lean_object* v_k_14_){
_start:
{
switch(lean_obj_tag(v_t_13_))
{
case 0:
{
lean_object* v_id_15_; lean_object* v_rupHints_16_; lean_object* v___x_17_; 
v_id_15_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_id_15_);
v_rupHints_16_ = lean_ctor_get(v_t_13_, 1);
lean_inc_ref(v_rupHints_16_);
lean_dec_ref_known(v_t_13_, 2);
v___x_17_ = lean_apply_2(v_k_14_, v_id_15_, v_rupHints_16_);
return v___x_17_;
}
case 1:
{
lean_object* v_id_18_; lean_object* v_c_19_; lean_object* v_rupHints_20_; lean_object* v___x_21_; 
v_id_18_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_id_18_);
v_c_19_ = lean_ctor_get(v_t_13_, 1);
lean_inc(v_c_19_);
v_rupHints_20_ = lean_ctor_get(v_t_13_, 2);
lean_inc_ref(v_rupHints_20_);
lean_dec_ref_known(v_t_13_, 3);
v___x_21_ = lean_apply_3(v_k_14_, v_id_18_, v_c_19_, v_rupHints_20_);
return v___x_21_;
}
case 2:
{
lean_object* v_id_22_; lean_object* v_c_23_; lean_object* v_pivot_24_; lean_object* v_rupHints_25_; lean_object* v_ratHints_26_; lean_object* v___x_27_; 
v_id_22_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_id_22_);
v_c_23_ = lean_ctor_get(v_t_13_, 1);
lean_inc(v_c_23_);
v_pivot_24_ = lean_ctor_get(v_t_13_, 2);
lean_inc_ref(v_pivot_24_);
v_rupHints_25_ = lean_ctor_get(v_t_13_, 3);
lean_inc_ref(v_rupHints_25_);
v_ratHints_26_ = lean_ctor_get(v_t_13_, 4);
lean_inc_ref(v_ratHints_26_);
lean_dec_ref_known(v_t_13_, 5);
v___x_27_ = lean_apply_5(v_k_14_, v_id_22_, v_c_23_, v_pivot_24_, v_rupHints_25_, v_ratHints_26_);
return v___x_27_;
}
default: 
{
lean_object* v_ids_28_; lean_object* v___x_29_; 
v_ids_28_ = lean_ctor_get(v_t_13_, 0);
lean_inc_ref(v_ids_28_);
lean_dec_ref_known(v_t_13_, 1);
v___x_29_ = lean_apply_1(v_k_14_, v_ids_28_);
return v___x_29_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorElim(lean_object* v_00_u03b2_30_, lean_object* v_00_u03b1_31_, lean_object* v_motive_32_, lean_object* v_ctorIdx_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_k_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_34_, v_k_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___boxed(lean_object* v_00_u03b2_38_, lean_object* v_00_u03b1_39_, lean_object* v_motive_40_, lean_object* v_ctorIdx_41_, lean_object* v_t_42_, lean_object* v_h_43_, lean_object* v_k_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim(v_00_u03b2_38_, v_00_u03b1_39_, v_motive_40_, v_ctorIdx_41_, v_t_42_, v_h_43_, v_k_44_);
lean_dec(v_ctorIdx_41_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addEmpty_elim___redArg(lean_object* v_t_46_, lean_object* v_addEmpty_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_46_, v_addEmpty_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addEmpty_elim(lean_object* v_00_u03b2_49_, lean_object* v_00_u03b1_50_, lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_addEmpty_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_52_, v_addEmpty_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addRup_elim___redArg(lean_object* v_t_56_, lean_object* v_addRup_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_56_, v_addRup_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addRup_elim(lean_object* v_00_u03b2_59_, lean_object* v_00_u03b1_60_, lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_addRup_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_62_, v_addRup_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addRat_elim___redArg(lean_object* v_t_66_, lean_object* v_addRat_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_66_, v_addRat_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_addRat_elim(lean_object* v_00_u03b2_69_, lean_object* v_00_u03b1_70_, lean_object* v_motive_71_, lean_object* v_t_72_, lean_object* v_h_73_, lean_object* v_addRat_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_72_, v_addRat_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_del_elim___redArg(lean_object* v_t_76_, lean_object* v_del_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_76_, v_del_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_del_elim(lean_object* v_00_u03b2_79_, lean_object* v_00_u03b1_80_, lean_object* v_motive_81_, lean_object* v_t_82_, lean_object* v_h_83_, lean_object* v_del_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Std_Tactic_BVDecide_LRAT_Action_ctorElim___redArg(v_t_82_, v_del_84_);
return v___x_85_;
}
}
lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg(){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___closed__1));
return v___x_92_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_93_;
v_res_93_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg();
stack->m_obj
 = v_res_93_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___boxed(lean_object* v___dummy_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg();
return v_res_95_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0(void){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg();
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(lean_object* v_00_u03b2_97_, lean_object* v_00_u03b1_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0, &l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0);
return v___x_99_;
}
}
lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___redArg(){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0, &l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0);
return v___x_101_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_102_;
v_res_102_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___redArg();
stack->m_obj
 = v_res_102_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___redArg___boxed(lean_object* v___dummy_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___redArg();
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction(lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v___x_107_; 
v___x_107_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0, &l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0);
return v___x_107_;
}
}
uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0(lean_object* v___f_108_, lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
lean_object* v_fst_111_; lean_object* v_snd_112_; lean_object* v_fst_113_; lean_object* v_snd_114_; uint8_t v___x_115_; 
v_fst_111_ = lean_ctor_get(v_x_109_, 0);
v_snd_112_ = lean_ctor_get(v_x_109_, 1);
v_fst_113_ = lean_ctor_get(v_x_110_, 0);
v_snd_114_ = lean_ctor_get(v_x_110_, 1);
v___x_115_ = lean_nat_dec_eq(v_fst_111_, v_fst_113_);
if (v___x_115_ == 0)
{
lean_dec_ref(v___f_108_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_116_ = lean_array_get_size(v_snd_112_);
v___x_117_ = lean_array_get_size(v_snd_114_);
v___x_118_ = lean_nat_dec_eq(v___x_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_dec_ref(v___f_108_);
return v___x_118_;
}
else
{
uint8_t v___x_119_; 
v___x_119_ = l_Array_isEqvAux___redArg(v_snd_112_, v_snd_114_, v___f_108_, v___x_116_);
return v___x_119_;
}
}
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_108_ = stack[0].m_obj;
lean_object* v_x_109_ = stack[1].m_obj;
lean_object* v_x_110_ = stack[2].m_obj;
uint8_t v_res_120_;
v_res_120_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0(v___f_108_, v_x_109_, v_x_110_);
stack->m_num = v_res_120_;
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
uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_x_131_, lean_object* v_x_132_){
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
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_129_ = stack[0].m_obj;
lean_object* v_inst_130_ = stack[1].m_obj;
lean_object* v_x_131_ = stack[2].m_obj;
lean_object* v_x_132_ = stack[3].m_obj;
uint8_t v_res_206_;
v_res_206_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(v_inst_129_, v_inst_130_, v_x_131_, v_x_132_);
stack->m_num = v_res_206_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___boxed(lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(v_inst_207_, v_inst_208_, v_x_209_, v_x_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq(lean_object* v_00_u03b2_213_, lean_object* v_00_u03b1_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
uint8_t v___x_219_; 
v___x_219_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(v_inst_215_, v_inst_216_, v_x_217_, v_x_218_);
return v___x_219_;
}
}
LEAN_EXPORT void l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_215_ = stack[2].m_obj;
lean_object* v_inst_216_ = stack[3].m_obj;
lean_object* v_x_217_ = stack[4].m_obj;
lean_object* v_x_218_ = stack[5].m_obj;
uint8_t v_res_220_;
v_res_220_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq(lean_box(0), lean_box(0), v_inst_215_, v_inst_216_, v_x_217_, v_x_218_);
stack->m_num = v_res_220_;
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed(lean_object* v_00_u03b2_221_, lean_object* v_00_u03b1_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
uint8_t v_res_227_; lean_object* v_r_228_; 
v_res_227_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq(v_00_u03b2_221_, v_00_u03b1_222_, v_inst_223_, v_inst_224_, v_x_225_, v_x_226_);
v_r_228_ = lean_box(v_res_227_);
return v_r_228_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction___redArg(lean_object* v_inst_229_, lean_object* v_inst_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed), 6, 4);
lean_closure_set(v___x_231_, 0, lean_box(0));
lean_closure_set(v___x_231_, 1, lean_box(0));
lean_closure_set(v___x_231_, 2, v_inst_229_);
lean_closure_set(v___x_231_, 3, v_inst_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction(lean_object* v_00_u03b2_232_, lean_object* v_00_u03b1_233_, lean_object* v_inst_234_, lean_object* v_inst_235_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed), 6, 4);
lean_closure_set(v___x_236_, 0, lean_box(0));
lean_closure_set(v___x_236_, 1, lean_box(0));
lean_closure_set(v___x_236_, 2, v_inst_234_);
lean_closure_set(v___x_236_, 3, v_inst_235_);
return v___x_236_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_244_ = lean_unsigned_to_nat(2u);
v___x_245_ = lean_nat_to_int(v___x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_unsigned_to_nat(1u);
v___x_247_ = lean_nat_to_int(v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(lean_object* v_inst_276_, lean_object* v_inst_277_, lean_object* v_x_278_, lean_object* v_prec_279_){
_start:
{
lean_object* v___f_280_; 
v___f_280_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0));
switch(lean_obj_tag(v_x_278_))
{
case 0:
{
lean_object* v_id_281_; lean_object* v_rupHints_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_306_; 
lean_dec_ref(v_inst_277_);
lean_dec_ref(v_inst_276_);
v_id_281_ = lean_ctor_get(v_x_278_, 0);
v_rupHints_282_ = lean_ctor_get(v_x_278_, 1);
v_isSharedCheck_306_ = !lean_is_exclusive(v_x_278_);
if (v_isSharedCheck_306_ == 0)
{
v___x_284_ = v_x_278_;
v_isShared_285_ = v_isSharedCheck_306_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_rupHints_282_);
lean_inc(v_id_281_);
lean_dec(v_x_278_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_306_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___y_287_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(1024u);
v___x_303_ = lean_nat_dec_le(v___x_302_, v_prec_279_);
if (v___x_303_ == 0)
{
lean_object* v___x_304_; 
v___x_304_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_287_ = v___x_304_;
goto v___jp_286_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_287_ = v___x_305_;
goto v___jp_286_;
}
v___jp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_288_ = lean_box(1);
v___x_289_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__3));
v___x_290_ = l_Nat_reprFast(v_id_281_);
v___x_291_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
if (v_isShared_285_ == 0)
{
lean_ctor_set_tag(v___x_284_, 5);
lean_ctor_set(v___x_284_, 1, v___x_291_);
lean_ctor_set(v___x_284_, 0, v___x_289_);
v___x_293_ = v___x_284_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v___x_291_);
v___x_293_ = v_reuseFailAlloc_301_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_294_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v___x_288_);
v___x_295_ = l_Array_repr___redArg(v___f_280_, v_rupHints_282_);
v___x_296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_294_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
lean_inc(v___y_287_);
v___x_297_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_297_, 0, v___y_287_);
lean_ctor_set(v___x_297_, 1, v___x_296_);
v___x_298_ = 0;
v___x_299_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_299_, 0, v___x_297_);
lean_ctor_set_uint8(v___x_299_, sizeof(void*)*1, v___x_298_);
v___x_300_ = l_Repr_addAppParen(v___x_299_, v_prec_279_);
return v___x_300_;
}
}
}
}
case 1:
{
lean_object* v_id_307_; lean_object* v_c_308_; lean_object* v_rupHints_309_; lean_object* v___y_311_; lean_object* v___x_328_; uint8_t v___x_329_; 
lean_dec_ref(v_inst_277_);
v_id_307_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_id_307_);
v_c_308_ = lean_ctor_get(v_x_278_, 1);
lean_inc(v_c_308_);
v_rupHints_309_ = lean_ctor_get(v_x_278_, 2);
lean_inc_ref(v_rupHints_309_);
lean_dec_ref_known(v_x_278_, 3);
v___x_328_ = lean_unsigned_to_nat(1024u);
v___x_329_ = lean_nat_dec_le(v___x_328_, v_prec_279_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_311_ = v___x_330_;
goto v___jp_310_;
}
else
{
lean_object* v___x_331_; 
v___x_331_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_311_ = v___x_331_;
goto v___jp_310_;
}
v___jp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_312_ = lean_box(1);
v___x_313_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__8));
v___x_314_ = l_Nat_reprFast(v_id_307_);
v___x_315_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_313_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___x_317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___x_312_);
v___x_318_ = lean_unsigned_to_nat(1024u);
v___x_319_ = lean_apply_2(v_inst_276_, v_c_308_, v___x_318_);
v___x_320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_317_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_312_);
v___x_322_ = l_Array_repr___redArg(v___f_280_, v_rupHints_309_);
v___x_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
lean_inc(v___y_311_);
v___x_324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_324_, 0, v___y_311_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = 0;
v___x_326_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*1, v___x_325_);
v___x_327_ = l_Repr_addAppParen(v___x_326_, v_prec_279_);
return v___x_327_;
}
}
case 2:
{
lean_object* v_id_332_; lean_object* v_c_333_; lean_object* v_pivot_334_; lean_object* v_rupHints_335_; lean_object* v_ratHints_336_; lean_object* v___f_337_; lean_object* v___x_338_; lean_object* v___y_340_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_id_332_ = lean_ctor_get(v_x_278_, 0);
lean_inc(v_id_332_);
v_c_333_ = lean_ctor_get(v_x_278_, 1);
lean_inc(v_c_333_);
v_pivot_334_ = lean_ctor_get(v_x_278_, 2);
lean_inc_ref(v_pivot_334_);
v_rupHints_335_ = lean_ctor_get(v_x_278_, 3);
lean_inc_ref(v_rupHints_335_);
v_ratHints_336_ = lean_ctor_get(v_x_278_, 4);
lean_inc_ref(v_ratHints_336_);
lean_dec_ref_known(v_x_278_, 5);
v___f_337_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__11));
v___x_338_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__13));
v___x_363_ = lean_unsigned_to_nat(1024u);
v___x_364_ = lean_nat_dec_le(v___x_363_, v_prec_279_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; 
v___x_365_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_340_ = v___x_365_;
goto v___jp_339_;
}
else
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_340_ = v___x_366_;
goto v___jp_339_;
}
v___jp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_341_ = lean_box(1);
v___x_342_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__16));
v___x_343_ = l_Nat_reprFast(v_id_332_);
v___x_344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
v___x_345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_342_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_341_);
v___x_347_ = lean_unsigned_to_nat(1024u);
v___x_348_ = lean_apply_2(v_inst_276_, v_c_333_, v___x_347_);
v___x_349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_346_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v___x_341_);
v___x_351_ = l_Prod_repr___redArg(v_inst_277_, v___f_337_, v_pivot_334_);
v___x_352_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_350_);
lean_ctor_set(v___x_352_, 1, v___x_351_);
v___x_353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_341_);
v___x_354_ = l_Array_repr___redArg(v___f_280_, v_rupHints_335_);
v___x_355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_353_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
lean_ctor_set(v___x_356_, 1, v___x_341_);
v___x_357_ = l_Array_repr___redArg(v___x_338_, v_ratHints_336_);
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_356_);
lean_ctor_set(v___x_358_, 1, v___x_357_);
lean_inc(v___y_340_);
v___x_359_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_359_, 0, v___y_340_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = 0;
v___x_361_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set_uint8(v___x_361_, sizeof(void*)*1, v___x_360_);
v___x_362_ = l_Repr_addAppParen(v___x_361_, v_prec_279_);
return v___x_362_;
}
}
default: 
{
lean_object* v_ids_367_; lean_object* v___y_369_; lean_object* v___x_377_; uint8_t v___x_378_; 
lean_dec_ref(v_inst_277_);
lean_dec_ref(v_inst_276_);
v_ids_367_ = lean_ctor_get(v_x_278_, 0);
lean_inc_ref(v_ids_367_);
lean_dec_ref_known(v_x_278_, 1);
v___x_377_ = lean_unsigned_to_nat(1024u);
v___x_378_ = lean_nat_dec_le(v___x_377_, v_prec_279_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
v___x_379_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_369_ = v___x_379_;
goto v___jp_368_;
}
else
{
lean_object* v___x_380_; 
v___x_380_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_369_ = v___x_380_;
goto v___jp_368_;
}
v___jp_368_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_370_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__19));
v___x_371_ = l_Array_repr___redArg(v___f_280_, v_ids_367_);
v___x_372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_370_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
lean_inc(v___y_369_);
v___x_373_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_373_, 0, v___y_369_);
lean_ctor_set(v___x_373_, 1, v___x_372_);
v___x_374_ = 0;
v___x_375_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*1, v___x_374_);
v___x_376_ = l_Repr_addAppParen(v___x_375_, v_prec_279_);
return v___x_376_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___boxed(lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_x_383_, lean_object* v_prec_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(v_inst_381_, v_inst_382_, v_x_383_, v_prec_384_);
lean_dec(v_prec_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr(lean_object* v_00_u03b2_386_, lean_object* v_00_u03b1_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_x_390_, lean_object* v_prec_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(v_inst_388_, v_inst_389_, v_x_390_, v_prec_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed(lean_object* v_00_u03b2_393_, lean_object* v_00_u03b1_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_x_397_, lean_object* v_prec_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr(v_00_u03b2_393_, v_00_u03b1_394_, v_inst_395_, v_inst_396_, v_x_397_, v_prec_398_);
lean_dec(v_prec_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction___redArg(lean_object* v_inst_400_, lean_object* v_inst_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed), 6, 4);
lean_closure_set(v___x_402_, 0, lean_box(0));
lean_closure_set(v___x_402_, 1, lean_box(0));
lean_closure_set(v___x_402_, 2, v_inst_400_);
lean_closure_set(v___x_402_, 3, v_inst_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction(lean_object* v_00_u03b2_403_, lean_object* v_00_u03b1_404_, lean_object* v_inst_405_, lean_object* v_inst_406_){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed), 6, 4);
lean_closure_set(v___x_407_, 0, lean_box(0));
lean_closure_set(v___x_407_, 1, lean_box(0));
lean_closure_set(v___x_407_, 2, v_inst_405_);
lean_closure_set(v___x_407_, 3, v_inst_406_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg(lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_x_432_){
_start:
{
lean_object* v___f_433_; 
v___f_433_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0));
switch(lean_obj_tag(v_x_432_))
{
case 0:
{
lean_object* v_id_434_; lean_object* v_rupHints_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec_ref(v_inst_431_);
lean_dec_ref(v_inst_430_);
v_id_434_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_id_434_);
v_rupHints_435_ = lean_ctor_get(v_x_432_, 1);
lean_inc_ref(v_rupHints_435_);
lean_dec_ref_known(v_x_432_, 2);
v___x_436_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__1));
v___x_437_ = l_Nat_reprFast(v_id_434_);
v___x_438_ = lean_string_append(v___x_436_, v___x_437_);
lean_dec_ref(v___x_437_);
v___x_439_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2));
v___x_440_ = lean_string_append(v___x_438_, v___x_439_);
v___x_441_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_442_ = lean_array_to_list(v_rupHints_435_);
v___x_443_ = l_List_toString___redArg(v___f_433_, v___x_442_);
v___x_444_ = lean_string_append(v___x_441_, v___x_443_);
lean_dec_ref(v___x_443_);
v___x_445_ = lean_string_append(v___x_440_, v___x_444_);
lean_dec_ref(v___x_444_);
v___x_446_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4));
v___x_447_ = lean_string_append(v___x_445_, v___x_446_);
return v___x_447_;
}
case 1:
{
lean_object* v_id_448_; lean_object* v_c_449_; lean_object* v_rupHints_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec_ref(v_inst_431_);
v_id_448_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_id_448_);
v_c_449_ = lean_ctor_get(v_x_432_, 1);
lean_inc(v_c_449_);
v_rupHints_450_ = lean_ctor_get(v_x_432_, 2);
lean_inc_ref(v_rupHints_450_);
lean_dec_ref_known(v_x_432_, 3);
v___x_451_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__5));
v___x_452_ = lean_apply_1(v_inst_430_, v_c_449_);
v___x_453_ = lean_string_append(v___x_451_, v___x_452_);
lean_dec_ref(v___x_452_);
v___x_454_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__6));
v___x_455_ = lean_string_append(v___x_453_, v___x_454_);
v___x_456_ = l_Nat_reprFast(v_id_448_);
v___x_457_ = lean_string_append(v___x_455_, v___x_456_);
lean_dec_ref(v___x_456_);
v___x_458_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2));
v___x_459_ = lean_string_append(v___x_457_, v___x_458_);
v___x_460_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_461_ = lean_array_to_list(v_rupHints_450_);
v___x_462_ = l_List_toString___redArg(v___f_433_, v___x_461_);
v___x_463_ = lean_string_append(v___x_460_, v___x_462_);
lean_dec_ref(v___x_462_);
v___x_464_ = lean_string_append(v___x_459_, v___x_463_);
lean_dec_ref(v___x_463_);
v___x_465_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4));
v___x_466_ = lean_string_append(v___x_464_, v___x_465_);
return v___x_466_;
}
case 2:
{
lean_object* v_pivot_467_; lean_object* v_id_468_; lean_object* v_c_469_; lean_object* v_rupHints_470_; lean_object* v_ratHints_471_; lean_object* v_fst_472_; lean_object* v_snd_473_; lean_object* v___f_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___y_490_; uint8_t v___x_509_; 
v_pivot_467_ = lean_ctor_get(v_x_432_, 2);
lean_inc_ref(v_pivot_467_);
v_id_468_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_id_468_);
v_c_469_ = lean_ctor_get(v_x_432_, 1);
lean_inc(v_c_469_);
v_rupHints_470_ = lean_ctor_get(v_x_432_, 3);
lean_inc_ref(v_rupHints_470_);
v_ratHints_471_ = lean_ctor_get(v_x_432_, 4);
lean_inc_ref(v_ratHints_471_);
lean_dec_ref_known(v_x_432_, 5);
v_fst_472_ = lean_ctor_get(v_pivot_467_, 0);
lean_inc(v_fst_472_);
v_snd_473_ = lean_ctor_get(v_pivot_467_, 1);
lean_inc(v_snd_473_);
lean_dec_ref(v_pivot_467_);
v___f_474_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__8));
v___x_475_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__9));
v___x_476_ = lean_apply_1(v_inst_430_, v_c_469_);
v___x_477_ = lean_string_append(v___x_475_, v___x_476_);
lean_dec_ref(v___x_476_);
v___x_478_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__10));
v___x_479_ = lean_string_append(v___x_477_, v___x_478_);
v___x_480_ = l_Nat_reprFast(v_id_468_);
v___x_481_ = lean_string_append(v___x_479_, v___x_480_);
lean_dec_ref(v___x_480_);
v___x_482_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__11));
v___x_483_ = lean_string_append(v___x_481_, v___x_482_);
v___x_484_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__12));
v___x_485_ = lean_apply_1(v_inst_431_, v_fst_472_);
v___x_486_ = lean_string_append(v___x_484_, v___x_485_);
lean_dec_ref(v___x_485_);
v___x_487_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__13));
v___x_488_ = lean_string_append(v___x_486_, v___x_487_);
v___x_509_ = lean_unbox(v_snd_473_);
lean_dec(v_snd_473_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
v___x_510_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__16));
v___y_490_ = v___x_510_;
goto v___jp_489_;
}
else
{
lean_object* v___x_511_; 
v___x_511_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__17));
v___y_490_ = v___x_511_;
goto v___jp_489_;
}
v___jp_489_:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_491_ = lean_string_append(v___x_488_, v___y_490_);
v___x_492_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4));
v___x_493_ = lean_string_append(v___x_491_, v___x_492_);
v___x_494_ = lean_string_append(v___x_483_, v___x_493_);
lean_dec_ref(v___x_493_);
v___x_495_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__14));
v___x_496_ = lean_string_append(v___x_494_, v___x_495_);
v___x_497_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_498_ = lean_array_to_list(v_rupHints_470_);
v___x_499_ = l_List_toString___redArg(v___f_433_, v___x_498_);
v___x_500_ = lean_string_append(v___x_497_, v___x_499_);
lean_dec_ref(v___x_499_);
v___x_501_ = lean_string_append(v___x_496_, v___x_500_);
lean_dec_ref(v___x_500_);
v___x_502_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__15));
v___x_503_ = lean_string_append(v___x_501_, v___x_502_);
v___x_504_ = lean_array_to_list(v_ratHints_471_);
v___x_505_ = l_List_toString___redArg(v___f_474_, v___x_504_);
v___x_506_ = lean_string_append(v___x_497_, v___x_505_);
lean_dec_ref(v___x_505_);
v___x_507_ = lean_string_append(v___x_503_, v___x_506_);
lean_dec_ref(v___x_506_);
v___x_508_ = lean_string_append(v___x_507_, v___x_492_);
return v___x_508_;
}
}
default: 
{
lean_object* v_ids_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec_ref(v_inst_431_);
lean_dec_ref(v_inst_430_);
v_ids_512_ = lean_ctor_get(v_x_432_, 0);
lean_inc_ref(v_ids_512_);
lean_dec_ref_known(v_x_432_, 1);
v___x_513_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__18));
v___x_514_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_515_ = lean_array_to_list(v_ids_512_);
v___x_516_ = l_List_toString___redArg(v___f_433_, v___x_515_);
v___x_517_ = lean_string_append(v___x_514_, v___x_516_);
lean_dec_ref(v___x_516_);
v___x_518_ = lean_string_append(v___x_513_, v___x_517_);
lean_dec_ref(v___x_517_);
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString(lean_object* v_00_u03b2_519_, lean_object* v_00_u03b1_520_, lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_x_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg(v_inst_521_, v_inst_522_, v_x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instToStringAction___redArg(lean_object* v_inst_525_, lean_object* v_inst_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Action_toString), 5, 4);
lean_closure_set(v___x_527_, 0, lean_box(0));
lean_closure_set(v___x_527_, 1, lean_box(0));
lean_closure_set(v___x_527_, 2, v_inst_525_);
lean_closure_set(v___x_527_, 3, v_inst_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instToStringAction(lean_object* v_00_u03b2_528_, lean_object* v_00_u03b1_529_, lean_object* v_inst_530_, lean_object* v_inst_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Action_toString), 5, 4);
lean_closure_set(v___x_532_, 0, lean_box(0));
lean_closure_set(v___x_532_, 1, lean_box(0));
lean_closure_set(v___x_532_, 2, v_inst_530_);
lean_closure_set(v___x_532_, 3, v_inst_531_);
return v___x_532_;
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
