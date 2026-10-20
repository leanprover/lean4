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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg(){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___closed__1));
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg___boxed(lean_object* v___dummy_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg();
return v_res_94_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0(void){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___redArg();
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default(lean_object* v_00_u03b2_96_, lean_object* v_00_u03b1_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0, &l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___redArg(){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0, &l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___redArg___boxed(lean_object* v___dummy_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_Tactic_BVDecide_LRAT_instInhabitedAction___redArg();
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instInhabitedAction(lean_object* v_a_103_, lean_object* v_a_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0, &l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_instInhabitedAction_default___closed__0);
return v___x_105_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0(lean_object* v___f_106_, lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
lean_object* v_fst_109_; lean_object* v_snd_110_; lean_object* v_fst_111_; lean_object* v_snd_112_; uint8_t v___x_113_; 
v_fst_109_ = lean_ctor_get(v_x_107_, 0);
v_snd_110_ = lean_ctor_get(v_x_107_, 1);
v_fst_111_ = lean_ctor_get(v_x_108_, 0);
v_snd_112_ = lean_ctor_get(v_x_108_, 1);
v___x_113_ = lean_nat_dec_eq(v_fst_109_, v_fst_111_);
if (v___x_113_ == 0)
{
lean_dec_ref(v___f_106_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_114_ = lean_array_get_size(v_snd_110_);
v___x_115_ = lean_array_get_size(v_snd_112_);
v___x_116_ = lean_nat_dec_eq(v___x_114_, v___x_115_);
if (v___x_116_ == 0)
{
lean_dec_ref(v___f_106_);
return v___x_116_;
}
else
{
uint8_t v___x_117_; 
v___x_117_ = l_Array_isEqvAux___redArg(v_snd_110_, v_snd_112_, v___f_106_, v___x_114_);
return v___x_117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0___boxed(lean_object* v___f_118_, lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___lam__0(v___f_118_, v_x_119_, v_x_120_);
lean_dec_ref(v_x_120_);
lean_dec_ref(v_x_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
switch(lean_obj_tag(v_x_128_))
{
case 0:
{
lean_dec_ref(v_inst_127_);
lean_dec_ref(v_inst_126_);
if (lean_obj_tag(v_x_129_) == 0)
{
lean_object* v_id_130_; lean_object* v_rupHints_131_; lean_object* v_id_132_; lean_object* v_rupHints_133_; uint8_t v___x_134_; 
v_id_130_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_id_130_);
v_rupHints_131_ = lean_ctor_get(v_x_128_, 1);
lean_inc_ref(v_rupHints_131_);
lean_dec_ref_known(v_x_128_, 2);
v_id_132_ = lean_ctor_get(v_x_129_, 0);
lean_inc(v_id_132_);
v_rupHints_133_ = lean_ctor_get(v_x_129_, 1);
lean_inc_ref(v_rupHints_133_);
lean_dec_ref_known(v_x_129_, 2);
v___x_134_ = lean_nat_dec_eq(v_id_130_, v_id_132_);
lean_dec(v_id_132_);
lean_dec(v_id_130_);
if (v___x_134_ == 0)
{
lean_dec_ref(v_rupHints_133_);
lean_dec_ref(v_rupHints_131_);
return v___x_134_;
}
else
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_135_ = lean_array_get_size(v_rupHints_131_);
v___x_136_ = lean_array_get_size(v_rupHints_133_);
v___x_137_ = lean_nat_dec_eq(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_dec_ref(v_rupHints_133_);
lean_dec_ref(v_rupHints_131_);
return v___x_137_;
}
else
{
lean_object* v___f_138_; uint8_t v___x_139_; 
v___f_138_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0));
v___x_139_ = l_Array_isEqvAux___redArg(v_rupHints_131_, v_rupHints_133_, v___f_138_, v___x_135_);
lean_dec_ref(v_rupHints_133_);
lean_dec_ref(v_rupHints_131_);
return v___x_139_;
}
}
}
else
{
uint8_t v___x_140_; 
lean_dec_ref_known(v_x_128_, 2);
lean_dec_ref(v_x_129_);
v___x_140_ = 0;
return v___x_140_;
}
}
case 1:
{
lean_dec_ref(v_inst_127_);
if (lean_obj_tag(v_x_129_) == 1)
{
lean_object* v_id_141_; lean_object* v_c_142_; lean_object* v_rupHints_143_; lean_object* v_id_144_; lean_object* v_c_145_; lean_object* v_rupHints_146_; uint8_t v___x_147_; 
v_id_141_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_id_141_);
v_c_142_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_c_142_);
v_rupHints_143_ = lean_ctor_get(v_x_128_, 2);
lean_inc_ref(v_rupHints_143_);
lean_dec_ref_known(v_x_128_, 3);
v_id_144_ = lean_ctor_get(v_x_129_, 0);
lean_inc(v_id_144_);
v_c_145_ = lean_ctor_get(v_x_129_, 1);
lean_inc(v_c_145_);
v_rupHints_146_ = lean_ctor_get(v_x_129_, 2);
lean_inc_ref(v_rupHints_146_);
lean_dec_ref_known(v_x_129_, 3);
v___x_147_ = lean_nat_dec_eq(v_id_141_, v_id_144_);
lean_dec(v_id_144_);
lean_dec(v_id_141_);
if (v___x_147_ == 0)
{
lean_dec_ref(v_rupHints_146_);
lean_dec(v_c_145_);
lean_dec_ref(v_rupHints_143_);
lean_dec(v_c_142_);
lean_dec_ref(v_inst_126_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = lean_apply_2(v_inst_126_, v_c_142_, v_c_145_);
v___x_149_ = lean_unbox(v___x_148_);
if (v___x_149_ == 0)
{
uint8_t v___x_150_; 
lean_dec_ref(v_rupHints_146_);
lean_dec_ref(v_rupHints_143_);
v___x_150_ = lean_unbox(v___x_148_);
return v___x_150_;
}
else
{
lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_151_ = lean_array_get_size(v_rupHints_143_);
v___x_152_ = lean_array_get_size(v_rupHints_146_);
v___x_153_ = lean_nat_dec_eq(v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_dec_ref(v_rupHints_146_);
lean_dec_ref(v_rupHints_143_);
return v___x_153_;
}
else
{
lean_object* v___f_154_; uint8_t v___x_155_; 
v___f_154_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0));
v___x_155_ = l_Array_isEqvAux___redArg(v_rupHints_143_, v_rupHints_146_, v___f_154_, v___x_151_);
lean_dec_ref(v_rupHints_146_);
lean_dec_ref(v_rupHints_143_);
return v___x_155_;
}
}
}
}
else
{
uint8_t v___x_156_; 
lean_dec_ref_known(v_x_128_, 3);
lean_dec_ref(v_x_129_);
lean_dec_ref(v_inst_126_);
v___x_156_ = 0;
return v___x_156_;
}
}
case 2:
{
if (lean_obj_tag(v_x_129_) == 2)
{
lean_object* v_id_157_; lean_object* v_c_158_; lean_object* v_pivot_159_; lean_object* v_rupHints_160_; lean_object* v_ratHints_161_; lean_object* v_id_162_; lean_object* v_c_163_; lean_object* v_pivot_164_; lean_object* v_rupHints_165_; lean_object* v_ratHints_166_; uint8_t v___x_167_; 
v_id_157_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_id_157_);
v_c_158_ = lean_ctor_get(v_x_128_, 1);
lean_inc(v_c_158_);
v_pivot_159_ = lean_ctor_get(v_x_128_, 2);
lean_inc_ref(v_pivot_159_);
v_rupHints_160_ = lean_ctor_get(v_x_128_, 3);
lean_inc_ref(v_rupHints_160_);
v_ratHints_161_ = lean_ctor_get(v_x_128_, 4);
lean_inc_ref(v_ratHints_161_);
lean_dec_ref_known(v_x_128_, 5);
v_id_162_ = lean_ctor_get(v_x_129_, 0);
lean_inc(v_id_162_);
v_c_163_ = lean_ctor_get(v_x_129_, 1);
lean_inc(v_c_163_);
v_pivot_164_ = lean_ctor_get(v_x_129_, 2);
lean_inc_ref(v_pivot_164_);
v_rupHints_165_ = lean_ctor_get(v_x_129_, 3);
lean_inc_ref(v_rupHints_165_);
v_ratHints_166_ = lean_ctor_get(v_x_129_, 4);
lean_inc_ref(v_ratHints_166_);
lean_dec_ref_known(v_x_129_, 5);
v___x_167_ = lean_nat_dec_eq(v_id_157_, v_id_162_);
lean_dec(v_id_162_);
lean_dec(v_id_157_);
if (v___x_167_ == 0)
{
lean_dec_ref(v_ratHints_166_);
lean_dec_ref(v_rupHints_165_);
lean_dec_ref(v_pivot_164_);
lean_dec(v_c_163_);
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_rupHints_160_);
lean_dec_ref(v_pivot_159_);
lean_dec(v_c_158_);
lean_dec_ref(v_inst_127_);
lean_dec_ref(v_inst_126_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_apply_2(v_inst_126_, v_c_158_, v_c_163_);
v___x_169_ = lean_unbox(v___x_168_);
if (v___x_169_ == 0)
{
uint8_t v___x_170_; 
lean_dec_ref(v_ratHints_166_);
lean_dec_ref(v_rupHints_165_);
lean_dec_ref(v_pivot_164_);
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_rupHints_160_);
lean_dec_ref(v_pivot_159_);
lean_dec_ref(v_inst_127_);
v___x_170_ = lean_unbox(v___x_168_);
return v___x_170_;
}
else
{
lean_object* v_fst_171_; lean_object* v_snd_172_; lean_object* v_fst_173_; lean_object* v_snd_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v_fst_171_ = lean_ctor_get(v_pivot_159_, 0);
lean_inc(v_fst_171_);
v_snd_172_ = lean_ctor_get(v_pivot_159_, 1);
lean_inc(v_snd_172_);
lean_dec_ref(v_pivot_159_);
v_fst_173_ = lean_ctor_get(v_pivot_164_, 0);
lean_inc(v_fst_173_);
v_snd_174_ = lean_ctor_get(v_pivot_164_, 1);
lean_inc(v_snd_174_);
lean_dec_ref(v_pivot_164_);
v___x_175_ = lean_apply_2(v_inst_127_, v_fst_171_, v_fst_173_);
v___x_176_ = lean_unbox(v___x_175_);
if (v___x_176_ == 0)
{
uint8_t v___x_177_; 
lean_dec(v_snd_174_);
lean_dec(v_snd_172_);
lean_dec_ref(v_ratHints_166_);
lean_dec_ref(v_rupHints_165_);
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_rupHints_160_);
v___x_177_ = lean_unbox(v___x_175_);
return v___x_177_;
}
else
{
lean_object* v___f_178_; lean_object* v___f_179_; uint8_t v___x_189_; 
v___f_178_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0));
v___f_179_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__1));
v___x_189_ = lean_unbox(v_snd_174_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; 
v___x_190_ = lean_unbox(v_snd_172_);
lean_dec(v_snd_172_);
if (v___x_190_ == 0)
{
lean_dec(v_snd_174_);
goto v___jp_180_;
}
else
{
uint8_t v___x_191_; 
lean_dec_ref(v_ratHints_166_);
lean_dec_ref(v_rupHints_165_);
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_rupHints_160_);
v___x_191_ = lean_unbox(v_snd_174_);
lean_dec(v_snd_174_);
return v___x_191_;
}
}
else
{
uint8_t v___x_192_; 
lean_dec(v_snd_174_);
v___x_192_ = lean_unbox(v_snd_172_);
if (v___x_192_ == 0)
{
uint8_t v___x_193_; 
lean_dec_ref(v_ratHints_166_);
lean_dec_ref(v_rupHints_165_);
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_rupHints_160_);
v___x_193_ = lean_unbox(v_snd_172_);
lean_dec(v_snd_172_);
return v___x_193_;
}
else
{
lean_dec(v_snd_172_);
goto v___jp_180_;
}
}
v___jp_180_:
{
lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_181_ = lean_array_get_size(v_rupHints_160_);
v___x_182_ = lean_array_get_size(v_rupHints_165_);
v___x_183_ = lean_nat_dec_eq(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_dec_ref(v_ratHints_166_);
lean_dec_ref(v_rupHints_165_);
lean_dec_ref(v_ratHints_161_);
lean_dec_ref(v_rupHints_160_);
return v___x_183_;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = l_Array_isEqvAux___redArg(v_rupHints_160_, v_rupHints_165_, v___f_178_, v___x_181_);
lean_dec_ref(v_rupHints_165_);
lean_dec_ref(v_rupHints_160_);
if (v___x_184_ == 0)
{
lean_dec_ref(v_ratHints_166_);
lean_dec_ref(v_ratHints_161_);
return v___x_184_;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_185_ = lean_array_get_size(v_ratHints_161_);
v___x_186_ = lean_array_get_size(v_ratHints_166_);
v___x_187_ = lean_nat_dec_eq(v___x_185_, v___x_186_);
if (v___x_187_ == 0)
{
lean_dec_ref(v_ratHints_166_);
lean_dec_ref(v_ratHints_161_);
return v___x_187_;
}
else
{
uint8_t v___x_188_; 
v___x_188_ = l_Array_isEqvAux___redArg(v_ratHints_161_, v_ratHints_166_, v___f_179_, v___x_185_);
lean_dec_ref(v_ratHints_166_);
lean_dec_ref(v_ratHints_161_);
return v___x_188_;
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
uint8_t v___x_194_; 
lean_dec_ref_known(v_x_128_, 5);
lean_dec_ref(v_x_129_);
lean_dec_ref(v_inst_127_);
lean_dec_ref(v_inst_126_);
v___x_194_ = 0;
return v___x_194_;
}
}
default: 
{
lean_dec_ref(v_inst_127_);
lean_dec_ref(v_inst_126_);
if (lean_obj_tag(v_x_129_) == 3)
{
lean_object* v_ids_195_; lean_object* v_ids_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_ids_195_ = lean_ctor_get(v_x_128_, 0);
lean_inc_ref(v_ids_195_);
lean_dec_ref_known(v_x_128_, 1);
v_ids_196_ = lean_ctor_get(v_x_129_, 0);
lean_inc_ref(v_ids_196_);
lean_dec_ref_known(v_x_129_, 1);
v___x_197_ = lean_array_get_size(v_ids_195_);
v___x_198_ = lean_array_get_size(v_ids_196_);
v___x_199_ = lean_nat_dec_eq(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
lean_dec_ref(v_ids_196_);
lean_dec_ref(v_ids_195_);
return v___x_199_;
}
else
{
lean_object* v___f_200_; uint8_t v___x_201_; 
v___f_200_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___closed__0));
v___x_201_ = l_Array_isEqvAux___redArg(v_ids_195_, v_ids_196_, v___f_200_, v___x_197_);
lean_dec_ref(v_ids_196_);
lean_dec_ref(v_ids_195_);
return v___x_201_;
}
}
else
{
uint8_t v___x_202_; 
lean_dec_ref_known(v_x_128_, 1);
lean_dec_ref(v_x_129_);
v___x_202_ = 0;
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg___boxed(lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_x_205_, lean_object* v_x_206_){
_start:
{
uint8_t v_res_207_; lean_object* v_r_208_; 
v_res_207_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(v_inst_203_, v_inst_204_, v_x_205_, v_x_206_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq(lean_object* v_00_u03b2_209_, lean_object* v_00_u03b1_210_, lean_object* v_inst_211_, lean_object* v_inst_212_, lean_object* v_x_213_, lean_object* v_x_214_){
_start:
{
uint8_t v___x_215_; 
v___x_215_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___redArg(v_inst_211_, v_inst_212_, v_x_213_, v_x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq___boxed(lean_object* v_00_u03b2_216_, lean_object* v_00_u03b1_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
uint8_t v_res_222_; lean_object* v_r_223_; 
v_res_222_ = l_Std_Tactic_BVDecide_LRAT_instBEqAction_beq(v_00_u03b2_216_, v_00_u03b1_217_, v_inst_218_, v_inst_219_, v_x_220_, v_x_221_);
v_r_223_ = lean_box(v_res_222_);
return v_r_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction___redArg(lean_object* v_inst_224_, lean_object* v_inst_225_){
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instBEqAction(lean_object* v_00_u03b2_227_, lean_object* v_00_u03b1_228_, lean_object* v_inst_229_, lean_object* v_inst_230_){
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
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; 
v___x_239_ = lean_unsigned_to_nat(2u);
v___x_240_ = lean_nat_to_int(v___x_239_);
return v___x_240_;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_unsigned_to_nat(1u);
v___x_242_ = lean_nat_to_int(v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_x_273_, lean_object* v_prec_274_){
_start:
{
lean_object* v___f_275_; 
v___f_275_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__0));
switch(lean_obj_tag(v_x_273_))
{
case 0:
{
lean_object* v_id_276_; lean_object* v_rupHints_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_301_; 
lean_dec_ref(v_inst_272_);
lean_dec_ref(v_inst_271_);
v_id_276_ = lean_ctor_get(v_x_273_, 0);
v_rupHints_277_ = lean_ctor_get(v_x_273_, 1);
v_isSharedCheck_301_ = !lean_is_exclusive(v_x_273_);
if (v_isSharedCheck_301_ == 0)
{
v___x_279_ = v_x_273_;
v_isShared_280_ = v_isSharedCheck_301_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_rupHints_277_);
lean_inc(v_id_276_);
lean_dec(v_x_273_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_301_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___y_282_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(1024u);
v___x_298_ = lean_nat_dec_le(v___x_297_, v_prec_274_);
if (v___x_298_ == 0)
{
lean_object* v___x_299_; 
v___x_299_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_282_ = v___x_299_;
goto v___jp_281_;
}
else
{
lean_object* v___x_300_; 
v___x_300_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_282_ = v___x_300_;
goto v___jp_281_;
}
v___jp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_283_ = lean_box(1);
v___x_284_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__3));
v___x_285_ = l_Nat_reprFast(v_id_276_);
v___x_286_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
if (v_isShared_280_ == 0)
{
lean_ctor_set_tag(v___x_279_, 5);
lean_ctor_set(v___x_279_, 1, v___x_286_);
lean_ctor_set(v___x_279_, 0, v___x_284_);
v___x_288_ = v___x_279_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v___x_286_);
v___x_288_ = v_reuseFailAlloc_296_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_289_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_283_);
v___x_290_ = l_Array_repr___redArg(v___f_275_, v_rupHints_277_);
v___x_291_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
lean_inc(v___y_282_);
v___x_292_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_292_, 0, v___y_282_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = 0;
v___x_294_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_294_, 0, v___x_292_);
lean_ctor_set_uint8(v___x_294_, sizeof(void*)*1, v___x_293_);
v___x_295_ = l_Repr_addAppParen(v___x_294_, v_prec_274_);
return v___x_295_;
}
}
}
}
case 1:
{
lean_object* v_id_302_; lean_object* v_c_303_; lean_object* v_rupHints_304_; lean_object* v___y_306_; lean_object* v___x_323_; uint8_t v___x_324_; 
lean_dec_ref(v_inst_272_);
v_id_302_ = lean_ctor_get(v_x_273_, 0);
lean_inc(v_id_302_);
v_c_303_ = lean_ctor_get(v_x_273_, 1);
lean_inc(v_c_303_);
v_rupHints_304_ = lean_ctor_get(v_x_273_, 2);
lean_inc_ref(v_rupHints_304_);
lean_dec_ref_known(v_x_273_, 3);
v___x_323_ = lean_unsigned_to_nat(1024u);
v___x_324_ = lean_nat_dec_le(v___x_323_, v_prec_274_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
v___x_325_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_306_ = v___x_325_;
goto v___jp_305_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_306_ = v___x_326_;
goto v___jp_305_;
}
v___jp_305_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_307_ = lean_box(1);
v___x_308_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__8));
v___x_309_ = l_Nat_reprFast(v_id_302_);
v___x_310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
v___x_311_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_308_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v___x_307_);
v___x_313_ = lean_unsigned_to_nat(1024u);
v___x_314_ = lean_apply_2(v_inst_271_, v_c_303_, v___x_313_);
v___x_315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_312_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_307_);
v___x_317_ = l_Array_repr___redArg(v___f_275_, v_rupHints_304_);
v___x_318_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
lean_inc(v___y_306_);
v___x_319_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_319_, 0, v___y_306_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = 0;
v___x_321_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set_uint8(v___x_321_, sizeof(void*)*1, v___x_320_);
v___x_322_ = l_Repr_addAppParen(v___x_321_, v_prec_274_);
return v___x_322_;
}
}
case 2:
{
lean_object* v_id_327_; lean_object* v_c_328_; lean_object* v_pivot_329_; lean_object* v_rupHints_330_; lean_object* v_ratHints_331_; lean_object* v___f_332_; lean_object* v___x_333_; lean_object* v___y_335_; lean_object* v___x_358_; uint8_t v___x_359_; 
v_id_327_ = lean_ctor_get(v_x_273_, 0);
lean_inc(v_id_327_);
v_c_328_ = lean_ctor_get(v_x_273_, 1);
lean_inc(v_c_328_);
v_pivot_329_ = lean_ctor_get(v_x_273_, 2);
lean_inc_ref(v_pivot_329_);
v_rupHints_330_ = lean_ctor_get(v_x_273_, 3);
lean_inc_ref(v_rupHints_330_);
v_ratHints_331_ = lean_ctor_get(v_x_273_, 4);
lean_inc_ref(v_ratHints_331_);
lean_dec_ref_known(v_x_273_, 5);
v___f_332_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__11));
v___x_333_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__13));
v___x_358_ = lean_unsigned_to_nat(1024u);
v___x_359_ = lean_nat_dec_le(v___x_358_, v_prec_274_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; 
v___x_360_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_335_ = v___x_360_;
goto v___jp_334_;
}
else
{
lean_object* v___x_361_; 
v___x_361_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_335_ = v___x_361_;
goto v___jp_334_;
}
v___jp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_336_ = lean_box(1);
v___x_337_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__16));
v___x_338_ = l_Nat_reprFast(v_id_327_);
v___x_339_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
v___x_340_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_337_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_336_);
v___x_342_ = lean_unsigned_to_nat(1024u);
v___x_343_ = lean_apply_2(v_inst_271_, v_c_328_, v___x_342_);
v___x_344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_341_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_336_);
v___x_346_ = l_Prod_repr___redArg(v_inst_272_, v___f_332_, v_pivot_329_);
v___x_347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_336_);
v___x_349_ = l_Array_repr___redArg(v___f_275_, v_rupHints_330_);
v___x_350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_336_);
v___x_352_ = l_Array_repr___redArg(v___x_333_, v_ratHints_331_);
v___x_353_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_351_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
lean_inc(v___y_335_);
v___x_354_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_354_, 0, v___y_335_);
lean_ctor_set(v___x_354_, 1, v___x_353_);
v___x_355_ = 0;
v___x_356_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_356_, 0, v___x_354_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*1, v___x_355_);
v___x_357_ = l_Repr_addAppParen(v___x_356_, v_prec_274_);
return v___x_357_;
}
}
default: 
{
lean_object* v_ids_362_; lean_object* v___y_364_; lean_object* v___x_372_; uint8_t v___x_373_; 
lean_dec_ref(v_inst_272_);
lean_dec_ref(v_inst_271_);
v_ids_362_ = lean_ctor_get(v_x_273_, 0);
lean_inc_ref(v_ids_362_);
lean_dec_ref_known(v_x_273_, 1);
v___x_372_ = lean_unsigned_to_nat(1024u);
v___x_373_ = lean_nat_dec_le(v___x_372_, v_prec_274_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
v___x_374_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__4);
v___y_364_ = v___x_374_;
goto v___jp_363_;
}
else
{
lean_object* v___x_375_; 
v___x_375_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5, &l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5_once, _init_l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__5);
v___y_364_ = v___x_375_;
goto v___jp_363_;
}
v___jp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; uint8_t v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_365_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___closed__19));
v___x_366_ = l_Array_repr___redArg(v___f_275_, v_ids_362_);
v___x_367_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_365_);
lean_ctor_set(v___x_367_, 1, v___x_366_);
lean_inc(v___y_364_);
v___x_368_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_368_, 0, v___y_364_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = 0;
v___x_370_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_370_, 0, v___x_368_);
lean_ctor_set_uint8(v___x_370_, sizeof(void*)*1, v___x_369_);
v___x_371_ = l_Repr_addAppParen(v___x_370_, v_prec_274_);
return v___x_371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg___boxed(lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_x_378_, lean_object* v_prec_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(v_inst_376_, v_inst_377_, v_x_378_, v_prec_379_);
lean_dec(v_prec_379_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr(lean_object* v_00_u03b2_381_, lean_object* v_00_u03b1_382_, lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_x_385_, lean_object* v_prec_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___redArg(v_inst_383_, v_inst_384_, v_x_385_, v_prec_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction_repr___boxed(lean_object* v_00_u03b2_388_, lean_object* v_00_u03b1_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_x_392_, lean_object* v_prec_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_Tactic_BVDecide_LRAT_instReprAction_repr(v_00_u03b2_388_, v_00_u03b1_389_, v_inst_390_, v_inst_391_, v_x_392_, v_prec_393_);
lean_dec(v_prec_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction___redArg(lean_object* v_inst_395_, lean_object* v_inst_396_){
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instReprAction(lean_object* v_00_u03b2_398_, lean_object* v_00_u03b1_399_, lean_object* v_inst_400_, lean_object* v_inst_401_){
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg(lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_x_427_){
_start:
{
lean_object* v___f_428_; 
v___f_428_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__0));
switch(lean_obj_tag(v_x_427_))
{
case 0:
{
lean_object* v_id_429_; lean_object* v_rupHints_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec_ref(v_inst_426_);
lean_dec_ref(v_inst_425_);
v_id_429_ = lean_ctor_get(v_x_427_, 0);
lean_inc(v_id_429_);
v_rupHints_430_ = lean_ctor_get(v_x_427_, 1);
lean_inc_ref(v_rupHints_430_);
lean_dec_ref_known(v_x_427_, 2);
v___x_431_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__1));
v___x_432_ = l_Nat_reprFast(v_id_429_);
v___x_433_ = lean_string_append(v___x_431_, v___x_432_);
lean_dec_ref(v___x_432_);
v___x_434_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2));
v___x_435_ = lean_string_append(v___x_433_, v___x_434_);
v___x_436_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_437_ = lean_array_to_list(v_rupHints_430_);
v___x_438_ = l_List_toString___redArg(v___f_428_, v___x_437_);
v___x_439_ = lean_string_append(v___x_436_, v___x_438_);
lean_dec_ref(v___x_438_);
v___x_440_ = lean_string_append(v___x_435_, v___x_439_);
lean_dec_ref(v___x_439_);
v___x_441_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4));
v___x_442_ = lean_string_append(v___x_440_, v___x_441_);
return v___x_442_;
}
case 1:
{
lean_object* v_id_443_; lean_object* v_c_444_; lean_object* v_rupHints_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec_ref(v_inst_426_);
v_id_443_ = lean_ctor_get(v_x_427_, 0);
lean_inc(v_id_443_);
v_c_444_ = lean_ctor_get(v_x_427_, 1);
lean_inc(v_c_444_);
v_rupHints_445_ = lean_ctor_get(v_x_427_, 2);
lean_inc_ref(v_rupHints_445_);
lean_dec_ref_known(v_x_427_, 3);
v___x_446_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__5));
v___x_447_ = lean_apply_1(v_inst_425_, v_c_444_);
v___x_448_ = lean_string_append(v___x_446_, v___x_447_);
lean_dec_ref(v___x_447_);
v___x_449_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__6));
v___x_450_ = lean_string_append(v___x_448_, v___x_449_);
v___x_451_ = l_Nat_reprFast(v_id_443_);
v___x_452_ = lean_string_append(v___x_450_, v___x_451_);
lean_dec_ref(v___x_451_);
v___x_453_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__2));
v___x_454_ = lean_string_append(v___x_452_, v___x_453_);
v___x_455_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_456_ = lean_array_to_list(v_rupHints_445_);
v___x_457_ = l_List_toString___redArg(v___f_428_, v___x_456_);
v___x_458_ = lean_string_append(v___x_455_, v___x_457_);
lean_dec_ref(v___x_457_);
v___x_459_ = lean_string_append(v___x_454_, v___x_458_);
lean_dec_ref(v___x_458_);
v___x_460_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4));
v___x_461_ = lean_string_append(v___x_459_, v___x_460_);
return v___x_461_;
}
case 2:
{
lean_object* v_pivot_462_; lean_object* v_id_463_; lean_object* v_c_464_; lean_object* v_rupHints_465_; lean_object* v_ratHints_466_; lean_object* v_fst_467_; lean_object* v_snd_468_; lean_object* v___f_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___y_485_; uint8_t v___x_504_; 
v_pivot_462_ = lean_ctor_get(v_x_427_, 2);
lean_inc_ref(v_pivot_462_);
v_id_463_ = lean_ctor_get(v_x_427_, 0);
lean_inc(v_id_463_);
v_c_464_ = lean_ctor_get(v_x_427_, 1);
lean_inc(v_c_464_);
v_rupHints_465_ = lean_ctor_get(v_x_427_, 3);
lean_inc_ref(v_rupHints_465_);
v_ratHints_466_ = lean_ctor_get(v_x_427_, 4);
lean_inc_ref(v_ratHints_466_);
lean_dec_ref_known(v_x_427_, 5);
v_fst_467_ = lean_ctor_get(v_pivot_462_, 0);
lean_inc(v_fst_467_);
v_snd_468_ = lean_ctor_get(v_pivot_462_, 1);
lean_inc(v_snd_468_);
lean_dec_ref(v_pivot_462_);
v___f_469_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__8));
v___x_470_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__9));
v___x_471_ = lean_apply_1(v_inst_425_, v_c_464_);
v___x_472_ = lean_string_append(v___x_470_, v___x_471_);
lean_dec_ref(v___x_471_);
v___x_473_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__10));
v___x_474_ = lean_string_append(v___x_472_, v___x_473_);
v___x_475_ = l_Nat_reprFast(v_id_463_);
v___x_476_ = lean_string_append(v___x_474_, v___x_475_);
lean_dec_ref(v___x_475_);
v___x_477_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__11));
v___x_478_ = lean_string_append(v___x_476_, v___x_477_);
v___x_479_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__12));
v___x_480_ = lean_apply_1(v_inst_426_, v_fst_467_);
v___x_481_ = lean_string_append(v___x_479_, v___x_480_);
lean_dec_ref(v___x_480_);
v___x_482_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__13));
v___x_483_ = lean_string_append(v___x_481_, v___x_482_);
v___x_504_ = lean_unbox(v_snd_468_);
lean_dec(v_snd_468_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; 
v___x_505_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__16));
v___y_485_ = v___x_505_;
goto v___jp_484_;
}
else
{
lean_object* v___x_506_; 
v___x_506_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__17));
v___y_485_ = v___x_506_;
goto v___jp_484_;
}
v___jp_484_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_486_ = lean_string_append(v___x_483_, v___y_485_);
v___x_487_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__4));
v___x_488_ = lean_string_append(v___x_486_, v___x_487_);
v___x_489_ = lean_string_append(v___x_478_, v___x_488_);
lean_dec_ref(v___x_488_);
v___x_490_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__14));
v___x_491_ = lean_string_append(v___x_489_, v___x_490_);
v___x_492_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_493_ = lean_array_to_list(v_rupHints_465_);
v___x_494_ = l_List_toString___redArg(v___f_428_, v___x_493_);
v___x_495_ = lean_string_append(v___x_492_, v___x_494_);
lean_dec_ref(v___x_494_);
v___x_496_ = lean_string_append(v___x_491_, v___x_495_);
lean_dec_ref(v___x_495_);
v___x_497_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__15));
v___x_498_ = lean_string_append(v___x_496_, v___x_497_);
v___x_499_ = lean_array_to_list(v_ratHints_466_);
v___x_500_ = l_List_toString___redArg(v___f_469_, v___x_499_);
v___x_501_ = lean_string_append(v___x_492_, v___x_500_);
lean_dec_ref(v___x_500_);
v___x_502_ = lean_string_append(v___x_498_, v___x_501_);
lean_dec_ref(v___x_501_);
v___x_503_ = lean_string_append(v___x_502_, v___x_487_);
return v___x_503_;
}
}
default: 
{
lean_object* v_ids_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec_ref(v_inst_426_);
lean_dec_ref(v_inst_425_);
v_ids_507_ = lean_ctor_get(v_x_427_, 0);
lean_inc_ref(v_ids_507_);
lean_dec_ref_known(v_x_427_, 1);
v___x_508_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__18));
v___x_509_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg___closed__3));
v___x_510_ = lean_array_to_list(v_ids_507_);
v___x_511_ = l_List_toString___redArg(v___f_428_, v___x_510_);
v___x_512_ = lean_string_append(v___x_509_, v___x_511_);
lean_dec_ref(v___x_511_);
v___x_513_ = lean_string_append(v___x_508_, v___x_512_);
lean_dec_ref(v___x_512_);
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Action_toString(lean_object* v_00_u03b2_514_, lean_object* v_00_u03b1_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_x_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_Tactic_BVDecide_LRAT_Action_toString___redArg(v_inst_516_, v_inst_517_, v_x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instToStringAction___redArg(lean_object* v_inst_520_, lean_object* v_inst_521_){
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_instToStringAction(lean_object* v_00_u03b2_523_, lean_object* v_00_u03b1_524_, lean_object* v_inst_525_, lean_object* v_inst_526_){
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
