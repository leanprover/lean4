// Lean compiler output
// Module: Lean.Declaration
// Imports: public import Lean.Expr import Init.Data.Ord.UInt import Init.Data.ToString.Macro
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
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_List_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorElim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_opaque_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_opaque_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_opaque_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_opaque_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_abbrev_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_abbrev_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_abbrev_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_abbrev_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_regular_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_regular_elim___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_regular_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_regular_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedReducibilityHints_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedReducibilityHints;
LEAN_EXPORT uint8_t l_Lean_instBEqReducibilityHints_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqReducibilityHints_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqReducibilityHints___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqReducibilityHints_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqReducibilityHints___closed__0 = (const lean_object*)&l_Lean_instBEqReducibilityHints___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqReducibilityHints = (const lean_object*)&l_Lean_instBEqReducibilityHints___closed__0_value;
LEAN_EXPORT uint32_t lean_reducibility_hints_get_height(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_getHeightEx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_compare(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_compare___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_ReducibilityHints_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ReducibilityHints_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ReducibilityHints_instOrd___closed__0 = (const lean_object*)&l_Lean_ReducibilityHints_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_ReducibilityHints_instOrd = (const lean_object*)&l_Lean_ReducibilityHints_instOrd___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_isAbbrev(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_isAbbrev___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_isRegular(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_isRegular___boxed(lean_object*);
static const lean_string_object l_Lean_instInhabitedConstantVal_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_instInhabitedConstantVal_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedConstantVal_default___closed__0_value;
static const lean_ctor_object l_Lean_instInhabitedConstantVal_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instInhabitedConstantVal_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_instInhabitedConstantVal_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedConstantVal_default___closed__1_value;
static lean_once_cell_t l_Lean_instInhabitedConstantVal_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedConstantVal_default___closed__2;
static lean_once_cell_t l_Lean_instInhabitedConstantVal_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedConstantVal_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstantVal_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstantVal;
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqConstantVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqConstantVal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqConstantVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqConstantVal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqConstantVal___closed__0 = (const lean_object*)&l_Lean_instBEqConstantVal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqConstantVal = (const lean_object*)&l_Lean_instBEqConstantVal___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedAxiomVal_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedAxiomVal_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAxiomVal_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedAxiomVal;
LEAN_EXPORT uint8_t l_Lean_instBEqAxiomVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqAxiomVal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqAxiomVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqAxiomVal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqAxiomVal___closed__0 = (const lean_object*)&l_Lean_instBEqAxiomVal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqAxiomVal = (const lean_object*)&l_Lean_instBEqAxiomVal___closed__0_value;
LEAN_EXPORT lean_object* lean_mk_axiom_val(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkAxiomValEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_axiom_val_is_unsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AxiomVal_isUnsafeEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedDefinitionSafety_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedDefinitionSafety;
LEAN_EXPORT uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionSafety_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqDefinitionSafety___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqDefinitionSafety_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqDefinitionSafety___closed__0 = (const lean_object*)&l_Lean_instBEqDefinitionSafety___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqDefinitionSafety = (const lean_object*)&l_Lean_instBEqDefinitionSafety___closed__0_value;
static const lean_string_object l_Lean_instReprDefinitionSafety_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.DefinitionSafety.unsafe"};
static const lean_object* l_Lean_instReprDefinitionSafety_repr___closed__0 = (const lean_object*)&l_Lean_instReprDefinitionSafety_repr___closed__0_value;
static const lean_ctor_object l_Lean_instReprDefinitionSafety_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDefinitionSafety_repr___closed__0_value)}};
static const lean_object* l_Lean_instReprDefinitionSafety_repr___closed__1 = (const lean_object*)&l_Lean_instReprDefinitionSafety_repr___closed__1_value;
static const lean_string_object l_Lean_instReprDefinitionSafety_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Lean.DefinitionSafety.safe"};
static const lean_object* l_Lean_instReprDefinitionSafety_repr___closed__2 = (const lean_object*)&l_Lean_instReprDefinitionSafety_repr___closed__2_value;
static const lean_ctor_object l_Lean_instReprDefinitionSafety_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDefinitionSafety_repr___closed__2_value)}};
static const lean_object* l_Lean_instReprDefinitionSafety_repr___closed__3 = (const lean_object*)&l_Lean_instReprDefinitionSafety_repr___closed__3_value;
static const lean_string_object l_Lean_instReprDefinitionSafety_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Lean.DefinitionSafety.partial"};
static const lean_object* l_Lean_instReprDefinitionSafety_repr___closed__4 = (const lean_object*)&l_Lean_instReprDefinitionSafety_repr___closed__4_value;
static const lean_ctor_object l_Lean_instReprDefinitionSafety_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprDefinitionSafety_repr___closed__4_value)}};
static const lean_object* l_Lean_instReprDefinitionSafety_repr___closed__5 = (const lean_object*)&l_Lean_instReprDefinitionSafety_repr___closed__5_value;
static lean_once_cell_t l_Lean_instReprDefinitionSafety_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprDefinitionSafety_repr___closed__6;
static lean_once_cell_t l_Lean_instReprDefinitionSafety_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprDefinitionSafety_repr___closed__7;
LEAN_EXPORT lean_object* l_Lean_instReprDefinitionSafety_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprDefinitionSafety_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprDefinitionSafety___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprDefinitionSafety_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprDefinitionSafety___closed__0 = (const lean_object*)&l_Lean_instReprDefinitionSafety___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprDefinitionSafety = (const lean_object*)&l_Lean_instReprDefinitionSafety___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedDefinitionVal_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedDefinitionVal_default___closed__0;
static const lean_ctor_object l_Lean_instInhabitedDefinitionVal_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedDefinitionVal_default___closed__1 = (const lean_object*)&l_Lean_instInhabitedDefinitionVal_default___closed__1_value;
static lean_once_cell_t l_Lean_instInhabitedDefinitionVal_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedDefinitionVal_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDefinitionVal_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDefinitionVal;
LEAN_EXPORT uint8_t l_Lean_instBEqDefinitionVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionVal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqDefinitionVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqDefinitionVal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqDefinitionVal___closed__0 = (const lean_object*)&l_Lean_instBEqDefinitionVal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqDefinitionVal = (const lean_object*)&l_Lean_instBEqDefinitionVal___closed__0_value;
LEAN_EXPORT lean_object* lean_mk_definition_val(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_definition_val_get_safety(lean_object*);
LEAN_EXPORT lean_object* l_Lean_DefinitionVal_getSafetyEx___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedTheoremVal_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedTheoremVal_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTheoremVal_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedTheoremVal;
LEAN_EXPORT uint8_t l_Lean_instBEqTheoremVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqTheoremVal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqTheoremVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqTheoremVal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqTheoremVal___closed__0 = (const lean_object*)&l_Lean_instBEqTheoremVal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqTheoremVal = (const lean_object*)&l_Lean_instBEqTheoremVal___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedOpaqueVal_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedOpaqueVal_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedOpaqueVal_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedOpaqueVal;
LEAN_EXPORT uint8_t l_Lean_instBEqOpaqueVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqOpaqueVal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqOpaqueVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqOpaqueVal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqOpaqueVal___closed__0 = (const lean_object*)&l_Lean_instBEqOpaqueVal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqOpaqueVal = (const lean_object*)&l_Lean_instBEqOpaqueVal___closed__0_value;
LEAN_EXPORT uint8_t lean_opaque_val_is_unsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_OpaqueVal_isUnsafeEx___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedConstructor_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedConstructor_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedConstructor_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedConstructor_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstructor_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstructor;
LEAN_EXPORT uint8_t l_Lean_instBEqConstructor_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqConstructor_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqConstructor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqConstructor_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqConstructor___closed__0 = (const lean_object*)&l_Lean_instBEqConstructor___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqConstructor = (const lean_object*)&l_Lean_instBEqConstructor___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedInductiveType_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedInductiveType_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedInductiveType_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedInductiveType;
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveType_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveType_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqInductiveType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqInductiveType_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqInductiveType___closed__0 = (const lean_object*)&l_Lean_instBEqInductiveType___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqInductiveType = (const lean_object*)&l_Lean_instBEqInductiveType___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedDeclaration_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedDeclaration_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclaration_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedDeclaration;
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqDeclaration_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqDeclaration_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqDeclaration___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqDeclaration_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqDeclaration___closed__0 = (const lean_object*)&l_Lean_instBEqDeclaration___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqDeclaration = (const lean_object*)&l_Lean_instBEqDeclaration___closed__0_value;
LEAN_EXPORT lean_object* lean_mk_inductive_decl(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkInductiveDeclEs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_is_unsafe_inductive_decl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_isUnsafeInductiveDeclEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_Declaration_definitionVal_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.Declaration"};
static const lean_object* l_Lean_Declaration_definitionVal_x21___closed__0 = (const lean_object*)&l_Lean_Declaration_definitionVal_x21___closed__0_value;
static const lean_string_object l_Lean_Declaration_definitionVal_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.Declaration.definitionVal!"};
static const lean_object* l_Lean_Declaration_definitionVal_x21___closed__1 = (const lean_object*)&l_Lean_Declaration_definitionVal_x21___closed__1_value;
static const lean_string_object l_Lean_Declaration_definitionVal_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Expected a `Declaration.defnDecl`."};
static const lean_object* l_Lean_Declaration_definitionVal_x21___closed__2 = (const lean_object*)&l_Lean_Declaration_definitionVal_x21___closed__2_value;
static lean_once_cell_t l_Lean_Declaration_definitionVal_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Declaration_definitionVal_x21___closed__3;
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Declaration_getTopLevelNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l_Lean_Declaration_getTopLevelNames___closed__0 = (const lean_object*)&l_Lean_Declaration_getTopLevelNames___closed__0_value;
static const lean_ctor_object l_Lean_Declaration_getTopLevelNames___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Declaration_getTopLevelNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_object* l_Lean_Declaration_getTopLevelNames___closed__1 = (const lean_object*)&l_Lean_Declaration_getTopLevelNames___closed__1_value;
static const lean_ctor_object l_Lean_Declaration_getTopLevelNames___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Declaration_getTopLevelNames___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Declaration_getTopLevelNames___closed__2 = (const lean_object*)&l_Lean_Declaration_getTopLevelNames___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Declaration_getTopLevelNames(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 106, 38, 217, 182, 144, 186, 220)}};
static const lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(lean_object*, lean_object*);
static const lean_string_object l_Lean_Declaration_getNames___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Declaration_getNames___closed__0 = (const lean_object*)&l_Lean_Declaration_getNames___closed__0_value;
static const lean_ctor_object l_Lean_Declaration_getNames___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Declaration_getTopLevelNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_Lean_Declaration_getNames___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Declaration_getNames___closed__1_value_aux_0),((lean_object*)&l_Lean_Declaration_getNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 113, 137, 82, 82, 132, 58, 248)}};
static const lean_object* l_Lean_Declaration_getNames___closed__1 = (const lean_object*)&l_Lean_Declaration_getNames___closed__1_value;
static const lean_string_object l_Lean_Declaration_getNames___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l_Lean_Declaration_getNames___closed__2 = (const lean_object*)&l_Lean_Declaration_getNames___closed__2_value;
static const lean_ctor_object l_Lean_Declaration_getNames___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Declaration_getTopLevelNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_Lean_Declaration_getNames___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Declaration_getNames___closed__3_value_aux_0),((lean_object*)&l_Lean_Declaration_getNames___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 125, 38, 34, 222, 200, 201, 80)}};
static const lean_object* l_Lean_Declaration_getNames___closed__3 = (const lean_object*)&l_Lean_Declaration_getNames___closed__3_value;
static const lean_string_object l_Lean_Declaration_getNames___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ind"};
static const lean_object* l_Lean_Declaration_getNames___closed__4 = (const lean_object*)&l_Lean_Declaration_getNames___closed__4_value;
static const lean_ctor_object l_Lean_Declaration_getNames___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Declaration_getTopLevelNames___closed__0_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_Lean_Declaration_getNames___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Declaration_getNames___closed__5_value_aux_0),((lean_object*)&l_Lean_Declaration_getNames___closed__4_value),LEAN_SCALAR_PTR_LITERAL(150, 213, 121, 152, 109, 27, 137, 60)}};
static const lean_object* l_Lean_Declaration_getNames___closed__5 = (const lean_object*)&l_Lean_Declaration_getNames___closed__5_value;
static const lean_ctor_object l_Lean_Declaration_getNames___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Declaration_getNames___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Declaration_getNames___closed__6 = (const lean_object*)&l_Lean_Declaration_getNames___closed__6_value;
static const lean_ctor_object l_Lean_Declaration_getNames___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Declaration_getNames___closed__3_value),((lean_object*)&l_Lean_Declaration_getNames___closed__6_value)}};
static const lean_object* l_Lean_Declaration_getNames___closed__7 = (const lean_object*)&l_Lean_Declaration_getNames___closed__7_value;
static const lean_ctor_object l_Lean_Declaration_getNames___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Declaration_getNames___closed__1_value),((lean_object*)&l_Lean_Declaration_getNames___closed__7_value)}};
static const lean_object* l_Lean_Declaration_getNames___closed__8 = (const lean_object*)&l_Lean_Declaration_getNames___closed__8_value;
static const lean_ctor_object l_Lean_Declaration_getNames___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Declaration_getTopLevelNames___closed__1_value),((lean_object*)&l_Lean_Declaration_getNames___closed__8_value)}};
static const lean_object* l_Lean_Declaration_getNames___closed__9 = (const lean_object*)&l_Lean_Declaration_getNames___closed__9_value;
static const lean_array_object l_Lean_Declaration_getNames___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Declaration_getNames___closed__10 = (const lean_object*)&l_Lean_Declaration_getNames___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Declaration_getNames(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedInductiveVal_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedInductiveVal_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedInductiveVal_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedInductiveVal;
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveVal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqInductiveVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqInductiveVal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqInductiveVal___closed__0 = (const lean_object*)&l_Lean_instBEqInductiveVal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqInductiveVal = (const lean_object*)&l_Lean_instBEqInductiveVal___closed__0_value;
LEAN_EXPORT lean_object* lean_mk_inductive_val(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkInductiveValEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_inductive_val_is_rec(lean_object*);
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isRecEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_inductive_val_is_unsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isUnsafeEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_inductive_val_is_reflexive(lean_object*);
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isReflexiveEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_InductiveVal_isNested(lean_object*);
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isNested___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedConstructorVal_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedConstructorVal_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstructorVal_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstructorVal;
LEAN_EXPORT uint8_t l_Lean_instBEqConstructorVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqConstructorVal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqConstructorVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqConstructorVal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqConstructorVal___closed__0 = (const lean_object*)&l_Lean_instBEqConstructorVal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqConstructorVal = (const lean_object*)&l_Lean_instBEqConstructorVal___closed__0_value;
LEAN_EXPORT lean_object* lean_mk_constructor_val(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkConstructorValEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_constructor_val_is_unsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstructorVal_isUnsafeEx___boxed(lean_object*);
static lean_once_cell_t l_Lean_instInhabitedRecursorRule_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedRecursorRule_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedRecursorRule_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedRecursorRule;
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorRule_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorRule_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqRecursorRule___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqRecursorRule_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqRecursorRule___closed__0 = (const lean_object*)&l_Lean_instBEqRecursorRule___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqRecursorRule = (const lean_object*)&l_Lean_instBEqRecursorRule___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedRecursorVal_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedRecursorVal_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedRecursorVal_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedRecursorVal;
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorVal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqRecursorVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqRecursorVal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqRecursorVal___closed__0 = (const lean_object*)&l_Lean_instBEqRecursorVal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqRecursorVal = (const lean_object*)&l_Lean_instBEqRecursorVal___closed__0_value;
LEAN_EXPORT lean_object* lean_mk_recursor_val(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkRecursorValEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_recursor_k(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RecursorVal_kEx___boxed(lean_object*);
LEAN_EXPORT uint8_t lean_recursor_is_unsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RecursorVal_isUnsafeEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorInduct(lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instInhabitedQuotKind_default;
LEAN_EXPORT uint8_t l_Lean_instInhabitedQuotKind;
LEAN_EXPORT uint8_t l_Lean_instBEqQuotKind_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instBEqQuotKind_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqQuotKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqQuotKind_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqQuotKind___closed__0 = (const lean_object*)&l_Lean_instBEqQuotKind___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqQuotKind = (const lean_object*)&l_Lean_instBEqQuotKind___closed__0_value;
static lean_once_cell_t l_Lean_instInhabitedQuotVal_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedQuotVal_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedQuotVal_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedQuotVal;
LEAN_EXPORT uint8_t l_Lean_instBEqQuotVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqQuotVal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqQuotVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqQuotVal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqQuotVal___closed__0 = (const lean_object*)&l_Lean_instBEqQuotVal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqQuotVal = (const lean_object*)&l_Lean_instBEqQuotVal___closed__0_value;
LEAN_EXPORT lean_object* lean_mk_quot_val(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkQuotValEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedConstantInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedConstantInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstantInfo_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstantInfo;
LEAN_EXPORT uint8_t l_Lean_instBEqConstantInfo_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqConstantInfo_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqConstantInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqConstantInfo_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqConstantInfo___closed__0 = (const lean_object*)&l_Lean_instBEqConstantInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqConstantInfo = (const lean_object*)&l_Lean_instBEqConstantInfo___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isUnsafe___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isPartial(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isPartial___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_ConstantInfo_value_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Lean.ConstantInfo.value!"};
static const lean_object* l_Lean_ConstantInfo_value_x21___closed__0 = (const lean_object*)&l_Lean_ConstantInfo_value_x21___closed__0_value;
static const lean_string_object l_Lean_ConstantInfo_value_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "declaration with value expected"};
static const lean_object* l_Lean_ConstantInfo_value_x21___closed__1 = (const lean_object*)&l_Lean_ConstantInfo_value_x21___closed__1_value;
static lean_once_cell_t l_Lean_ConstantInfo_value_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ConstantInfo_value_x21___closed__2;
static lean_once_cell_t l_Lean_ConstantInfo_value_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ConstantInfo_value_x21___closed__3;
static const lean_string_object l_Lean_ConstantInfo_value_x21___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "declaration with value expected, but "};
static const lean_object* l_Lean_ConstantInfo_value_x21___closed__4 = (const lean_object*)&l_Lean_ConstantInfo_value_x21___closed__4_value;
static const lean_string_object l_Lean_ConstantInfo_value_x21___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " has none"};
static const lean_object* l_Lean_ConstantInfo_value_x21___closed__5 = (const lean_object*)&l_Lean_ConstantInfo_value_x21___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isCtor(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isCtor___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isAxiom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isAxiom___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isInductive(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isInductive___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isDefinition(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isDefinition___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isTheorem(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isTheorem___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(lean_object*);
static const lean_string_object l_Lean_ConstantInfo_inductiveVal_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Lean.ConstantInfo.inductiveVal!"};
static const lean_object* l_Lean_ConstantInfo_inductiveVal_x21___closed__0 = (const lean_object*)&l_Lean_ConstantInfo_inductiveVal_x21___closed__0_value;
static const lean_string_object l_Lean_ConstantInfo_inductiveVal_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Expected a `ConstantInfo.inductInfo`."};
static const lean_object* l_Lean_ConstantInfo_inductiveVal_x21___closed__1 = (const lean_object*)&l_Lean_ConstantInfo_inductiveVal_x21___closed__1_value;
static lean_once_cell_t l_Lean_ConstantInfo_inductiveVal_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ConstantInfo_inductiveVal_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkRecName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_ReducibilityHints_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 2)
{
uint32_t v_a_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_a_7_ = lean_ctor_get_uint32(v_t_5_, 0);
v___x_8_ = lean_box_uint32(v_a_7_);
v___x_9_ = lean_apply_1(v_k_6_, v___x_8_);
return v___x_9_;
}
else
{
return v_k_6_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorElim___redArg___boxed(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_10_, v_k_11_);
lean_dec(v_t_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_ReducibilityHints_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_t_21_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_opaque_elim___redArg(lean_object* v_t_25_, lean_object* v_opaque_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_25_, v_opaque_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_opaque_elim___redArg___boxed(lean_object* v_t_28_, lean_object* v_opaque_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_ReducibilityHints_opaque_elim___redArg(v_t_28_, v_opaque_29_);
lean_dec(v_t_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_opaque_elim(lean_object* v_motive_31_, lean_object* v_t_32_, lean_object* v_h_33_, lean_object* v_opaque_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_32_, v_opaque_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_opaque_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_opaque_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_ReducibilityHints_opaque_elim(v_motive_36_, v_t_37_, v_h_38_, v_opaque_39_);
lean_dec(v_t_37_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_abbrev_elim___redArg(lean_object* v_t_41_, lean_object* v_abbrev_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_41_, v_abbrev_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_abbrev_elim___redArg___boxed(lean_object* v_t_44_, lean_object* v_abbrev_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_ReducibilityHints_abbrev_elim___redArg(v_t_44_, v_abbrev_45_);
lean_dec(v_t_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_abbrev_elim(lean_object* v_motive_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_abbrev_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_48_, v_abbrev_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_abbrev_elim___boxed(lean_object* v_motive_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_abbrev_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_ReducibilityHints_abbrev_elim(v_motive_52_, v_t_53_, v_h_54_, v_abbrev_55_);
lean_dec(v_t_53_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_regular_elim___redArg(lean_object* v_t_57_, lean_object* v_regular_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_57_, v_regular_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_regular_elim___redArg___boxed(lean_object* v_t_60_, lean_object* v_regular_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_ReducibilityHints_regular_elim___redArg(v_t_60_, v_regular_61_);
lean_dec(v_t_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_regular_elim(lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_regular_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_64_, v_regular_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_regular_elim___boxed(lean_object* v_motive_68_, lean_object* v_t_69_, lean_object* v_h_70_, lean_object* v_regular_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_ReducibilityHints_regular_elim(v_motive_68_, v_t_69_, v_h_70_, v_regular_71_);
lean_dec(v_t_69_);
return v_res_72_;
}
}
static lean_object* _init_l_Lean_instInhabitedReducibilityHints_default(void){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_box(0);
return v___x_73_;
}
}
static lean_object* _init_l_Lean_instInhabitedReducibilityHints(void){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = lean_box(0);
return v___x_74_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqReducibilityHints_beq(lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
switch(lean_obj_tag(v_x_75_))
{
case 0:
{
if (lean_obj_tag(v_x_76_) == 0)
{
uint8_t v___x_77_; 
v___x_77_ = 1;
return v___x_77_;
}
else
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
case 1:
{
if (lean_obj_tag(v_x_76_) == 1)
{
uint8_t v___x_79_; 
v___x_79_ = 1;
return v___x_79_;
}
else
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
default: 
{
if (lean_obj_tag(v_x_76_) == 2)
{
uint32_t v_a_81_; uint32_t v_a_82_; uint8_t v___x_83_; 
v_a_81_ = lean_ctor_get_uint32(v_x_75_, 0);
v_a_82_ = lean_ctor_get_uint32(v_x_76_, 0);
v___x_83_ = lean_uint32_dec_eq(v_a_81_, v_a_82_);
return v___x_83_;
}
else
{
uint8_t v___x_84_; 
v___x_84_ = 0;
return v___x_84_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqReducibilityHints_beq___boxed(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Lean_instBEqReducibilityHints_beq(v_x_85_, v_x_86_);
lean_dec(v_x_86_);
lean_dec(v_x_85_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT uint32_t lean_reducibility_hints_get_height(lean_object* v_h_91_){
_start:
{
if (lean_obj_tag(v_h_91_) == 2)
{
uint32_t v_a_92_; 
v_a_92_ = lean_ctor_get_uint32(v_h_91_, 0);
lean_dec_ref_known(v_h_91_, 0);
return v_a_92_;
}
else
{
uint32_t v___x_93_; 
lean_dec(v_h_91_);
v___x_93_ = 0;
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_getHeightEx___boxed(lean_object* v_h_94_){
_start:
{
uint32_t v_res_95_; lean_object* v_r_96_; 
v_res_95_ = lean_reducibility_hints_get_height(v_h_94_);
v_r_96_ = lean_box_uint32(v_res_95_);
return v_r_96_;
}
}
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_lt(lean_object* v_x_97_, lean_object* v_x_98_){
_start:
{
switch(lean_obj_tag(v_x_97_))
{
case 1:
{
if (lean_obj_tag(v_x_98_) == 1)
{
uint8_t v___x_99_; 
v___x_99_ = 0;
return v___x_99_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = 1;
return v___x_100_;
}
}
case 2:
{
switch(lean_obj_tag(v_x_98_))
{
case 2:
{
uint32_t v_a_101_; uint32_t v_a_102_; uint8_t v___x_103_; 
v_a_101_ = lean_ctor_get_uint32(v_x_97_, 0);
v_a_102_ = lean_ctor_get_uint32(v_x_98_, 0);
v___x_103_ = lean_uint32_dec_lt(v_a_102_, v_a_101_);
return v___x_103_;
}
case 0:
{
uint8_t v___x_104_; 
v___x_104_ = 1;
return v___x_104_;
}
default: 
{
uint8_t v___x_105_; 
v___x_105_ = 0;
return v___x_105_;
}
}
}
default: 
{
uint8_t v___x_106_; 
v___x_106_ = 0;
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_lt___boxed(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = l_Lean_ReducibilityHints_lt(v_x_107_, v_x_108_);
lean_dec(v_x_108_);
lean_dec(v_x_107_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_compare(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
switch(lean_obj_tag(v_x_111_))
{
case 0:
{
if (lean_obj_tag(v_x_112_) == 0)
{
uint8_t v___x_113_; 
v___x_113_ = 1;
return v___x_113_;
}
else
{
uint8_t v___x_114_; 
v___x_114_ = 2;
return v___x_114_;
}
}
case 1:
{
if (lean_obj_tag(v_x_112_) == 1)
{
uint8_t v___x_115_; 
v___x_115_ = 1;
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
}
default: 
{
switch(lean_obj_tag(v_x_112_))
{
case 0:
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
case 1:
{
uint8_t v___x_118_; 
v___x_118_ = 2;
return v___x_118_;
}
default: 
{
uint32_t v_a_119_; uint32_t v_a_120_; uint8_t v___x_121_; 
v_a_119_ = lean_ctor_get_uint32(v_x_111_, 0);
v_a_120_ = lean_ctor_get_uint32(v_x_112_, 0);
v___x_121_ = lean_uint32_dec_lt(v_a_120_, v_a_119_);
if (v___x_121_ == 0)
{
uint8_t v___x_122_; 
v___x_122_ = lean_uint32_dec_eq(v_a_120_, v_a_119_);
if (v___x_122_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 2;
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 1;
return v___x_124_;
}
}
else
{
uint8_t v___x_125_; 
v___x_125_ = 0;
return v___x_125_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_compare___boxed(lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = l_Lean_ReducibilityHints_compare(v_x_126_, v_x_127_);
lean_dec(v_x_127_);
lean_dec(v_x_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_isAbbrev(lean_object* v_x_132_){
_start:
{
if (lean_obj_tag(v_x_132_) == 1)
{
uint8_t v___x_133_; 
v___x_133_ = 1;
return v___x_133_;
}
else
{
uint8_t v___x_134_; 
v___x_134_ = 0;
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_isAbbrev___boxed(lean_object* v_x_135_){
_start:
{
uint8_t v_res_136_; lean_object* v_r_137_; 
v_res_136_ = l_Lean_ReducibilityHints_isAbbrev(v_x_135_);
lean_dec(v_x_135_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_isRegular(lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_138_) == 2)
{
uint8_t v___x_139_; 
v___x_139_ = 1;
return v___x_139_;
}
else
{
uint8_t v___x_140_; 
v___x_140_ = 0;
return v___x_140_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_isRegular___boxed(lean_object* v_x_141_){
_start:
{
uint8_t v_res_142_; lean_object* v_r_143_; 
v_res_142_ = l_Lean_ReducibilityHints_isRegular(v_x_141_);
lean_dec(v_x_141_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal_default___closed__2(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_147_ = lean_box(0);
v___x_148_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_149_ = l_Lean_Expr_const___override(v___x_148_, v___x_147_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal_default___closed__3(void){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_150_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__2, &l_Lean_instInhabitedConstantVal_default___closed__2_once, _init_l_Lean_instInhabitedConstantVal_default___closed__2);
v___x_151_ = lean_box(0);
v___x_152_ = lean_box(0);
v___x_153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_151_);
lean_ctor_set(v___x_153_, 2, v___x_150_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal_default(void){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__3, &l_Lean_instInhabitedConstantVal_default___closed__3_once, _init_l_Lean_instInhabitedConstantVal_default___closed__3);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal(void){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_instInhabitedConstantVal_default;
return v___x_155_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
if (lean_obj_tag(v_x_157_) == 0)
{
uint8_t v___x_158_; 
v___x_158_ = 1;
return v___x_158_;
}
else
{
uint8_t v___x_159_; 
v___x_159_ = 0;
return v___x_159_;
}
}
else
{
if (lean_obj_tag(v_x_157_) == 0)
{
uint8_t v___x_160_; 
v___x_160_ = 0;
return v___x_160_;
}
else
{
lean_object* v_head_161_; lean_object* v_tail_162_; lean_object* v_head_163_; lean_object* v_tail_164_; uint8_t v___x_165_; 
v_head_161_ = lean_ctor_get(v_x_156_, 0);
v_tail_162_ = lean_ctor_get(v_x_156_, 1);
v_head_163_ = lean_ctor_get(v_x_157_, 0);
v_tail_164_ = lean_ctor_get(v_x_157_, 1);
v___x_165_ = lean_name_eq(v_head_161_, v_head_163_);
if (v___x_165_ == 0)
{
return v___x_165_;
}
else
{
v_x_156_ = v_tail_162_;
v_x_157_ = v_tail_164_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0___boxed(lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
uint8_t v_res_169_; lean_object* v_r_170_; 
v_res_169_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_x_167_, v_x_168_);
lean_dec(v_x_168_);
lean_dec(v_x_167_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstantVal_beq(lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
lean_object* v_name_173_; lean_object* v_levelParams_174_; lean_object* v_type_175_; lean_object* v_name_176_; lean_object* v_levelParams_177_; lean_object* v_type_178_; uint8_t v___x_179_; 
v_name_173_ = lean_ctor_get(v_x_171_, 0);
v_levelParams_174_ = lean_ctor_get(v_x_171_, 1);
v_type_175_ = lean_ctor_get(v_x_171_, 2);
v_name_176_ = lean_ctor_get(v_x_172_, 0);
v_levelParams_177_ = lean_ctor_get(v_x_172_, 1);
v_type_178_ = lean_ctor_get(v_x_172_, 2);
v___x_179_ = lean_name_eq(v_name_173_, v_name_176_);
if (v___x_179_ == 0)
{
return v___x_179_;
}
else
{
uint8_t v___x_180_; 
v___x_180_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_levelParams_174_, v_levelParams_177_);
if (v___x_180_ == 0)
{
return v___x_180_;
}
else
{
uint8_t v___x_181_; 
v___x_181_ = lean_expr_eqv(v_type_175_, v_type_178_);
return v___x_181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstantVal_beq___boxed(lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
uint8_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Lean_instBEqConstantVal_beq(v_x_182_, v_x_183_);
lean_dec_ref(v_x_183_);
lean_dec_ref(v_x_182_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
static lean_object* _init_l_Lean_instInhabitedAxiomVal_default___closed__0(void){
_start:
{
uint8_t v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = 0;
v___x_189_ = l_Lean_instInhabitedConstantVal_default;
v___x_190_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_188_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_instInhabitedAxiomVal_default(void){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_obj_once(&l_Lean_instInhabitedAxiomVal_default___closed__0, &l_Lean_instInhabitedAxiomVal_default___closed__0_once, _init_l_Lean_instInhabitedAxiomVal_default___closed__0);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_instInhabitedAxiomVal(void){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_instInhabitedAxiomVal_default;
return v___x_192_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAxiomVal_beq(lean_object* v_x_193_, lean_object* v_x_194_){
_start:
{
lean_object* v_toConstantVal_195_; uint8_t v_isUnsafe_196_; lean_object* v_toConstantVal_197_; uint8_t v_isUnsafe_198_; uint8_t v___x_199_; 
v_toConstantVal_195_ = lean_ctor_get(v_x_193_, 0);
v_isUnsafe_196_ = lean_ctor_get_uint8(v_x_193_, sizeof(void*)*1);
v_toConstantVal_197_ = lean_ctor_get(v_x_194_, 0);
v_isUnsafe_198_ = lean_ctor_get_uint8(v_x_194_, sizeof(void*)*1);
v___x_199_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_195_, v_toConstantVal_197_);
if (v___x_199_ == 0)
{
return v___x_199_;
}
else
{
if (v_isUnsafe_198_ == 0)
{
if (v_isUnsafe_196_ == 0)
{
return v___x_199_;
}
else
{
return v_isUnsafe_198_;
}
}
else
{
return v_isUnsafe_196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAxiomVal_beq___boxed(lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Lean_instBEqAxiomVal_beq(v_x_200_, v_x_201_);
lean_dec_ref(v_x_201_);
lean_dec_ref(v_x_200_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT lean_object* lean_mk_axiom_val(lean_object* v_name_206_, lean_object* v_levelParams_207_, lean_object* v_type_208_, uint8_t v_isUnsafe_209_){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_210_, 0, v_name_206_);
lean_ctor_set(v___x_210_, 1, v_levelParams_207_);
lean_ctor_set(v___x_210_, 2, v_type_208_);
v___x_211_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*1, v_isUnsafe_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAxiomValEx___boxed(lean_object* v_name_212_, lean_object* v_levelParams_213_, lean_object* v_type_214_, lean_object* v_isUnsafe_215_){
_start:
{
uint8_t v_isUnsafe_boxed_216_; lean_object* v_res_217_; 
v_isUnsafe_boxed_216_ = lean_unbox(v_isUnsafe_215_);
v_res_217_ = lean_mk_axiom_val(v_name_212_, v_levelParams_213_, v_type_214_, v_isUnsafe_boxed_216_);
return v_res_217_;
}
}
LEAN_EXPORT uint8_t lean_axiom_val_is_unsafe(lean_object* v_v_218_){
_start:
{
uint8_t v_isUnsafe_219_; 
v_isUnsafe_219_ = lean_ctor_get_uint8(v_v_218_, sizeof(void*)*1);
lean_dec_ref(v_v_218_);
return v_isUnsafe_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_AxiomVal_isUnsafeEx___boxed(lean_object* v_v_220_){
_start:
{
uint8_t v_res_221_; lean_object* v_r_222_; 
v_res_221_ = lean_axiom_val_is_unsafe(v_v_220_);
v_r_222_ = lean_box(v_res_221_);
return v_r_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorIdx___impl(uint8_t v_x_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_box(v_x_223_);
v___x_225_ = lean_obj_tag_nat(v___x_224_);
lean_dec(v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorIdx___impl___boxed(lean_object* v_x_226_){
_start:
{
uint8_t v_x_4__boxed_227_; lean_object* v_res_228_; 
v_x_4__boxed_227_ = lean_unbox(v_x_226_);
v_res_228_ = l_Lean_DefinitionSafety_ctorIdx___impl(v_x_4__boxed_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg(lean_object* v_k_229_){
_start:
{
lean_inc(v_k_229_);
return v_k_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg___boxed(lean_object* v_k_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_DefinitionSafety_ctorElim___redArg(v_k_230_);
lean_dec(v_k_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim(lean_object* v_motive_232_, lean_object* v_ctorIdx_233_, uint8_t v_t_234_, lean_object* v_h_235_, lean_object* v_k_236_){
_start:
{
lean_inc(v_k_236_);
return v_k_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___boxed(lean_object* v_motive_237_, lean_object* v_ctorIdx_238_, lean_object* v_t_239_, lean_object* v_h_240_, lean_object* v_k_241_){
_start:
{
uint8_t v_t_boxed_242_; lean_object* v_res_243_; 
v_t_boxed_242_ = lean_unbox(v_t_239_);
v_res_243_ = l_Lean_DefinitionSafety_ctorElim(v_motive_237_, v_ctorIdx_238_, v_t_boxed_242_, v_h_240_, v_k_241_);
lean_dec(v_k_241_);
lean_dec(v_ctorIdx_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___redArg(lean_object* v_unsafe_244_){
_start:
{
lean_inc(v_unsafe_244_);
return v_unsafe_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___redArg___boxed(lean_object* v_unsafe_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_DefinitionSafety_unsafe_elim___redArg(v_unsafe_245_);
lean_dec(v_unsafe_245_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim(lean_object* v_motive_247_, uint8_t v_t_248_, lean_object* v_h_249_, lean_object* v_unsafe_250_){
_start:
{
lean_inc(v_unsafe_250_);
return v_unsafe_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___boxed(lean_object* v_motive_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_unsafe_254_){
_start:
{
uint8_t v_t_boxed_255_; lean_object* v_res_256_; 
v_t_boxed_255_ = lean_unbox(v_t_252_);
v_res_256_ = l_Lean_DefinitionSafety_unsafe_elim(v_motive_251_, v_t_boxed_255_, v_h_253_, v_unsafe_254_);
lean_dec(v_unsafe_254_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg(lean_object* v_safe_257_){
_start:
{
lean_inc(v_safe_257_);
return v_safe_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg___boxed(lean_object* v_safe_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_DefinitionSafety_safe_elim___redArg(v_safe_258_);
lean_dec(v_safe_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim(lean_object* v_motive_260_, uint8_t v_t_261_, lean_object* v_h_262_, lean_object* v_safe_263_){
_start:
{
lean_inc(v_safe_263_);
return v_safe_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___boxed(lean_object* v_motive_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_safe_267_){
_start:
{
uint8_t v_t_boxed_268_; lean_object* v_res_269_; 
v_t_boxed_268_ = lean_unbox(v_t_265_);
v_res_269_ = l_Lean_DefinitionSafety_safe_elim(v_motive_264_, v_t_boxed_268_, v_h_266_, v_safe_267_);
lean_dec(v_safe_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg(lean_object* v_partial_270_){
_start:
{
lean_inc(v_partial_270_);
return v_partial_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg___boxed(lean_object* v_partial_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_DefinitionSafety_partial_elim___redArg(v_partial_271_);
lean_dec(v_partial_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim(lean_object* v_motive_273_, uint8_t v_t_274_, lean_object* v_h_275_, lean_object* v_partial_276_){
_start:
{
lean_inc(v_partial_276_);
return v_partial_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___boxed(lean_object* v_motive_277_, lean_object* v_t_278_, lean_object* v_h_279_, lean_object* v_partial_280_){
_start:
{
uint8_t v_t_boxed_281_; lean_object* v_res_282_; 
v_t_boxed_281_ = lean_unbox(v_t_278_);
v_res_282_ = l_Lean_DefinitionSafety_partial_elim(v_motive_277_, v_t_boxed_281_, v_h_279_, v_partial_280_);
lean_dec(v_partial_280_);
return v_res_282_;
}
}
static uint8_t _init_l_Lean_instInhabitedDefinitionSafety_default(void){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = 0;
return v___x_283_;
}
}
static uint8_t _init_l_Lean_instInhabitedDefinitionSafety(void){
_start:
{
uint8_t v___x_284_; 
v___x_284_ = 0;
return v___x_284_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t v_x_285_, uint8_t v_y_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_287_ = lean_box(v_x_285_);
v___x_288_ = lean_obj_tag_nat(v___x_287_);
lean_dec(v___x_287_);
v___x_289_ = lean_box(v_y_286_);
v___x_290_ = lean_obj_tag_nat(v___x_289_);
lean_dec(v___x_289_);
v___x_291_ = lean_nat_dec_eq(v___x_288_, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionSafety_beq___boxed(lean_object* v_x_292_, lean_object* v_y_293_){
_start:
{
uint8_t v_x_24__boxed_294_; uint8_t v_y_25__boxed_295_; uint8_t v_res_296_; lean_object* v_r_297_; 
v_x_24__boxed_294_ = lean_unbox(v_x_292_);
v_y_25__boxed_295_ = lean_unbox(v_y_293_);
v_res_296_ = l_Lean_instBEqDefinitionSafety_beq(v_x_24__boxed_294_, v_y_25__boxed_295_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
static lean_object* _init_l_Lean_instReprDefinitionSafety_repr___closed__6(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(2u);
v___x_310_ = lean_nat_to_int(v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_instReprDefinitionSafety_repr___closed__7(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_to_int(v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDefinitionSafety_repr(uint8_t v_x_313_, lean_object* v_prec_314_){
_start:
{
lean_object* v___y_316_; lean_object* v___y_323_; lean_object* v___y_330_; 
switch(v_x_313_)
{
case 0:
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = lean_unsigned_to_nat(1024u);
v___x_337_ = lean_nat_dec_le(v___x_336_, v_prec_314_);
if (v___x_337_ == 0)
{
lean_object* v___x_338_; 
v___x_338_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_316_ = v___x_338_;
goto v___jp_315_;
}
else
{
lean_object* v___x_339_; 
v___x_339_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_316_ = v___x_339_;
goto v___jp_315_;
}
}
case 1:
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = lean_unsigned_to_nat(1024u);
v___x_341_ = lean_nat_dec_le(v___x_340_, v_prec_314_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_323_ = v___x_342_;
goto v___jp_322_;
}
else
{
lean_object* v___x_343_; 
v___x_343_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_323_ = v___x_343_;
goto v___jp_322_;
}
}
default: 
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(1024u);
v___x_345_ = lean_nat_dec_le(v___x_344_, v_prec_314_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
v___x_346_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_330_ = v___x_346_;
goto v___jp_329_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_330_ = v___x_347_;
goto v___jp_329_;
}
}
}
v___jp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_317_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__1));
lean_inc(v___y_316_);
v___x_318_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_318_, 0, v___y_316_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
v___x_319_ = 0;
v___x_320_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set_uint8(v___x_320_, sizeof(void*)*1, v___x_319_);
v___x_321_ = l_Repr_addAppParen(v___x_320_, v_prec_314_);
return v___x_321_;
}
v___jp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_324_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__3));
lean_inc(v___y_323_);
v___x_325_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_325_, 0, v___y_323_);
lean_ctor_set(v___x_325_, 1, v___x_324_);
v___x_326_ = 0;
v___x_327_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_327_, 0, v___x_325_);
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*1, v___x_326_);
v___x_328_ = l_Repr_addAppParen(v___x_327_, v_prec_314_);
return v___x_328_;
}
v___jp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_331_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__5));
lean_inc(v___y_330_);
v___x_332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_332_, 0, v___y_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = 0;
v___x_334_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set_uint8(v___x_334_, sizeof(void*)*1, v___x_333_);
v___x_335_ = l_Repr_addAppParen(v___x_334_, v_prec_314_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDefinitionSafety_repr___boxed(lean_object* v_x_348_, lean_object* v_prec_349_){
_start:
{
uint8_t v_x_171__boxed_350_; lean_object* v_res_351_; 
v_x_171__boxed_350_ = lean_unbox(v_x_348_);
v_res_351_ = l_Lean_instReprDefinitionSafety_repr(v_x_171__boxed_350_, v_prec_349_);
lean_dec(v_prec_349_);
return v_res_351_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default___closed__0(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = lean_box(0);
v___x_355_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_356_ = l_Lean_Expr_const___override(v___x_355_, v___x_354_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default___closed__2(void){
_start:
{
lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_360_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_361_ = 0;
v___x_362_ = lean_box(0);
v___x_363_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_364_ = l_Lean_instInhabitedConstantVal_default;
v___x_365_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
lean_ctor_set(v___x_365_, 2, v___x_362_);
lean_ctor_set(v___x_365_, 3, v___x_360_);
lean_ctor_set_uint8(v___x_365_, sizeof(void*)*4, v___x_361_);
return v___x_365_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default(void){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__2, &l_Lean_instInhabitedDefinitionVal_default___closed__2_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__2);
return v___x_366_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal(void){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_instInhabitedDefinitionVal_default;
return v___x_367_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDefinitionVal_beq(lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
lean_object* v_toConstantVal_370_; lean_object* v_value_371_; lean_object* v_hints_372_; uint8_t v_safety_373_; lean_object* v_all_374_; lean_object* v_toConstantVal_375_; lean_object* v_value_376_; lean_object* v_hints_377_; uint8_t v_safety_378_; lean_object* v_all_379_; uint8_t v___x_380_; 
v_toConstantVal_370_ = lean_ctor_get(v_x_368_, 0);
v_value_371_ = lean_ctor_get(v_x_368_, 1);
v_hints_372_ = lean_ctor_get(v_x_368_, 2);
v_safety_373_ = lean_ctor_get_uint8(v_x_368_, sizeof(void*)*4);
v_all_374_ = lean_ctor_get(v_x_368_, 3);
v_toConstantVal_375_ = lean_ctor_get(v_x_369_, 0);
v_value_376_ = lean_ctor_get(v_x_369_, 1);
v_hints_377_ = lean_ctor_get(v_x_369_, 2);
v_safety_378_ = lean_ctor_get_uint8(v_x_369_, sizeof(void*)*4);
v_all_379_ = lean_ctor_get(v_x_369_, 3);
v___x_380_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_370_, v_toConstantVal_375_);
if (v___x_380_ == 0)
{
return v___x_380_;
}
else
{
uint8_t v___x_381_; 
v___x_381_ = lean_expr_eqv(v_value_371_, v_value_376_);
if (v___x_381_ == 0)
{
return v___x_381_;
}
else
{
uint8_t v___x_382_; 
v___x_382_ = l_Lean_instBEqReducibilityHints_beq(v_hints_372_, v_hints_377_);
if (v___x_382_ == 0)
{
return v___x_382_;
}
else
{
uint8_t v___x_383_; 
v___x_383_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_373_, v_safety_378_);
if (v___x_383_ == 0)
{
return v___x_383_;
}
else
{
uint8_t v___x_384_; 
v___x_384_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_374_, v_all_379_);
return v___x_384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionVal_beq___boxed(lean_object* v_x_385_, lean_object* v_x_386_){
_start:
{
uint8_t v_res_387_; lean_object* v_r_388_; 
v_res_387_ = l_Lean_instBEqDefinitionVal_beq(v_x_385_, v_x_386_);
lean_dec_ref(v_x_386_);
lean_dec_ref(v_x_385_);
v_r_388_ = lean_box(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT lean_object* lean_mk_definition_val(lean_object* v_name_391_, lean_object* v_levelParams_392_, lean_object* v_type_393_, lean_object* v_value_394_, lean_object* v_hints_395_, uint8_t v_safety_396_, lean_object* v_all_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_398_, 0, v_name_391_);
lean_ctor_set(v___x_398_, 1, v_levelParams_392_);
lean_ctor_set(v___x_398_, 2, v_type_393_);
v___x_399_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_399_, 0, v___x_398_);
lean_ctor_set(v___x_399_, 1, v_value_394_);
lean_ctor_set(v___x_399_, 2, v_hints_395_);
lean_ctor_set(v___x_399_, 3, v_all_397_);
lean_ctor_set_uint8(v___x_399_, sizeof(void*)*4, v_safety_396_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValEx___boxed(lean_object* v_name_400_, lean_object* v_levelParams_401_, lean_object* v_type_402_, lean_object* v_value_403_, lean_object* v_hints_404_, lean_object* v_safety_405_, lean_object* v_all_406_){
_start:
{
uint8_t v_safety_boxed_407_; lean_object* v_res_408_; 
v_safety_boxed_407_ = lean_unbox(v_safety_405_);
v_res_408_ = lean_mk_definition_val(v_name_400_, v_levelParams_401_, v_type_402_, v_value_403_, v_hints_404_, v_safety_boxed_407_, v_all_406_);
return v_res_408_;
}
}
LEAN_EXPORT uint8_t lean_definition_val_get_safety(lean_object* v_v_409_){
_start:
{
uint8_t v_safety_410_; 
v_safety_410_ = lean_ctor_get_uint8(v_v_409_, sizeof(void*)*4);
lean_dec_ref(v_v_409_);
return v_safety_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionVal_getSafetyEx___boxed(lean_object* v_v_411_){
_start:
{
uint8_t v_res_412_; lean_object* v_r_413_; 
v_res_412_ = lean_definition_val_get_safety(v_v_411_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default___closed__0(void){
_start:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_414_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_415_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_416_ = l_Lean_instInhabitedConstantVal_default;
v___x_417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_415_);
lean_ctor_set(v___x_417_, 2, v___x_414_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default(void){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = lean_obj_once(&l_Lean_instInhabitedTheoremVal_default___closed__0, &l_Lean_instInhabitedTheoremVal_default___closed__0_once, _init_l_Lean_instInhabitedTheoremVal_default___closed__0);
return v___x_418_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal(void){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l_Lean_instInhabitedTheoremVal_default;
return v___x_419_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqTheoremVal_beq(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
lean_object* v_toConstantVal_422_; lean_object* v_value_423_; lean_object* v_all_424_; lean_object* v_toConstantVal_425_; lean_object* v_value_426_; lean_object* v_all_427_; uint8_t v___x_428_; 
v_toConstantVal_422_ = lean_ctor_get(v_x_420_, 0);
v_value_423_ = lean_ctor_get(v_x_420_, 1);
v_all_424_ = lean_ctor_get(v_x_420_, 2);
v_toConstantVal_425_ = lean_ctor_get(v_x_421_, 0);
v_value_426_ = lean_ctor_get(v_x_421_, 1);
v_all_427_ = lean_ctor_get(v_x_421_, 2);
v___x_428_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_422_, v_toConstantVal_425_);
if (v___x_428_ == 0)
{
return v___x_428_;
}
else
{
uint8_t v___x_429_; 
v___x_429_ = lean_expr_eqv(v_value_423_, v_value_426_);
if (v___x_429_ == 0)
{
return v___x_429_;
}
else
{
uint8_t v___x_430_; 
v___x_430_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_424_, v_all_427_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqTheoremVal_beq___boxed(lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
uint8_t v_res_433_; lean_object* v_r_434_; 
v_res_433_ = l_Lean_instBEqTheoremVal_beq(v_x_431_, v_x_432_);
lean_dec_ref(v_x_432_);
lean_dec_ref(v_x_431_);
v_r_434_ = lean_box(v_res_433_);
return v_r_434_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default___closed__0(void){
_start:
{
lean_object* v___x_437_; uint8_t v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_437_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_438_ = 0;
v___x_439_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_440_ = l_Lean_instInhabitedConstantVal_default;
v___x_441_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___x_439_);
lean_ctor_set(v___x_441_, 2, v___x_437_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*3, v___x_438_);
return v___x_441_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default(void){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = lean_obj_once(&l_Lean_instInhabitedOpaqueVal_default___closed__0, &l_Lean_instInhabitedOpaqueVal_default___closed__0_once, _init_l_Lean_instInhabitedOpaqueVal_default___closed__0);
return v___x_442_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal(void){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_instInhabitedOpaqueVal_default;
return v___x_443_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqOpaqueVal_beq(lean_object* v_x_444_, lean_object* v_x_445_){
_start:
{
lean_object* v_toConstantVal_446_; lean_object* v_value_447_; uint8_t v_isUnsafe_448_; lean_object* v_all_449_; lean_object* v_toConstantVal_450_; lean_object* v_value_451_; uint8_t v_isUnsafe_452_; lean_object* v_all_453_; uint8_t v___x_454_; 
v_toConstantVal_446_ = lean_ctor_get(v_x_444_, 0);
v_value_447_ = lean_ctor_get(v_x_444_, 1);
v_isUnsafe_448_ = lean_ctor_get_uint8(v_x_444_, sizeof(void*)*3);
v_all_449_ = lean_ctor_get(v_x_444_, 2);
v_toConstantVal_450_ = lean_ctor_get(v_x_445_, 0);
v_value_451_ = lean_ctor_get(v_x_445_, 1);
v_isUnsafe_452_ = lean_ctor_get_uint8(v_x_445_, sizeof(void*)*3);
v_all_453_ = lean_ctor_get(v_x_445_, 2);
v___x_454_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_446_, v_toConstantVal_450_);
if (v___x_454_ == 0)
{
return v___x_454_;
}
else
{
uint8_t v___x_455_; 
v___x_455_ = lean_expr_eqv(v_value_447_, v_value_451_);
if (v___x_455_ == 0)
{
return v___x_455_;
}
else
{
if (v_isUnsafe_452_ == 0)
{
if (v_isUnsafe_448_ == 0)
{
uint8_t v___x_456_; 
v___x_456_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_449_, v_all_453_);
return v___x_456_;
}
else
{
return v_isUnsafe_452_;
}
}
else
{
if (v_isUnsafe_448_ == 0)
{
return v_isUnsafe_448_;
}
else
{
uint8_t v___x_457_; 
v___x_457_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_449_, v_all_453_);
return v___x_457_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqOpaqueVal_beq___boxed(lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
uint8_t v_res_460_; lean_object* v_r_461_; 
v_res_460_ = l_Lean_instBEqOpaqueVal_beq(v_x_458_, v_x_459_);
lean_dec_ref(v_x_459_);
lean_dec_ref(v_x_458_);
v_r_461_ = lean_box(v_res_460_);
return v_r_461_;
}
}
LEAN_EXPORT uint8_t lean_opaque_val_is_unsafe(lean_object* v_v_464_){
_start:
{
uint8_t v_isUnsafe_465_; 
v_isUnsafe_465_ = lean_ctor_get_uint8(v_v_464_, sizeof(void*)*3);
lean_dec_ref(v_v_464_);
return v_isUnsafe_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpaqueVal_isUnsafeEx___boxed(lean_object* v_v_466_){
_start:
{
uint8_t v_res_467_; lean_object* v_r_468_; 
v_res_467_ = lean_opaque_val_is_unsafe(v_v_466_);
v_r_468_ = lean_box(v_res_467_);
return v_r_468_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__0(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_box(0);
v___x_470_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_471_ = l_Lean_Expr_const___override(v___x_470_, v___x_469_);
return v___x_471_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__1(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_473_ = lean_box(0);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v___x_472_);
return v___x_474_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default(void){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__1, &l_Lean_instInhabitedConstructor_default___closed__1_once, _init_l_Lean_instInhabitedConstructor_default___closed__1);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor(void){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_instInhabitedConstructor_default;
return v___x_476_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructor_beq(lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
lean_object* v_name_479_; lean_object* v_type_480_; lean_object* v_name_481_; lean_object* v_type_482_; uint8_t v___x_483_; 
v_name_479_ = lean_ctor_get(v_x_477_, 0);
v_type_480_ = lean_ctor_get(v_x_477_, 1);
v_name_481_ = lean_ctor_get(v_x_478_, 0);
v_type_482_ = lean_ctor_get(v_x_478_, 1);
v___x_483_ = lean_name_eq(v_name_479_, v_name_481_);
if (v___x_483_ == 0)
{
return v___x_483_;
}
else
{
uint8_t v___x_484_; 
v___x_484_ = lean_expr_eqv(v_type_480_, v_type_482_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructor_beq___boxed(lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
uint8_t v_res_487_; lean_object* v_r_488_; 
v_res_487_ = l_Lean_instBEqConstructor_beq(v_x_485_, v_x_486_);
lean_dec_ref(v_x_486_);
lean_dec_ref(v_x_485_);
v_r_488_ = lean_box(v_res_487_);
return v_r_488_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default___closed__0(void){
_start:
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_491_ = lean_box(0);
v___x_492_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_493_ = lean_box(0);
v___x_494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
lean_ctor_set(v___x_494_, 2, v___x_491_);
return v___x_494_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default(void){
_start:
{
lean_object* v___x_495_; 
v___x_495_ = lean_obj_once(&l_Lean_instInhabitedInductiveType_default___closed__0, &l_Lean_instInhabitedInductiveType_default___closed__0_once, _init_l_Lean_instInhabitedInductiveType_default___closed__0);
return v___x_495_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType(void){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_instInhabitedInductiveType_default;
return v___x_496_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
if (lean_obj_tag(v_x_497_) == 0)
{
if (lean_obj_tag(v_x_498_) == 0)
{
uint8_t v___x_499_; 
v___x_499_ = 1;
return v___x_499_;
}
else
{
uint8_t v___x_500_; 
v___x_500_ = 0;
return v___x_500_;
}
}
else
{
if (lean_obj_tag(v_x_498_) == 0)
{
uint8_t v___x_501_; 
v___x_501_ = 0;
return v___x_501_;
}
else
{
lean_object* v_head_502_; lean_object* v_tail_503_; lean_object* v_head_504_; lean_object* v_tail_505_; uint8_t v___x_506_; 
v_head_502_ = lean_ctor_get(v_x_497_, 0);
v_tail_503_ = lean_ctor_get(v_x_497_, 1);
v_head_504_ = lean_ctor_get(v_x_498_, 0);
v_tail_505_ = lean_ctor_get(v_x_498_, 1);
v___x_506_ = l_Lean_instBEqConstructor_beq(v_head_502_, v_head_504_);
if (v___x_506_ == 0)
{
return v___x_506_;
}
else
{
v_x_497_ = v_tail_503_;
v_x_498_ = v_tail_505_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0___boxed(lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
uint8_t v_res_510_; lean_object* v_r_511_; 
v_res_510_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_x_508_, v_x_509_);
lean_dec(v_x_509_);
lean_dec(v_x_508_);
v_r_511_ = lean_box(v_res_510_);
return v_r_511_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveType_beq(lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
lean_object* v_name_514_; lean_object* v_type_515_; lean_object* v_ctors_516_; lean_object* v_name_517_; lean_object* v_type_518_; lean_object* v_ctors_519_; uint8_t v___x_520_; 
v_name_514_ = lean_ctor_get(v_x_512_, 0);
v_type_515_ = lean_ctor_get(v_x_512_, 1);
v_ctors_516_ = lean_ctor_get(v_x_512_, 2);
v_name_517_ = lean_ctor_get(v_x_513_, 0);
v_type_518_ = lean_ctor_get(v_x_513_, 1);
v_ctors_519_ = lean_ctor_get(v_x_513_, 2);
v___x_520_ = lean_name_eq(v_name_514_, v_name_517_);
if (v___x_520_ == 0)
{
return v___x_520_;
}
else
{
uint8_t v___x_521_; 
v___x_521_ = lean_expr_eqv(v_type_515_, v_type_518_);
if (v___x_521_ == 0)
{
return v___x_521_;
}
else
{
uint8_t v___x_522_; 
v___x_522_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_ctors_516_, v_ctors_519_);
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveType_beq___boxed(lean_object* v_x_523_, lean_object* v_x_524_){
_start:
{
uint8_t v_res_525_; lean_object* v_r_526_; 
v_res_525_ = l_Lean_instBEqInductiveType_beq(v_x_523_, v_x_524_);
lean_dec_ref(v_x_524_);
lean_dec_ref(v_x_523_);
v_r_526_ = lean_box(v_res_525_);
return v_r_526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___impl(lean_object* v_x_529_){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = lean_obj_tag_nat(v_x_529_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___impl___boxed(lean_object* v_x_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_Declaration_ctorIdx___impl(v_x_531_);
lean_dec(v_x_531_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___redArg(lean_object* v_t_533_, lean_object* v_k_534_){
_start:
{
switch(lean_obj_tag(v_t_533_))
{
case 4:
{
return v_k_534_;
}
case 5:
{
lean_object* v_defns_535_; lean_object* v___x_536_; 
v_defns_535_ = lean_ctor_get(v_t_533_, 0);
lean_inc(v_defns_535_);
lean_dec_ref_known(v_t_533_, 1);
v___x_536_ = lean_apply_1(v_k_534_, v_defns_535_);
return v___x_536_;
}
case 6:
{
lean_object* v_lparams_537_; lean_object* v_nparams_538_; lean_object* v_types_539_; uint8_t v_isUnsafe_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_lparams_537_ = lean_ctor_get(v_t_533_, 0);
lean_inc(v_lparams_537_);
v_nparams_538_ = lean_ctor_get(v_t_533_, 1);
lean_inc(v_nparams_538_);
v_types_539_ = lean_ctor_get(v_t_533_, 2);
lean_inc(v_types_539_);
v_isUnsafe_540_ = lean_ctor_get_uint8(v_t_533_, sizeof(void*)*3);
lean_dec_ref_known(v_t_533_, 3);
v___x_541_ = lean_box(v_isUnsafe_540_);
v___x_542_ = lean_apply_4(v_k_534_, v_lparams_537_, v_nparams_538_, v_types_539_, v___x_541_);
return v___x_542_;
}
default: 
{
lean_object* v_val_543_; lean_object* v___x_544_; 
v_val_543_ = lean_ctor_get(v_t_533_, 0);
lean_inc_ref(v_val_543_);
lean_dec(v_t_533_);
v___x_544_ = lean_apply_1(v_k_534_, v_val_543_);
return v___x_544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim(lean_object* v_motive_545_, lean_object* v_ctorIdx_546_, lean_object* v_t_547_, lean_object* v_h_548_, lean_object* v_k_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_Declaration_ctorElim___redArg(v_t_547_, v_k_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___boxed(lean_object* v_motive_551_, lean_object* v_ctorIdx_552_, lean_object* v_t_553_, lean_object* v_h_554_, lean_object* v_k_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lean_Declaration_ctorElim(v_motive_551_, v_ctorIdx_552_, v_t_553_, v_h_554_, v_k_555_);
lean_dec(v_ctorIdx_552_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim___redArg(lean_object* v_t_557_, lean_object* v_axiomDecl_558_){
_start:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Declaration_ctorElim___redArg(v_t_557_, v_axiomDecl_558_);
return v___x_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim(lean_object* v_motive_560_, lean_object* v_t_561_, lean_object* v_h_562_, lean_object* v_axiomDecl_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Declaration_ctorElim___redArg(v_t_561_, v_axiomDecl_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim___redArg(lean_object* v_t_565_, lean_object* v_defnDecl_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l_Lean_Declaration_ctorElim___redArg(v_t_565_, v_defnDecl_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim(lean_object* v_motive_568_, lean_object* v_t_569_, lean_object* v_h_570_, lean_object* v_defnDecl_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Declaration_ctorElim___redArg(v_t_569_, v_defnDecl_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim___redArg(lean_object* v_t_573_, lean_object* v_thmDecl_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Lean_Declaration_ctorElim___redArg(v_t_573_, v_thmDecl_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim(lean_object* v_motive_576_, lean_object* v_t_577_, lean_object* v_h_578_, lean_object* v_thmDecl_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Declaration_ctorElim___redArg(v_t_577_, v_thmDecl_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim___redArg(lean_object* v_t_581_, lean_object* v_opaqueDecl_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_Declaration_ctorElim___redArg(v_t_581_, v_opaqueDecl_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim(lean_object* v_motive_584_, lean_object* v_t_585_, lean_object* v_h_586_, lean_object* v_opaqueDecl_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Declaration_ctorElim___redArg(v_t_585_, v_opaqueDecl_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim___redArg(lean_object* v_t_589_, lean_object* v_quotDecl_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Declaration_ctorElim___redArg(v_t_589_, v_quotDecl_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim(lean_object* v_motive_592_, lean_object* v_t_593_, lean_object* v_h_594_, lean_object* v_quotDecl_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Declaration_ctorElim___redArg(v_t_593_, v_quotDecl_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim___redArg(lean_object* v_t_597_, lean_object* v_mutualDefnDecl_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Declaration_ctorElim___redArg(v_t_597_, v_mutualDefnDecl_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim(lean_object* v_motive_600_, lean_object* v_t_601_, lean_object* v_h_602_, lean_object* v_mutualDefnDecl_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Declaration_ctorElim___redArg(v_t_601_, v_mutualDefnDecl_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim___redArg(lean_object* v_t_605_, lean_object* v_inductDecl_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Declaration_ctorElim___redArg(v_t_605_, v_inductDecl_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim(lean_object* v_motive_608_, lean_object* v_t_609_, lean_object* v_h_610_, lean_object* v_inductDecl_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_Declaration_ctorElim___redArg(v_t_609_, v_inductDecl_611_);
return v___x_612_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default___closed__0(void){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = l_Lean_instInhabitedAxiomVal_default;
v___x_614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
return v___x_614_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default(void){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = lean_obj_once(&l_Lean_instInhabitedDeclaration_default___closed__0, &l_Lean_instInhabitedDeclaration_default___closed__0_once, _init_l_Lean_instInhabitedDeclaration_default___closed__0);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration(void){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_instInhabitedDeclaration_default;
return v___x_616_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
if (lean_obj_tag(v_x_617_) == 0)
{
if (lean_obj_tag(v_x_618_) == 0)
{
uint8_t v___x_619_; 
v___x_619_ = 1;
return v___x_619_;
}
else
{
uint8_t v___x_620_; 
v___x_620_ = 0;
return v___x_620_;
}
}
else
{
if (lean_obj_tag(v_x_618_) == 0)
{
uint8_t v___x_621_; 
v___x_621_ = 0;
return v___x_621_;
}
else
{
lean_object* v_head_622_; lean_object* v_tail_623_; lean_object* v_head_624_; lean_object* v_tail_625_; uint8_t v___x_626_; 
v_head_622_ = lean_ctor_get(v_x_617_, 0);
v_tail_623_ = lean_ctor_get(v_x_617_, 1);
v_head_624_ = lean_ctor_get(v_x_618_, 0);
v_tail_625_ = lean_ctor_get(v_x_618_, 1);
v___x_626_ = l_Lean_instBEqDefinitionVal_beq(v_head_622_, v_head_624_);
if (v___x_626_ == 0)
{
return v___x_626_;
}
else
{
v_x_617_ = v_tail_623_;
v_x_618_ = v_tail_625_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0___boxed(lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
uint8_t v_res_630_; lean_object* v_r_631_; 
v_res_630_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_x_628_, v_x_629_);
lean_dec(v_x_629_);
lean_dec(v_x_628_);
v_r_631_ = lean_box(v_res_630_);
return v_r_631_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
if (lean_obj_tag(v_x_632_) == 0)
{
if (lean_obj_tag(v_x_633_) == 0)
{
uint8_t v___x_634_; 
v___x_634_ = 1;
return v___x_634_;
}
else
{
uint8_t v___x_635_; 
v___x_635_ = 0;
return v___x_635_;
}
}
else
{
if (lean_obj_tag(v_x_633_) == 0)
{
uint8_t v___x_636_; 
v___x_636_ = 0;
return v___x_636_;
}
else
{
lean_object* v_head_637_; lean_object* v_tail_638_; lean_object* v_head_639_; lean_object* v_tail_640_; uint8_t v___x_641_; 
v_head_637_ = lean_ctor_get(v_x_632_, 0);
v_tail_638_ = lean_ctor_get(v_x_632_, 1);
v_head_639_ = lean_ctor_get(v_x_633_, 0);
v_tail_640_ = lean_ctor_get(v_x_633_, 1);
v___x_641_ = l_Lean_instBEqInductiveType_beq(v_head_637_, v_head_639_);
if (v___x_641_ == 0)
{
return v___x_641_;
}
else
{
v_x_632_ = v_tail_638_;
v_x_633_ = v_tail_640_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1___boxed(lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
uint8_t v_res_645_; lean_object* v_r_646_; 
v_res_645_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_x_643_, v_x_644_);
lean_dec(v_x_644_);
lean_dec(v_x_643_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDeclaration_beq(lean_object* v_x_647_, lean_object* v_x_648_){
_start:
{
switch(lean_obj_tag(v_x_647_))
{
case 0:
{
if (lean_obj_tag(v_x_648_) == 0)
{
lean_object* v_val_649_; lean_object* v_val_650_; uint8_t v___x_651_; 
v_val_649_ = lean_ctor_get(v_x_647_, 0);
v_val_650_ = lean_ctor_get(v_x_648_, 0);
v___x_651_ = l_Lean_instBEqAxiomVal_beq(v_val_649_, v_val_650_);
return v___x_651_;
}
else
{
uint8_t v___x_652_; 
v___x_652_ = 0;
return v___x_652_;
}
}
case 1:
{
if (lean_obj_tag(v_x_648_) == 1)
{
lean_object* v_val_653_; lean_object* v_val_654_; uint8_t v___x_655_; 
v_val_653_ = lean_ctor_get(v_x_647_, 0);
v_val_654_ = lean_ctor_get(v_x_648_, 0);
v___x_655_ = l_Lean_instBEqDefinitionVal_beq(v_val_653_, v_val_654_);
return v___x_655_;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = 0;
return v___x_656_;
}
}
case 2:
{
if (lean_obj_tag(v_x_648_) == 2)
{
lean_object* v_val_657_; lean_object* v_val_658_; uint8_t v___x_659_; 
v_val_657_ = lean_ctor_get(v_x_647_, 0);
v_val_658_ = lean_ctor_get(v_x_648_, 0);
v___x_659_ = l_Lean_instBEqTheoremVal_beq(v_val_657_, v_val_658_);
return v___x_659_;
}
else
{
uint8_t v___x_660_; 
v___x_660_ = 0;
return v___x_660_;
}
}
case 3:
{
if (lean_obj_tag(v_x_648_) == 3)
{
lean_object* v_val_661_; lean_object* v_val_662_; uint8_t v___x_663_; 
v_val_661_ = lean_ctor_get(v_x_647_, 0);
v_val_662_ = lean_ctor_get(v_x_648_, 0);
v___x_663_ = l_Lean_instBEqOpaqueVal_beq(v_val_661_, v_val_662_);
return v___x_663_;
}
else
{
uint8_t v___x_664_; 
v___x_664_ = 0;
return v___x_664_;
}
}
case 4:
{
if (lean_obj_tag(v_x_648_) == 4)
{
uint8_t v___x_665_; 
v___x_665_ = 1;
return v___x_665_;
}
else
{
uint8_t v___x_666_; 
v___x_666_ = 0;
return v___x_666_;
}
}
case 5:
{
if (lean_obj_tag(v_x_648_) == 5)
{
lean_object* v_defns_667_; lean_object* v_defns_668_; uint8_t v___x_669_; 
v_defns_667_ = lean_ctor_get(v_x_647_, 0);
v_defns_668_ = lean_ctor_get(v_x_648_, 0);
v___x_669_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_defns_667_, v_defns_668_);
return v___x_669_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = 0;
return v___x_670_;
}
}
default: 
{
if (lean_obj_tag(v_x_648_) == 6)
{
lean_object* v_lparams_671_; lean_object* v_nparams_672_; lean_object* v_types_673_; uint8_t v_isUnsafe_674_; lean_object* v_lparams_675_; lean_object* v_nparams_676_; lean_object* v_types_677_; uint8_t v_isUnsafe_678_; uint8_t v___x_679_; 
v_lparams_671_ = lean_ctor_get(v_x_647_, 0);
v_nparams_672_ = lean_ctor_get(v_x_647_, 1);
v_types_673_ = lean_ctor_get(v_x_647_, 2);
v_isUnsafe_674_ = lean_ctor_get_uint8(v_x_647_, sizeof(void*)*3);
v_lparams_675_ = lean_ctor_get(v_x_648_, 0);
v_nparams_676_ = lean_ctor_get(v_x_648_, 1);
v_types_677_ = lean_ctor_get(v_x_648_, 2);
v_isUnsafe_678_ = lean_ctor_get_uint8(v_x_648_, sizeof(void*)*3);
v___x_679_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_lparams_671_, v_lparams_675_);
if (v___x_679_ == 0)
{
return v___x_679_;
}
else
{
uint8_t v___x_680_; 
v___x_680_ = lean_nat_dec_eq(v_nparams_672_, v_nparams_676_);
if (v___x_680_ == 0)
{
return v___x_680_;
}
else
{
uint8_t v___x_681_; 
v___x_681_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_types_673_, v_types_677_);
if (v___x_681_ == 0)
{
return v___x_681_;
}
else
{
if (v_isUnsafe_678_ == 0)
{
if (v_isUnsafe_674_ == 0)
{
return v___x_681_;
}
else
{
return v_isUnsafe_678_;
}
}
else
{
return v_isUnsafe_674_;
}
}
}
}
}
else
{
uint8_t v___x_682_; 
v___x_682_ = 0;
return v___x_682_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDeclaration_beq___boxed(lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
uint8_t v_res_685_; lean_object* v_r_686_; 
v_res_685_ = l_Lean_instBEqDeclaration_beq(v_x_683_, v_x_684_);
lean_dec(v_x_684_);
lean_dec(v_x_683_);
v_r_686_ = lean_box(v_res_685_);
return v_r_686_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_decl(lean_object* v_lparams_689_, lean_object* v_nparams_690_, lean_object* v_types_691_, uint8_t v_isUnsafe_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_693_, 0, v_lparams_689_);
lean_ctor_set(v___x_693_, 1, v_nparams_690_);
lean_ctor_set(v___x_693_, 2, v_types_691_);
lean_ctor_set_uint8(v___x_693_, sizeof(void*)*3, v_isUnsafe_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveDeclEs___boxed(lean_object* v_lparams_694_, lean_object* v_nparams_695_, lean_object* v_types_696_, lean_object* v_isUnsafe_697_){
_start:
{
uint8_t v_isUnsafe_boxed_698_; lean_object* v_res_699_; 
v_isUnsafe_boxed_698_ = lean_unbox(v_isUnsafe_697_);
v_res_699_ = lean_mk_inductive_decl(v_lparams_694_, v_nparams_695_, v_types_696_, v_isUnsafe_boxed_698_);
return v_res_699_;
}
}
LEAN_EXPORT uint8_t lean_is_unsafe_inductive_decl(lean_object* v_x_700_){
_start:
{
if (lean_obj_tag(v_x_700_) == 6)
{
uint8_t v_isUnsafe_701_; 
v_isUnsafe_701_ = lean_ctor_get_uint8(v_x_700_, sizeof(void*)*3);
lean_dec_ref_known(v_x_700_, 3);
return v_isUnsafe_701_;
}
else
{
uint8_t v___x_702_; 
lean_dec(v_x_700_);
v___x_702_ = 0;
return v___x_702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_isUnsafeInductiveDeclEx___boxed(lean_object* v_x_703_){
_start:
{
uint8_t v_res_704_; lean_object* v_r_705_; 
v_res_704_ = lean_is_unsafe_inductive_decl(v_x_703_);
v_r_705_ = lean_box(v_res_704_);
return v_r_705_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(lean_object* v_msg_706_){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = l_Lean_instInhabitedDefinitionVal_default;
v___x_708_ = lean_panic_fn_borrowed(v___x_707_, v_msg_706_);
return v___x_708_;
}
}
static lean_object* _init_l_Lean_Declaration_definitionVal_x21___closed__3(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_712_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__2));
v___x_713_ = lean_unsigned_to_nat(9u);
v___x_714_ = lean_unsigned_to_nat(189u);
v___x_715_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__1));
v___x_716_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_717_ = l_mkPanicMessageWithDecl(v___x_716_, v___x_715_, v___x_714_, v___x_713_, v___x_712_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21(lean_object* v_x_718_){
_start:
{
if (lean_obj_tag(v_x_718_) == 1)
{
lean_object* v_val_719_; 
v_val_719_ = lean_ctor_get(v_x_718_, 0);
lean_inc_ref(v_val_719_);
return v_val_719_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = lean_obj_once(&l_Lean_Declaration_definitionVal_x21___closed__3, &l_Lean_Declaration_definitionVal_x21___closed__3_once, _init_l_Lean_Declaration_definitionVal_x21___closed__3);
v___x_721_ = l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(v___x_720_);
return v___x_721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21___boxed(lean_object* v_x_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Lean_Declaration_definitionVal_x21(v_x_722_);
lean_dec(v_x_722_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
if (lean_obj_tag(v_a_724_) == 0)
{
lean_object* v___x_726_; 
v___x_726_ = l_List_reverse___redArg(v_a_725_);
return v___x_726_;
}
else
{
lean_object* v_head_727_; lean_object* v_toConstantVal_728_; lean_object* v_tail_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_738_; 
v_head_727_ = lean_ctor_get(v_a_724_, 0);
v_toConstantVal_728_ = lean_ctor_get(v_head_727_, 0);
lean_inc_ref(v_toConstantVal_728_);
v_tail_729_ = lean_ctor_get(v_a_724_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_a_724_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v_a_724_, 0);
lean_dec(v_unused_739_);
v___x_731_ = v_a_724_;
v_isShared_732_ = v_isSharedCheck_738_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_tail_729_);
lean_dec(v_a_724_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_738_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v_name_733_; lean_object* v___x_735_; 
v_name_733_ = lean_ctor_get(v_toConstantVal_728_, 0);
lean_inc(v_name_733_);
lean_dec_ref(v_toConstantVal_728_);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v_a_725_);
lean_ctor_set(v___x_731_, 0, v_name_733_);
v___x_735_ = v___x_731_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_name_733_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v_a_725_);
v___x_735_ = v_reuseFailAlloc_737_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
v_a_724_ = v_tail_729_;
v_a_725_ = v___x_735_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
if (lean_obj_tag(v_a_740_) == 0)
{
lean_object* v___x_742_; 
v___x_742_ = l_List_reverse___redArg(v_a_741_);
return v___x_742_;
}
else
{
lean_object* v_head_743_; lean_object* v_tail_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_753_; 
v_head_743_ = lean_ctor_get(v_a_740_, 0);
v_tail_744_ = lean_ctor_get(v_a_740_, 1);
v_isSharedCheck_753_ = !lean_is_exclusive(v_a_740_);
if (v_isSharedCheck_753_ == 0)
{
v___x_746_ = v_a_740_;
v_isShared_747_ = v_isSharedCheck_753_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_tail_744_);
lean_inc(v_head_743_);
lean_dec(v_a_740_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_753_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_name_748_; lean_object* v___x_750_; 
v_name_748_ = lean_ctor_get(v_head_743_, 0);
lean_inc(v_name_748_);
lean_dec(v_head_743_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v_a_741_);
lean_ctor_set(v___x_746_, 0, v_name_748_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_name_748_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_a_741_);
v___x_750_ = v_reuseFailAlloc_752_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
v_a_740_ = v_tail_744_;
v_a_741_ = v___x_750_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getTopLevelNames(lean_object* v_x_760_){
_start:
{
switch(lean_obj_tag(v_x_760_))
{
case 4:
{
lean_object* v___x_761_; 
v___x_761_ = ((lean_object*)(l_Lean_Declaration_getTopLevelNames___closed__2));
return v___x_761_;
}
case 5:
{
lean_object* v_defns_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_defns_762_ = lean_ctor_get(v_x_760_, 0);
lean_inc(v_defns_762_);
lean_dec_ref_known(v_x_760_, 1);
v___x_763_ = lean_box(0);
v___x_764_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_762_, v___x_763_);
return v___x_764_;
}
case 6:
{
lean_object* v_types_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v_types_765_ = lean_ctor_get(v_x_760_, 2);
lean_inc(v_types_765_);
lean_dec_ref_known(v_x_760_, 3);
v___x_766_ = lean_box(0);
v___x_767_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(v_types_765_, v___x_766_);
return v___x_767_;
}
default: 
{
lean_object* v_val_768_; lean_object* v_toConstantVal_769_; lean_object* v_name_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v_val_768_ = lean_ctor_get(v_x_760_, 0);
lean_inc_ref(v_val_768_);
lean_dec(v_x_760_);
v_toConstantVal_769_ = lean_ctor_get(v_val_768_, 0);
lean_inc_ref(v_toConstantVal_769_);
lean_dec_ref(v_val_768_);
v_name_770_ = lean_ctor_get(v_toConstantVal_769_, 0);
lean_inc(v_name_770_);
lean_dec_ref(v_toConstantVal_769_);
v___x_771_ = lean_box(0);
v___x_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_772_, 0, v_name_770_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
return v___x_772_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
if (lean_obj_tag(v_a_773_) == 0)
{
lean_object* v___x_775_; 
v___x_775_ = l_List_reverse___redArg(v_a_774_);
return v___x_775_;
}
else
{
lean_object* v_head_776_; lean_object* v_tail_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_786_; 
v_head_776_ = lean_ctor_get(v_a_773_, 0);
v_tail_777_ = lean_ctor_get(v_a_773_, 1);
v_isSharedCheck_786_ = !lean_is_exclusive(v_a_773_);
if (v_isSharedCheck_786_ == 0)
{
v___x_779_ = v_a_773_;
v_isShared_780_ = v_isSharedCheck_786_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_tail_777_);
lean_inc(v_head_776_);
lean_dec(v_a_773_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_786_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v_name_781_; lean_object* v___x_783_; 
v_name_781_ = lean_ctor_get(v_head_776_, 0);
lean_inc(v_name_781_);
lean_dec(v_head_776_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 1, v_a_774_);
lean_ctor_set(v___x_779_, 0, v_name_781_);
v___x_783_ = v___x_779_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_name_781_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_a_774_);
v___x_783_ = v_reuseFailAlloc_785_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
v_a_773_ = v_tail_777_;
v_a_774_ = v___x_783_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
if (lean_obj_tag(v_a_790_) == 0)
{
lean_object* v___x_792_; 
v___x_792_ = lean_array_to_list(v_a_791_);
return v___x_792_;
}
else
{
lean_object* v_head_793_; lean_object* v_tail_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_810_; 
v_head_793_ = lean_ctor_get(v_a_790_, 0);
v_tail_794_ = lean_ctor_get(v_a_790_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v_a_790_);
if (v_isSharedCheck_810_ == 0)
{
v___x_796_ = v_a_790_;
v_isShared_797_ = v_isSharedCheck_810_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_tail_794_);
lean_inc(v_head_793_);
lean_dec(v_a_790_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_810_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v_name_798_; lean_object* v_ctors_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_805_; 
v_name_798_ = lean_ctor_get(v_head_793_, 0);
lean_inc(v_name_798_);
v_ctors_799_ = lean_ctor_get(v_head_793_, 2);
lean_inc(v_ctors_799_);
lean_dec(v_head_793_);
v___x_800_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1));
v___x_801_ = l_Lean_Name_appendCore(v_name_798_, v___x_800_);
v___x_802_ = lean_box(0);
v___x_803_ = l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(v_ctors_799_, v___x_802_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___x_803_);
lean_ctor_set(v___x_796_, 0, v___x_801_);
v___x_805_ = v___x_796_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_801_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_803_);
v___x_805_ = v_reuseFailAlloc_809_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_806_, 0, v_name_798_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_791_, v___x_806_);
v_a_790_ = v_tail_794_;
v_a_791_ = v___x_807_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getNames(lean_object* v_x_837_){
_start:
{
switch(lean_obj_tag(v_x_837_))
{
case 4:
{
lean_object* v___x_838_; 
v___x_838_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__9));
return v___x_838_;
}
case 5:
{
lean_object* v_defns_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_defns_839_ = lean_ctor_get(v_x_837_, 0);
lean_inc(v_defns_839_);
lean_dec_ref_known(v_x_837_, 1);
v___x_840_ = lean_box(0);
v___x_841_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_839_, v___x_840_);
return v___x_841_;
}
case 6:
{
lean_object* v_types_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_types_842_ = lean_ctor_get(v_x_837_, 2);
lean_inc(v_types_842_);
lean_dec_ref_known(v_x_837_, 3);
v___x_843_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__10));
v___x_844_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(v_types_842_, v___x_843_);
return v___x_844_;
}
default: 
{
lean_object* v_val_845_; lean_object* v_toConstantVal_846_; lean_object* v_name_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_val_845_ = lean_ctor_get(v_x_837_, 0);
lean_inc_ref(v_val_845_);
lean_dec(v_x_837_);
v_toConstantVal_846_ = lean_ctor_get(v_val_845_, 0);
lean_inc_ref(v_toConstantVal_846_);
lean_dec_ref(v_val_845_);
v_name_847_ = lean_ctor_get(v_toConstantVal_846_, 0);
lean_inc(v_name_847_);
lean_dec_ref(v_toConstantVal_846_);
v___x_848_ = lean_box(0);
v___x_849_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_849_, 0, v_name_847_);
lean_ctor_set(v___x_849_, 1, v___x_848_);
return v___x_849_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__0(lean_object* v_f_850_, lean_object* v_value_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_apply_2(v_f_850_, v_a_852_, v_value_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__3(lean_object* v_f_854_, lean_object* v_value_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = lean_apply_2(v_f_854_, v_a_856_, v_value_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__1(lean_object* v_f_858_, lean_object* v_toBind_859_, lean_object* v_a_860_, lean_object* v_v_861_){
_start:
{
lean_object* v_toConstantVal_862_; lean_object* v_value_863_; lean_object* v_type_864_; lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_toConstantVal_862_ = lean_ctor_get(v_v_861_, 0);
lean_inc_ref(v_toConstantVal_862_);
v_value_863_ = lean_ctor_get(v_v_861_, 1);
lean_inc_ref(v_value_863_);
lean_dec_ref(v_v_861_);
v_type_864_ = lean_ctor_get(v_toConstantVal_862_, 2);
lean_inc_ref(v_type_864_);
lean_dec_ref(v_toConstantVal_862_);
lean_inc(v_f_858_);
v___f_865_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__3), 3, 2);
lean_closure_set(v___f_865_, 0, v_f_858_);
lean_closure_set(v___f_865_, 1, v_value_863_);
v___x_866_ = lean_apply_2(v_f_858_, v_a_860_, v_type_864_);
v___x_867_ = lean_apply_4(v_toBind_859_, lean_box(0), lean_box(0), v___x_866_, v___f_865_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__2(lean_object* v_f_868_, lean_object* v_a_869_, lean_object* v_ctor_870_){
_start:
{
lean_object* v_type_871_; lean_object* v___x_872_; 
v_type_871_ = lean_ctor_get(v_ctor_870_, 1);
lean_inc_ref(v_type_871_);
lean_dec_ref(v_ctor_870_);
v___x_872_ = lean_apply_2(v_f_868_, v_a_869_, v_type_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__4(lean_object* v_inst_873_, lean_object* v___f_874_, lean_object* v_ctors_875_, lean_object* v_a_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_List_foldlM___redArg(v_inst_873_, v___f_874_, v_a_876_, v_ctors_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__5(lean_object* v_inst_878_, lean_object* v___f_879_, lean_object* v_f_880_, lean_object* v_toBind_881_, lean_object* v_a_882_, lean_object* v_inductType_883_){
_start:
{
lean_object* v_type_884_; lean_object* v_ctors_885_; lean_object* v___f_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v_type_884_ = lean_ctor_get(v_inductType_883_, 1);
lean_inc_ref(v_type_884_);
v_ctors_885_ = lean_ctor_get(v_inductType_883_, 2);
lean_inc(v_ctors_885_);
lean_dec_ref(v_inductType_883_);
v___f_886_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__4), 4, 3);
lean_closure_set(v___f_886_, 0, v_inst_878_);
lean_closure_set(v___f_886_, 1, v___f_879_);
lean_closure_set(v___f_886_, 2, v_ctors_885_);
v___x_887_ = lean_apply_2(v_f_880_, v_a_882_, v_type_884_);
v___x_888_ = lean_apply_4(v_toBind_881_, lean_box(0), lean_box(0), v___x_887_, v___f_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object* v_inst_889_, lean_object* v_d_890_, lean_object* v_f_891_, lean_object* v_a_892_){
_start:
{
switch(lean_obj_tag(v_d_890_))
{
case 0:
{
lean_object* v_val_893_; lean_object* v_toConstantVal_894_; lean_object* v_type_895_; lean_object* v___x_896_; 
lean_dec_ref(v_inst_889_);
v_val_893_ = lean_ctor_get(v_d_890_, 0);
lean_inc_ref(v_val_893_);
lean_dec_ref_known(v_d_890_, 1);
v_toConstantVal_894_ = lean_ctor_get(v_val_893_, 0);
lean_inc_ref(v_toConstantVal_894_);
lean_dec_ref(v_val_893_);
v_type_895_ = lean_ctor_get(v_toConstantVal_894_, 2);
lean_inc_ref(v_type_895_);
lean_dec_ref(v_toConstantVal_894_);
v___x_896_ = lean_apply_2(v_f_891_, v_a_892_, v_type_895_);
return v___x_896_;
}
case 4:
{
lean_object* v_toApplicative_897_; lean_object* v_toPure_898_; lean_object* v___x_899_; 
v_toApplicative_897_ = lean_ctor_get(v_inst_889_, 0);
lean_inc_ref(v_toApplicative_897_);
lean_dec(v_f_891_);
lean_dec_ref(v_inst_889_);
v_toPure_898_ = lean_ctor_get(v_toApplicative_897_, 1);
lean_inc(v_toPure_898_);
lean_dec_ref(v_toApplicative_897_);
v___x_899_ = lean_apply_2(v_toPure_898_, lean_box(0), v_a_892_);
return v___x_899_;
}
case 5:
{
lean_object* v_toBind_900_; lean_object* v_defns_901_; lean_object* v___f_902_; lean_object* v___x_903_; 
v_toBind_900_ = lean_ctor_get(v_inst_889_, 1);
v_defns_901_ = lean_ctor_get(v_d_890_, 0);
lean_inc(v_defns_901_);
lean_dec_ref_known(v_d_890_, 1);
lean_inc(v_toBind_900_);
v___f_902_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_902_, 0, v_f_891_);
lean_closure_set(v___f_902_, 1, v_toBind_900_);
v___x_903_ = l_List_foldlM___redArg(v_inst_889_, v___f_902_, v_a_892_, v_defns_901_);
return v___x_903_;
}
case 6:
{
lean_object* v_toBind_904_; lean_object* v_types_905_; lean_object* v___f_906_; lean_object* v___f_907_; lean_object* v___x_908_; 
v_toBind_904_ = lean_ctor_get(v_inst_889_, 1);
v_types_905_ = lean_ctor_get(v_d_890_, 2);
lean_inc(v_types_905_);
lean_dec_ref_known(v_d_890_, 3);
lean_inc(v_f_891_);
v___f_906_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__2), 3, 1);
lean_closure_set(v___f_906_, 0, v_f_891_);
lean_inc(v_toBind_904_);
lean_inc_ref(v_inst_889_);
v___f_907_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__5), 6, 4);
lean_closure_set(v___f_907_, 0, v_inst_889_);
lean_closure_set(v___f_907_, 1, v___f_906_);
lean_closure_set(v___f_907_, 2, v_f_891_);
lean_closure_set(v___f_907_, 3, v_toBind_904_);
v___x_908_ = l_List_foldlM___redArg(v_inst_889_, v___f_907_, v_a_892_, v_types_905_);
return v___x_908_;
}
default: 
{
lean_object* v_val_909_; lean_object* v_toConstantVal_910_; lean_object* v_toBind_911_; lean_object* v_value_912_; lean_object* v_type_913_; lean_object* v___f_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_val_909_ = lean_ctor_get(v_d_890_, 0);
lean_inc_ref(v_val_909_);
lean_dec(v_d_890_);
v_toConstantVal_910_ = lean_ctor_get(v_val_909_, 0);
lean_inc_ref(v_toConstantVal_910_);
v_toBind_911_ = lean_ctor_get(v_inst_889_, 1);
lean_inc(v_toBind_911_);
lean_dec_ref(v_inst_889_);
v_value_912_ = lean_ctor_get(v_val_909_, 1);
lean_inc_ref(v_value_912_);
lean_dec_ref(v_val_909_);
v_type_913_ = lean_ctor_get(v_toConstantVal_910_, 2);
lean_inc_ref(v_type_913_);
lean_dec_ref(v_toConstantVal_910_);
lean_inc(v_f_891_);
v___f_914_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_914_, 0, v_f_891_);
lean_closure_set(v___f_914_, 1, v_value_912_);
v___x_915_ = lean_apply_2(v_f_891_, v_a_892_, v_type_913_);
v___x_916_ = lean_apply_4(v_toBind_911_, lean_box(0), lean_box(0), v___x_915_, v___f_914_);
return v___x_916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM(lean_object* v_00_u03b1_917_, lean_object* v_m_918_, lean_object* v_inst_919_, lean_object* v_d_920_, lean_object* v_f_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_Declaration_foldExprM___redArg(v_inst_919_, v_d_920_, v_f_921_, v_a_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg___lam__0(lean_object* v_f_924_, lean_object* v_x_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = lean_apply_1(v_f_924_, v_a_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg(lean_object* v_inst_928_, lean_object* v_d_929_, lean_object* v_f_930_){
_start:
{
lean_object* v___f_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___f_931_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_931_, 0, v_f_930_);
v___x_932_ = lean_box(0);
v___x_933_ = l_Lean_Declaration_foldExprM___redArg(v_inst_928_, v_d_929_, v___f_931_, v___x_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM(lean_object* v_m_934_, lean_object* v_inst_935_, lean_object* v_d_936_, lean_object* v_f_937_){
_start:
{
lean_object* v___f_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___f_938_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_938_, 0, v_f_937_);
v___x_939_ = lean_box(0);
v___x_940_ = l_Lean_Declaration_foldExprM___redArg(v_inst_935_, v_d_936_, v___f_938_, v___x_939_);
return v___x_940_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default___closed__0(void){
_start:
{
uint8_t v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_941_ = 0;
v___x_942_ = lean_box(0);
v___x_943_ = lean_unsigned_to_nat(0u);
v___x_944_ = l_Lean_instInhabitedConstantVal_default;
v___x_945_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v___x_943_);
lean_ctor_set(v___x_945_, 2, v___x_943_);
lean_ctor_set(v___x_945_, 3, v___x_942_);
lean_ctor_set(v___x_945_, 4, v___x_942_);
lean_ctor_set(v___x_945_, 5, v___x_943_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*6, v___x_941_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*6 + 1, v___x_941_);
lean_ctor_set_uint8(v___x_945_, sizeof(void*)*6 + 2, v___x_941_);
return v___x_945_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default(void){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = lean_obj_once(&l_Lean_instInhabitedInductiveVal_default___closed__0, &l_Lean_instInhabitedInductiveVal_default___closed__0_once, _init_l_Lean_instInhabitedInductiveVal_default___closed__0);
return v___x_946_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal(void){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Lean_instInhabitedInductiveVal_default;
return v___x_947_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveVal_beq(lean_object* v_x_948_, lean_object* v_x_949_){
_start:
{
lean_object* v_toConstantVal_950_; lean_object* v_numParams_951_; lean_object* v_numIndices_952_; lean_object* v_all_953_; lean_object* v_ctors_954_; lean_object* v_numNested_955_; uint8_t v_isRec_956_; uint8_t v_isUnsafe_957_; uint8_t v_isReflexive_958_; lean_object* v_toConstantVal_959_; lean_object* v_numParams_960_; lean_object* v_numIndices_961_; lean_object* v_all_962_; lean_object* v_ctors_963_; lean_object* v_numNested_964_; uint8_t v_isRec_965_; uint8_t v_isUnsafe_966_; uint8_t v_isReflexive_967_; uint8_t v___y_969_; uint8_t v___y_971_; uint8_t v___x_972_; 
v_toConstantVal_950_ = lean_ctor_get(v_x_948_, 0);
v_numParams_951_ = lean_ctor_get(v_x_948_, 1);
v_numIndices_952_ = lean_ctor_get(v_x_948_, 2);
v_all_953_ = lean_ctor_get(v_x_948_, 3);
v_ctors_954_ = lean_ctor_get(v_x_948_, 4);
v_numNested_955_ = lean_ctor_get(v_x_948_, 5);
v_isRec_956_ = lean_ctor_get_uint8(v_x_948_, sizeof(void*)*6);
v_isUnsafe_957_ = lean_ctor_get_uint8(v_x_948_, sizeof(void*)*6 + 1);
v_isReflexive_958_ = lean_ctor_get_uint8(v_x_948_, sizeof(void*)*6 + 2);
v_toConstantVal_959_ = lean_ctor_get(v_x_949_, 0);
v_numParams_960_ = lean_ctor_get(v_x_949_, 1);
v_numIndices_961_ = lean_ctor_get(v_x_949_, 2);
v_all_962_ = lean_ctor_get(v_x_949_, 3);
v_ctors_963_ = lean_ctor_get(v_x_949_, 4);
v_numNested_964_ = lean_ctor_get(v_x_949_, 5);
v_isRec_965_ = lean_ctor_get_uint8(v_x_949_, sizeof(void*)*6);
v_isUnsafe_966_ = lean_ctor_get_uint8(v_x_949_, sizeof(void*)*6 + 1);
v_isReflexive_967_ = lean_ctor_get_uint8(v_x_949_, sizeof(void*)*6 + 2);
v___x_972_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_950_, v_toConstantVal_959_);
if (v___x_972_ == 0)
{
return v___x_972_;
}
else
{
uint8_t v___x_973_; 
v___x_973_ = lean_nat_dec_eq(v_numParams_951_, v_numParams_960_);
if (v___x_973_ == 0)
{
return v___x_973_;
}
else
{
uint8_t v___x_974_; 
v___x_974_ = lean_nat_dec_eq(v_numIndices_952_, v_numIndices_961_);
if (v___x_974_ == 0)
{
return v___x_974_;
}
else
{
uint8_t v___x_975_; 
v___x_975_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_953_, v_all_962_);
if (v___x_975_ == 0)
{
return v___x_975_;
}
else
{
uint8_t v___x_976_; 
v___x_976_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_ctors_954_, v_ctors_963_);
if (v___x_976_ == 0)
{
return v___x_976_;
}
else
{
uint8_t v___x_977_; 
v___x_977_ = lean_nat_dec_eq(v_numNested_955_, v_numNested_964_);
if (v___x_977_ == 0)
{
return v___x_977_;
}
else
{
if (v_isRec_965_ == 0)
{
if (v_isRec_956_ == 0)
{
v___y_971_ = v___x_977_;
goto v___jp_970_;
}
else
{
return v_isRec_965_;
}
}
else
{
if (v_isRec_956_ == 0)
{
return v_isRec_956_;
}
else
{
v___y_971_ = v_isRec_956_;
goto v___jp_970_;
}
}
}
}
}
}
}
}
v___jp_968_:
{
if (v_isReflexive_967_ == 0)
{
if (v_isReflexive_958_ == 0)
{
return v___y_969_;
}
else
{
return v_isReflexive_967_;
}
}
else
{
return v_isReflexive_958_;
}
}
v___jp_970_:
{
if (v_isUnsafe_966_ == 0)
{
if (v_isUnsafe_957_ == 0)
{
v___y_969_ = v___y_971_;
goto v___jp_968_;
}
else
{
return v_isUnsafe_966_;
}
}
else
{
if (v_isUnsafe_957_ == 0)
{
return v_isUnsafe_957_;
}
else
{
v___y_969_ = v_isUnsafe_957_;
goto v___jp_968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveVal_beq___boxed(lean_object* v_x_978_, lean_object* v_x_979_){
_start:
{
uint8_t v_res_980_; lean_object* v_r_981_; 
v_res_980_ = l_Lean_instBEqInductiveVal_beq(v_x_978_, v_x_979_);
lean_dec_ref(v_x_979_);
lean_dec_ref(v_x_978_);
v_r_981_ = lean_box(v_res_980_);
return v_r_981_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_val(lean_object* v_name_984_, lean_object* v_levelParams_985_, lean_object* v_type_986_, lean_object* v_numParams_987_, lean_object* v_numIndices_988_, lean_object* v_all_989_, lean_object* v_ctors_990_, lean_object* v_numNested_991_, uint8_t v_isRec_992_, uint8_t v_isUnsafe_993_, uint8_t v_isReflexive_994_){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_995_, 0, v_name_984_);
lean_ctor_set(v___x_995_, 1, v_levelParams_985_);
lean_ctor_set(v___x_995_, 2, v_type_986_);
v___x_996_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_996_, 0, v___x_995_);
lean_ctor_set(v___x_996_, 1, v_numParams_987_);
lean_ctor_set(v___x_996_, 2, v_numIndices_988_);
lean_ctor_set(v___x_996_, 3, v_all_989_);
lean_ctor_set(v___x_996_, 4, v_ctors_990_);
lean_ctor_set(v___x_996_, 5, v_numNested_991_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*6, v_isRec_992_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*6 + 1, v_isUnsafe_993_);
lean_ctor_set_uint8(v___x_996_, sizeof(void*)*6 + 2, v_isReflexive_994_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveValEx___boxed(lean_object* v_name_997_, lean_object* v_levelParams_998_, lean_object* v_type_999_, lean_object* v_numParams_1000_, lean_object* v_numIndices_1001_, lean_object* v_all_1002_, lean_object* v_ctors_1003_, lean_object* v_numNested_1004_, lean_object* v_isRec_1005_, lean_object* v_isUnsafe_1006_, lean_object* v_isReflexive_1007_){
_start:
{
uint8_t v_isRec_boxed_1008_; uint8_t v_isUnsafe_boxed_1009_; uint8_t v_isReflexive_boxed_1010_; lean_object* v_res_1011_; 
v_isRec_boxed_1008_ = lean_unbox(v_isRec_1005_);
v_isUnsafe_boxed_1009_ = lean_unbox(v_isUnsafe_1006_);
v_isReflexive_boxed_1010_ = lean_unbox(v_isReflexive_1007_);
v_res_1011_ = lean_mk_inductive_val(v_name_997_, v_levelParams_998_, v_type_999_, v_numParams_1000_, v_numIndices_1001_, v_all_1002_, v_ctors_1003_, v_numNested_1004_, v_isRec_boxed_1008_, v_isUnsafe_boxed_1009_, v_isReflexive_boxed_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_rec(lean_object* v_v_1012_){
_start:
{
uint8_t v_isRec_1013_; 
v_isRec_1013_ = lean_ctor_get_uint8(v_v_1012_, sizeof(void*)*6);
lean_dec_ref(v_v_1012_);
return v_isRec_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isRecEx___boxed(lean_object* v_v_1014_){
_start:
{
uint8_t v_res_1015_; lean_object* v_r_1016_; 
v_res_1015_ = lean_inductive_val_is_rec(v_v_1014_);
v_r_1016_ = lean_box(v_res_1015_);
return v_r_1016_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_unsafe(lean_object* v_v_1017_){
_start:
{
uint8_t v_isUnsafe_1018_; 
v_isUnsafe_1018_ = lean_ctor_get_uint8(v_v_1017_, sizeof(void*)*6 + 1);
lean_dec_ref(v_v_1017_);
return v_isUnsafe_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isUnsafeEx___boxed(lean_object* v_v_1019_){
_start:
{
uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_res_1020_ = lean_inductive_val_is_unsafe(v_v_1019_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_reflexive(lean_object* v_v_1022_){
_start:
{
uint8_t v_isReflexive_1023_; 
v_isReflexive_1023_ = lean_ctor_get_uint8(v_v_1022_, sizeof(void*)*6 + 2);
lean_dec_ref(v_v_1022_);
return v_isReflexive_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isReflexiveEx___boxed(lean_object* v_v_1024_){
_start:
{
uint8_t v_res_1025_; lean_object* v_r_1026_; 
v_res_1025_ = lean_inductive_val_is_reflexive(v_v_1024_);
v_r_1026_ = lean_box(v_res_1025_);
return v_r_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors(lean_object* v_v_1027_){
_start:
{
lean_object* v_ctors_1028_; lean_object* v___x_1029_; 
v_ctors_1028_ = lean_ctor_get(v_v_1027_, 4);
v___x_1029_ = l_List_lengthTR___redArg(v_ctors_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors___boxed(lean_object* v_v_1030_){
_start:
{
lean_object* v_res_1031_; 
v_res_1031_ = l_Lean_InductiveVal_numCtors(v_v_1030_);
lean_dec_ref(v_v_1030_);
return v_res_1031_;
}
}
LEAN_EXPORT uint8_t l_Lean_InductiveVal_isNested(lean_object* v_v_1032_){
_start:
{
lean_object* v_numNested_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_numNested_1033_ = lean_ctor_get(v_v_1032_, 5);
v___x_1034_ = lean_unsigned_to_nat(0u);
v___x_1035_ = lean_nat_dec_lt(v___x_1034_, v_numNested_1033_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isNested___boxed(lean_object* v_v_1036_){
_start:
{
uint8_t v_res_1037_; lean_object* v_r_1038_; 
v_res_1037_ = l_Lean_InductiveVal_isNested(v_v_1036_);
lean_dec_ref(v_v_1036_);
v_r_1038_ = lean_box(v_res_1037_);
return v_r_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object* v_v_1039_){
_start:
{
lean_object* v_all_1040_; lean_object* v_numNested_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v_all_1040_ = lean_ctor_get(v_v_1039_, 3);
v_numNested_1041_ = lean_ctor_get(v_v_1039_, 5);
v___x_1042_ = l_List_lengthTR___redArg(v_all_1040_);
v___x_1043_ = lean_nat_add(v___x_1042_, v_numNested_1041_);
lean_dec(v___x_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers___boxed(lean_object* v_v_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_InductiveVal_numTypeFormers(v_v_1044_);
lean_dec_ref(v_v_1044_);
return v_res_1045_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1046_ = 0;
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = lean_box(0);
v___x_1049_ = l_Lean_instInhabitedConstantVal_default;
v___x_1050_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v___x_1048_);
lean_ctor_set(v___x_1050_, 2, v___x_1047_);
lean_ctor_set(v___x_1050_, 3, v___x_1047_);
lean_ctor_set(v___x_1050_, 4, v___x_1047_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*5, v___x_1046_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default(void){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_obj_once(&l_Lean_instInhabitedConstructorVal_default___closed__0, &l_Lean_instInhabitedConstructorVal_default___closed__0_once, _init_l_Lean_instInhabitedConstructorVal_default___closed__0);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal(void){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_instInhabitedConstructorVal_default;
return v___x_1052_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructorVal_beq(lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
lean_object* v_toConstantVal_1055_; lean_object* v_induct_1056_; lean_object* v_cidx_1057_; lean_object* v_numParams_1058_; lean_object* v_numFields_1059_; uint8_t v_isUnsafe_1060_; lean_object* v_toConstantVal_1061_; lean_object* v_induct_1062_; lean_object* v_cidx_1063_; lean_object* v_numParams_1064_; lean_object* v_numFields_1065_; uint8_t v_isUnsafe_1066_; uint8_t v___x_1067_; 
v_toConstantVal_1055_ = lean_ctor_get(v_x_1053_, 0);
v_induct_1056_ = lean_ctor_get(v_x_1053_, 1);
v_cidx_1057_ = lean_ctor_get(v_x_1053_, 2);
v_numParams_1058_ = lean_ctor_get(v_x_1053_, 3);
v_numFields_1059_ = lean_ctor_get(v_x_1053_, 4);
v_isUnsafe_1060_ = lean_ctor_get_uint8(v_x_1053_, sizeof(void*)*5);
v_toConstantVal_1061_ = lean_ctor_get(v_x_1054_, 0);
v_induct_1062_ = lean_ctor_get(v_x_1054_, 1);
v_cidx_1063_ = lean_ctor_get(v_x_1054_, 2);
v_numParams_1064_ = lean_ctor_get(v_x_1054_, 3);
v_numFields_1065_ = lean_ctor_get(v_x_1054_, 4);
v_isUnsafe_1066_ = lean_ctor_get_uint8(v_x_1054_, sizeof(void*)*5);
v___x_1067_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1055_, v_toConstantVal_1061_);
if (v___x_1067_ == 0)
{
return v___x_1067_;
}
else
{
uint8_t v___x_1068_; 
v___x_1068_ = lean_name_eq(v_induct_1056_, v_induct_1062_);
if (v___x_1068_ == 0)
{
return v___x_1068_;
}
else
{
uint8_t v___x_1069_; 
v___x_1069_ = lean_nat_dec_eq(v_cidx_1057_, v_cidx_1063_);
if (v___x_1069_ == 0)
{
return v___x_1069_;
}
else
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_nat_dec_eq(v_numParams_1058_, v_numParams_1064_);
if (v___x_1070_ == 0)
{
return v___x_1070_;
}
else
{
uint8_t v___x_1071_; 
v___x_1071_ = lean_nat_dec_eq(v_numFields_1059_, v_numFields_1065_);
if (v___x_1071_ == 0)
{
return v___x_1071_;
}
else
{
if (v_isUnsafe_1066_ == 0)
{
if (v_isUnsafe_1060_ == 0)
{
return v___x_1071_;
}
else
{
return v_isUnsafe_1066_;
}
}
else
{
return v_isUnsafe_1060_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructorVal_beq___boxed(lean_object* v_x_1072_, lean_object* v_x_1073_){
_start:
{
uint8_t v_res_1074_; lean_object* v_r_1075_; 
v_res_1074_ = l_Lean_instBEqConstructorVal_beq(v_x_1072_, v_x_1073_);
lean_dec_ref(v_x_1073_);
lean_dec_ref(v_x_1072_);
v_r_1075_ = lean_box(v_res_1074_);
return v_r_1075_;
}
}
LEAN_EXPORT lean_object* lean_mk_constructor_val(lean_object* v_name_1078_, lean_object* v_levelParams_1079_, lean_object* v_type_1080_, lean_object* v_induct_1081_, lean_object* v_cidx_1082_, lean_object* v_numParams_1083_, lean_object* v_numFields_1084_, uint8_t v_isUnsafe_1085_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1086_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1086_, 0, v_name_1078_);
lean_ctor_set(v___x_1086_, 1, v_levelParams_1079_);
lean_ctor_set(v___x_1086_, 2, v_type_1080_);
v___x_1087_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v_induct_1081_);
lean_ctor_set(v___x_1087_, 2, v_cidx_1082_);
lean_ctor_set(v___x_1087_, 3, v_numParams_1083_);
lean_ctor_set(v___x_1087_, 4, v_numFields_1084_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*5, v_isUnsafe_1085_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstructorValEx___boxed(lean_object* v_name_1088_, lean_object* v_levelParams_1089_, lean_object* v_type_1090_, lean_object* v_induct_1091_, lean_object* v_cidx_1092_, lean_object* v_numParams_1093_, lean_object* v_numFields_1094_, lean_object* v_isUnsafe_1095_){
_start:
{
uint8_t v_isUnsafe_boxed_1096_; lean_object* v_res_1097_; 
v_isUnsafe_boxed_1096_ = lean_unbox(v_isUnsafe_1095_);
v_res_1097_ = lean_mk_constructor_val(v_name_1088_, v_levelParams_1089_, v_type_1090_, v_induct_1091_, v_cidx_1092_, v_numParams_1093_, v_numFields_1094_, v_isUnsafe_boxed_1096_);
return v_res_1097_;
}
}
LEAN_EXPORT uint8_t lean_constructor_val_is_unsafe(lean_object* v_v_1098_){
_start:
{
uint8_t v_isUnsafe_1099_; 
v_isUnsafe_1099_ = lean_ctor_get_uint8(v_v_1098_, sizeof(void*)*5);
lean_dec_ref(v_v_1098_);
return v_isUnsafe_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstructorVal_isUnsafeEx___boxed(lean_object* v_v_1100_){
_start:
{
uint8_t v_res_1101_; lean_object* v_r_1102_; 
v_res_1101_ = lean_constructor_val_is_unsafe(v_v_1100_);
v_r_1102_ = lean_box(v_res_1101_);
return v_r_1102_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default___closed__0(void){
_start:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1103_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
lean_ctor_set(v___x_1106_, 1, v___x_1104_);
lean_ctor_set(v___x_1106_, 2, v___x_1103_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default(void){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_obj_once(&l_Lean_instInhabitedRecursorRule_default___closed__0, &l_Lean_instInhabitedRecursorRule_default___closed__0_once, _init_l_Lean_instInhabitedRecursorRule_default___closed__0);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule(void){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l_Lean_instInhabitedRecursorRule_default;
return v___x_1108_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorRule_beq(lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
lean_object* v_ctor_1111_; lean_object* v_nfields_1112_; lean_object* v_rhs_1113_; lean_object* v_ctor_1114_; lean_object* v_nfields_1115_; lean_object* v_rhs_1116_; uint8_t v___x_1117_; 
v_ctor_1111_ = lean_ctor_get(v_x_1109_, 0);
v_nfields_1112_ = lean_ctor_get(v_x_1109_, 1);
v_rhs_1113_ = lean_ctor_get(v_x_1109_, 2);
v_ctor_1114_ = lean_ctor_get(v_x_1110_, 0);
v_nfields_1115_ = lean_ctor_get(v_x_1110_, 1);
v_rhs_1116_ = lean_ctor_get(v_x_1110_, 2);
v___x_1117_ = lean_name_eq(v_ctor_1111_, v_ctor_1114_);
if (v___x_1117_ == 0)
{
return v___x_1117_;
}
else
{
uint8_t v___x_1118_; 
v___x_1118_ = lean_nat_dec_eq(v_nfields_1112_, v_nfields_1115_);
if (v___x_1118_ == 0)
{
return v___x_1118_;
}
else
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_expr_eqv(v_rhs_1113_, v_rhs_1116_);
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorRule_beq___boxed(lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
uint8_t v_res_1122_; lean_object* v_r_1123_; 
v_res_1122_ = l_Lean_instBEqRecursorRule_beq(v_x_1120_, v_x_1121_);
lean_dec_ref(v_x_1121_);
lean_dec_ref(v_x_1120_);
v_r_1123_ = lean_box(v_res_1122_);
return v_r_1123_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1126_ = 0;
v___x_1127_ = lean_unsigned_to_nat(0u);
v___x_1128_ = lean_box(0);
v___x_1129_ = l_Lean_instInhabitedConstantVal_default;
v___x_1130_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
lean_ctor_set(v___x_1130_, 1, v___x_1128_);
lean_ctor_set(v___x_1130_, 2, v___x_1127_);
lean_ctor_set(v___x_1130_, 3, v___x_1127_);
lean_ctor_set(v___x_1130_, 4, v___x_1127_);
lean_ctor_set(v___x_1130_, 5, v___x_1127_);
lean_ctor_set(v___x_1130_, 6, v___x_1128_);
lean_ctor_set_uint8(v___x_1130_, sizeof(void*)*7, v___x_1126_);
lean_ctor_set_uint8(v___x_1130_, sizeof(void*)*7 + 1, v___x_1126_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default(void){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_obj_once(&l_Lean_instInhabitedRecursorVal_default___closed__0, &l_Lean_instInhabitedRecursorVal_default___closed__0_once, _init_l_Lean_instInhabitedRecursorVal_default___closed__0);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal(void){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_instInhabitedRecursorVal_default;
return v___x_1132_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(lean_object* v_x_1133_, lean_object* v_x_1134_){
_start:
{
if (lean_obj_tag(v_x_1133_) == 0)
{
if (lean_obj_tag(v_x_1134_) == 0)
{
uint8_t v___x_1135_; 
v___x_1135_ = 1;
return v___x_1135_;
}
else
{
uint8_t v___x_1136_; 
v___x_1136_ = 0;
return v___x_1136_;
}
}
else
{
if (lean_obj_tag(v_x_1134_) == 0)
{
uint8_t v___x_1137_; 
v___x_1137_ = 0;
return v___x_1137_;
}
else
{
lean_object* v_head_1138_; lean_object* v_tail_1139_; lean_object* v_head_1140_; lean_object* v_tail_1141_; uint8_t v___x_1142_; 
v_head_1138_ = lean_ctor_get(v_x_1133_, 0);
v_tail_1139_ = lean_ctor_get(v_x_1133_, 1);
v_head_1140_ = lean_ctor_get(v_x_1134_, 0);
v_tail_1141_ = lean_ctor_get(v_x_1134_, 1);
v___x_1142_ = l_Lean_instBEqRecursorRule_beq(v_head_1138_, v_head_1140_);
if (v___x_1142_ == 0)
{
return v___x_1142_;
}
else
{
v_x_1133_ = v_tail_1139_;
v_x_1134_ = v_tail_1141_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0___boxed(lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
uint8_t v_res_1146_; lean_object* v_r_1147_; 
v_res_1146_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_x_1144_, v_x_1145_);
lean_dec(v_x_1145_);
lean_dec(v_x_1144_);
v_r_1147_ = lean_box(v_res_1146_);
return v_r_1147_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorVal_beq(lean_object* v_x_1148_, lean_object* v_x_1149_){
_start:
{
lean_object* v_toConstantVal_1150_; lean_object* v_all_1151_; lean_object* v_numParams_1152_; lean_object* v_numIndices_1153_; lean_object* v_numMotives_1154_; lean_object* v_numMinors_1155_; lean_object* v_rules_1156_; uint8_t v_k_1157_; uint8_t v_isUnsafe_1158_; lean_object* v_toConstantVal_1159_; lean_object* v_all_1160_; lean_object* v_numParams_1161_; lean_object* v_numIndices_1162_; lean_object* v_numMotives_1163_; lean_object* v_numMinors_1164_; lean_object* v_rules_1165_; uint8_t v_k_1166_; uint8_t v_isUnsafe_1167_; uint8_t v___y_1169_; uint8_t v___x_1170_; 
v_toConstantVal_1150_ = lean_ctor_get(v_x_1148_, 0);
v_all_1151_ = lean_ctor_get(v_x_1148_, 1);
v_numParams_1152_ = lean_ctor_get(v_x_1148_, 2);
v_numIndices_1153_ = lean_ctor_get(v_x_1148_, 3);
v_numMotives_1154_ = lean_ctor_get(v_x_1148_, 4);
v_numMinors_1155_ = lean_ctor_get(v_x_1148_, 5);
v_rules_1156_ = lean_ctor_get(v_x_1148_, 6);
v_k_1157_ = lean_ctor_get_uint8(v_x_1148_, sizeof(void*)*7);
v_isUnsafe_1158_ = lean_ctor_get_uint8(v_x_1148_, sizeof(void*)*7 + 1);
v_toConstantVal_1159_ = lean_ctor_get(v_x_1149_, 0);
v_all_1160_ = lean_ctor_get(v_x_1149_, 1);
v_numParams_1161_ = lean_ctor_get(v_x_1149_, 2);
v_numIndices_1162_ = lean_ctor_get(v_x_1149_, 3);
v_numMotives_1163_ = lean_ctor_get(v_x_1149_, 4);
v_numMinors_1164_ = lean_ctor_get(v_x_1149_, 5);
v_rules_1165_ = lean_ctor_get(v_x_1149_, 6);
v_k_1166_ = lean_ctor_get_uint8(v_x_1149_, sizeof(void*)*7);
v_isUnsafe_1167_ = lean_ctor_get_uint8(v_x_1149_, sizeof(void*)*7 + 1);
v___x_1170_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1150_, v_toConstantVal_1159_);
if (v___x_1170_ == 0)
{
return v___x_1170_;
}
else
{
uint8_t v___x_1171_; 
v___x_1171_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_1151_, v_all_1160_);
if (v___x_1171_ == 0)
{
return v___x_1171_;
}
else
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_nat_dec_eq(v_numParams_1152_, v_numParams_1161_);
if (v___x_1172_ == 0)
{
return v___x_1172_;
}
else
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_nat_dec_eq(v_numIndices_1153_, v_numIndices_1162_);
if (v___x_1173_ == 0)
{
return v___x_1173_;
}
else
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_nat_dec_eq(v_numMotives_1154_, v_numMotives_1163_);
if (v___x_1174_ == 0)
{
return v___x_1174_;
}
else
{
uint8_t v___x_1175_; 
v___x_1175_ = lean_nat_dec_eq(v_numMinors_1155_, v_numMinors_1164_);
if (v___x_1175_ == 0)
{
return v___x_1175_;
}
else
{
uint8_t v___x_1176_; 
v___x_1176_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_rules_1156_, v_rules_1165_);
if (v___x_1176_ == 0)
{
return v___x_1176_;
}
else
{
if (v_k_1166_ == 0)
{
if (v_k_1157_ == 0)
{
v___y_1169_ = v___x_1176_;
goto v___jp_1168_;
}
else
{
return v_k_1166_;
}
}
else
{
if (v_k_1157_ == 0)
{
return v_k_1157_;
}
else
{
v___y_1169_ = v_k_1157_;
goto v___jp_1168_;
}
}
}
}
}
}
}
}
}
v___jp_1168_:
{
if (v_isUnsafe_1167_ == 0)
{
if (v_isUnsafe_1158_ == 0)
{
return v___y_1169_;
}
else
{
return v_isUnsafe_1167_;
}
}
else
{
return v_isUnsafe_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorVal_beq___boxed(lean_object* v_x_1177_, lean_object* v_x_1178_){
_start:
{
uint8_t v_res_1179_; lean_object* v_r_1180_; 
v_res_1179_ = l_Lean_instBEqRecursorVal_beq(v_x_1177_, v_x_1178_);
lean_dec_ref(v_x_1178_);
lean_dec_ref(v_x_1177_);
v_r_1180_ = lean_box(v_res_1179_);
return v_r_1180_;
}
}
LEAN_EXPORT lean_object* lean_mk_recursor_val(lean_object* v_name_1183_, lean_object* v_levelParams_1184_, lean_object* v_type_1185_, lean_object* v_all_1186_, lean_object* v_numParams_1187_, lean_object* v_numIndices_1188_, lean_object* v_numMotives_1189_, lean_object* v_numMinors_1190_, lean_object* v_rules_1191_, uint8_t v_k_1192_, uint8_t v_isUnsafe_1193_){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1194_, 0, v_name_1183_);
lean_ctor_set(v___x_1194_, 1, v_levelParams_1184_);
lean_ctor_set(v___x_1194_, 2, v_type_1185_);
v___x_1195_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v_all_1186_);
lean_ctor_set(v___x_1195_, 2, v_numParams_1187_);
lean_ctor_set(v___x_1195_, 3, v_numIndices_1188_);
lean_ctor_set(v___x_1195_, 4, v_numMotives_1189_);
lean_ctor_set(v___x_1195_, 5, v_numMinors_1190_);
lean_ctor_set(v___x_1195_, 6, v_rules_1191_);
lean_ctor_set_uint8(v___x_1195_, sizeof(void*)*7, v_k_1192_);
lean_ctor_set_uint8(v___x_1195_, sizeof(void*)*7 + 1, v_isUnsafe_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecursorValEx___boxed(lean_object* v_name_1196_, lean_object* v_levelParams_1197_, lean_object* v_type_1198_, lean_object* v_all_1199_, lean_object* v_numParams_1200_, lean_object* v_numIndices_1201_, lean_object* v_numMotives_1202_, lean_object* v_numMinors_1203_, lean_object* v_rules_1204_, lean_object* v_k_1205_, lean_object* v_isUnsafe_1206_){
_start:
{
uint8_t v_k_boxed_1207_; uint8_t v_isUnsafe_boxed_1208_; lean_object* v_res_1209_; 
v_k_boxed_1207_ = lean_unbox(v_k_1205_);
v_isUnsafe_boxed_1208_ = lean_unbox(v_isUnsafe_1206_);
v_res_1209_ = lean_mk_recursor_val(v_name_1196_, v_levelParams_1197_, v_type_1198_, v_all_1199_, v_numParams_1200_, v_numIndices_1201_, v_numMotives_1202_, v_numMinors_1203_, v_rules_1204_, v_k_boxed_1207_, v_isUnsafe_boxed_1208_);
return v_res_1209_;
}
}
LEAN_EXPORT uint8_t lean_recursor_k(lean_object* v_v_1210_){
_start:
{
uint8_t v_k_1211_; 
v_k_1211_ = lean_ctor_get_uint8(v_v_1210_, sizeof(void*)*7);
lean_dec_ref(v_v_1210_);
return v_k_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_kEx___boxed(lean_object* v_v_1212_){
_start:
{
uint8_t v_res_1213_; lean_object* v_r_1214_; 
v_res_1213_ = lean_recursor_k(v_v_1212_);
v_r_1214_ = lean_box(v_res_1213_);
return v_r_1214_;
}
}
LEAN_EXPORT uint8_t lean_recursor_is_unsafe(lean_object* v_v_1215_){
_start:
{
uint8_t v_isUnsafe_1216_; 
v_isUnsafe_1216_ = lean_ctor_get_uint8(v_v_1215_, sizeof(void*)*7 + 1);
lean_dec_ref(v_v_1215_);
return v_isUnsafe_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_isUnsafeEx___boxed(lean_object* v_v_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = lean_recursor_is_unsafe(v_v_1217_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object* v_v_1220_){
_start:
{
lean_object* v_numParams_1221_; lean_object* v_numIndices_1222_; lean_object* v_numMotives_1223_; lean_object* v_numMinors_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; 
v_numParams_1221_ = lean_ctor_get(v_v_1220_, 2);
v_numIndices_1222_ = lean_ctor_get(v_v_1220_, 3);
v_numMotives_1223_ = lean_ctor_get(v_v_1220_, 4);
v_numMinors_1224_ = lean_ctor_get(v_v_1220_, 5);
v___x_1225_ = lean_nat_add(v_numParams_1221_, v_numMotives_1223_);
v___x_1226_ = lean_nat_add(v___x_1225_, v_numMinors_1224_);
lean_dec(v___x_1225_);
v___x_1227_ = lean_nat_add(v___x_1226_, v_numIndices_1222_);
lean_dec(v___x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx___boxed(lean_object* v_v_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_RecursorVal_getMajorIdx(v_v_1228_);
lean_dec_ref(v_v_1228_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx(lean_object* v_v_1230_){
_start:
{
lean_object* v_numParams_1231_; lean_object* v_numMotives_1232_; lean_object* v_numMinors_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v_numParams_1231_ = lean_ctor_get(v_v_1230_, 2);
v_numMotives_1232_ = lean_ctor_get(v_v_1230_, 4);
v_numMinors_1233_ = lean_ctor_get(v_v_1230_, 5);
v___x_1234_ = lean_nat_add(v_numParams_1231_, v_numMotives_1232_);
v___x_1235_ = lean_nat_add(v___x_1234_, v_numMinors_1233_);
lean_dec(v___x_1234_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx___boxed(lean_object* v_v_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_RecursorVal_getFirstIndexIdx(v_v_1236_);
lean_dec_ref(v_v_1236_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx(lean_object* v_v_1238_){
_start:
{
lean_object* v_numParams_1239_; lean_object* v_numMotives_1240_; lean_object* v___x_1241_; 
v_numParams_1239_ = lean_ctor_get(v_v_1238_, 2);
v_numMotives_1240_ = lean_ctor_get(v_v_1238_, 4);
v___x_1241_ = lean_nat_add(v_numParams_1239_, v_numMotives_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx___boxed(lean_object* v_v_1242_){
_start:
{
lean_object* v_res_1243_; 
v_res_1243_ = l_Lean_RecursorVal_getFirstMinorIdx(v_v_1242_);
lean_dec_ref(v_v_1242_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(lean_object* v_x_1244_, lean_object* v_x_1245_){
_start:
{
lean_object* v_zero_1246_; uint8_t v_isZero_1247_; 
v_zero_1246_ = lean_unsigned_to_nat(0u);
v_isZero_1247_ = lean_nat_dec_eq(v_x_1244_, v_zero_1246_);
if (v_isZero_1247_ == 1)
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_dec(v_x_1244_);
v___x_1248_ = l_Lean_Expr_bindingDomain_x21(v_x_1245_);
lean_dec_ref(v_x_1245_);
v___x_1249_ = l_Lean_Expr_getAppFn(v___x_1248_);
lean_dec_ref(v___x_1248_);
v___x_1250_ = l_Lean_Expr_constName_x21(v___x_1249_);
lean_dec_ref(v___x_1249_);
return v___x_1250_;
}
else
{
lean_object* v_one_1251_; lean_object* v_n_1252_; lean_object* v___x_1253_; 
v_one_1251_ = lean_unsigned_to_nat(1u);
v_n_1252_ = lean_nat_sub(v_x_1244_, v_one_1251_);
lean_dec(v_x_1244_);
v___x_1253_ = l_Lean_Expr_bindingBody_x21(v_x_1245_);
lean_dec_ref(v_x_1245_);
v_x_1244_ = v_n_1252_;
v_x_1245_ = v___x_1253_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorInduct(lean_object* v_v_1255_){
_start:
{
lean_object* v_toConstantVal_1256_; lean_object* v_type_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v_toConstantVal_1256_ = lean_ctor_get(v_v_1255_, 0);
v_type_1257_ = lean_ctor_get(v_toConstantVal_1256_, 2);
lean_inc_ref(v_type_1257_);
v___x_1258_ = l_Lean_RecursorVal_getMajorIdx(v_v_1255_);
lean_dec_ref(v_v_1255_);
v___x_1259_ = l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(v___x_1258_, v_type_1257_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___impl(uint8_t v_x_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_box(v_x_1260_);
v___x_1262_ = lean_obj_tag_nat(v___x_1261_);
lean_dec(v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___impl___boxed(lean_object* v_x_1263_){
_start:
{
uint8_t v_x_4__boxed_1264_; lean_object* v_res_1265_; 
v_x_4__boxed_1264_ = lean_unbox(v_x_1263_);
v_res_1265_ = l_Lean_QuotKind_ctorIdx___impl(v_x_4__boxed_1264_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg(lean_object* v_k_1266_){
_start:
{
lean_inc(v_k_1266_);
return v_k_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg___boxed(lean_object* v_k_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_QuotKind_ctorElim___redArg(v_k_1267_);
lean_dec(v_k_1267_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim(lean_object* v_motive_1269_, lean_object* v_ctorIdx_1270_, uint8_t v_t_1271_, lean_object* v_h_1272_, lean_object* v_k_1273_){
_start:
{
lean_inc(v_k_1273_);
return v_k_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___boxed(lean_object* v_motive_1274_, lean_object* v_ctorIdx_1275_, lean_object* v_t_1276_, lean_object* v_h_1277_, lean_object* v_k_1278_){
_start:
{
uint8_t v_t_boxed_1279_; lean_object* v_res_1280_; 
v_t_boxed_1279_ = lean_unbox(v_t_1276_);
v_res_1280_ = l_Lean_QuotKind_ctorElim(v_motive_1274_, v_ctorIdx_1275_, v_t_boxed_1279_, v_h_1277_, v_k_1278_);
lean_dec(v_k_1278_);
lean_dec(v_ctorIdx_1275_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg(lean_object* v_type_1281_){
_start:
{
lean_inc(v_type_1281_);
return v_type_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg___boxed(lean_object* v_type_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_QuotKind_type_elim___redArg(v_type_1282_);
lean_dec(v_type_1282_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim(lean_object* v_motive_1284_, uint8_t v_t_1285_, lean_object* v_h_1286_, lean_object* v_type_1287_){
_start:
{
lean_inc(v_type_1287_);
return v_type_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___boxed(lean_object* v_motive_1288_, lean_object* v_t_1289_, lean_object* v_h_1290_, lean_object* v_type_1291_){
_start:
{
uint8_t v_t_boxed_1292_; lean_object* v_res_1293_; 
v_t_boxed_1292_ = lean_unbox(v_t_1289_);
v_res_1293_ = l_Lean_QuotKind_type_elim(v_motive_1288_, v_t_boxed_1292_, v_h_1290_, v_type_1291_);
lean_dec(v_type_1291_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg(lean_object* v_ctor_1294_){
_start:
{
lean_inc(v_ctor_1294_);
return v_ctor_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg___boxed(lean_object* v_ctor_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Lean_QuotKind_ctor_elim___redArg(v_ctor_1295_);
lean_dec(v_ctor_1295_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim(lean_object* v_motive_1297_, uint8_t v_t_1298_, lean_object* v_h_1299_, lean_object* v_ctor_1300_){
_start:
{
lean_inc(v_ctor_1300_);
return v_ctor_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___boxed(lean_object* v_motive_1301_, lean_object* v_t_1302_, lean_object* v_h_1303_, lean_object* v_ctor_1304_){
_start:
{
uint8_t v_t_boxed_1305_; lean_object* v_res_1306_; 
v_t_boxed_1305_ = lean_unbox(v_t_1302_);
v_res_1306_ = l_Lean_QuotKind_ctor_elim(v_motive_1301_, v_t_boxed_1305_, v_h_1303_, v_ctor_1304_);
lean_dec(v_ctor_1304_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg(lean_object* v_lift_1307_){
_start:
{
lean_inc(v_lift_1307_);
return v_lift_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg___boxed(lean_object* v_lift_1308_){
_start:
{
lean_object* v_res_1309_; 
v_res_1309_ = l_Lean_QuotKind_lift_elim___redArg(v_lift_1308_);
lean_dec(v_lift_1308_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim(lean_object* v_motive_1310_, uint8_t v_t_1311_, lean_object* v_h_1312_, lean_object* v_lift_1313_){
_start:
{
lean_inc(v_lift_1313_);
return v_lift_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___boxed(lean_object* v_motive_1314_, lean_object* v_t_1315_, lean_object* v_h_1316_, lean_object* v_lift_1317_){
_start:
{
uint8_t v_t_boxed_1318_; lean_object* v_res_1319_; 
v_t_boxed_1318_ = lean_unbox(v_t_1315_);
v_res_1319_ = l_Lean_QuotKind_lift_elim(v_motive_1314_, v_t_boxed_1318_, v_h_1316_, v_lift_1317_);
lean_dec(v_lift_1317_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg(lean_object* v_ind_1320_){
_start:
{
lean_inc(v_ind_1320_);
return v_ind_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg___boxed(lean_object* v_ind_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Lean_QuotKind_ind_elim___redArg(v_ind_1321_);
lean_dec(v_ind_1321_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim(lean_object* v_motive_1323_, uint8_t v_t_1324_, lean_object* v_h_1325_, lean_object* v_ind_1326_){
_start:
{
lean_inc(v_ind_1326_);
return v_ind_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___boxed(lean_object* v_motive_1327_, lean_object* v_t_1328_, lean_object* v_h_1329_, lean_object* v_ind_1330_){
_start:
{
uint8_t v_t_boxed_1331_; lean_object* v_res_1332_; 
v_t_boxed_1331_ = lean_unbox(v_t_1328_);
v_res_1332_ = l_Lean_QuotKind_ind_elim(v_motive_1327_, v_t_boxed_1331_, v_h_1329_, v_ind_1330_);
lean_dec(v_ind_1330_);
return v_res_1332_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind_default(void){
_start:
{
uint8_t v___x_1333_; 
v___x_1333_ = 0;
return v___x_1333_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind(void){
_start:
{
uint8_t v___x_1334_; 
v___x_1334_ = 0;
return v___x_1334_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqQuotKind_beq(uint8_t v_x_1335_, uint8_t v_y_1336_){
_start:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1337_ = lean_box(v_x_1335_);
v___x_1338_ = lean_obj_tag_nat(v___x_1337_);
lean_dec(v___x_1337_);
v___x_1339_ = lean_box(v_y_1336_);
v___x_1340_ = lean_obj_tag_nat(v___x_1339_);
lean_dec(v___x_1339_);
v___x_1341_ = lean_nat_dec_eq(v___x_1338_, v___x_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqQuotKind_beq___boxed(lean_object* v_x_1342_, lean_object* v_y_1343_){
_start:
{
uint8_t v_x_24__boxed_1344_; uint8_t v_y_25__boxed_1345_; uint8_t v_res_1346_; lean_object* v_r_1347_; 
v_x_24__boxed_1344_ = lean_unbox(v_x_1342_);
v_y_25__boxed_1345_ = lean_unbox(v_y_1343_);
v_res_1346_ = l_Lean_instBEqQuotKind_beq(v_x_24__boxed_1344_, v_y_25__boxed_1345_);
v_r_1347_ = lean_box(v_res_1346_);
return v_r_1347_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default___closed__0(void){
_start:
{
uint8_t v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1350_ = 0;
v___x_1351_ = l_Lean_instInhabitedConstantVal_default;
v___x_1352_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1352_, 0, v___x_1351_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*1, v___x_1350_);
return v___x_1352_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default(void){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_obj_once(&l_Lean_instInhabitedQuotVal_default___closed__0, &l_Lean_instInhabitedQuotVal_default___closed__0_once, _init_l_Lean_instInhabitedQuotVal_default___closed__0);
return v___x_1353_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal(void){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Lean_instInhabitedQuotVal_default;
return v___x_1354_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqQuotVal_beq(lean_object* v_x_1355_, lean_object* v_x_1356_){
_start:
{
lean_object* v_toConstantVal_1357_; uint8_t v_kind_1358_; lean_object* v_toConstantVal_1359_; uint8_t v_kind_1360_; uint8_t v___x_1361_; 
v_toConstantVal_1357_ = lean_ctor_get(v_x_1355_, 0);
v_kind_1358_ = lean_ctor_get_uint8(v_x_1355_, sizeof(void*)*1);
v_toConstantVal_1359_ = lean_ctor_get(v_x_1356_, 0);
v_kind_1360_ = lean_ctor_get_uint8(v_x_1356_, sizeof(void*)*1);
v___x_1361_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1357_, v_toConstantVal_1359_);
if (v___x_1361_ == 0)
{
return v___x_1361_;
}
else
{
uint8_t v___x_1362_; 
v___x_1362_ = l_Lean_instBEqQuotKind_beq(v_kind_1358_, v_kind_1360_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqQuotVal_beq___boxed(lean_object* v_x_1363_, lean_object* v_x_1364_){
_start:
{
uint8_t v_res_1365_; lean_object* v_r_1366_; 
v_res_1365_ = l_Lean_instBEqQuotVal_beq(v_x_1363_, v_x_1364_);
lean_dec_ref(v_x_1364_);
lean_dec_ref(v_x_1363_);
v_r_1366_ = lean_box(v_res_1365_);
return v_r_1366_;
}
}
LEAN_EXPORT lean_object* lean_mk_quot_val(lean_object* v_name_1369_, lean_object* v_levelParams_1370_, lean_object* v_type_1371_, uint8_t v_kind_1372_){
_start:
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1373_, 0, v_name_1369_);
lean_ctor_set(v___x_1373_, 1, v_levelParams_1370_);
lean_ctor_set(v___x_1373_, 2, v_type_1371_);
v___x_1374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1374_, 0, v___x_1373_);
lean_ctor_set_uint8(v___x_1374_, sizeof(void*)*1, v_kind_1372_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkQuotValEx___boxed(lean_object* v_name_1375_, lean_object* v_levelParams_1376_, lean_object* v_type_1377_, lean_object* v_kind_1378_){
_start:
{
uint8_t v_kind_boxed_1379_; lean_object* v_res_1380_; 
v_kind_boxed_1379_ = lean_unbox(v_kind_1378_);
v_res_1380_ = lean_mk_quot_val(v_name_1375_, v_levelParams_1376_, v_type_1377_, v_kind_boxed_1379_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___impl(lean_object* v_x_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_obj_tag_nat(v_x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___impl___boxed(lean_object* v_x_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Lean_ConstantInfo_ctorIdx___impl(v_x_1383_);
lean_dec_ref(v_x_1383_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___redArg(lean_object* v_t_1385_, lean_object* v_k_1386_){
_start:
{
lean_object* v_val_1387_; lean_object* v___x_1388_; 
v_val_1387_ = lean_ctor_get(v_t_1385_, 0);
lean_inc_ref(v_val_1387_);
lean_dec_ref(v_t_1385_);
v___x_1388_ = lean_apply_1(v_k_1386_, v_val_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim(lean_object* v_motive_1389_, lean_object* v_ctorIdx_1390_, lean_object* v_t_1391_, lean_object* v_h_1392_, lean_object* v_k_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1391_, v_k_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___boxed(lean_object* v_motive_1395_, lean_object* v_ctorIdx_1396_, lean_object* v_t_1397_, lean_object* v_h_1398_, lean_object* v_k_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_ConstantInfo_ctorElim(v_motive_1395_, v_ctorIdx_1396_, v_t_1397_, v_h_1398_, v_k_1399_);
lean_dec(v_ctorIdx_1396_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim___redArg(lean_object* v_t_1401_, lean_object* v_axiomInfo_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1401_, v_axiomInfo_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim(lean_object* v_motive_1404_, lean_object* v_t_1405_, lean_object* v_h_1406_, lean_object* v_axiomInfo_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1405_, v_axiomInfo_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim___redArg(lean_object* v_t_1409_, lean_object* v_defnInfo_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1409_, v_defnInfo_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim(lean_object* v_motive_1412_, lean_object* v_t_1413_, lean_object* v_h_1414_, lean_object* v_defnInfo_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1413_, v_defnInfo_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim___redArg(lean_object* v_t_1417_, lean_object* v_thmInfo_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1417_, v_thmInfo_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim(lean_object* v_motive_1420_, lean_object* v_t_1421_, lean_object* v_h_1422_, lean_object* v_thmInfo_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1421_, v_thmInfo_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim___redArg(lean_object* v_t_1425_, lean_object* v_opaqueInfo_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1425_, v_opaqueInfo_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim(lean_object* v_motive_1428_, lean_object* v_t_1429_, lean_object* v_h_1430_, lean_object* v_opaqueInfo_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1429_, v_opaqueInfo_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim___redArg(lean_object* v_t_1433_, lean_object* v_quotInfo_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1433_, v_quotInfo_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim(lean_object* v_motive_1436_, lean_object* v_t_1437_, lean_object* v_h_1438_, lean_object* v_quotInfo_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1437_, v_quotInfo_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim___redArg(lean_object* v_t_1441_, lean_object* v_inductInfo_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1441_, v_inductInfo_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim(lean_object* v_motive_1444_, lean_object* v_t_1445_, lean_object* v_h_1446_, lean_object* v_inductInfo_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1445_, v_inductInfo_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim___redArg(lean_object* v_t_1449_, lean_object* v_ctorInfo_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1449_, v_ctorInfo_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim(lean_object* v_motive_1452_, lean_object* v_t_1453_, lean_object* v_h_1454_, lean_object* v_ctorInfo_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1453_, v_ctorInfo_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim___redArg(lean_object* v_t_1457_, lean_object* v_recInfo_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1457_, v_recInfo_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim(lean_object* v_motive_1460_, lean_object* v_t_1461_, lean_object* v_h_1462_, lean_object* v_recInfo_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1461_, v_recInfo_1463_);
return v___x_1464_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default___closed__0(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = l_Lean_instInhabitedAxiomVal_default;
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v___x_1465_);
return v___x_1466_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default(void){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = lean_obj_once(&l_Lean_instInhabitedConstantInfo_default___closed__0, &l_Lean_instInhabitedConstantInfo_default___closed__0_once, _init_l_Lean_instInhabitedConstantInfo_default___closed__0);
return v___x_1467_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo(void){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_instInhabitedConstantInfo_default;
return v___x_1468_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstantInfo_beq(lean_object* v_x_1469_, lean_object* v_x_1470_){
_start:
{
switch(lean_obj_tag(v_x_1469_))
{
case 0:
{
if (lean_obj_tag(v_x_1470_) == 0)
{
lean_object* v_val_1471_; lean_object* v_val_1472_; uint8_t v___x_1473_; 
v_val_1471_ = lean_ctor_get(v_x_1469_, 0);
v_val_1472_ = lean_ctor_get(v_x_1470_, 0);
v___x_1473_ = l_Lean_instBEqAxiomVal_beq(v_val_1471_, v_val_1472_);
return v___x_1473_;
}
else
{
uint8_t v___x_1474_; 
v___x_1474_ = 0;
return v___x_1474_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1470_) == 1)
{
lean_object* v_val_1475_; lean_object* v_val_1476_; uint8_t v___x_1477_; 
v_val_1475_ = lean_ctor_get(v_x_1469_, 0);
v_val_1476_ = lean_ctor_get(v_x_1470_, 0);
v___x_1477_ = l_Lean_instBEqDefinitionVal_beq(v_val_1475_, v_val_1476_);
return v___x_1477_;
}
else
{
uint8_t v___x_1478_; 
v___x_1478_ = 0;
return v___x_1478_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1470_) == 2)
{
lean_object* v_val_1479_; lean_object* v_val_1480_; uint8_t v___x_1481_; 
v_val_1479_ = lean_ctor_get(v_x_1469_, 0);
v_val_1480_ = lean_ctor_get(v_x_1470_, 0);
v___x_1481_ = l_Lean_instBEqTheoremVal_beq(v_val_1479_, v_val_1480_);
return v___x_1481_;
}
else
{
uint8_t v___x_1482_; 
v___x_1482_ = 0;
return v___x_1482_;
}
}
case 3:
{
if (lean_obj_tag(v_x_1470_) == 3)
{
lean_object* v_val_1483_; lean_object* v_val_1484_; uint8_t v___x_1485_; 
v_val_1483_ = lean_ctor_get(v_x_1469_, 0);
v_val_1484_ = lean_ctor_get(v_x_1470_, 0);
v___x_1485_ = l_Lean_instBEqOpaqueVal_beq(v_val_1483_, v_val_1484_);
return v___x_1485_;
}
else
{
uint8_t v___x_1486_; 
v___x_1486_ = 0;
return v___x_1486_;
}
}
case 4:
{
if (lean_obj_tag(v_x_1470_) == 4)
{
lean_object* v_val_1487_; lean_object* v_val_1488_; uint8_t v___x_1489_; 
v_val_1487_ = lean_ctor_get(v_x_1469_, 0);
v_val_1488_ = lean_ctor_get(v_x_1470_, 0);
v___x_1489_ = l_Lean_instBEqQuotVal_beq(v_val_1487_, v_val_1488_);
return v___x_1489_;
}
else
{
uint8_t v___x_1490_; 
v___x_1490_ = 0;
return v___x_1490_;
}
}
case 5:
{
if (lean_obj_tag(v_x_1470_) == 5)
{
lean_object* v_val_1491_; lean_object* v_val_1492_; uint8_t v___x_1493_; 
v_val_1491_ = lean_ctor_get(v_x_1469_, 0);
v_val_1492_ = lean_ctor_get(v_x_1470_, 0);
v___x_1493_ = l_Lean_instBEqInductiveVal_beq(v_val_1491_, v_val_1492_);
return v___x_1493_;
}
else
{
uint8_t v___x_1494_; 
v___x_1494_ = 0;
return v___x_1494_;
}
}
case 6:
{
if (lean_obj_tag(v_x_1470_) == 6)
{
lean_object* v_val_1495_; lean_object* v_val_1496_; uint8_t v___x_1497_; 
v_val_1495_ = lean_ctor_get(v_x_1469_, 0);
v_val_1496_ = lean_ctor_get(v_x_1470_, 0);
v___x_1497_ = l_Lean_instBEqConstructorVal_beq(v_val_1495_, v_val_1496_);
return v___x_1497_;
}
else
{
uint8_t v___x_1498_; 
v___x_1498_ = 0;
return v___x_1498_;
}
}
default: 
{
if (lean_obj_tag(v_x_1470_) == 7)
{
lean_object* v_val_1499_; lean_object* v_val_1500_; uint8_t v___x_1501_; 
v_val_1499_ = lean_ctor_get(v_x_1469_, 0);
v_val_1500_ = lean_ctor_get(v_x_1470_, 0);
v___x_1501_ = l_Lean_instBEqRecursorVal_beq(v_val_1499_, v_val_1500_);
return v___x_1501_;
}
else
{
uint8_t v___x_1502_; 
v___x_1502_ = 0;
return v___x_1502_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstantInfo_beq___boxed(lean_object* v_x_1503_, lean_object* v_x_1504_){
_start:
{
uint8_t v_res_1505_; lean_object* v_r_1506_; 
v_res_1505_ = l_Lean_instBEqConstantInfo_beq(v_x_1503_, v_x_1504_);
lean_dec_ref(v_x_1504_);
lean_dec_ref(v_x_1503_);
v_r_1506_ = lean_box(v_res_1505_);
return v_r_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object* v_x_1509_){
_start:
{
lean_object* v_val_1510_; lean_object* v_toConstantVal_1511_; 
v_val_1510_ = lean_ctor_get(v_x_1509_, 0);
v_toConstantVal_1511_ = lean_ctor_get(v_val_1510_, 0);
lean_inc_ref(v_toConstantVal_1511_);
return v_toConstantVal_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object* v_x_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_ConstantInfo_toConstantVal(v_x_1512_);
lean_dec_ref(v_x_1512_);
return v_res_1513_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object* v_x_1514_){
_start:
{
switch(lean_obj_tag(v_x_1514_))
{
case 0:
{
lean_object* v_val_1515_; uint8_t v_isUnsafe_1516_; 
v_val_1515_ = lean_ctor_get(v_x_1514_, 0);
v_isUnsafe_1516_ = lean_ctor_get_uint8(v_val_1515_, sizeof(void*)*1);
return v_isUnsafe_1516_;
}
case 1:
{
lean_object* v_val_1517_; uint8_t v_safety_1518_; uint8_t v___x_1519_; uint8_t v___x_1520_; 
v_val_1517_ = lean_ctor_get(v_x_1514_, 0);
v_safety_1518_ = lean_ctor_get_uint8(v_val_1517_, sizeof(void*)*4);
v___x_1519_ = 0;
v___x_1520_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1518_, v___x_1519_);
return v___x_1520_;
}
case 3:
{
lean_object* v_val_1521_; uint8_t v_isUnsafe_1522_; 
v_val_1521_ = lean_ctor_get(v_x_1514_, 0);
v_isUnsafe_1522_ = lean_ctor_get_uint8(v_val_1521_, sizeof(void*)*3);
return v_isUnsafe_1522_;
}
case 5:
{
lean_object* v_val_1523_; uint8_t v_isUnsafe_1524_; 
v_val_1523_ = lean_ctor_get(v_x_1514_, 0);
v_isUnsafe_1524_ = lean_ctor_get_uint8(v_val_1523_, sizeof(void*)*6 + 1);
return v_isUnsafe_1524_;
}
case 6:
{
lean_object* v_val_1525_; uint8_t v_isUnsafe_1526_; 
v_val_1525_ = lean_ctor_get(v_x_1514_, 0);
v_isUnsafe_1526_ = lean_ctor_get_uint8(v_val_1525_, sizeof(void*)*5);
return v_isUnsafe_1526_;
}
case 7:
{
lean_object* v_val_1527_; uint8_t v_isUnsafe_1528_; 
v_val_1527_ = lean_ctor_get(v_x_1514_, 0);
v_isUnsafe_1528_ = lean_ctor_get_uint8(v_val_1527_, sizeof(void*)*7 + 1);
return v_isUnsafe_1528_;
}
default: 
{
uint8_t v___x_1529_; 
v___x_1529_ = 0;
return v___x_1529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isUnsafe___boxed(lean_object* v_x_1530_){
_start:
{
uint8_t v_res_1531_; lean_object* v_r_1532_; 
v_res_1531_ = l_Lean_ConstantInfo_isUnsafe(v_x_1530_);
lean_dec_ref(v_x_1530_);
v_r_1532_ = lean_box(v_res_1531_);
return v_r_1532_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isPartial(lean_object* v_x_1533_){
_start:
{
if (lean_obj_tag(v_x_1533_) == 1)
{
lean_object* v_val_1534_; uint8_t v_safety_1535_; uint8_t v___x_1536_; uint8_t v___x_1537_; 
v_val_1534_ = lean_ctor_get(v_x_1533_, 0);
v_safety_1535_ = lean_ctor_get_uint8(v_val_1534_, sizeof(void*)*4);
v___x_1536_ = 2;
v___x_1537_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1535_, v___x_1536_);
return v___x_1537_;
}
else
{
uint8_t v___x_1538_; 
v___x_1538_ = 0;
return v___x_1538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isPartial___boxed(lean_object* v_x_1539_){
_start:
{
uint8_t v_res_1540_; lean_object* v_r_1541_; 
v_res_1540_ = l_Lean_ConstantInfo_isPartial(v_x_1539_);
lean_dec_ref(v_x_1539_);
v_r_1541_ = lean_box(v_res_1540_);
return v_r_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name(lean_object* v_d_1542_){
_start:
{
lean_object* v___x_1543_; lean_object* v_name_1544_; 
v___x_1543_ = l_Lean_ConstantInfo_toConstantVal(v_d_1542_);
v_name_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_name_1544_);
lean_dec_ref(v___x_1543_);
return v_name_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name___boxed(lean_object* v_d_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_ConstantInfo_name(v_d_1545_);
lean_dec_ref(v_d_1545_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams(lean_object* v_d_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v_levelParams_1549_; 
v___x_1548_ = l_Lean_ConstantInfo_toConstantVal(v_d_1547_);
v_levelParams_1549_ = lean_ctor_get(v___x_1548_, 1);
lean_inc(v_levelParams_1549_);
lean_dec_ref(v___x_1548_);
return v_levelParams_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams___boxed(lean_object* v_d_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_ConstantInfo_levelParams(v_d_1550_);
lean_dec_ref(v_d_1550_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object* v_d_1552_){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = l_Lean_ConstantInfo_levelParams(v_d_1552_);
v___x_1554_ = l_List_lengthTR___redArg(v___x_1553_);
lean_dec(v___x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams___boxed(lean_object* v_d_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Lean_ConstantInfo_numLevelParams(v_d_1555_);
lean_dec_ref(v_d_1555_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type(lean_object* v_d_1557_){
_start:
{
lean_object* v___x_1558_; lean_object* v_type_1559_; 
v___x_1558_ = l_Lean_ConstantInfo_toConstantVal(v_d_1557_);
v_type_1559_ = lean_ctor_get(v___x_1558_, 2);
lean_inc_ref(v_type_1559_);
lean_dec_ref(v___x_1558_);
return v_type_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type___boxed(lean_object* v_d_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_ConstantInfo_type(v_d_1560_);
lean_dec_ref(v_d_1560_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f(lean_object* v_info_1562_, uint8_t v_allowOpaque_1563_){
_start:
{
switch(lean_obj_tag(v_info_1562_))
{
case 1:
{
lean_object* v_val_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1572_; 
v_val_1564_ = lean_ctor_get(v_info_1562_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_info_1562_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1566_ = v_info_1562_;
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_val_1564_);
lean_dec(v_info_1562_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v_value_1568_; lean_object* v___x_1570_; 
v_value_1568_ = lean_ctor_get(v_val_1564_, 1);
lean_inc_ref(v_value_1568_);
lean_dec_ref(v_val_1564_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v_value_1568_);
v___x_1570_ = v___x_1566_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_value_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
case 2:
{
lean_object* v_val_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1582_; 
v_val_1573_ = lean_ctor_get(v_info_1562_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_info_1562_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1575_ = v_info_1562_;
v_isShared_1576_ = v_isSharedCheck_1582_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_val_1573_);
lean_dec(v_info_1562_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1582_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
if (v_allowOpaque_1563_ == 0)
{
lean_object* v___x_1577_; 
lean_del_object(v___x_1575_);
lean_dec_ref(v_val_1573_);
v___x_1577_ = lean_box(0);
return v___x_1577_;
}
else
{
lean_object* v_value_1578_; lean_object* v___x_1580_; 
v_value_1578_ = lean_ctor_get(v_val_1573_, 1);
lean_inc_ref(v_value_1578_);
lean_dec_ref(v_val_1573_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set_tag(v___x_1575_, 1);
lean_ctor_set(v___x_1575_, 0, v_value_1578_);
v___x_1580_ = v___x_1575_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_value_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
case 3:
{
lean_object* v_val_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1592_; 
v_val_1583_ = lean_ctor_get(v_info_1562_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_info_1562_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1585_ = v_info_1562_;
v_isShared_1586_ = v_isSharedCheck_1592_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_val_1583_);
lean_dec(v_info_1562_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1592_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
if (v_allowOpaque_1563_ == 0)
{
lean_object* v___x_1587_; 
lean_del_object(v___x_1585_);
lean_dec_ref(v_val_1583_);
v___x_1587_ = lean_box(0);
return v___x_1587_;
}
else
{
lean_object* v_value_1588_; lean_object* v___x_1590_; 
v_value_1588_ = lean_ctor_get(v_val_1583_, 1);
lean_inc_ref(v_value_1588_);
lean_dec_ref(v_val_1583_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set_tag(v___x_1585_, 1);
lean_ctor_set(v___x_1585_, 0, v_value_1588_);
v___x_1590_ = v___x_1585_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_value_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
default: 
{
lean_object* v___x_1593_; 
lean_dec_ref(v_info_1562_);
v___x_1593_ = lean_box(0);
return v___x_1593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f___boxed(lean_object* v_info_1594_, lean_object* v_allowOpaque_1595_){
_start:
{
uint8_t v_allowOpaque_boxed_1596_; lean_object* v_res_1597_; 
v_allowOpaque_boxed_1596_ = lean_unbox(v_allowOpaque_1595_);
v_res_1597_ = l_Lean_ConstantInfo_value_x3f(v_info_1594_, v_allowOpaque_boxed_1596_);
return v_res_1597_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_hasValue(lean_object* v_info_1598_, uint8_t v_allowOpaque_1599_){
_start:
{
switch(lean_obj_tag(v_info_1598_))
{
case 1:
{
uint8_t v___x_1600_; 
v___x_1600_ = 1;
return v___x_1600_;
}
case 2:
{
return v_allowOpaque_1599_;
}
case 3:
{
return v_allowOpaque_1599_;
}
default: 
{
uint8_t v___x_1601_; 
v___x_1601_ = 0;
return v___x_1601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object* v_info_1602_, lean_object* v_allowOpaque_1603_){
_start:
{
uint8_t v_allowOpaque_boxed_1604_; uint8_t v_res_1605_; lean_object* v_r_1606_; 
v_allowOpaque_boxed_1604_ = lean_unbox(v_allowOpaque_1603_);
v_res_1605_ = l_Lean_ConstantInfo_hasValue(v_info_1602_, v_allowOpaque_boxed_1604_);
lean_dec_ref(v_info_1602_);
v_r_1606_ = lean_box(v_res_1605_);
return v_r_1606_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(lean_object* v_msg_1607_){
_start:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1608_ = l_Lean_instInhabitedExpr;
v___x_1609_ = lean_panic_fn_borrowed(v___x_1608_, v_msg_1607_);
return v___x_1609_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__2(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1612_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1613_ = lean_unsigned_to_nat(62u);
v___x_1614_ = lean_unsigned_to_nat(490u);
v___x_1615_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1616_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1617_ = l_mkPanicMessageWithDecl(v___x_1616_, v___x_1615_, v___x_1614_, v___x_1613_, v___x_1612_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__3(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1618_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1619_ = lean_unsigned_to_nat(62u);
v___x_1620_ = lean_unsigned_to_nat(491u);
v___x_1621_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1622_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1623_ = l_mkPanicMessageWithDecl(v___x_1622_, v___x_1621_, v___x_1620_, v___x_1619_, v___x_1618_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21(lean_object* v_info_1626_, uint8_t v_allowOpaque_1627_){
_start:
{
switch(lean_obj_tag(v_info_1626_))
{
case 1:
{
lean_object* v_val_1628_; lean_object* v_value_1629_; 
v_val_1628_ = lean_ctor_get(v_info_1626_, 0);
v_value_1629_ = lean_ctor_get(v_val_1628_, 1);
lean_inc_ref(v_value_1629_);
return v_value_1629_;
}
case 2:
{
if (v_allowOpaque_1627_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__2, &l_Lean_ConstantInfo_value_x21___closed__2_once, _init_l_Lean_ConstantInfo_value_x21___closed__2);
v___x_1631_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1630_);
return v___x_1631_;
}
else
{
lean_object* v_val_1632_; lean_object* v_value_1633_; 
v_val_1632_ = lean_ctor_get(v_info_1626_, 0);
v_value_1633_ = lean_ctor_get(v_val_1632_, 1);
lean_inc_ref(v_value_1633_);
return v_value_1633_;
}
}
case 3:
{
if (v_allowOpaque_1627_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
v___x_1634_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__3, &l_Lean_ConstantInfo_value_x21___closed__3_once, _init_l_Lean_ConstantInfo_value_x21___closed__3);
v___x_1635_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1634_);
return v___x_1635_;
}
else
{
lean_object* v_val_1636_; lean_object* v_value_1637_; 
v_val_1636_ = lean_ctor_get(v_info_1626_, 0);
v_value_1637_ = lean_ctor_get(v_val_1636_, 1);
lean_inc_ref(v_value_1637_);
return v_value_1637_;
}
}
default: 
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1638_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1639_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1640_ = lean_unsigned_to_nat(492u);
v___x_1641_ = lean_unsigned_to_nat(31u);
v___x_1642_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__4));
v___x_1643_ = l_Lean_ConstantInfo_name(v_info_1626_);
v___x_1644_ = 1;
v___x_1645_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1643_, v___x_1644_);
v___x_1646_ = lean_string_append(v___x_1642_, v___x_1645_);
lean_dec_ref(v___x_1645_);
v___x_1647_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__5));
v___x_1648_ = lean_string_append(v___x_1646_, v___x_1647_);
v___x_1649_ = l_mkPanicMessageWithDecl(v___x_1638_, v___x_1639_, v___x_1640_, v___x_1641_, v___x_1648_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1649_);
return v___x_1650_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21___boxed(lean_object* v_info_1651_, lean_object* v_allowOpaque_1652_){
_start:
{
uint8_t v_allowOpaque_boxed_1653_; lean_object* v_res_1654_; 
v_allowOpaque_boxed_1653_ = lean_unbox(v_allowOpaque_1652_);
v_res_1654_ = l_Lean_ConstantInfo_value_x21(v_info_1651_, v_allowOpaque_boxed_1653_);
lean_dec_ref(v_info_1651_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints(lean_object* v_x_1655_){
_start:
{
if (lean_obj_tag(v_x_1655_) == 1)
{
lean_object* v_val_1656_; lean_object* v_hints_1657_; 
v_val_1656_ = lean_ctor_get(v_x_1655_, 0);
v_hints_1657_ = lean_ctor_get(v_val_1656_, 2);
lean_inc(v_hints_1657_);
return v_hints_1657_;
}
else
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_box(0);
return v___x_1658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object* v_x_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Lean_ConstantInfo_hints(v_x_1659_);
lean_dec_ref(v_x_1659_);
return v_res_1660_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isCtor(lean_object* v_x_1661_){
_start:
{
if (lean_obj_tag(v_x_1661_) == 6)
{
uint8_t v___x_1662_; 
v___x_1662_ = 1;
return v___x_1662_;
}
else
{
uint8_t v___x_1663_; 
v___x_1663_ = 0;
return v___x_1663_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isCtor___boxed(lean_object* v_x_1664_){
_start:
{
uint8_t v_res_1665_; lean_object* v_r_1666_; 
v_res_1665_ = l_Lean_ConstantInfo_isCtor(v_x_1664_);
lean_dec_ref(v_x_1664_);
v_r_1666_ = lean_box(v_res_1665_);
return v_r_1666_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isAxiom(lean_object* v_x_1667_){
_start:
{
if (lean_obj_tag(v_x_1667_) == 0)
{
uint8_t v___x_1668_; 
v___x_1668_ = 1;
return v___x_1668_;
}
else
{
uint8_t v___x_1669_; 
v___x_1669_ = 0;
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isAxiom___boxed(lean_object* v_x_1670_){
_start:
{
uint8_t v_res_1671_; lean_object* v_r_1672_; 
v_res_1671_ = l_Lean_ConstantInfo_isAxiom(v_x_1670_);
lean_dec_ref(v_x_1670_);
v_r_1672_ = lean_box(v_res_1671_);
return v_r_1672_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isInductive(lean_object* v_x_1673_){
_start:
{
if (lean_obj_tag(v_x_1673_) == 5)
{
uint8_t v___x_1674_; 
v___x_1674_ = 1;
return v___x_1674_;
}
else
{
uint8_t v___x_1675_; 
v___x_1675_ = 0;
return v___x_1675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isInductive___boxed(lean_object* v_x_1676_){
_start:
{
uint8_t v_res_1677_; lean_object* v_r_1678_; 
v_res_1677_ = l_Lean_ConstantInfo_isInductive(v_x_1676_);
lean_dec_ref(v_x_1676_);
v_r_1678_ = lean_box(v_res_1677_);
return v_r_1678_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isDefinition(lean_object* v_x_1679_){
_start:
{
if (lean_obj_tag(v_x_1679_) == 1)
{
uint8_t v___x_1680_; 
v___x_1680_ = 1;
return v___x_1680_;
}
else
{
uint8_t v___x_1681_; 
v___x_1681_ = 0;
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isDefinition___boxed(lean_object* v_x_1682_){
_start:
{
uint8_t v_res_1683_; lean_object* v_r_1684_; 
v_res_1683_ = l_Lean_ConstantInfo_isDefinition(v_x_1682_);
lean_dec_ref(v_x_1682_);
v_r_1684_ = lean_box(v_res_1683_);
return v_r_1684_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isTheorem(lean_object* v_x_1685_){
_start:
{
if (lean_obj_tag(v_x_1685_) == 2)
{
uint8_t v___x_1686_; 
v___x_1686_ = 1;
return v___x_1686_;
}
else
{
uint8_t v___x_1687_; 
v___x_1687_ = 0;
return v___x_1687_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isTheorem___boxed(lean_object* v_x_1688_){
_start:
{
uint8_t v_res_1689_; lean_object* v_r_1690_; 
v_res_1689_ = l_Lean_ConstantInfo_isTheorem(v_x_1688_);
lean_dec_ref(v_x_1688_);
v_r_1690_ = lean_box(v_res_1689_);
return v_r_1690_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(lean_object* v_msg_1691_){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = l_Lean_instInhabitedInductiveVal_default;
v___x_1693_ = lean_panic_fn_borrowed(v___x_1692_, v_msg_1691_);
return v___x_1693_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1696_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__1));
v___x_1697_ = lean_unsigned_to_nat(9u);
v___x_1698_ = lean_unsigned_to_nat(520u);
v___x_1699_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__0));
v___x_1700_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1701_ = l_mkPanicMessageWithDecl(v___x_1700_, v___x_1699_, v___x_1698_, v___x_1697_, v___x_1696_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object* v_x_1702_){
_start:
{
if (lean_obj_tag(v_x_1702_) == 5)
{
lean_object* v_val_1703_; 
v_val_1703_ = lean_ctor_get(v_x_1702_, 0);
lean_inc_ref(v_val_1703_);
return v_val_1703_;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_obj_once(&l_Lean_ConstantInfo_inductiveVal_x21___closed__2, &l_Lean_ConstantInfo_inductiveVal_x21___closed__2_once, _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2);
v___x_1705_ = l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(v___x_1704_);
return v___x_1705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21___boxed(lean_object* v_x_1706_){
_start:
{
lean_object* v_res_1707_; 
v_res_1707_ = l_Lean_ConstantInfo_inductiveVal_x21(v_x_1706_);
lean_dec_ref(v_x_1706_);
return v_res_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all(lean_object* v_x_1708_){
_start:
{
switch(lean_obj_tag(v_x_1708_))
{
case 5:
{
lean_object* v_val_1709_; lean_object* v_all_1710_; 
v_val_1709_ = lean_ctor_get(v_x_1708_, 0);
v_all_1710_ = lean_ctor_get(v_val_1709_, 3);
lean_inc(v_all_1710_);
return v_all_1710_;
}
case 1:
{
lean_object* v_val_1711_; lean_object* v_all_1712_; 
v_val_1711_ = lean_ctor_get(v_x_1708_, 0);
v_all_1712_ = lean_ctor_get(v_val_1711_, 3);
lean_inc(v_all_1712_);
return v_all_1712_;
}
case 2:
{
lean_object* v_val_1713_; lean_object* v_all_1714_; 
v_val_1713_ = lean_ctor_get(v_x_1708_, 0);
v_all_1714_ = lean_ctor_get(v_val_1713_, 2);
lean_inc(v_all_1714_);
return v_all_1714_;
}
case 3:
{
lean_object* v_val_1715_; lean_object* v_all_1716_; 
v_val_1715_ = lean_ctor_get(v_x_1708_, 0);
v_all_1716_ = lean_ctor_get(v_val_1715_, 2);
lean_inc(v_all_1716_);
return v_all_1716_;
}
default: 
{
lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = l_Lean_ConstantInfo_name(v_x_1708_);
v___x_1718_ = lean_box(0);
v___x_1719_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1717_);
lean_ctor_set(v___x_1719_, 1, v___x_1718_);
return v___x_1719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all___boxed(lean_object* v_x_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Lean_ConstantInfo_all(v_x_1720_);
lean_dec_ref(v_x_1720_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecName(lean_object* v_declName_1722_){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0));
v___x_1724_ = l_Lean_Name_str___override(v_declName_1722_, v___x_1723_);
return v___x_1724_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Declaration(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedReducibilityHints_default = _init_l_Lean_instInhabitedReducibilityHints_default();
lean_mark_persistent(l_Lean_instInhabitedReducibilityHints_default);
l_Lean_instInhabitedReducibilityHints = _init_l_Lean_instInhabitedReducibilityHints();
lean_mark_persistent(l_Lean_instInhabitedReducibilityHints);
l_Lean_instInhabitedConstantVal_default = _init_l_Lean_instInhabitedConstantVal_default();
lean_mark_persistent(l_Lean_instInhabitedConstantVal_default);
l_Lean_instInhabitedConstantVal = _init_l_Lean_instInhabitedConstantVal();
lean_mark_persistent(l_Lean_instInhabitedConstantVal);
l_Lean_instInhabitedAxiomVal_default = _init_l_Lean_instInhabitedAxiomVal_default();
lean_mark_persistent(l_Lean_instInhabitedAxiomVal_default);
l_Lean_instInhabitedAxiomVal = _init_l_Lean_instInhabitedAxiomVal();
lean_mark_persistent(l_Lean_instInhabitedAxiomVal);
l_Lean_instInhabitedDefinitionSafety_default = _init_l_Lean_instInhabitedDefinitionSafety_default();
l_Lean_instInhabitedDefinitionSafety = _init_l_Lean_instInhabitedDefinitionSafety();
l_Lean_instInhabitedDefinitionVal_default = _init_l_Lean_instInhabitedDefinitionVal_default();
lean_mark_persistent(l_Lean_instInhabitedDefinitionVal_default);
l_Lean_instInhabitedDefinitionVal = _init_l_Lean_instInhabitedDefinitionVal();
lean_mark_persistent(l_Lean_instInhabitedDefinitionVal);
l_Lean_instInhabitedTheoremVal_default = _init_l_Lean_instInhabitedTheoremVal_default();
lean_mark_persistent(l_Lean_instInhabitedTheoremVal_default);
l_Lean_instInhabitedTheoremVal = _init_l_Lean_instInhabitedTheoremVal();
lean_mark_persistent(l_Lean_instInhabitedTheoremVal);
l_Lean_instInhabitedOpaqueVal_default = _init_l_Lean_instInhabitedOpaqueVal_default();
lean_mark_persistent(l_Lean_instInhabitedOpaqueVal_default);
l_Lean_instInhabitedOpaqueVal = _init_l_Lean_instInhabitedOpaqueVal();
lean_mark_persistent(l_Lean_instInhabitedOpaqueVal);
l_Lean_instInhabitedConstructor_default = _init_l_Lean_instInhabitedConstructor_default();
lean_mark_persistent(l_Lean_instInhabitedConstructor_default);
l_Lean_instInhabitedConstructor = _init_l_Lean_instInhabitedConstructor();
lean_mark_persistent(l_Lean_instInhabitedConstructor);
l_Lean_instInhabitedInductiveType_default = _init_l_Lean_instInhabitedInductiveType_default();
lean_mark_persistent(l_Lean_instInhabitedInductiveType_default);
l_Lean_instInhabitedInductiveType = _init_l_Lean_instInhabitedInductiveType();
lean_mark_persistent(l_Lean_instInhabitedInductiveType);
l_Lean_instInhabitedDeclaration_default = _init_l_Lean_instInhabitedDeclaration_default();
lean_mark_persistent(l_Lean_instInhabitedDeclaration_default);
l_Lean_instInhabitedDeclaration = _init_l_Lean_instInhabitedDeclaration();
lean_mark_persistent(l_Lean_instInhabitedDeclaration);
l_Lean_instInhabitedInductiveVal_default = _init_l_Lean_instInhabitedInductiveVal_default();
lean_mark_persistent(l_Lean_instInhabitedInductiveVal_default);
l_Lean_instInhabitedInductiveVal = _init_l_Lean_instInhabitedInductiveVal();
lean_mark_persistent(l_Lean_instInhabitedInductiveVal);
l_Lean_instInhabitedConstructorVal_default = _init_l_Lean_instInhabitedConstructorVal_default();
lean_mark_persistent(l_Lean_instInhabitedConstructorVal_default);
l_Lean_instInhabitedConstructorVal = _init_l_Lean_instInhabitedConstructorVal();
lean_mark_persistent(l_Lean_instInhabitedConstructorVal);
l_Lean_instInhabitedRecursorRule_default = _init_l_Lean_instInhabitedRecursorRule_default();
lean_mark_persistent(l_Lean_instInhabitedRecursorRule_default);
l_Lean_instInhabitedRecursorRule = _init_l_Lean_instInhabitedRecursorRule();
lean_mark_persistent(l_Lean_instInhabitedRecursorRule);
l_Lean_instInhabitedRecursorVal_default = _init_l_Lean_instInhabitedRecursorVal_default();
lean_mark_persistent(l_Lean_instInhabitedRecursorVal_default);
l_Lean_instInhabitedRecursorVal = _init_l_Lean_instInhabitedRecursorVal();
lean_mark_persistent(l_Lean_instInhabitedRecursorVal);
l_Lean_instInhabitedQuotKind_default = _init_l_Lean_instInhabitedQuotKind_default();
l_Lean_instInhabitedQuotKind = _init_l_Lean_instInhabitedQuotKind();
l_Lean_instInhabitedQuotVal_default = _init_l_Lean_instInhabitedQuotVal_default();
lean_mark_persistent(l_Lean_instInhabitedQuotVal_default);
l_Lean_instInhabitedQuotVal = _init_l_Lean_instInhabitedQuotVal();
lean_mark_persistent(l_Lean_instInhabitedQuotVal);
l_Lean_instInhabitedConstantInfo_default = _init_l_Lean_instInhabitedConstantInfo_default();
lean_mark_persistent(l_Lean_instInhabitedConstantInfo_default);
l_Lean_instInhabitedConstantInfo = _init_l_Lean_instInhabitedConstantInfo();
lean_mark_persistent(l_Lean_instInhabitedConstantInfo);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Declaration(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Declaration(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_UInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Declaration(builtin);
}
#ifdef __cplusplus
}
#endif
