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
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* lean_mk_reducibility_hints_regular(uint32_t);
LEAN_EXPORT lean_object* l_Lean_mkReducibilityHintsRegularEx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* lean_mk_theorem_val(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedOpaqueVal_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedOpaqueVal_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedOpaqueVal_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedOpaqueVal;
LEAN_EXPORT uint8_t l_Lean_instBEqOpaqueVal_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqOpaqueVal_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqOpaqueVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqOpaqueVal_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqOpaqueVal___closed__0 = (const lean_object*)&l_Lean_instBEqOpaqueVal___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instBEqOpaqueVal = (const lean_object*)&l_Lean_instBEqOpaqueVal___closed__0_value;
LEAN_EXPORT lean_object* lean_mk_opaque_val(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkOpaqueValEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT uint8_t lean_quot_val_kind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_QuotVal_kindEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorIdx(lean_object* v_x_1_){
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
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_ReducibilityHints_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 2)
{
uint32_t v_a_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_a_9_ = lean_ctor_get_uint32(v_t_7_, 0);
v___x_10_ = lean_box_uint32(v_a_9_);
v___x_11_ = lean_apply_1(v_k_8_, v___x_10_);
return v___x_11_;
}
else
{
return v_k_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorElim___redArg___boxed(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_12_, v_k_13_);
lean_dec(v_t_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_ReducibilityHints_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_t_23_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_opaque_elim___redArg(lean_object* v_t_27_, lean_object* v_opaque_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_27_, v_opaque_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_opaque_elim___redArg___boxed(lean_object* v_t_30_, lean_object* v_opaque_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_ReducibilityHints_opaque_elim___redArg(v_t_30_, v_opaque_31_);
lean_dec(v_t_30_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_opaque_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_opaque_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_34_, v_opaque_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_opaque_elim___boxed(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_opaque_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_ReducibilityHints_opaque_elim(v_motive_38_, v_t_39_, v_h_40_, v_opaque_41_);
lean_dec(v_t_39_);
return v_res_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_abbrev_elim___redArg(lean_object* v_t_43_, lean_object* v_abbrev_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_43_, v_abbrev_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_abbrev_elim___redArg___boxed(lean_object* v_t_46_, lean_object* v_abbrev_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Lean_ReducibilityHints_abbrev_elim___redArg(v_t_46_, v_abbrev_47_);
lean_dec(v_t_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_abbrev_elim(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_abbrev_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_50_, v_abbrev_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_abbrev_elim___boxed(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_abbrev_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_ReducibilityHints_abbrev_elim(v_motive_54_, v_t_55_, v_h_56_, v_abbrev_57_);
lean_dec(v_t_55_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_regular_elim___redArg(lean_object* v_t_59_, lean_object* v_regular_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_59_, v_regular_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_regular_elim___redArg___boxed(lean_object* v_t_62_, lean_object* v_regular_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_ReducibilityHints_regular_elim___redArg(v_t_62_, v_regular_63_);
lean_dec(v_t_62_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_regular_elim(lean_object* v_motive_65_, lean_object* v_t_66_, lean_object* v_h_67_, lean_object* v_regular_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l_Lean_ReducibilityHints_ctorElim___redArg(v_t_66_, v_regular_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_regular_elim___boxed(lean_object* v_motive_70_, lean_object* v_t_71_, lean_object* v_h_72_, lean_object* v_regular_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_ReducibilityHints_regular_elim(v_motive_70_, v_t_71_, v_h_72_, v_regular_73_);
lean_dec(v_t_71_);
return v_res_74_;
}
}
static lean_object* _init_l_Lean_instInhabitedReducibilityHints_default(void){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = lean_box(0);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_instInhabitedReducibilityHints(void){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = lean_box(0);
return v___x_76_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqReducibilityHints_beq(lean_object* v_x_77_, lean_object* v_x_78_){
_start:
{
switch(lean_obj_tag(v_x_77_))
{
case 0:
{
if (lean_obj_tag(v_x_78_) == 0)
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
case 1:
{
if (lean_obj_tag(v_x_78_) == 1)
{
uint8_t v___x_81_; 
v___x_81_ = 1;
return v___x_81_;
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
}
default: 
{
if (lean_obj_tag(v_x_78_) == 2)
{
uint32_t v_a_83_; uint32_t v_a_84_; uint8_t v___x_85_; 
v_a_83_ = lean_ctor_get_uint32(v_x_77_, 0);
v_a_84_ = lean_ctor_get_uint32(v_x_78_, 0);
v___x_85_ = lean_uint32_dec_eq(v_a_83_, v_a_84_);
return v___x_85_;
}
else
{
uint8_t v___x_86_; 
v___x_86_ = 0;
return v___x_86_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqReducibilityHints_beq___boxed(lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Lean_instBEqReducibilityHints_beq(v_x_87_, v_x_88_);
lean_dec(v_x_88_);
lean_dec(v_x_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT lean_object* lean_mk_reducibility_hints_regular(uint32_t v_h_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_alloc_ctor(2, 0, 4);
lean_ctor_set_uint32(v___x_94_, 0, v_h_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkReducibilityHintsRegularEx___boxed(lean_object* v_h_95_){
_start:
{
uint32_t v_h_boxed_96_; lean_object* v_res_97_; 
v_h_boxed_96_ = lean_unbox_uint32(v_h_95_);
lean_dec(v_h_95_);
v_res_97_ = lean_mk_reducibility_hints_regular(v_h_boxed_96_);
return v_res_97_;
}
}
LEAN_EXPORT uint32_t lean_reducibility_hints_get_height(lean_object* v_h_98_){
_start:
{
if (lean_obj_tag(v_h_98_) == 2)
{
uint32_t v_a_99_; 
v_a_99_ = lean_ctor_get_uint32(v_h_98_, 0);
lean_dec_ref_known(v_h_98_, 0);
return v_a_99_;
}
else
{
uint32_t v___x_100_; 
lean_dec(v_h_98_);
v___x_100_ = 0;
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_getHeightEx___boxed(lean_object* v_h_101_){
_start:
{
uint32_t v_res_102_; lean_object* v_r_103_; 
v_res_102_ = lean_reducibility_hints_get_height(v_h_101_);
v_r_103_ = lean_box_uint32(v_res_102_);
return v_r_103_;
}
}
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_lt(lean_object* v_x_104_, lean_object* v_x_105_){
_start:
{
switch(lean_obj_tag(v_x_104_))
{
case 1:
{
if (lean_obj_tag(v_x_105_) == 1)
{
uint8_t v___x_106_; 
v___x_106_ = 0;
return v___x_106_;
}
else
{
uint8_t v___x_107_; 
v___x_107_ = 1;
return v___x_107_;
}
}
case 2:
{
switch(lean_obj_tag(v_x_105_))
{
case 2:
{
uint32_t v_a_108_; uint32_t v_a_109_; uint8_t v___x_110_; 
v_a_108_ = lean_ctor_get_uint32(v_x_104_, 0);
v_a_109_ = lean_ctor_get_uint32(v_x_105_, 0);
v___x_110_ = lean_uint32_dec_lt(v_a_109_, v_a_108_);
return v___x_110_;
}
case 0:
{
uint8_t v___x_111_; 
v___x_111_ = 1;
return v___x_111_;
}
default: 
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
}
default: 
{
uint8_t v___x_113_; 
v___x_113_ = 0;
return v___x_113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_lt___boxed(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Lean_ReducibilityHints_lt(v_x_114_, v_x_115_);
lean_dec(v_x_115_);
lean_dec(v_x_114_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_compare(lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
switch(lean_obj_tag(v_x_118_))
{
case 0:
{
if (lean_obj_tag(v_x_119_) == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 1;
return v___x_120_;
}
else
{
uint8_t v___x_121_; 
v___x_121_ = 2;
return v___x_121_;
}
}
case 1:
{
if (lean_obj_tag(v_x_119_) == 1)
{
uint8_t v___x_122_; 
v___x_122_ = 1;
return v___x_122_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = 0;
return v___x_123_;
}
}
default: 
{
switch(lean_obj_tag(v_x_119_))
{
case 0:
{
uint8_t v___x_124_; 
v___x_124_ = 0;
return v___x_124_;
}
case 1:
{
uint8_t v___x_125_; 
v___x_125_ = 2;
return v___x_125_;
}
default: 
{
uint32_t v_a_126_; uint32_t v_a_127_; uint8_t v___x_128_; 
v_a_126_ = lean_ctor_get_uint32(v_x_118_, 0);
v_a_127_ = lean_ctor_get_uint32(v_x_119_, 0);
v___x_128_ = lean_uint32_dec_lt(v_a_127_, v_a_126_);
if (v___x_128_ == 0)
{
uint8_t v___x_129_; 
v___x_129_ = lean_uint32_dec_eq(v_a_127_, v_a_126_);
if (v___x_129_ == 0)
{
uint8_t v___x_130_; 
v___x_130_ = 2;
return v___x_130_;
}
else
{
uint8_t v___x_131_; 
v___x_131_ = 1;
return v___x_131_;
}
}
else
{
uint8_t v___x_132_; 
v___x_132_ = 0;
return v___x_132_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_compare___boxed(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Lean_ReducibilityHints_compare(v_x_133_, v_x_134_);
lean_dec(v_x_134_);
lean_dec(v_x_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_isAbbrev(lean_object* v_x_139_){
_start:
{
if (lean_obj_tag(v_x_139_) == 1)
{
uint8_t v___x_140_; 
v___x_140_ = 1;
return v___x_140_;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = 0;
return v___x_141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_isAbbrev___boxed(lean_object* v_x_142_){
_start:
{
uint8_t v_res_143_; lean_object* v_r_144_; 
v_res_143_ = l_Lean_ReducibilityHints_isAbbrev(v_x_142_);
lean_dec(v_x_142_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_isRegular(lean_object* v_x_145_){
_start:
{
if (lean_obj_tag(v_x_145_) == 2)
{
uint8_t v___x_146_; 
v___x_146_ = 1;
return v___x_146_;
}
else
{
uint8_t v___x_147_; 
v___x_147_ = 0;
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_isRegular___boxed(lean_object* v_x_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Lean_ReducibilityHints_isRegular(v_x_148_);
lean_dec(v_x_148_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal_default___closed__2(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_154_ = lean_box(0);
v___x_155_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_156_ = l_Lean_Expr_const___override(v___x_155_, v___x_154_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal_default___closed__3(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_157_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__2, &l_Lean_instInhabitedConstantVal_default___closed__2_once, _init_l_Lean_instInhabitedConstantVal_default___closed__2);
v___x_158_ = lean_box(0);
v___x_159_ = lean_box(0);
v___x_160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v___x_158_);
lean_ctor_set(v___x_160_, 2, v___x_157_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal_default(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__3, &l_Lean_instInhabitedConstantVal_default___closed__3_once, _init_l_Lean_instInhabitedConstantVal_default___closed__3);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal(void){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_instInhabitedConstantVal_default;
return v___x_162_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
if (lean_obj_tag(v_x_163_) == 0)
{
if (lean_obj_tag(v_x_164_) == 0)
{
uint8_t v___x_165_; 
v___x_165_ = 1;
return v___x_165_;
}
else
{
uint8_t v___x_166_; 
v___x_166_ = 0;
return v___x_166_;
}
}
else
{
if (lean_obj_tag(v_x_164_) == 0)
{
uint8_t v___x_167_; 
v___x_167_ = 0;
return v___x_167_;
}
else
{
lean_object* v_head_168_; lean_object* v_tail_169_; lean_object* v_head_170_; lean_object* v_tail_171_; uint8_t v___x_172_; 
v_head_168_ = lean_ctor_get(v_x_163_, 0);
v_tail_169_ = lean_ctor_get(v_x_163_, 1);
v_head_170_ = lean_ctor_get(v_x_164_, 0);
v_tail_171_ = lean_ctor_get(v_x_164_, 1);
v___x_172_ = lean_name_eq(v_head_168_, v_head_170_);
if (v___x_172_ == 0)
{
return v___x_172_;
}
else
{
v_x_163_ = v_tail_169_;
v_x_164_ = v_tail_171_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0___boxed(lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
uint8_t v_res_176_; lean_object* v_r_177_; 
v_res_176_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_x_174_, v_x_175_);
lean_dec(v_x_175_);
lean_dec(v_x_174_);
v_r_177_ = lean_box(v_res_176_);
return v_r_177_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstantVal_beq(lean_object* v_x_178_, lean_object* v_x_179_){
_start:
{
lean_object* v_name_180_; lean_object* v_levelParams_181_; lean_object* v_type_182_; lean_object* v_name_183_; lean_object* v_levelParams_184_; lean_object* v_type_185_; uint8_t v___x_186_; 
v_name_180_ = lean_ctor_get(v_x_178_, 0);
v_levelParams_181_ = lean_ctor_get(v_x_178_, 1);
v_type_182_ = lean_ctor_get(v_x_178_, 2);
v_name_183_ = lean_ctor_get(v_x_179_, 0);
v_levelParams_184_ = lean_ctor_get(v_x_179_, 1);
v_type_185_ = lean_ctor_get(v_x_179_, 2);
v___x_186_ = lean_name_eq(v_name_180_, v_name_183_);
if (v___x_186_ == 0)
{
return v___x_186_;
}
else
{
uint8_t v___x_187_; 
v___x_187_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_levelParams_181_, v_levelParams_184_);
if (v___x_187_ == 0)
{
return v___x_187_;
}
else
{
uint8_t v___x_188_; 
v___x_188_ = lean_expr_eqv(v_type_182_, v_type_185_);
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstantVal_beq___boxed(lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
uint8_t v_res_191_; lean_object* v_r_192_; 
v_res_191_ = l_Lean_instBEqConstantVal_beq(v_x_189_, v_x_190_);
lean_dec_ref(v_x_190_);
lean_dec_ref(v_x_189_);
v_r_192_ = lean_box(v_res_191_);
return v_r_192_;
}
}
static lean_object* _init_l_Lean_instInhabitedAxiomVal_default___closed__0(void){
_start:
{
uint8_t v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = 0;
v___x_196_ = l_Lean_instInhabitedConstantVal_default;
v___x_197_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*1, v___x_195_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_instInhabitedAxiomVal_default(void){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_obj_once(&l_Lean_instInhabitedAxiomVal_default___closed__0, &l_Lean_instInhabitedAxiomVal_default___closed__0_once, _init_l_Lean_instInhabitedAxiomVal_default___closed__0);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_instInhabitedAxiomVal(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = l_Lean_instInhabitedAxiomVal_default;
return v___x_199_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAxiomVal_beq(lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
lean_object* v_toConstantVal_202_; uint8_t v_isUnsafe_203_; lean_object* v_toConstantVal_204_; uint8_t v_isUnsafe_205_; uint8_t v___x_206_; 
v_toConstantVal_202_ = lean_ctor_get(v_x_200_, 0);
v_isUnsafe_203_ = lean_ctor_get_uint8(v_x_200_, sizeof(void*)*1);
v_toConstantVal_204_ = lean_ctor_get(v_x_201_, 0);
v_isUnsafe_205_ = lean_ctor_get_uint8(v_x_201_, sizeof(void*)*1);
v___x_206_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_202_, v_toConstantVal_204_);
if (v___x_206_ == 0)
{
return v___x_206_;
}
else
{
if (v_isUnsafe_205_ == 0)
{
if (v_isUnsafe_203_ == 0)
{
return v___x_206_;
}
else
{
return v_isUnsafe_205_;
}
}
else
{
return v_isUnsafe_203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAxiomVal_beq___boxed(lean_object* v_x_207_, lean_object* v_x_208_){
_start:
{
uint8_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = l_Lean_instBEqAxiomVal_beq(v_x_207_, v_x_208_);
lean_dec_ref(v_x_208_);
lean_dec_ref(v_x_207_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* lean_mk_axiom_val(lean_object* v_name_213_, lean_object* v_levelParams_214_, lean_object* v_type_215_, uint8_t v_isUnsafe_216_){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_217_, 0, v_name_213_);
lean_ctor_set(v___x_217_, 1, v_levelParams_214_);
lean_ctor_set(v___x_217_, 2, v_type_215_);
v___x_218_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_218_, 0, v___x_217_);
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*1, v_isUnsafe_216_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAxiomValEx___boxed(lean_object* v_name_219_, lean_object* v_levelParams_220_, lean_object* v_type_221_, lean_object* v_isUnsafe_222_){
_start:
{
uint8_t v_isUnsafe_boxed_223_; lean_object* v_res_224_; 
v_isUnsafe_boxed_223_ = lean_unbox(v_isUnsafe_222_);
v_res_224_ = lean_mk_axiom_val(v_name_219_, v_levelParams_220_, v_type_221_, v_isUnsafe_boxed_223_);
return v_res_224_;
}
}
LEAN_EXPORT uint8_t lean_axiom_val_is_unsafe(lean_object* v_v_225_){
_start:
{
uint8_t v_isUnsafe_226_; 
v_isUnsafe_226_ = lean_ctor_get_uint8(v_v_225_, sizeof(void*)*1);
lean_dec_ref(v_v_225_);
return v_isUnsafe_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_AxiomVal_isUnsafeEx___boxed(lean_object* v_v_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = lean_axiom_val_is_unsafe(v_v_227_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorIdx(uint8_t v_x_230_){
_start:
{
switch(v_x_230_)
{
case 0:
{
lean_object* v___x_231_; 
v___x_231_ = lean_unsigned_to_nat(0u);
return v___x_231_;
}
case 1:
{
lean_object* v___x_232_; 
v___x_232_ = lean_unsigned_to_nat(1u);
return v___x_232_;
}
default: 
{
lean_object* v___x_233_; 
v___x_233_ = lean_unsigned_to_nat(2u);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorIdx___boxed(lean_object* v_x_234_){
_start:
{
uint8_t v_x_boxed_235_; lean_object* v_res_236_; 
v_x_boxed_235_ = lean_unbox(v_x_234_);
v_res_236_ = l_Lean_DefinitionSafety_ctorIdx(v_x_boxed_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg(lean_object* v_k_237_){
_start:
{
lean_inc(v_k_237_);
return v_k_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg___boxed(lean_object* v_k_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_DefinitionSafety_ctorElim___redArg(v_k_238_);
lean_dec(v_k_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim(lean_object* v_motive_240_, lean_object* v_ctorIdx_241_, uint8_t v_t_242_, lean_object* v_h_243_, lean_object* v_k_244_){
_start:
{
lean_inc(v_k_244_);
return v_k_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___boxed(lean_object* v_motive_245_, lean_object* v_ctorIdx_246_, lean_object* v_t_247_, lean_object* v_h_248_, lean_object* v_k_249_){
_start:
{
uint8_t v_t_boxed_250_; lean_object* v_res_251_; 
v_t_boxed_250_ = lean_unbox(v_t_247_);
v_res_251_ = l_Lean_DefinitionSafety_ctorElim(v_motive_245_, v_ctorIdx_246_, v_t_boxed_250_, v_h_248_, v_k_249_);
lean_dec(v_k_249_);
lean_dec(v_ctorIdx_246_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___redArg(lean_object* v_unsafe_252_){
_start:
{
lean_inc(v_unsafe_252_);
return v_unsafe_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___redArg___boxed(lean_object* v_unsafe_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_DefinitionSafety_unsafe_elim___redArg(v_unsafe_253_);
lean_dec(v_unsafe_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim(lean_object* v_motive_255_, uint8_t v_t_256_, lean_object* v_h_257_, lean_object* v_unsafe_258_){
_start:
{
lean_inc(v_unsafe_258_);
return v_unsafe_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___boxed(lean_object* v_motive_259_, lean_object* v_t_260_, lean_object* v_h_261_, lean_object* v_unsafe_262_){
_start:
{
uint8_t v_t_boxed_263_; lean_object* v_res_264_; 
v_t_boxed_263_ = lean_unbox(v_t_260_);
v_res_264_ = l_Lean_DefinitionSafety_unsafe_elim(v_motive_259_, v_t_boxed_263_, v_h_261_, v_unsafe_262_);
lean_dec(v_unsafe_262_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg(lean_object* v_safe_265_){
_start:
{
lean_inc(v_safe_265_);
return v_safe_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg___boxed(lean_object* v_safe_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_DefinitionSafety_safe_elim___redArg(v_safe_266_);
lean_dec(v_safe_266_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim(lean_object* v_motive_268_, uint8_t v_t_269_, lean_object* v_h_270_, lean_object* v_safe_271_){
_start:
{
lean_inc(v_safe_271_);
return v_safe_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___boxed(lean_object* v_motive_272_, lean_object* v_t_273_, lean_object* v_h_274_, lean_object* v_safe_275_){
_start:
{
uint8_t v_t_boxed_276_; lean_object* v_res_277_; 
v_t_boxed_276_ = lean_unbox(v_t_273_);
v_res_277_ = l_Lean_DefinitionSafety_safe_elim(v_motive_272_, v_t_boxed_276_, v_h_274_, v_safe_275_);
lean_dec(v_safe_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg(lean_object* v_partial_278_){
_start:
{
lean_inc(v_partial_278_);
return v_partial_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg___boxed(lean_object* v_partial_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_DefinitionSafety_partial_elim___redArg(v_partial_279_);
lean_dec(v_partial_279_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim(lean_object* v_motive_281_, uint8_t v_t_282_, lean_object* v_h_283_, lean_object* v_partial_284_){
_start:
{
lean_inc(v_partial_284_);
return v_partial_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___boxed(lean_object* v_motive_285_, lean_object* v_t_286_, lean_object* v_h_287_, lean_object* v_partial_288_){
_start:
{
uint8_t v_t_boxed_289_; lean_object* v_res_290_; 
v_t_boxed_289_ = lean_unbox(v_t_286_);
v_res_290_ = l_Lean_DefinitionSafety_partial_elim(v_motive_285_, v_t_boxed_289_, v_h_287_, v_partial_288_);
lean_dec(v_partial_288_);
return v_res_290_;
}
}
static uint8_t _init_l_Lean_instInhabitedDefinitionSafety_default(void){
_start:
{
uint8_t v___x_291_; 
v___x_291_ = 0;
return v___x_291_;
}
}
static uint8_t _init_l_Lean_instInhabitedDefinitionSafety(void){
_start:
{
uint8_t v___x_292_; 
v___x_292_ = 0;
return v___x_292_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t v_x_293_, uint8_t v_y_294_){
_start:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_295_ = l_Lean_DefinitionSafety_ctorIdx(v_x_293_);
v___x_296_ = l_Lean_DefinitionSafety_ctorIdx(v_y_294_);
v___x_297_ = lean_nat_dec_eq(v___x_295_, v___x_296_);
lean_dec(v___x_296_);
lean_dec(v___x_295_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionSafety_beq___boxed(lean_object* v_x_298_, lean_object* v_y_299_){
_start:
{
uint8_t v_x_21__boxed_300_; uint8_t v_y_22__boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_x_21__boxed_300_ = lean_unbox(v_x_298_);
v_y_22__boxed_301_ = lean_unbox(v_y_299_);
v_res_302_ = l_Lean_instBEqDefinitionSafety_beq(v_x_21__boxed_300_, v_y_22__boxed_301_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
static lean_object* _init_l_Lean_instReprDefinitionSafety_repr___closed__6(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(2u);
v___x_316_ = lean_nat_to_int(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_instReprDefinitionSafety_repr___closed__7(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_unsigned_to_nat(1u);
v___x_318_ = lean_nat_to_int(v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDefinitionSafety_repr(uint8_t v_x_319_, lean_object* v_prec_320_){
_start:
{
lean_object* v___y_322_; lean_object* v___y_329_; lean_object* v___y_336_; 
switch(v_x_319_)
{
case 0:
{
lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_342_ = lean_unsigned_to_nat(1024u);
v___x_343_ = lean_nat_dec_le(v___x_342_, v_prec_320_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; 
v___x_344_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_322_ = v___x_344_;
goto v___jp_321_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_322_ = v___x_345_;
goto v___jp_321_;
}
}
case 1:
{
lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_346_ = lean_unsigned_to_nat(1024u);
v___x_347_ = lean_nat_dec_le(v___x_346_, v_prec_320_);
if (v___x_347_ == 0)
{
lean_object* v___x_348_; 
v___x_348_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_329_ = v___x_348_;
goto v___jp_328_;
}
else
{
lean_object* v___x_349_; 
v___x_349_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_329_ = v___x_349_;
goto v___jp_328_;
}
}
default: 
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(1024u);
v___x_351_ = lean_nat_dec_le(v___x_350_, v_prec_320_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_336_ = v___x_352_;
goto v___jp_335_;
}
else
{
lean_object* v___x_353_; 
v___x_353_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_336_ = v___x_353_;
goto v___jp_335_;
}
}
}
v___jp_321_:
{
lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_323_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__1));
lean_inc(v___y_322_);
v___x_324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_324_, 0, v___y_322_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = 0;
v___x_326_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*1, v___x_325_);
v___x_327_ = l_Repr_addAppParen(v___x_326_, v_prec_320_);
return v___x_327_;
}
v___jp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; uint8_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_330_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__3));
lean_inc(v___y_329_);
v___x_331_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_331_, 0, v___y_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = 0;
v___x_333_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_333_, 0, v___x_331_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*1, v___x_332_);
v___x_334_ = l_Repr_addAppParen(v___x_333_, v_prec_320_);
return v___x_334_;
}
v___jp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_337_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__5));
lean_inc(v___y_336_);
v___x_338_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_338_, 0, v___y_336_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
v___x_339_ = 0;
v___x_340_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_340_, 0, v___x_338_);
lean_ctor_set_uint8(v___x_340_, sizeof(void*)*1, v___x_339_);
v___x_341_ = l_Repr_addAppParen(v___x_340_, v_prec_320_);
return v___x_341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDefinitionSafety_repr___boxed(lean_object* v_x_354_, lean_object* v_prec_355_){
_start:
{
uint8_t v_x_171__boxed_356_; lean_object* v_res_357_; 
v_x_171__boxed_356_ = lean_unbox(v_x_354_);
v_res_357_ = l_Lean_instReprDefinitionSafety_repr(v_x_171__boxed_356_, v_prec_355_);
lean_dec(v_prec_355_);
return v_res_357_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default___closed__0(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = lean_box(0);
v___x_361_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_362_ = l_Lean_Expr_const___override(v___x_361_, v___x_360_);
return v___x_362_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default___closed__2(void){
_start:
{
lean_object* v___x_366_; uint8_t v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_366_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_367_ = 0;
v___x_368_ = lean_box(0);
v___x_369_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_370_ = l_Lean_instInhabitedConstantVal_default;
v___x_371_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v___x_369_);
lean_ctor_set(v___x_371_, 2, v___x_368_);
lean_ctor_set(v___x_371_, 3, v___x_366_);
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*4, v___x_367_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__2, &l_Lean_instInhabitedDefinitionVal_default___closed__2_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__2);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal(void){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_instInhabitedDefinitionVal_default;
return v___x_373_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDefinitionVal_beq(lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
lean_object* v_toConstantVal_376_; lean_object* v_value_377_; lean_object* v_hints_378_; uint8_t v_safety_379_; lean_object* v_all_380_; lean_object* v_toConstantVal_381_; lean_object* v_value_382_; lean_object* v_hints_383_; uint8_t v_safety_384_; lean_object* v_all_385_; uint8_t v___x_386_; 
v_toConstantVal_376_ = lean_ctor_get(v_x_374_, 0);
v_value_377_ = lean_ctor_get(v_x_374_, 1);
v_hints_378_ = lean_ctor_get(v_x_374_, 2);
v_safety_379_ = lean_ctor_get_uint8(v_x_374_, sizeof(void*)*4);
v_all_380_ = lean_ctor_get(v_x_374_, 3);
v_toConstantVal_381_ = lean_ctor_get(v_x_375_, 0);
v_value_382_ = lean_ctor_get(v_x_375_, 1);
v_hints_383_ = lean_ctor_get(v_x_375_, 2);
v_safety_384_ = lean_ctor_get_uint8(v_x_375_, sizeof(void*)*4);
v_all_385_ = lean_ctor_get(v_x_375_, 3);
v___x_386_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_376_, v_toConstantVal_381_);
if (v___x_386_ == 0)
{
return v___x_386_;
}
else
{
uint8_t v___x_387_; 
v___x_387_ = lean_expr_eqv(v_value_377_, v_value_382_);
if (v___x_387_ == 0)
{
return v___x_387_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = l_Lean_instBEqReducibilityHints_beq(v_hints_378_, v_hints_383_);
if (v___x_388_ == 0)
{
return v___x_388_;
}
else
{
uint8_t v___x_389_; 
v___x_389_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_379_, v_safety_384_);
if (v___x_389_ == 0)
{
return v___x_389_;
}
else
{
uint8_t v___x_390_; 
v___x_390_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_380_, v_all_385_);
return v___x_390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionVal_beq___boxed(lean_object* v_x_391_, lean_object* v_x_392_){
_start:
{
uint8_t v_res_393_; lean_object* v_r_394_; 
v_res_393_ = l_Lean_instBEqDefinitionVal_beq(v_x_391_, v_x_392_);
lean_dec_ref(v_x_392_);
lean_dec_ref(v_x_391_);
v_r_394_ = lean_box(v_res_393_);
return v_r_394_;
}
}
LEAN_EXPORT lean_object* lean_mk_definition_val(lean_object* v_name_397_, lean_object* v_levelParams_398_, lean_object* v_type_399_, lean_object* v_value_400_, lean_object* v_hints_401_, uint8_t v_safety_402_, lean_object* v_all_403_){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_404_, 0, v_name_397_);
lean_ctor_set(v___x_404_, 1, v_levelParams_398_);
lean_ctor_set(v___x_404_, 2, v_type_399_);
v___x_405_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_value_400_);
lean_ctor_set(v___x_405_, 2, v_hints_401_);
lean_ctor_set(v___x_405_, 3, v_all_403_);
lean_ctor_set_uint8(v___x_405_, sizeof(void*)*4, v_safety_402_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValEx___boxed(lean_object* v_name_406_, lean_object* v_levelParams_407_, lean_object* v_type_408_, lean_object* v_value_409_, lean_object* v_hints_410_, lean_object* v_safety_411_, lean_object* v_all_412_){
_start:
{
uint8_t v_safety_boxed_413_; lean_object* v_res_414_; 
v_safety_boxed_413_ = lean_unbox(v_safety_411_);
v_res_414_ = lean_mk_definition_val(v_name_406_, v_levelParams_407_, v_type_408_, v_value_409_, v_hints_410_, v_safety_boxed_413_, v_all_412_);
return v_res_414_;
}
}
LEAN_EXPORT uint8_t lean_definition_val_get_safety(lean_object* v_v_415_){
_start:
{
uint8_t v_safety_416_; 
v_safety_416_ = lean_ctor_get_uint8(v_v_415_, sizeof(void*)*4);
lean_dec_ref(v_v_415_);
return v_safety_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionVal_getSafetyEx___boxed(lean_object* v_v_417_){
_start:
{
uint8_t v_res_418_; lean_object* v_r_419_; 
v_res_418_ = lean_definition_val_get_safety(v_v_417_);
v_r_419_ = lean_box(v_res_418_);
return v_r_419_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default___closed__0(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_421_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_422_ = l_Lean_instInhabitedConstantVal_default;
v___x_423_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
lean_ctor_set(v___x_423_, 2, v___x_420_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default(void){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = lean_obj_once(&l_Lean_instInhabitedTheoremVal_default___closed__0, &l_Lean_instInhabitedTheoremVal_default___closed__0_once, _init_l_Lean_instInhabitedTheoremVal_default___closed__0);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal(void){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Lean_instInhabitedTheoremVal_default;
return v___x_425_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqTheoremVal_beq(lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
lean_object* v_toConstantVal_428_; lean_object* v_value_429_; lean_object* v_all_430_; lean_object* v_toConstantVal_431_; lean_object* v_value_432_; lean_object* v_all_433_; uint8_t v___x_434_; 
v_toConstantVal_428_ = lean_ctor_get(v_x_426_, 0);
v_value_429_ = lean_ctor_get(v_x_426_, 1);
v_all_430_ = lean_ctor_get(v_x_426_, 2);
v_toConstantVal_431_ = lean_ctor_get(v_x_427_, 0);
v_value_432_ = lean_ctor_get(v_x_427_, 1);
v_all_433_ = lean_ctor_get(v_x_427_, 2);
v___x_434_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_428_, v_toConstantVal_431_);
if (v___x_434_ == 0)
{
return v___x_434_;
}
else
{
uint8_t v___x_435_; 
v___x_435_ = lean_expr_eqv(v_value_429_, v_value_432_);
if (v___x_435_ == 0)
{
return v___x_435_;
}
else
{
uint8_t v___x_436_; 
v___x_436_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_430_, v_all_433_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqTheoremVal_beq___boxed(lean_object* v_x_437_, lean_object* v_x_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Lean_instBEqTheoremVal_beq(v_x_437_, v_x_438_);
lean_dec_ref(v_x_438_);
lean_dec_ref(v_x_437_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* lean_mk_theorem_val(lean_object* v_name_443_, lean_object* v_levelParams_444_, lean_object* v_type_445_, lean_object* v_value_446_, lean_object* v_all_447_){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_448_, 0, v_name_443_);
lean_ctor_set(v___x_448_, 1, v_levelParams_444_);
lean_ctor_set(v___x_448_, 2, v_type_445_);
v___x_449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v_value_446_);
lean_ctor_set(v___x_449_, 2, v_all_447_);
return v___x_449_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default___closed__0(void){
_start:
{
lean_object* v___x_450_; uint8_t v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_450_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_451_ = 0;
v___x_452_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_453_ = l_Lean_instInhabitedConstantVal_default;
v___x_454_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v___x_452_);
lean_ctor_set(v___x_454_, 2, v___x_450_);
lean_ctor_set_uint8(v___x_454_, sizeof(void*)*3, v___x_451_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default(void){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = lean_obj_once(&l_Lean_instInhabitedOpaqueVal_default___closed__0, &l_Lean_instInhabitedOpaqueVal_default___closed__0_once, _init_l_Lean_instInhabitedOpaqueVal_default___closed__0);
return v___x_455_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal(void){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_instInhabitedOpaqueVal_default;
return v___x_456_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqOpaqueVal_beq(lean_object* v_x_457_, lean_object* v_x_458_){
_start:
{
lean_object* v_toConstantVal_459_; lean_object* v_value_460_; uint8_t v_isUnsafe_461_; lean_object* v_all_462_; lean_object* v_toConstantVal_463_; lean_object* v_value_464_; uint8_t v_isUnsafe_465_; lean_object* v_all_466_; uint8_t v___y_468_; uint8_t v___x_470_; 
v_toConstantVal_459_ = lean_ctor_get(v_x_457_, 0);
v_value_460_ = lean_ctor_get(v_x_457_, 1);
v_isUnsafe_461_ = lean_ctor_get_uint8(v_x_457_, sizeof(void*)*3);
v_all_462_ = lean_ctor_get(v_x_457_, 2);
v_toConstantVal_463_ = lean_ctor_get(v_x_458_, 0);
v_value_464_ = lean_ctor_get(v_x_458_, 1);
v_isUnsafe_465_ = lean_ctor_get_uint8(v_x_458_, sizeof(void*)*3);
v_all_466_ = lean_ctor_get(v_x_458_, 2);
v___x_470_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_459_, v_toConstantVal_463_);
if (v___x_470_ == 0)
{
return v___x_470_;
}
else
{
uint8_t v___x_471_; 
v___x_471_ = lean_expr_eqv(v_value_460_, v_value_464_);
if (v___x_471_ == 0)
{
return v___x_471_;
}
else
{
if (v_isUnsafe_465_ == 0)
{
if (v_isUnsafe_461_ == 0)
{
v___y_468_ = v___x_471_;
goto v___jp_467_;
}
else
{
return v_isUnsafe_465_;
}
}
else
{
v___y_468_ = v_isUnsafe_461_;
goto v___jp_467_;
}
}
}
v___jp_467_:
{
if (v___y_468_ == 0)
{
return v___y_468_;
}
else
{
uint8_t v___x_469_; 
v___x_469_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_462_, v_all_466_);
return v___x_469_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqOpaqueVal_beq___boxed(lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = l_Lean_instBEqOpaqueVal_beq(v_x_472_, v_x_473_);
lean_dec_ref(v_x_473_);
lean_dec_ref(v_x_472_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT lean_object* lean_mk_opaque_val(lean_object* v_name_478_, lean_object* v_levelParams_479_, lean_object* v_type_480_, lean_object* v_value_481_, uint8_t v_isUnsafe_482_, lean_object* v_all_483_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_484_, 0, v_name_478_);
lean_ctor_set(v___x_484_, 1, v_levelParams_479_);
lean_ctor_set(v___x_484_, 2, v_type_480_);
v___x_485_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_485_, 0, v___x_484_);
lean_ctor_set(v___x_485_, 1, v_value_481_);
lean_ctor_set(v___x_485_, 2, v_all_483_);
lean_ctor_set_uint8(v___x_485_, sizeof(void*)*3, v_isUnsafe_482_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOpaqueValEx___boxed(lean_object* v_name_486_, lean_object* v_levelParams_487_, lean_object* v_type_488_, lean_object* v_value_489_, lean_object* v_isUnsafe_490_, lean_object* v_all_491_){
_start:
{
uint8_t v_isUnsafe_boxed_492_; lean_object* v_res_493_; 
v_isUnsafe_boxed_492_ = lean_unbox(v_isUnsafe_490_);
v_res_493_ = lean_mk_opaque_val(v_name_486_, v_levelParams_487_, v_type_488_, v_value_489_, v_isUnsafe_boxed_492_, v_all_491_);
return v_res_493_;
}
}
LEAN_EXPORT uint8_t lean_opaque_val_is_unsafe(lean_object* v_v_494_){
_start:
{
uint8_t v_isUnsafe_495_; 
v_isUnsafe_495_ = lean_ctor_get_uint8(v_v_494_, sizeof(void*)*3);
lean_dec_ref(v_v_494_);
return v_isUnsafe_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpaqueVal_isUnsafeEx___boxed(lean_object* v_v_496_){
_start:
{
uint8_t v_res_497_; lean_object* v_r_498_; 
v_res_497_ = lean_opaque_val_is_unsafe(v_v_496_);
v_r_498_ = lean_box(v_res_497_);
return v_r_498_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__0(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = lean_box(0);
v___x_500_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_501_ = l_Lean_Expr_const___override(v___x_500_, v___x_499_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__1(void){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_502_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_503_ = lean_box(0);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v___x_502_);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default(void){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__1, &l_Lean_instInhabitedConstructor_default___closed__1_once, _init_l_Lean_instInhabitedConstructor_default___closed__1);
return v___x_505_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor(void){
_start:
{
lean_object* v___x_506_; 
v___x_506_ = l_Lean_instInhabitedConstructor_default;
return v___x_506_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructor_beq(lean_object* v_x_507_, lean_object* v_x_508_){
_start:
{
lean_object* v_name_509_; lean_object* v_type_510_; lean_object* v_name_511_; lean_object* v_type_512_; uint8_t v___x_513_; 
v_name_509_ = lean_ctor_get(v_x_507_, 0);
v_type_510_ = lean_ctor_get(v_x_507_, 1);
v_name_511_ = lean_ctor_get(v_x_508_, 0);
v_type_512_ = lean_ctor_get(v_x_508_, 1);
v___x_513_ = lean_name_eq(v_name_509_, v_name_511_);
if (v___x_513_ == 0)
{
return v___x_513_;
}
else
{
uint8_t v___x_514_; 
v___x_514_ = lean_expr_eqv(v_type_510_, v_type_512_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructor_beq___boxed(lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
uint8_t v_res_517_; lean_object* v_r_518_; 
v_res_517_ = l_Lean_instBEqConstructor_beq(v_x_515_, v_x_516_);
lean_dec_ref(v_x_516_);
lean_dec_ref(v_x_515_);
v_r_518_ = lean_box(v_res_517_);
return v_r_518_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default___closed__0(void){
_start:
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_521_ = lean_box(0);
v___x_522_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_523_ = lean_box(0);
v___x_524_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
lean_ctor_set(v___x_524_, 1, v___x_522_);
lean_ctor_set(v___x_524_, 2, v___x_521_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default(void){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = lean_obj_once(&l_Lean_instInhabitedInductiveType_default___closed__0, &l_Lean_instInhabitedInductiveType_default___closed__0_once, _init_l_Lean_instInhabitedInductiveType_default___closed__0);
return v___x_525_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType(void){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_instInhabitedInductiveType_default;
return v___x_526_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
if (lean_obj_tag(v_x_527_) == 0)
{
if (lean_obj_tag(v_x_528_) == 0)
{
uint8_t v___x_529_; 
v___x_529_ = 1;
return v___x_529_;
}
else
{
uint8_t v___x_530_; 
v___x_530_ = 0;
return v___x_530_;
}
}
else
{
if (lean_obj_tag(v_x_528_) == 0)
{
uint8_t v___x_531_; 
v___x_531_ = 0;
return v___x_531_;
}
else
{
lean_object* v_head_532_; lean_object* v_tail_533_; lean_object* v_head_534_; lean_object* v_tail_535_; uint8_t v___x_536_; 
v_head_532_ = lean_ctor_get(v_x_527_, 0);
v_tail_533_ = lean_ctor_get(v_x_527_, 1);
v_head_534_ = lean_ctor_get(v_x_528_, 0);
v_tail_535_ = lean_ctor_get(v_x_528_, 1);
v___x_536_ = l_Lean_instBEqConstructor_beq(v_head_532_, v_head_534_);
if (v___x_536_ == 0)
{
return v___x_536_;
}
else
{
v_x_527_ = v_tail_533_;
v_x_528_ = v_tail_535_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0___boxed(lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
uint8_t v_res_540_; lean_object* v_r_541_; 
v_res_540_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_x_538_, v_x_539_);
lean_dec(v_x_539_);
lean_dec(v_x_538_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveType_beq(lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
lean_object* v_name_544_; lean_object* v_type_545_; lean_object* v_ctors_546_; lean_object* v_name_547_; lean_object* v_type_548_; lean_object* v_ctors_549_; uint8_t v___x_550_; 
v_name_544_ = lean_ctor_get(v_x_542_, 0);
v_type_545_ = lean_ctor_get(v_x_542_, 1);
v_ctors_546_ = lean_ctor_get(v_x_542_, 2);
v_name_547_ = lean_ctor_get(v_x_543_, 0);
v_type_548_ = lean_ctor_get(v_x_543_, 1);
v_ctors_549_ = lean_ctor_get(v_x_543_, 2);
v___x_550_ = lean_name_eq(v_name_544_, v_name_547_);
if (v___x_550_ == 0)
{
return v___x_550_;
}
else
{
uint8_t v___x_551_; 
v___x_551_ = lean_expr_eqv(v_type_545_, v_type_548_);
if (v___x_551_ == 0)
{
return v___x_551_;
}
else
{
uint8_t v___x_552_; 
v___x_552_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_ctors_546_, v_ctors_549_);
return v___x_552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveType_beq___boxed(lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
uint8_t v_res_555_; lean_object* v_r_556_; 
v_res_555_ = l_Lean_instBEqInductiveType_beq(v_x_553_, v_x_554_);
lean_dec_ref(v_x_554_);
lean_dec_ref(v_x_553_);
v_r_556_ = lean_box(v_res_555_);
return v_r_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx(lean_object* v_x_559_){
_start:
{
switch(lean_obj_tag(v_x_559_))
{
case 0:
{
lean_object* v___x_560_; 
v___x_560_ = lean_unsigned_to_nat(0u);
return v___x_560_;
}
case 1:
{
lean_object* v___x_561_; 
v___x_561_ = lean_unsigned_to_nat(1u);
return v___x_561_;
}
case 2:
{
lean_object* v___x_562_; 
v___x_562_ = lean_unsigned_to_nat(2u);
return v___x_562_;
}
case 3:
{
lean_object* v___x_563_; 
v___x_563_ = lean_unsigned_to_nat(3u);
return v___x_563_;
}
case 4:
{
lean_object* v___x_564_; 
v___x_564_ = lean_unsigned_to_nat(4u);
return v___x_564_;
}
case 5:
{
lean_object* v___x_565_; 
v___x_565_ = lean_unsigned_to_nat(5u);
return v___x_565_;
}
default: 
{
lean_object* v___x_566_; 
v___x_566_ = lean_unsigned_to_nat(6u);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___boxed(lean_object* v_x_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Declaration_ctorIdx(v_x_567_);
lean_dec(v_x_567_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___redArg(lean_object* v_t_569_, lean_object* v_k_570_){
_start:
{
switch(lean_obj_tag(v_t_569_))
{
case 4:
{
return v_k_570_;
}
case 5:
{
lean_object* v_defns_571_; lean_object* v___x_572_; 
v_defns_571_ = lean_ctor_get(v_t_569_, 0);
lean_inc(v_defns_571_);
lean_dec_ref_known(v_t_569_, 1);
v___x_572_ = lean_apply_1(v_k_570_, v_defns_571_);
return v___x_572_;
}
case 6:
{
lean_object* v_lparams_573_; lean_object* v_nparams_574_; lean_object* v_types_575_; uint8_t v_isUnsafe_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_lparams_573_ = lean_ctor_get(v_t_569_, 0);
lean_inc(v_lparams_573_);
v_nparams_574_ = lean_ctor_get(v_t_569_, 1);
lean_inc(v_nparams_574_);
v_types_575_ = lean_ctor_get(v_t_569_, 2);
lean_inc(v_types_575_);
v_isUnsafe_576_ = lean_ctor_get_uint8(v_t_569_, sizeof(void*)*3);
lean_dec_ref_known(v_t_569_, 3);
v___x_577_ = lean_box(v_isUnsafe_576_);
v___x_578_ = lean_apply_4(v_k_570_, v_lparams_573_, v_nparams_574_, v_types_575_, v___x_577_);
return v___x_578_;
}
default: 
{
lean_object* v_val_579_; lean_object* v___x_580_; 
v_val_579_ = lean_ctor_get(v_t_569_, 0);
lean_inc_ref(v_val_579_);
lean_dec(v_t_569_);
v___x_580_ = lean_apply_1(v_k_570_, v_val_579_);
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim(lean_object* v_motive_581_, lean_object* v_ctorIdx_582_, lean_object* v_t_583_, lean_object* v_h_584_, lean_object* v_k_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_Declaration_ctorElim___redArg(v_t_583_, v_k_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___boxed(lean_object* v_motive_587_, lean_object* v_ctorIdx_588_, lean_object* v_t_589_, lean_object* v_h_590_, lean_object* v_k_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l_Lean_Declaration_ctorElim(v_motive_587_, v_ctorIdx_588_, v_t_589_, v_h_590_, v_k_591_);
lean_dec(v_ctorIdx_588_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim___redArg(lean_object* v_t_593_, lean_object* v_axiomDecl_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Declaration_ctorElim___redArg(v_t_593_, v_axiomDecl_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim(lean_object* v_motive_596_, lean_object* v_t_597_, lean_object* v_h_598_, lean_object* v_axiomDecl_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Declaration_ctorElim___redArg(v_t_597_, v_axiomDecl_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim___redArg(lean_object* v_t_601_, lean_object* v_defnDecl_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Declaration_ctorElim___redArg(v_t_601_, v_defnDecl_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim(lean_object* v_motive_604_, lean_object* v_t_605_, lean_object* v_h_606_, lean_object* v_defnDecl_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Declaration_ctorElim___redArg(v_t_605_, v_defnDecl_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim___redArg(lean_object* v_t_609_, lean_object* v_thmDecl_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Declaration_ctorElim___redArg(v_t_609_, v_thmDecl_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim(lean_object* v_motive_612_, lean_object* v_t_613_, lean_object* v_h_614_, lean_object* v_thmDecl_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_Declaration_ctorElim___redArg(v_t_613_, v_thmDecl_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim___redArg(lean_object* v_t_617_, lean_object* v_opaqueDecl_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_Declaration_ctorElim___redArg(v_t_617_, v_opaqueDecl_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim(lean_object* v_motive_620_, lean_object* v_t_621_, lean_object* v_h_622_, lean_object* v_opaqueDecl_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Declaration_ctorElim___redArg(v_t_621_, v_opaqueDecl_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim___redArg(lean_object* v_t_625_, lean_object* v_quotDecl_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Declaration_ctorElim___redArg(v_t_625_, v_quotDecl_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim(lean_object* v_motive_628_, lean_object* v_t_629_, lean_object* v_h_630_, lean_object* v_quotDecl_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Declaration_ctorElim___redArg(v_t_629_, v_quotDecl_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim___redArg(lean_object* v_t_633_, lean_object* v_mutualDefnDecl_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_Declaration_ctorElim___redArg(v_t_633_, v_mutualDefnDecl_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim(lean_object* v_motive_636_, lean_object* v_t_637_, lean_object* v_h_638_, lean_object* v_mutualDefnDecl_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Declaration_ctorElim___redArg(v_t_637_, v_mutualDefnDecl_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim___redArg(lean_object* v_t_641_, lean_object* v_inductDecl_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Declaration_ctorElim___redArg(v_t_641_, v_inductDecl_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim(lean_object* v_motive_644_, lean_object* v_t_645_, lean_object* v_h_646_, lean_object* v_inductDecl_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Declaration_ctorElim___redArg(v_t_645_, v_inductDecl_647_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default___closed__0(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_649_ = l_Lean_instInhabitedAxiomVal_default;
v___x_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default(void){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = lean_obj_once(&l_Lean_instInhabitedDeclaration_default___closed__0, &l_Lean_instInhabitedDeclaration_default___closed__0_once, _init_l_Lean_instInhabitedDeclaration_default___closed__0);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration(void){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l_Lean_instInhabitedDeclaration_default;
return v___x_652_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(lean_object* v_x_653_, lean_object* v_x_654_){
_start:
{
if (lean_obj_tag(v_x_653_) == 0)
{
if (lean_obj_tag(v_x_654_) == 0)
{
uint8_t v___x_655_; 
v___x_655_ = 1;
return v___x_655_;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = 0;
return v___x_656_;
}
}
else
{
if (lean_obj_tag(v_x_654_) == 0)
{
uint8_t v___x_657_; 
v___x_657_ = 0;
return v___x_657_;
}
else
{
lean_object* v_head_658_; lean_object* v_tail_659_; lean_object* v_head_660_; lean_object* v_tail_661_; uint8_t v___x_662_; 
v_head_658_ = lean_ctor_get(v_x_653_, 0);
v_tail_659_ = lean_ctor_get(v_x_653_, 1);
v_head_660_ = lean_ctor_get(v_x_654_, 0);
v_tail_661_ = lean_ctor_get(v_x_654_, 1);
v___x_662_ = l_Lean_instBEqDefinitionVal_beq(v_head_658_, v_head_660_);
if (v___x_662_ == 0)
{
return v___x_662_;
}
else
{
v_x_653_ = v_tail_659_;
v_x_654_ = v_tail_661_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0___boxed(lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
uint8_t v_res_666_; lean_object* v_r_667_; 
v_res_666_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_x_664_, v_x_665_);
lean_dec(v_x_665_);
lean_dec(v_x_664_);
v_r_667_ = lean_box(v_res_666_);
return v_r_667_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
if (lean_obj_tag(v_x_668_) == 0)
{
if (lean_obj_tag(v_x_669_) == 0)
{
uint8_t v___x_670_; 
v___x_670_ = 1;
return v___x_670_;
}
else
{
uint8_t v___x_671_; 
v___x_671_ = 0;
return v___x_671_;
}
}
else
{
if (lean_obj_tag(v_x_669_) == 0)
{
uint8_t v___x_672_; 
v___x_672_ = 0;
return v___x_672_;
}
else
{
lean_object* v_head_673_; lean_object* v_tail_674_; lean_object* v_head_675_; lean_object* v_tail_676_; uint8_t v___x_677_; 
v_head_673_ = lean_ctor_get(v_x_668_, 0);
v_tail_674_ = lean_ctor_get(v_x_668_, 1);
v_head_675_ = lean_ctor_get(v_x_669_, 0);
v_tail_676_ = lean_ctor_get(v_x_669_, 1);
v___x_677_ = l_Lean_instBEqInductiveType_beq(v_head_673_, v_head_675_);
if (v___x_677_ == 0)
{
return v___x_677_;
}
else
{
v_x_668_ = v_tail_674_;
v_x_669_ = v_tail_676_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1___boxed(lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_x_679_, v_x_680_);
lean_dec(v_x_680_);
lean_dec(v_x_679_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDeclaration_beq(lean_object* v_x_683_, lean_object* v_x_684_){
_start:
{
switch(lean_obj_tag(v_x_683_))
{
case 0:
{
if (lean_obj_tag(v_x_684_) == 0)
{
lean_object* v_val_685_; lean_object* v_val_686_; uint8_t v___x_687_; 
v_val_685_ = lean_ctor_get(v_x_683_, 0);
v_val_686_ = lean_ctor_get(v_x_684_, 0);
v___x_687_ = l_Lean_instBEqAxiomVal_beq(v_val_685_, v_val_686_);
return v___x_687_;
}
else
{
uint8_t v___x_688_; 
v___x_688_ = 0;
return v___x_688_;
}
}
case 1:
{
if (lean_obj_tag(v_x_684_) == 1)
{
lean_object* v_val_689_; lean_object* v_val_690_; uint8_t v___x_691_; 
v_val_689_ = lean_ctor_get(v_x_683_, 0);
v_val_690_ = lean_ctor_get(v_x_684_, 0);
v___x_691_ = l_Lean_instBEqDefinitionVal_beq(v_val_689_, v_val_690_);
return v___x_691_;
}
else
{
uint8_t v___x_692_; 
v___x_692_ = 0;
return v___x_692_;
}
}
case 2:
{
if (lean_obj_tag(v_x_684_) == 2)
{
lean_object* v_val_693_; lean_object* v_val_694_; uint8_t v___x_695_; 
v_val_693_ = lean_ctor_get(v_x_683_, 0);
v_val_694_ = lean_ctor_get(v_x_684_, 0);
v___x_695_ = l_Lean_instBEqTheoremVal_beq(v_val_693_, v_val_694_);
return v___x_695_;
}
else
{
uint8_t v___x_696_; 
v___x_696_ = 0;
return v___x_696_;
}
}
case 3:
{
if (lean_obj_tag(v_x_684_) == 3)
{
lean_object* v_val_697_; lean_object* v_val_698_; uint8_t v___x_699_; 
v_val_697_ = lean_ctor_get(v_x_683_, 0);
v_val_698_ = lean_ctor_get(v_x_684_, 0);
v___x_699_ = l_Lean_instBEqOpaqueVal_beq(v_val_697_, v_val_698_);
return v___x_699_;
}
else
{
uint8_t v___x_700_; 
v___x_700_ = 0;
return v___x_700_;
}
}
case 4:
{
if (lean_obj_tag(v_x_684_) == 4)
{
uint8_t v___x_701_; 
v___x_701_ = 1;
return v___x_701_;
}
else
{
uint8_t v___x_702_; 
v___x_702_ = 0;
return v___x_702_;
}
}
case 5:
{
if (lean_obj_tag(v_x_684_) == 5)
{
lean_object* v_defns_703_; lean_object* v_defns_704_; uint8_t v___x_705_; 
v_defns_703_ = lean_ctor_get(v_x_683_, 0);
v_defns_704_ = lean_ctor_get(v_x_684_, 0);
v___x_705_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_defns_703_, v_defns_704_);
return v___x_705_;
}
else
{
uint8_t v___x_706_; 
v___x_706_ = 0;
return v___x_706_;
}
}
default: 
{
if (lean_obj_tag(v_x_684_) == 6)
{
lean_object* v_lparams_707_; lean_object* v_nparams_708_; lean_object* v_types_709_; uint8_t v_isUnsafe_710_; lean_object* v_lparams_711_; lean_object* v_nparams_712_; lean_object* v_types_713_; uint8_t v_isUnsafe_714_; uint8_t v___x_715_; 
v_lparams_707_ = lean_ctor_get(v_x_683_, 0);
v_nparams_708_ = lean_ctor_get(v_x_683_, 1);
v_types_709_ = lean_ctor_get(v_x_683_, 2);
v_isUnsafe_710_ = lean_ctor_get_uint8(v_x_683_, sizeof(void*)*3);
v_lparams_711_ = lean_ctor_get(v_x_684_, 0);
v_nparams_712_ = lean_ctor_get(v_x_684_, 1);
v_types_713_ = lean_ctor_get(v_x_684_, 2);
v_isUnsafe_714_ = lean_ctor_get_uint8(v_x_684_, sizeof(void*)*3);
v___x_715_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_lparams_707_, v_lparams_711_);
if (v___x_715_ == 0)
{
return v___x_715_;
}
else
{
uint8_t v___x_716_; 
v___x_716_ = lean_nat_dec_eq(v_nparams_708_, v_nparams_712_);
if (v___x_716_ == 0)
{
return v___x_716_;
}
else
{
uint8_t v___x_717_; 
v___x_717_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_types_709_, v_types_713_);
if (v___x_717_ == 0)
{
return v___x_717_;
}
else
{
if (v_isUnsafe_714_ == 0)
{
if (v_isUnsafe_710_ == 0)
{
return v___x_717_;
}
else
{
return v_isUnsafe_714_;
}
}
else
{
return v_isUnsafe_710_;
}
}
}
}
}
else
{
uint8_t v___x_718_; 
v___x_718_ = 0;
return v___x_718_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDeclaration_beq___boxed(lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Lean_instBEqDeclaration_beq(v_x_719_, v_x_720_);
lean_dec(v_x_720_);
lean_dec(v_x_719_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_decl(lean_object* v_lparams_725_, lean_object* v_nparams_726_, lean_object* v_types_727_, uint8_t v_isUnsafe_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_729_, 0, v_lparams_725_);
lean_ctor_set(v___x_729_, 1, v_nparams_726_);
lean_ctor_set(v___x_729_, 2, v_types_727_);
lean_ctor_set_uint8(v___x_729_, sizeof(void*)*3, v_isUnsafe_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveDeclEs___boxed(lean_object* v_lparams_730_, lean_object* v_nparams_731_, lean_object* v_types_732_, lean_object* v_isUnsafe_733_){
_start:
{
uint8_t v_isUnsafe_boxed_734_; lean_object* v_res_735_; 
v_isUnsafe_boxed_734_ = lean_unbox(v_isUnsafe_733_);
v_res_735_ = lean_mk_inductive_decl(v_lparams_730_, v_nparams_731_, v_types_732_, v_isUnsafe_boxed_734_);
return v_res_735_;
}
}
LEAN_EXPORT uint8_t lean_is_unsafe_inductive_decl(lean_object* v_x_736_){
_start:
{
if (lean_obj_tag(v_x_736_) == 6)
{
uint8_t v_isUnsafe_737_; 
v_isUnsafe_737_ = lean_ctor_get_uint8(v_x_736_, sizeof(void*)*3);
lean_dec_ref_known(v_x_736_, 3);
return v_isUnsafe_737_;
}
else
{
uint8_t v___x_738_; 
lean_dec(v_x_736_);
v___x_738_ = 0;
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_isUnsafeInductiveDeclEx___boxed(lean_object* v_x_739_){
_start:
{
uint8_t v_res_740_; lean_object* v_r_741_; 
v_res_740_ = lean_is_unsafe_inductive_decl(v_x_739_);
v_r_741_ = lean_box(v_res_740_);
return v_r_741_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(lean_object* v_msg_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = l_Lean_instInhabitedDefinitionVal_default;
v___x_744_ = lean_panic_fn_borrowed(v___x_743_, v_msg_742_);
return v___x_744_;
}
}
static lean_object* _init_l_Lean_Declaration_definitionVal_x21___closed__3(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_748_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__2));
v___x_749_ = lean_unsigned_to_nat(9u);
v___x_750_ = lean_unsigned_to_nat(206u);
v___x_751_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__1));
v___x_752_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_753_ = l_mkPanicMessageWithDecl(v___x_752_, v___x_751_, v___x_750_, v___x_749_, v___x_748_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21(lean_object* v_x_754_){
_start:
{
if (lean_obj_tag(v_x_754_) == 1)
{
lean_object* v_val_755_; 
v_val_755_ = lean_ctor_get(v_x_754_, 0);
lean_inc_ref(v_val_755_);
return v_val_755_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = lean_obj_once(&l_Lean_Declaration_definitionVal_x21___closed__3, &l_Lean_Declaration_definitionVal_x21___closed__3_once, _init_l_Lean_Declaration_definitionVal_x21___closed__3);
v___x_757_ = l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(v___x_756_);
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21___boxed(lean_object* v_x_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Declaration_definitionVal_x21(v_x_758_);
lean_dec(v_x_758_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
if (lean_obj_tag(v_a_760_) == 0)
{
lean_object* v___x_762_; 
v___x_762_ = l_List_reverse___redArg(v_a_761_);
return v___x_762_;
}
else
{
lean_object* v_head_763_; lean_object* v_toConstantVal_764_; lean_object* v_tail_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_774_; 
v_head_763_ = lean_ctor_get(v_a_760_, 0);
v_toConstantVal_764_ = lean_ctor_get(v_head_763_, 0);
lean_inc_ref(v_toConstantVal_764_);
v_tail_765_ = lean_ctor_get(v_a_760_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v_a_760_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; 
v_unused_775_ = lean_ctor_get(v_a_760_, 0);
lean_dec(v_unused_775_);
v___x_767_ = v_a_760_;
v_isShared_768_ = v_isSharedCheck_774_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_tail_765_);
lean_dec(v_a_760_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_774_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_name_769_; lean_object* v___x_771_; 
v_name_769_ = lean_ctor_get(v_toConstantVal_764_, 0);
lean_inc(v_name_769_);
lean_dec_ref(v_toConstantVal_764_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v_a_761_);
lean_ctor_set(v___x_767_, 0, v_name_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_name_769_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_a_761_);
v___x_771_ = v_reuseFailAlloc_773_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
v_a_760_ = v_tail_765_;
v_a_761_ = v___x_771_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
if (lean_obj_tag(v_a_776_) == 0)
{
lean_object* v___x_778_; 
v___x_778_ = l_List_reverse___redArg(v_a_777_);
return v___x_778_;
}
else
{
lean_object* v_head_779_; lean_object* v_tail_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_789_; 
v_head_779_ = lean_ctor_get(v_a_776_, 0);
v_tail_780_ = lean_ctor_get(v_a_776_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_a_776_);
if (v_isSharedCheck_789_ == 0)
{
v___x_782_ = v_a_776_;
v_isShared_783_ = v_isSharedCheck_789_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_tail_780_);
lean_inc(v_head_779_);
lean_dec(v_a_776_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_789_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_name_784_; lean_object* v___x_786_; 
v_name_784_ = lean_ctor_get(v_head_779_, 0);
lean_inc(v_name_784_);
lean_dec(v_head_779_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 1, v_a_777_);
lean_ctor_set(v___x_782_, 0, v_name_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_name_784_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_a_777_);
v___x_786_ = v_reuseFailAlloc_788_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
v_a_776_ = v_tail_780_;
v_a_777_ = v___x_786_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getTopLevelNames(lean_object* v_x_796_){
_start:
{
switch(lean_obj_tag(v_x_796_))
{
case 4:
{
lean_object* v___x_797_; 
v___x_797_ = ((lean_object*)(l_Lean_Declaration_getTopLevelNames___closed__2));
return v___x_797_;
}
case 5:
{
lean_object* v_defns_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
v_defns_798_ = lean_ctor_get(v_x_796_, 0);
lean_inc(v_defns_798_);
lean_dec_ref_known(v_x_796_, 1);
v___x_799_ = lean_box(0);
v___x_800_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_798_, v___x_799_);
return v___x_800_;
}
case 6:
{
lean_object* v_types_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v_types_801_ = lean_ctor_get(v_x_796_, 2);
lean_inc(v_types_801_);
lean_dec_ref_known(v_x_796_, 3);
v___x_802_ = lean_box(0);
v___x_803_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(v_types_801_, v___x_802_);
return v___x_803_;
}
default: 
{
lean_object* v_val_804_; lean_object* v_toConstantVal_805_; lean_object* v_name_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_val_804_ = lean_ctor_get(v_x_796_, 0);
lean_inc_ref(v_val_804_);
lean_dec(v_x_796_);
v_toConstantVal_805_ = lean_ctor_get(v_val_804_, 0);
lean_inc_ref(v_toConstantVal_805_);
lean_dec_ref(v_val_804_);
v_name_806_ = lean_ctor_get(v_toConstantVal_805_, 0);
lean_inc(v_name_806_);
lean_dec_ref(v_toConstantVal_805_);
v___x_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_808_, 0, v_name_806_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
return v___x_808_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(lean_object* v_a_809_, lean_object* v_a_810_){
_start:
{
if (lean_obj_tag(v_a_809_) == 0)
{
lean_object* v___x_811_; 
v___x_811_ = l_List_reverse___redArg(v_a_810_);
return v___x_811_;
}
else
{
lean_object* v_head_812_; lean_object* v_tail_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_822_; 
v_head_812_ = lean_ctor_get(v_a_809_, 0);
v_tail_813_ = lean_ctor_get(v_a_809_, 1);
v_isSharedCheck_822_ = !lean_is_exclusive(v_a_809_);
if (v_isSharedCheck_822_ == 0)
{
v___x_815_ = v_a_809_;
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_tail_813_);
lean_inc(v_head_812_);
lean_dec(v_a_809_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_822_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v_name_817_; lean_object* v___x_819_; 
v_name_817_ = lean_ctor_get(v_head_812_, 0);
lean_inc(v_name_817_);
lean_dec(v_head_812_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 1, v_a_810_);
lean_ctor_set(v___x_815_, 0, v_name_817_);
v___x_819_ = v___x_815_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_name_817_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_a_810_);
v___x_819_ = v_reuseFailAlloc_821_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
v_a_809_ = v_tail_813_;
v_a_810_ = v___x_819_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
if (lean_obj_tag(v_a_826_) == 0)
{
lean_object* v___x_828_; 
v___x_828_ = lean_array_to_list(v_a_827_);
return v___x_828_;
}
else
{
lean_object* v_head_829_; lean_object* v_tail_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_846_; 
v_head_829_ = lean_ctor_get(v_a_826_, 0);
v_tail_830_ = lean_ctor_get(v_a_826_, 1);
v_isSharedCheck_846_ = !lean_is_exclusive(v_a_826_);
if (v_isSharedCheck_846_ == 0)
{
v___x_832_ = v_a_826_;
v_isShared_833_ = v_isSharedCheck_846_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_tail_830_);
lean_inc(v_head_829_);
lean_dec(v_a_826_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_846_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_name_834_; lean_object* v_ctors_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_841_; 
v_name_834_ = lean_ctor_get(v_head_829_, 0);
lean_inc(v_name_834_);
v_ctors_835_ = lean_ctor_get(v_head_829_, 2);
lean_inc(v_ctors_835_);
lean_dec(v_head_829_);
v___x_836_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1));
v___x_837_ = l_Lean_Name_appendCore(v_name_834_, v___x_836_);
v___x_838_ = lean_box(0);
v___x_839_ = l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(v_ctors_835_, v___x_838_);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v___x_839_);
lean_ctor_set(v___x_832_, 0, v___x_837_);
v___x_841_ = v___x_832_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_837_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v___x_839_);
v___x_841_ = v_reuseFailAlloc_845_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_842_, 0, v_name_834_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_827_, v___x_842_);
v_a_826_ = v_tail_830_;
v_a_827_ = v___x_843_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getNames(lean_object* v_x_873_){
_start:
{
switch(lean_obj_tag(v_x_873_))
{
case 4:
{
lean_object* v___x_874_; 
v___x_874_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__9));
return v___x_874_;
}
case 5:
{
lean_object* v_defns_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_defns_875_ = lean_ctor_get(v_x_873_, 0);
lean_inc(v_defns_875_);
lean_dec_ref_known(v_x_873_, 1);
v___x_876_ = lean_box(0);
v___x_877_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_875_, v___x_876_);
return v___x_877_;
}
case 6:
{
lean_object* v_types_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_types_878_ = lean_ctor_get(v_x_873_, 2);
lean_inc(v_types_878_);
lean_dec_ref_known(v_x_873_, 3);
v___x_879_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__10));
v___x_880_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(v_types_878_, v___x_879_);
return v___x_880_;
}
default: 
{
lean_object* v_val_881_; lean_object* v_toConstantVal_882_; lean_object* v_name_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_val_881_ = lean_ctor_get(v_x_873_, 0);
lean_inc_ref(v_val_881_);
lean_dec(v_x_873_);
v_toConstantVal_882_ = lean_ctor_get(v_val_881_, 0);
lean_inc_ref(v_toConstantVal_882_);
lean_dec_ref(v_val_881_);
v_name_883_ = lean_ctor_get(v_toConstantVal_882_, 0);
lean_inc(v_name_883_);
lean_dec_ref(v_toConstantVal_882_);
v___x_884_ = lean_box(0);
v___x_885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_885_, 0, v_name_883_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
return v___x_885_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__0(lean_object* v_f_886_, lean_object* v_value_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = lean_apply_2(v_f_886_, v_a_888_, v_value_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__3(lean_object* v_f_890_, lean_object* v_value_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_893_; 
v___x_893_ = lean_apply_2(v_f_890_, v_a_892_, v_value_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__1(lean_object* v_f_894_, lean_object* v_toBind_895_, lean_object* v_a_896_, lean_object* v_v_897_){
_start:
{
lean_object* v_toConstantVal_898_; lean_object* v_value_899_; lean_object* v_type_900_; lean_object* v___f_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v_toConstantVal_898_ = lean_ctor_get(v_v_897_, 0);
lean_inc_ref(v_toConstantVal_898_);
v_value_899_ = lean_ctor_get(v_v_897_, 1);
lean_inc_ref(v_value_899_);
lean_dec_ref(v_v_897_);
v_type_900_ = lean_ctor_get(v_toConstantVal_898_, 2);
lean_inc_ref(v_type_900_);
lean_dec_ref(v_toConstantVal_898_);
lean_inc(v_f_894_);
v___f_901_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__3), 3, 2);
lean_closure_set(v___f_901_, 0, v_f_894_);
lean_closure_set(v___f_901_, 1, v_value_899_);
v___x_902_ = lean_apply_2(v_f_894_, v_a_896_, v_type_900_);
v___x_903_ = lean_apply_4(v_toBind_895_, lean_box(0), lean_box(0), v___x_902_, v___f_901_);
return v___x_903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__2(lean_object* v_f_904_, lean_object* v_a_905_, lean_object* v_ctor_906_){
_start:
{
lean_object* v_type_907_; lean_object* v___x_908_; 
v_type_907_ = lean_ctor_get(v_ctor_906_, 1);
lean_inc_ref(v_type_907_);
lean_dec_ref(v_ctor_906_);
v___x_908_ = lean_apply_2(v_f_904_, v_a_905_, v_type_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__4(lean_object* v_inst_909_, lean_object* v___f_910_, lean_object* v_ctors_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_List_foldlM___redArg(v_inst_909_, v___f_910_, v_a_912_, v_ctors_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__5(lean_object* v_inst_914_, lean_object* v___f_915_, lean_object* v_f_916_, lean_object* v_toBind_917_, lean_object* v_a_918_, lean_object* v_inductType_919_){
_start:
{
lean_object* v_type_920_; lean_object* v_ctors_921_; lean_object* v___f_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v_type_920_ = lean_ctor_get(v_inductType_919_, 1);
lean_inc_ref(v_type_920_);
v_ctors_921_ = lean_ctor_get(v_inductType_919_, 2);
lean_inc(v_ctors_921_);
lean_dec_ref(v_inductType_919_);
v___f_922_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__4), 4, 3);
lean_closure_set(v___f_922_, 0, v_inst_914_);
lean_closure_set(v___f_922_, 1, v___f_915_);
lean_closure_set(v___f_922_, 2, v_ctors_921_);
v___x_923_ = lean_apply_2(v_f_916_, v_a_918_, v_type_920_);
v___x_924_ = lean_apply_4(v_toBind_917_, lean_box(0), lean_box(0), v___x_923_, v___f_922_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object* v_inst_925_, lean_object* v_d_926_, lean_object* v_f_927_, lean_object* v_a_928_){
_start:
{
switch(lean_obj_tag(v_d_926_))
{
case 0:
{
lean_object* v_val_929_; lean_object* v_toConstantVal_930_; lean_object* v_type_931_; lean_object* v___x_932_; 
lean_dec_ref(v_inst_925_);
v_val_929_ = lean_ctor_get(v_d_926_, 0);
lean_inc_ref(v_val_929_);
lean_dec_ref_known(v_d_926_, 1);
v_toConstantVal_930_ = lean_ctor_get(v_val_929_, 0);
lean_inc_ref(v_toConstantVal_930_);
lean_dec_ref(v_val_929_);
v_type_931_ = lean_ctor_get(v_toConstantVal_930_, 2);
lean_inc_ref(v_type_931_);
lean_dec_ref(v_toConstantVal_930_);
v___x_932_ = lean_apply_2(v_f_927_, v_a_928_, v_type_931_);
return v___x_932_;
}
case 4:
{
lean_object* v_toApplicative_933_; lean_object* v_toPure_934_; lean_object* v___x_935_; 
v_toApplicative_933_ = lean_ctor_get(v_inst_925_, 0);
lean_inc_ref(v_toApplicative_933_);
lean_dec(v_f_927_);
lean_dec_ref(v_inst_925_);
v_toPure_934_ = lean_ctor_get(v_toApplicative_933_, 1);
lean_inc(v_toPure_934_);
lean_dec_ref(v_toApplicative_933_);
v___x_935_ = lean_apply_2(v_toPure_934_, lean_box(0), v_a_928_);
return v___x_935_;
}
case 5:
{
lean_object* v_toBind_936_; lean_object* v_defns_937_; lean_object* v___f_938_; lean_object* v___x_939_; 
v_toBind_936_ = lean_ctor_get(v_inst_925_, 1);
v_defns_937_ = lean_ctor_get(v_d_926_, 0);
lean_inc(v_defns_937_);
lean_dec_ref_known(v_d_926_, 1);
lean_inc(v_toBind_936_);
v___f_938_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_938_, 0, v_f_927_);
lean_closure_set(v___f_938_, 1, v_toBind_936_);
v___x_939_ = l_List_foldlM___redArg(v_inst_925_, v___f_938_, v_a_928_, v_defns_937_);
return v___x_939_;
}
case 6:
{
lean_object* v_toBind_940_; lean_object* v_types_941_; lean_object* v___f_942_; lean_object* v___f_943_; lean_object* v___x_944_; 
v_toBind_940_ = lean_ctor_get(v_inst_925_, 1);
v_types_941_ = lean_ctor_get(v_d_926_, 2);
lean_inc(v_types_941_);
lean_dec_ref_known(v_d_926_, 3);
lean_inc(v_f_927_);
v___f_942_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__2), 3, 1);
lean_closure_set(v___f_942_, 0, v_f_927_);
lean_inc(v_toBind_940_);
lean_inc_ref(v_inst_925_);
v___f_943_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__5), 6, 4);
lean_closure_set(v___f_943_, 0, v_inst_925_);
lean_closure_set(v___f_943_, 1, v___f_942_);
lean_closure_set(v___f_943_, 2, v_f_927_);
lean_closure_set(v___f_943_, 3, v_toBind_940_);
v___x_944_ = l_List_foldlM___redArg(v_inst_925_, v___f_943_, v_a_928_, v_types_941_);
return v___x_944_;
}
default: 
{
lean_object* v_val_945_; lean_object* v_toConstantVal_946_; lean_object* v_toBind_947_; lean_object* v_value_948_; lean_object* v_type_949_; lean_object* v___f_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v_val_945_ = lean_ctor_get(v_d_926_, 0);
lean_inc_ref(v_val_945_);
lean_dec(v_d_926_);
v_toConstantVal_946_ = lean_ctor_get(v_val_945_, 0);
lean_inc_ref(v_toConstantVal_946_);
v_toBind_947_ = lean_ctor_get(v_inst_925_, 1);
lean_inc(v_toBind_947_);
lean_dec_ref(v_inst_925_);
v_value_948_ = lean_ctor_get(v_val_945_, 1);
lean_inc_ref(v_value_948_);
lean_dec_ref(v_val_945_);
v_type_949_ = lean_ctor_get(v_toConstantVal_946_, 2);
lean_inc_ref(v_type_949_);
lean_dec_ref(v_toConstantVal_946_);
lean_inc(v_f_927_);
v___f_950_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_950_, 0, v_f_927_);
lean_closure_set(v___f_950_, 1, v_value_948_);
v___x_951_ = lean_apply_2(v_f_927_, v_a_928_, v_type_949_);
v___x_952_ = lean_apply_4(v_toBind_947_, lean_box(0), lean_box(0), v___x_951_, v___f_950_);
return v___x_952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM(lean_object* v_00_u03b1_953_, lean_object* v_m_954_, lean_object* v_inst_955_, lean_object* v_d_956_, lean_object* v_f_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_959_; 
v___x_959_ = l_Lean_Declaration_foldExprM___redArg(v_inst_955_, v_d_956_, v_f_957_, v_a_958_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg___lam__0(lean_object* v_f_960_, lean_object* v_x_961_, lean_object* v_a_962_){
_start:
{
lean_object* v___x_963_; 
v___x_963_ = lean_apply_1(v_f_960_, v_a_962_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg(lean_object* v_inst_964_, lean_object* v_d_965_, lean_object* v_f_966_){
_start:
{
lean_object* v___f_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___f_967_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_967_, 0, v_f_966_);
v___x_968_ = lean_box(0);
v___x_969_ = l_Lean_Declaration_foldExprM___redArg(v_inst_964_, v_d_965_, v___f_967_, v___x_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM(lean_object* v_m_970_, lean_object* v_inst_971_, lean_object* v_d_972_, lean_object* v_f_973_){
_start:
{
lean_object* v___f_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v___f_974_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_974_, 0, v_f_973_);
v___x_975_ = lean_box(0);
v___x_976_ = l_Lean_Declaration_foldExprM___redArg(v_inst_971_, v_d_972_, v___f_974_, v___x_975_);
return v___x_976_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default___closed__0(void){
_start:
{
uint8_t v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_977_ = 0;
v___x_978_ = lean_box(0);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = l_Lean_instInhabitedConstantVal_default;
v___x_981_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_979_);
lean_ctor_set(v___x_981_, 2, v___x_979_);
lean_ctor_set(v___x_981_, 3, v___x_978_);
lean_ctor_set(v___x_981_, 4, v___x_978_);
lean_ctor_set(v___x_981_, 5, v___x_979_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*6, v___x_977_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*6 + 1, v___x_977_);
lean_ctor_set_uint8(v___x_981_, sizeof(void*)*6 + 2, v___x_977_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default(void){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = lean_obj_once(&l_Lean_instInhabitedInductiveVal_default___closed__0, &l_Lean_instInhabitedInductiveVal_default___closed__0_once, _init_l_Lean_instInhabitedInductiveVal_default___closed__0);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal(void){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = l_Lean_instInhabitedInductiveVal_default;
return v___x_983_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveVal_beq(lean_object* v_x_984_, lean_object* v_x_985_){
_start:
{
lean_object* v_toConstantVal_986_; lean_object* v_numParams_987_; lean_object* v_numIndices_988_; lean_object* v_all_989_; lean_object* v_ctors_990_; lean_object* v_numNested_991_; uint8_t v_isRec_992_; uint8_t v_isUnsafe_993_; uint8_t v_isReflexive_994_; lean_object* v_toConstantVal_995_; lean_object* v_numParams_996_; lean_object* v_numIndices_997_; lean_object* v_all_998_; lean_object* v_ctors_999_; lean_object* v_numNested_1000_; uint8_t v_isRec_1001_; uint8_t v_isUnsafe_1002_; uint8_t v_isReflexive_1003_; uint8_t v___y_1005_; uint8_t v___y_1007_; uint8_t v___x_1008_; 
v_toConstantVal_986_ = lean_ctor_get(v_x_984_, 0);
v_numParams_987_ = lean_ctor_get(v_x_984_, 1);
v_numIndices_988_ = lean_ctor_get(v_x_984_, 2);
v_all_989_ = lean_ctor_get(v_x_984_, 3);
v_ctors_990_ = lean_ctor_get(v_x_984_, 4);
v_numNested_991_ = lean_ctor_get(v_x_984_, 5);
v_isRec_992_ = lean_ctor_get_uint8(v_x_984_, sizeof(void*)*6);
v_isUnsafe_993_ = lean_ctor_get_uint8(v_x_984_, sizeof(void*)*6 + 1);
v_isReflexive_994_ = lean_ctor_get_uint8(v_x_984_, sizeof(void*)*6 + 2);
v_toConstantVal_995_ = lean_ctor_get(v_x_985_, 0);
v_numParams_996_ = lean_ctor_get(v_x_985_, 1);
v_numIndices_997_ = lean_ctor_get(v_x_985_, 2);
v_all_998_ = lean_ctor_get(v_x_985_, 3);
v_ctors_999_ = lean_ctor_get(v_x_985_, 4);
v_numNested_1000_ = lean_ctor_get(v_x_985_, 5);
v_isRec_1001_ = lean_ctor_get_uint8(v_x_985_, sizeof(void*)*6);
v_isUnsafe_1002_ = lean_ctor_get_uint8(v_x_985_, sizeof(void*)*6 + 1);
v_isReflexive_1003_ = lean_ctor_get_uint8(v_x_985_, sizeof(void*)*6 + 2);
v___x_1008_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_986_, v_toConstantVal_995_);
if (v___x_1008_ == 0)
{
return v___x_1008_;
}
else
{
uint8_t v___x_1009_; 
v___x_1009_ = lean_nat_dec_eq(v_numParams_987_, v_numParams_996_);
if (v___x_1009_ == 0)
{
return v___x_1009_;
}
else
{
uint8_t v___x_1010_; 
v___x_1010_ = lean_nat_dec_eq(v_numIndices_988_, v_numIndices_997_);
if (v___x_1010_ == 0)
{
return v___x_1010_;
}
else
{
uint8_t v___x_1011_; 
v___x_1011_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_989_, v_all_998_);
if (v___x_1011_ == 0)
{
return v___x_1011_;
}
else
{
uint8_t v___x_1012_; 
v___x_1012_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_ctors_990_, v_ctors_999_);
if (v___x_1012_ == 0)
{
return v___x_1012_;
}
else
{
uint8_t v___x_1013_; 
v___x_1013_ = lean_nat_dec_eq(v_numNested_991_, v_numNested_1000_);
if (v___x_1013_ == 0)
{
return v___x_1013_;
}
else
{
if (v_isRec_1001_ == 0)
{
if (v_isRec_992_ == 0)
{
v___y_1007_ = v___x_1013_;
goto v___jp_1006_;
}
else
{
return v_isRec_1001_;
}
}
else
{
v___y_1007_ = v_isRec_992_;
goto v___jp_1006_;
}
}
}
}
}
}
}
v___jp_1004_:
{
if (v_isReflexive_1003_ == 0)
{
if (v_isReflexive_994_ == 0)
{
return v___y_1005_;
}
else
{
return v_isReflexive_1003_;
}
}
else
{
return v_isReflexive_994_;
}
}
v___jp_1006_:
{
if (v___y_1007_ == 0)
{
return v___y_1007_;
}
else
{
if (v_isUnsafe_1002_ == 0)
{
if (v_isUnsafe_993_ == 0)
{
v___y_1005_ = v___y_1007_;
goto v___jp_1004_;
}
else
{
return v_isUnsafe_1002_;
}
}
else
{
if (v_isUnsafe_993_ == 0)
{
return v_isUnsafe_993_;
}
else
{
v___y_1005_ = v_isUnsafe_993_;
goto v___jp_1004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveVal_beq___boxed(lean_object* v_x_1014_, lean_object* v_x_1015_){
_start:
{
uint8_t v_res_1016_; lean_object* v_r_1017_; 
v_res_1016_ = l_Lean_instBEqInductiveVal_beq(v_x_1014_, v_x_1015_);
lean_dec_ref(v_x_1015_);
lean_dec_ref(v_x_1014_);
v_r_1017_ = lean_box(v_res_1016_);
return v_r_1017_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_val(lean_object* v_name_1020_, lean_object* v_levelParams_1021_, lean_object* v_type_1022_, lean_object* v_numParams_1023_, lean_object* v_numIndices_1024_, lean_object* v_all_1025_, lean_object* v_ctors_1026_, lean_object* v_numNested_1027_, uint8_t v_isRec_1028_, uint8_t v_isUnsafe_1029_, uint8_t v_isReflexive_1030_){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1031_, 0, v_name_1020_);
lean_ctor_set(v___x_1031_, 1, v_levelParams_1021_);
lean_ctor_set(v___x_1031_, 2, v_type_1022_);
v___x_1032_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v_numParams_1023_);
lean_ctor_set(v___x_1032_, 2, v_numIndices_1024_);
lean_ctor_set(v___x_1032_, 3, v_all_1025_);
lean_ctor_set(v___x_1032_, 4, v_ctors_1026_);
lean_ctor_set(v___x_1032_, 5, v_numNested_1027_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*6, v_isRec_1028_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*6 + 1, v_isUnsafe_1029_);
lean_ctor_set_uint8(v___x_1032_, sizeof(void*)*6 + 2, v_isReflexive_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveValEx___boxed(lean_object* v_name_1033_, lean_object* v_levelParams_1034_, lean_object* v_type_1035_, lean_object* v_numParams_1036_, lean_object* v_numIndices_1037_, lean_object* v_all_1038_, lean_object* v_ctors_1039_, lean_object* v_numNested_1040_, lean_object* v_isRec_1041_, lean_object* v_isUnsafe_1042_, lean_object* v_isReflexive_1043_){
_start:
{
uint8_t v_isRec_boxed_1044_; uint8_t v_isUnsafe_boxed_1045_; uint8_t v_isReflexive_boxed_1046_; lean_object* v_res_1047_; 
v_isRec_boxed_1044_ = lean_unbox(v_isRec_1041_);
v_isUnsafe_boxed_1045_ = lean_unbox(v_isUnsafe_1042_);
v_isReflexive_boxed_1046_ = lean_unbox(v_isReflexive_1043_);
v_res_1047_ = lean_mk_inductive_val(v_name_1033_, v_levelParams_1034_, v_type_1035_, v_numParams_1036_, v_numIndices_1037_, v_all_1038_, v_ctors_1039_, v_numNested_1040_, v_isRec_boxed_1044_, v_isUnsafe_boxed_1045_, v_isReflexive_boxed_1046_);
return v_res_1047_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_rec(lean_object* v_v_1048_){
_start:
{
uint8_t v_isRec_1049_; 
v_isRec_1049_ = lean_ctor_get_uint8(v_v_1048_, sizeof(void*)*6);
lean_dec_ref(v_v_1048_);
return v_isRec_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isRecEx___boxed(lean_object* v_v_1050_){
_start:
{
uint8_t v_res_1051_; lean_object* v_r_1052_; 
v_res_1051_ = lean_inductive_val_is_rec(v_v_1050_);
v_r_1052_ = lean_box(v_res_1051_);
return v_r_1052_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_unsafe(lean_object* v_v_1053_){
_start:
{
uint8_t v_isUnsafe_1054_; 
v_isUnsafe_1054_ = lean_ctor_get_uint8(v_v_1053_, sizeof(void*)*6 + 1);
lean_dec_ref(v_v_1053_);
return v_isUnsafe_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isUnsafeEx___boxed(lean_object* v_v_1055_){
_start:
{
uint8_t v_res_1056_; lean_object* v_r_1057_; 
v_res_1056_ = lean_inductive_val_is_unsafe(v_v_1055_);
v_r_1057_ = lean_box(v_res_1056_);
return v_r_1057_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_reflexive(lean_object* v_v_1058_){
_start:
{
uint8_t v_isReflexive_1059_; 
v_isReflexive_1059_ = lean_ctor_get_uint8(v_v_1058_, sizeof(void*)*6 + 2);
lean_dec_ref(v_v_1058_);
return v_isReflexive_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isReflexiveEx___boxed(lean_object* v_v_1060_){
_start:
{
uint8_t v_res_1061_; lean_object* v_r_1062_; 
v_res_1061_ = lean_inductive_val_is_reflexive(v_v_1060_);
v_r_1062_ = lean_box(v_res_1061_);
return v_r_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors(lean_object* v_v_1063_){
_start:
{
lean_object* v_ctors_1064_; lean_object* v___x_1065_; 
v_ctors_1064_ = lean_ctor_get(v_v_1063_, 4);
v___x_1065_ = l_List_lengthTR___redArg(v_ctors_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors___boxed(lean_object* v_v_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_InductiveVal_numCtors(v_v_1066_);
lean_dec_ref(v_v_1066_);
return v_res_1067_;
}
}
LEAN_EXPORT uint8_t l_Lean_InductiveVal_isNested(lean_object* v_v_1068_){
_start:
{
lean_object* v_numNested_1069_; lean_object* v___x_1070_; uint8_t v___x_1071_; 
v_numNested_1069_ = lean_ctor_get(v_v_1068_, 5);
v___x_1070_ = lean_unsigned_to_nat(0u);
v___x_1071_ = lean_nat_dec_lt(v___x_1070_, v_numNested_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isNested___boxed(lean_object* v_v_1072_){
_start:
{
uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_res_1073_ = l_Lean_InductiveVal_isNested(v_v_1072_);
lean_dec_ref(v_v_1072_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object* v_v_1075_){
_start:
{
lean_object* v_all_1076_; lean_object* v_numNested_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_all_1076_ = lean_ctor_get(v_v_1075_, 3);
v_numNested_1077_ = lean_ctor_get(v_v_1075_, 5);
v___x_1078_ = l_List_lengthTR___redArg(v_all_1076_);
v___x_1079_ = lean_nat_add(v___x_1078_, v_numNested_1077_);
lean_dec(v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers___boxed(lean_object* v_v_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_InductiveVal_numTypeFormers(v_v_1080_);
lean_dec_ref(v_v_1080_);
return v_res_1081_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1082_ = 0;
v___x_1083_ = lean_unsigned_to_nat(0u);
v___x_1084_ = lean_box(0);
v___x_1085_ = l_Lean_instInhabitedConstantVal_default;
v___x_1086_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v___x_1084_);
lean_ctor_set(v___x_1086_, 2, v___x_1083_);
lean_ctor_set(v___x_1086_, 3, v___x_1083_);
lean_ctor_set(v___x_1086_, 4, v___x_1083_);
lean_ctor_set_uint8(v___x_1086_, sizeof(void*)*5, v___x_1082_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default(void){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_obj_once(&l_Lean_instInhabitedConstructorVal_default___closed__0, &l_Lean_instInhabitedConstructorVal_default___closed__0_once, _init_l_Lean_instInhabitedConstructorVal_default___closed__0);
return v___x_1087_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal(void){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_instInhabitedConstructorVal_default;
return v___x_1088_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructorVal_beq(lean_object* v_x_1089_, lean_object* v_x_1090_){
_start:
{
lean_object* v_toConstantVal_1091_; lean_object* v_induct_1092_; lean_object* v_cidx_1093_; lean_object* v_numParams_1094_; lean_object* v_numFields_1095_; uint8_t v_isUnsafe_1096_; lean_object* v_toConstantVal_1097_; lean_object* v_induct_1098_; lean_object* v_cidx_1099_; lean_object* v_numParams_1100_; lean_object* v_numFields_1101_; uint8_t v_isUnsafe_1102_; uint8_t v___x_1103_; 
v_toConstantVal_1091_ = lean_ctor_get(v_x_1089_, 0);
v_induct_1092_ = lean_ctor_get(v_x_1089_, 1);
v_cidx_1093_ = lean_ctor_get(v_x_1089_, 2);
v_numParams_1094_ = lean_ctor_get(v_x_1089_, 3);
v_numFields_1095_ = lean_ctor_get(v_x_1089_, 4);
v_isUnsafe_1096_ = lean_ctor_get_uint8(v_x_1089_, sizeof(void*)*5);
v_toConstantVal_1097_ = lean_ctor_get(v_x_1090_, 0);
v_induct_1098_ = lean_ctor_get(v_x_1090_, 1);
v_cidx_1099_ = lean_ctor_get(v_x_1090_, 2);
v_numParams_1100_ = lean_ctor_get(v_x_1090_, 3);
v_numFields_1101_ = lean_ctor_get(v_x_1090_, 4);
v_isUnsafe_1102_ = lean_ctor_get_uint8(v_x_1090_, sizeof(void*)*5);
v___x_1103_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1091_, v_toConstantVal_1097_);
if (v___x_1103_ == 0)
{
return v___x_1103_;
}
else
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_name_eq(v_induct_1092_, v_induct_1098_);
if (v___x_1104_ == 0)
{
return v___x_1104_;
}
else
{
uint8_t v___x_1105_; 
v___x_1105_ = lean_nat_dec_eq(v_cidx_1093_, v_cidx_1099_);
if (v___x_1105_ == 0)
{
return v___x_1105_;
}
else
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_nat_dec_eq(v_numParams_1094_, v_numParams_1100_);
if (v___x_1106_ == 0)
{
return v___x_1106_;
}
else
{
uint8_t v___x_1107_; 
v___x_1107_ = lean_nat_dec_eq(v_numFields_1095_, v_numFields_1101_);
if (v___x_1107_ == 0)
{
return v___x_1107_;
}
else
{
if (v_isUnsafe_1102_ == 0)
{
if (v_isUnsafe_1096_ == 0)
{
return v___x_1107_;
}
else
{
return v_isUnsafe_1102_;
}
}
else
{
return v_isUnsafe_1096_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructorVal_beq___boxed(lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
uint8_t v_res_1110_; lean_object* v_r_1111_; 
v_res_1110_ = l_Lean_instBEqConstructorVal_beq(v_x_1108_, v_x_1109_);
lean_dec_ref(v_x_1109_);
lean_dec_ref(v_x_1108_);
v_r_1111_ = lean_box(v_res_1110_);
return v_r_1111_;
}
}
LEAN_EXPORT lean_object* lean_mk_constructor_val(lean_object* v_name_1114_, lean_object* v_levelParams_1115_, lean_object* v_type_1116_, lean_object* v_induct_1117_, lean_object* v_cidx_1118_, lean_object* v_numParams_1119_, lean_object* v_numFields_1120_, uint8_t v_isUnsafe_1121_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1122_, 0, v_name_1114_);
lean_ctor_set(v___x_1122_, 1, v_levelParams_1115_);
lean_ctor_set(v___x_1122_, 2, v_type_1116_);
v___x_1123_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
lean_ctor_set(v___x_1123_, 1, v_induct_1117_);
lean_ctor_set(v___x_1123_, 2, v_cidx_1118_);
lean_ctor_set(v___x_1123_, 3, v_numParams_1119_);
lean_ctor_set(v___x_1123_, 4, v_numFields_1120_);
lean_ctor_set_uint8(v___x_1123_, sizeof(void*)*5, v_isUnsafe_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstructorValEx___boxed(lean_object* v_name_1124_, lean_object* v_levelParams_1125_, lean_object* v_type_1126_, lean_object* v_induct_1127_, lean_object* v_cidx_1128_, lean_object* v_numParams_1129_, lean_object* v_numFields_1130_, lean_object* v_isUnsafe_1131_){
_start:
{
uint8_t v_isUnsafe_boxed_1132_; lean_object* v_res_1133_; 
v_isUnsafe_boxed_1132_ = lean_unbox(v_isUnsafe_1131_);
v_res_1133_ = lean_mk_constructor_val(v_name_1124_, v_levelParams_1125_, v_type_1126_, v_induct_1127_, v_cidx_1128_, v_numParams_1129_, v_numFields_1130_, v_isUnsafe_boxed_1132_);
return v_res_1133_;
}
}
LEAN_EXPORT uint8_t lean_constructor_val_is_unsafe(lean_object* v_v_1134_){
_start:
{
uint8_t v_isUnsafe_1135_; 
v_isUnsafe_1135_ = lean_ctor_get_uint8(v_v_1134_, sizeof(void*)*5);
lean_dec_ref(v_v_1134_);
return v_isUnsafe_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstructorVal_isUnsafeEx___boxed(lean_object* v_v_1136_){
_start:
{
uint8_t v_res_1137_; lean_object* v_r_1138_; 
v_res_1137_ = lean_constructor_val_is_unsafe(v_v_1136_);
v_r_1138_ = lean_box(v_res_1137_);
return v_r_1138_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default___closed__0(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1139_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v___x_1140_);
lean_ctor_set(v___x_1142_, 2, v___x_1139_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default(void){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_obj_once(&l_Lean_instInhabitedRecursorRule_default___closed__0, &l_Lean_instInhabitedRecursorRule_default___closed__0_once, _init_l_Lean_instInhabitedRecursorRule_default___closed__0);
return v___x_1143_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule(void){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_instInhabitedRecursorRule_default;
return v___x_1144_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorRule_beq(lean_object* v_x_1145_, lean_object* v_x_1146_){
_start:
{
lean_object* v_ctor_1147_; lean_object* v_nfields_1148_; lean_object* v_rhs_1149_; lean_object* v_ctor_1150_; lean_object* v_nfields_1151_; lean_object* v_rhs_1152_; uint8_t v___x_1153_; 
v_ctor_1147_ = lean_ctor_get(v_x_1145_, 0);
v_nfields_1148_ = lean_ctor_get(v_x_1145_, 1);
v_rhs_1149_ = lean_ctor_get(v_x_1145_, 2);
v_ctor_1150_ = lean_ctor_get(v_x_1146_, 0);
v_nfields_1151_ = lean_ctor_get(v_x_1146_, 1);
v_rhs_1152_ = lean_ctor_get(v_x_1146_, 2);
v___x_1153_ = lean_name_eq(v_ctor_1147_, v_ctor_1150_);
if (v___x_1153_ == 0)
{
return v___x_1153_;
}
else
{
uint8_t v___x_1154_; 
v___x_1154_ = lean_nat_dec_eq(v_nfields_1148_, v_nfields_1151_);
if (v___x_1154_ == 0)
{
return v___x_1154_;
}
else
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_expr_eqv(v_rhs_1149_, v_rhs_1152_);
return v___x_1155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorRule_beq___boxed(lean_object* v_x_1156_, lean_object* v_x_1157_){
_start:
{
uint8_t v_res_1158_; lean_object* v_r_1159_; 
v_res_1158_ = l_Lean_instBEqRecursorRule_beq(v_x_1156_, v_x_1157_);
lean_dec_ref(v_x_1157_);
lean_dec_ref(v_x_1156_);
v_r_1159_ = lean_box(v_res_1158_);
return v_r_1159_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1162_ = 0;
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = lean_box(0);
v___x_1165_ = l_Lean_instInhabitedConstantVal_default;
v___x_1166_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
lean_ctor_set(v___x_1166_, 1, v___x_1164_);
lean_ctor_set(v___x_1166_, 2, v___x_1163_);
lean_ctor_set(v___x_1166_, 3, v___x_1163_);
lean_ctor_set(v___x_1166_, 4, v___x_1163_);
lean_ctor_set(v___x_1166_, 5, v___x_1163_);
lean_ctor_set(v___x_1166_, 6, v___x_1164_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*7, v___x_1162_);
lean_ctor_set_uint8(v___x_1166_, sizeof(void*)*7 + 1, v___x_1162_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default(void){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_obj_once(&l_Lean_instInhabitedRecursorVal_default___closed__0, &l_Lean_instInhabitedRecursorVal_default___closed__0_once, _init_l_Lean_instInhabitedRecursorVal_default___closed__0);
return v___x_1167_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal(void){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_instInhabitedRecursorVal_default;
return v___x_1168_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(lean_object* v_x_1169_, lean_object* v_x_1170_){
_start:
{
if (lean_obj_tag(v_x_1169_) == 0)
{
if (lean_obj_tag(v_x_1170_) == 0)
{
uint8_t v___x_1171_; 
v___x_1171_ = 1;
return v___x_1171_;
}
else
{
uint8_t v___x_1172_; 
v___x_1172_ = 0;
return v___x_1172_;
}
}
else
{
if (lean_obj_tag(v_x_1170_) == 0)
{
uint8_t v___x_1173_; 
v___x_1173_ = 0;
return v___x_1173_;
}
else
{
lean_object* v_head_1174_; lean_object* v_tail_1175_; lean_object* v_head_1176_; lean_object* v_tail_1177_; uint8_t v___x_1178_; 
v_head_1174_ = lean_ctor_get(v_x_1169_, 0);
v_tail_1175_ = lean_ctor_get(v_x_1169_, 1);
v_head_1176_ = lean_ctor_get(v_x_1170_, 0);
v_tail_1177_ = lean_ctor_get(v_x_1170_, 1);
v___x_1178_ = l_Lean_instBEqRecursorRule_beq(v_head_1174_, v_head_1176_);
if (v___x_1178_ == 0)
{
return v___x_1178_;
}
else
{
v_x_1169_ = v_tail_1175_;
v_x_1170_ = v_tail_1177_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0___boxed(lean_object* v_x_1180_, lean_object* v_x_1181_){
_start:
{
uint8_t v_res_1182_; lean_object* v_r_1183_; 
v_res_1182_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_x_1180_, v_x_1181_);
lean_dec(v_x_1181_);
lean_dec(v_x_1180_);
v_r_1183_ = lean_box(v_res_1182_);
return v_r_1183_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorVal_beq(lean_object* v_x_1184_, lean_object* v_x_1185_){
_start:
{
lean_object* v_toConstantVal_1186_; lean_object* v_all_1187_; lean_object* v_numParams_1188_; lean_object* v_numIndices_1189_; lean_object* v_numMotives_1190_; lean_object* v_numMinors_1191_; lean_object* v_rules_1192_; uint8_t v_k_1193_; uint8_t v_isUnsafe_1194_; lean_object* v_toConstantVal_1195_; lean_object* v_all_1196_; lean_object* v_numParams_1197_; lean_object* v_numIndices_1198_; lean_object* v_numMotives_1199_; lean_object* v_numMinors_1200_; lean_object* v_rules_1201_; uint8_t v_k_1202_; uint8_t v_isUnsafe_1203_; uint8_t v___y_1205_; uint8_t v___x_1206_; 
v_toConstantVal_1186_ = lean_ctor_get(v_x_1184_, 0);
v_all_1187_ = lean_ctor_get(v_x_1184_, 1);
v_numParams_1188_ = lean_ctor_get(v_x_1184_, 2);
v_numIndices_1189_ = lean_ctor_get(v_x_1184_, 3);
v_numMotives_1190_ = lean_ctor_get(v_x_1184_, 4);
v_numMinors_1191_ = lean_ctor_get(v_x_1184_, 5);
v_rules_1192_ = lean_ctor_get(v_x_1184_, 6);
v_k_1193_ = lean_ctor_get_uint8(v_x_1184_, sizeof(void*)*7);
v_isUnsafe_1194_ = lean_ctor_get_uint8(v_x_1184_, sizeof(void*)*7 + 1);
v_toConstantVal_1195_ = lean_ctor_get(v_x_1185_, 0);
v_all_1196_ = lean_ctor_get(v_x_1185_, 1);
v_numParams_1197_ = lean_ctor_get(v_x_1185_, 2);
v_numIndices_1198_ = lean_ctor_get(v_x_1185_, 3);
v_numMotives_1199_ = lean_ctor_get(v_x_1185_, 4);
v_numMinors_1200_ = lean_ctor_get(v_x_1185_, 5);
v_rules_1201_ = lean_ctor_get(v_x_1185_, 6);
v_k_1202_ = lean_ctor_get_uint8(v_x_1185_, sizeof(void*)*7);
v_isUnsafe_1203_ = lean_ctor_get_uint8(v_x_1185_, sizeof(void*)*7 + 1);
v___x_1206_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1186_, v_toConstantVal_1195_);
if (v___x_1206_ == 0)
{
return v___x_1206_;
}
else
{
uint8_t v___x_1207_; 
v___x_1207_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_1187_, v_all_1196_);
if (v___x_1207_ == 0)
{
return v___x_1207_;
}
else
{
uint8_t v___x_1208_; 
v___x_1208_ = lean_nat_dec_eq(v_numParams_1188_, v_numParams_1197_);
if (v___x_1208_ == 0)
{
return v___x_1208_;
}
else
{
uint8_t v___x_1209_; 
v___x_1209_ = lean_nat_dec_eq(v_numIndices_1189_, v_numIndices_1198_);
if (v___x_1209_ == 0)
{
return v___x_1209_;
}
else
{
uint8_t v___x_1210_; 
v___x_1210_ = lean_nat_dec_eq(v_numMotives_1190_, v_numMotives_1199_);
if (v___x_1210_ == 0)
{
return v___x_1210_;
}
else
{
uint8_t v___x_1211_; 
v___x_1211_ = lean_nat_dec_eq(v_numMinors_1191_, v_numMinors_1200_);
if (v___x_1211_ == 0)
{
return v___x_1211_;
}
else
{
uint8_t v___x_1212_; 
v___x_1212_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_rules_1192_, v_rules_1201_);
if (v___x_1212_ == 0)
{
return v___x_1212_;
}
else
{
if (v_k_1202_ == 0)
{
if (v_k_1193_ == 0)
{
v___y_1205_ = v___x_1212_;
goto v___jp_1204_;
}
else
{
return v_k_1202_;
}
}
else
{
v___y_1205_ = v_k_1193_;
goto v___jp_1204_;
}
}
}
}
}
}
}
}
v___jp_1204_:
{
if (v___y_1205_ == 0)
{
return v___y_1205_;
}
else
{
if (v_isUnsafe_1203_ == 0)
{
if (v_isUnsafe_1194_ == 0)
{
return v___y_1205_;
}
else
{
return v_isUnsafe_1203_;
}
}
else
{
return v_isUnsafe_1194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorVal_beq___boxed(lean_object* v_x_1213_, lean_object* v_x_1214_){
_start:
{
uint8_t v_res_1215_; lean_object* v_r_1216_; 
v_res_1215_ = l_Lean_instBEqRecursorVal_beq(v_x_1213_, v_x_1214_);
lean_dec_ref(v_x_1214_);
lean_dec_ref(v_x_1213_);
v_r_1216_ = lean_box(v_res_1215_);
return v_r_1216_;
}
}
LEAN_EXPORT lean_object* lean_mk_recursor_val(lean_object* v_name_1219_, lean_object* v_levelParams_1220_, lean_object* v_type_1221_, lean_object* v_all_1222_, lean_object* v_numParams_1223_, lean_object* v_numIndices_1224_, lean_object* v_numMotives_1225_, lean_object* v_numMinors_1226_, lean_object* v_rules_1227_, uint8_t v_k_1228_, uint8_t v_isUnsafe_1229_){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1230_, 0, v_name_1219_);
lean_ctor_set(v___x_1230_, 1, v_levelParams_1220_);
lean_ctor_set(v___x_1230_, 2, v_type_1221_);
v___x_1231_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v_all_1222_);
lean_ctor_set(v___x_1231_, 2, v_numParams_1223_);
lean_ctor_set(v___x_1231_, 3, v_numIndices_1224_);
lean_ctor_set(v___x_1231_, 4, v_numMotives_1225_);
lean_ctor_set(v___x_1231_, 5, v_numMinors_1226_);
lean_ctor_set(v___x_1231_, 6, v_rules_1227_);
lean_ctor_set_uint8(v___x_1231_, sizeof(void*)*7, v_k_1228_);
lean_ctor_set_uint8(v___x_1231_, sizeof(void*)*7 + 1, v_isUnsafe_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecursorValEx___boxed(lean_object* v_name_1232_, lean_object* v_levelParams_1233_, lean_object* v_type_1234_, lean_object* v_all_1235_, lean_object* v_numParams_1236_, lean_object* v_numIndices_1237_, lean_object* v_numMotives_1238_, lean_object* v_numMinors_1239_, lean_object* v_rules_1240_, lean_object* v_k_1241_, lean_object* v_isUnsafe_1242_){
_start:
{
uint8_t v_k_boxed_1243_; uint8_t v_isUnsafe_boxed_1244_; lean_object* v_res_1245_; 
v_k_boxed_1243_ = lean_unbox(v_k_1241_);
v_isUnsafe_boxed_1244_ = lean_unbox(v_isUnsafe_1242_);
v_res_1245_ = lean_mk_recursor_val(v_name_1232_, v_levelParams_1233_, v_type_1234_, v_all_1235_, v_numParams_1236_, v_numIndices_1237_, v_numMotives_1238_, v_numMinors_1239_, v_rules_1240_, v_k_boxed_1243_, v_isUnsafe_boxed_1244_);
return v_res_1245_;
}
}
LEAN_EXPORT uint8_t lean_recursor_k(lean_object* v_v_1246_){
_start:
{
uint8_t v_k_1247_; 
v_k_1247_ = lean_ctor_get_uint8(v_v_1246_, sizeof(void*)*7);
lean_dec_ref(v_v_1246_);
return v_k_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_kEx___boxed(lean_object* v_v_1248_){
_start:
{
uint8_t v_res_1249_; lean_object* v_r_1250_; 
v_res_1249_ = lean_recursor_k(v_v_1248_);
v_r_1250_ = lean_box(v_res_1249_);
return v_r_1250_;
}
}
LEAN_EXPORT uint8_t lean_recursor_is_unsafe(lean_object* v_v_1251_){
_start:
{
uint8_t v_isUnsafe_1252_; 
v_isUnsafe_1252_ = lean_ctor_get_uint8(v_v_1251_, sizeof(void*)*7 + 1);
lean_dec_ref(v_v_1251_);
return v_isUnsafe_1252_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_isUnsafeEx___boxed(lean_object* v_v_1253_){
_start:
{
uint8_t v_res_1254_; lean_object* v_r_1255_; 
v_res_1254_ = lean_recursor_is_unsafe(v_v_1253_);
v_r_1255_ = lean_box(v_res_1254_);
return v_r_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object* v_v_1256_){
_start:
{
lean_object* v_numParams_1257_; lean_object* v_numIndices_1258_; lean_object* v_numMotives_1259_; lean_object* v_numMinors_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
v_numParams_1257_ = lean_ctor_get(v_v_1256_, 2);
v_numIndices_1258_ = lean_ctor_get(v_v_1256_, 3);
v_numMotives_1259_ = lean_ctor_get(v_v_1256_, 4);
v_numMinors_1260_ = lean_ctor_get(v_v_1256_, 5);
v___x_1261_ = lean_nat_add(v_numParams_1257_, v_numMotives_1259_);
v___x_1262_ = lean_nat_add(v___x_1261_, v_numMinors_1260_);
lean_dec(v___x_1261_);
v___x_1263_ = lean_nat_add(v___x_1262_, v_numIndices_1258_);
lean_dec(v___x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx___boxed(lean_object* v_v_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_RecursorVal_getMajorIdx(v_v_1264_);
lean_dec_ref(v_v_1264_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx(lean_object* v_v_1266_){
_start:
{
lean_object* v_numParams_1267_; lean_object* v_numMotives_1268_; lean_object* v_numMinors_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v_numParams_1267_ = lean_ctor_get(v_v_1266_, 2);
v_numMotives_1268_ = lean_ctor_get(v_v_1266_, 4);
v_numMinors_1269_ = lean_ctor_get(v_v_1266_, 5);
v___x_1270_ = lean_nat_add(v_numParams_1267_, v_numMotives_1268_);
v___x_1271_ = lean_nat_add(v___x_1270_, v_numMinors_1269_);
lean_dec(v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx___boxed(lean_object* v_v_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Lean_RecursorVal_getFirstIndexIdx(v_v_1272_);
lean_dec_ref(v_v_1272_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx(lean_object* v_v_1274_){
_start:
{
lean_object* v_numParams_1275_; lean_object* v_numMotives_1276_; lean_object* v___x_1277_; 
v_numParams_1275_ = lean_ctor_get(v_v_1274_, 2);
v_numMotives_1276_ = lean_ctor_get(v_v_1274_, 4);
v___x_1277_ = lean_nat_add(v_numParams_1275_, v_numMotives_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx___boxed(lean_object* v_v_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_RecursorVal_getFirstMinorIdx(v_v_1278_);
lean_dec_ref(v_v_1278_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(lean_object* v_x_1280_, lean_object* v_x_1281_){
_start:
{
lean_object* v_zero_1282_; uint8_t v_isZero_1283_; 
v_zero_1282_ = lean_unsigned_to_nat(0u);
v_isZero_1283_ = lean_nat_dec_eq(v_x_1280_, v_zero_1282_);
if (v_isZero_1283_ == 1)
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
lean_dec(v_x_1280_);
v___x_1284_ = l_Lean_Expr_bindingDomain_x21(v_x_1281_);
lean_dec_ref(v_x_1281_);
v___x_1285_ = l_Lean_Expr_getAppFn(v___x_1284_);
lean_dec_ref(v___x_1284_);
v___x_1286_ = l_Lean_Expr_constName_x21(v___x_1285_);
lean_dec_ref(v___x_1285_);
return v___x_1286_;
}
else
{
lean_object* v_one_1287_; lean_object* v_n_1288_; lean_object* v___x_1289_; 
v_one_1287_ = lean_unsigned_to_nat(1u);
v_n_1288_ = lean_nat_sub(v_x_1280_, v_one_1287_);
lean_dec(v_x_1280_);
v___x_1289_ = l_Lean_Expr_bindingBody_x21(v_x_1281_);
lean_dec_ref(v_x_1281_);
v_x_1280_ = v_n_1288_;
v_x_1281_ = v___x_1289_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorInduct(lean_object* v_v_1291_){
_start:
{
lean_object* v_toConstantVal_1292_; lean_object* v_type_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; 
v_toConstantVal_1292_ = lean_ctor_get(v_v_1291_, 0);
v_type_1293_ = lean_ctor_get(v_toConstantVal_1292_, 2);
lean_inc_ref(v_type_1293_);
v___x_1294_ = l_Lean_RecursorVal_getMajorIdx(v_v_1291_);
lean_dec_ref(v_v_1291_);
v___x_1295_ = l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(v___x_1294_, v_type_1293_);
return v___x_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx(uint8_t v_x_1296_){
_start:
{
switch(v_x_1296_)
{
case 0:
{
lean_object* v___x_1297_; 
v___x_1297_ = lean_unsigned_to_nat(0u);
return v___x_1297_;
}
case 1:
{
lean_object* v___x_1298_; 
v___x_1298_ = lean_unsigned_to_nat(1u);
return v___x_1298_;
}
case 2:
{
lean_object* v___x_1299_; 
v___x_1299_ = lean_unsigned_to_nat(2u);
return v___x_1299_;
}
default: 
{
lean_object* v___x_1300_; 
v___x_1300_ = lean_unsigned_to_nat(3u);
return v___x_1300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___boxed(lean_object* v_x_1301_){
_start:
{
uint8_t v_x_boxed_1302_; lean_object* v_res_1303_; 
v_x_boxed_1302_ = lean_unbox(v_x_1301_);
v_res_1303_ = l_Lean_QuotKind_ctorIdx(v_x_boxed_1302_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg(lean_object* v_k_1304_){
_start:
{
lean_inc(v_k_1304_);
return v_k_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg___boxed(lean_object* v_k_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_QuotKind_ctorElim___redArg(v_k_1305_);
lean_dec(v_k_1305_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim(lean_object* v_motive_1307_, lean_object* v_ctorIdx_1308_, uint8_t v_t_1309_, lean_object* v_h_1310_, lean_object* v_k_1311_){
_start:
{
lean_inc(v_k_1311_);
return v_k_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___boxed(lean_object* v_motive_1312_, lean_object* v_ctorIdx_1313_, lean_object* v_t_1314_, lean_object* v_h_1315_, lean_object* v_k_1316_){
_start:
{
uint8_t v_t_boxed_1317_; lean_object* v_res_1318_; 
v_t_boxed_1317_ = lean_unbox(v_t_1314_);
v_res_1318_ = l_Lean_QuotKind_ctorElim(v_motive_1312_, v_ctorIdx_1313_, v_t_boxed_1317_, v_h_1315_, v_k_1316_);
lean_dec(v_k_1316_);
lean_dec(v_ctorIdx_1313_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg(lean_object* v_type_1319_){
_start:
{
lean_inc(v_type_1319_);
return v_type_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg___boxed(lean_object* v_type_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_QuotKind_type_elim___redArg(v_type_1320_);
lean_dec(v_type_1320_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim(lean_object* v_motive_1322_, uint8_t v_t_1323_, lean_object* v_h_1324_, lean_object* v_type_1325_){
_start:
{
lean_inc(v_type_1325_);
return v_type_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___boxed(lean_object* v_motive_1326_, lean_object* v_t_1327_, lean_object* v_h_1328_, lean_object* v_type_1329_){
_start:
{
uint8_t v_t_boxed_1330_; lean_object* v_res_1331_; 
v_t_boxed_1330_ = lean_unbox(v_t_1327_);
v_res_1331_ = l_Lean_QuotKind_type_elim(v_motive_1326_, v_t_boxed_1330_, v_h_1328_, v_type_1329_);
lean_dec(v_type_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg(lean_object* v_ctor_1332_){
_start:
{
lean_inc(v_ctor_1332_);
return v_ctor_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg___boxed(lean_object* v_ctor_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_QuotKind_ctor_elim___redArg(v_ctor_1333_);
lean_dec(v_ctor_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim(lean_object* v_motive_1335_, uint8_t v_t_1336_, lean_object* v_h_1337_, lean_object* v_ctor_1338_){
_start:
{
lean_inc(v_ctor_1338_);
return v_ctor_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___boxed(lean_object* v_motive_1339_, lean_object* v_t_1340_, lean_object* v_h_1341_, lean_object* v_ctor_1342_){
_start:
{
uint8_t v_t_boxed_1343_; lean_object* v_res_1344_; 
v_t_boxed_1343_ = lean_unbox(v_t_1340_);
v_res_1344_ = l_Lean_QuotKind_ctor_elim(v_motive_1339_, v_t_boxed_1343_, v_h_1341_, v_ctor_1342_);
lean_dec(v_ctor_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg(lean_object* v_lift_1345_){
_start:
{
lean_inc(v_lift_1345_);
return v_lift_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg___boxed(lean_object* v_lift_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_QuotKind_lift_elim___redArg(v_lift_1346_);
lean_dec(v_lift_1346_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim(lean_object* v_motive_1348_, uint8_t v_t_1349_, lean_object* v_h_1350_, lean_object* v_lift_1351_){
_start:
{
lean_inc(v_lift_1351_);
return v_lift_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___boxed(lean_object* v_motive_1352_, lean_object* v_t_1353_, lean_object* v_h_1354_, lean_object* v_lift_1355_){
_start:
{
uint8_t v_t_boxed_1356_; lean_object* v_res_1357_; 
v_t_boxed_1356_ = lean_unbox(v_t_1353_);
v_res_1357_ = l_Lean_QuotKind_lift_elim(v_motive_1352_, v_t_boxed_1356_, v_h_1354_, v_lift_1355_);
lean_dec(v_lift_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg(lean_object* v_ind_1358_){
_start:
{
lean_inc(v_ind_1358_);
return v_ind_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg___boxed(lean_object* v_ind_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_QuotKind_ind_elim___redArg(v_ind_1359_);
lean_dec(v_ind_1359_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim(lean_object* v_motive_1361_, uint8_t v_t_1362_, lean_object* v_h_1363_, lean_object* v_ind_1364_){
_start:
{
lean_inc(v_ind_1364_);
return v_ind_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___boxed(lean_object* v_motive_1365_, lean_object* v_t_1366_, lean_object* v_h_1367_, lean_object* v_ind_1368_){
_start:
{
uint8_t v_t_boxed_1369_; lean_object* v_res_1370_; 
v_t_boxed_1369_ = lean_unbox(v_t_1366_);
v_res_1370_ = l_Lean_QuotKind_ind_elim(v_motive_1365_, v_t_boxed_1369_, v_h_1367_, v_ind_1368_);
lean_dec(v_ind_1368_);
return v_res_1370_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind_default(void){
_start:
{
uint8_t v___x_1371_; 
v___x_1371_ = 0;
return v___x_1371_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind(void){
_start:
{
uint8_t v___x_1372_; 
v___x_1372_ = 0;
return v___x_1372_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqQuotKind_beq(uint8_t v_x_1373_, uint8_t v_y_1374_){
_start:
{
lean_object* v___x_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1375_ = l_Lean_QuotKind_ctorIdx(v_x_1373_);
v___x_1376_ = l_Lean_QuotKind_ctorIdx(v_y_1374_);
v___x_1377_ = lean_nat_dec_eq(v___x_1375_, v___x_1376_);
lean_dec(v___x_1376_);
lean_dec(v___x_1375_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqQuotKind_beq___boxed(lean_object* v_x_1378_, lean_object* v_y_1379_){
_start:
{
uint8_t v_x_21__boxed_1380_; uint8_t v_y_22__boxed_1381_; uint8_t v_res_1382_; lean_object* v_r_1383_; 
v_x_21__boxed_1380_ = lean_unbox(v_x_1378_);
v_y_22__boxed_1381_ = lean_unbox(v_y_1379_);
v_res_1382_ = l_Lean_instBEqQuotKind_beq(v_x_21__boxed_1380_, v_y_22__boxed_1381_);
v_r_1383_ = lean_box(v_res_1382_);
return v_r_1383_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default___closed__0(void){
_start:
{
uint8_t v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = 0;
v___x_1387_ = l_Lean_instInhabitedConstantVal_default;
v___x_1388_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1388_, 0, v___x_1387_);
lean_ctor_set_uint8(v___x_1388_, sizeof(void*)*1, v___x_1386_);
return v___x_1388_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default(void){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = lean_obj_once(&l_Lean_instInhabitedQuotVal_default___closed__0, &l_Lean_instInhabitedQuotVal_default___closed__0_once, _init_l_Lean_instInhabitedQuotVal_default___closed__0);
return v___x_1389_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal(void){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Lean_instInhabitedQuotVal_default;
return v___x_1390_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqQuotVal_beq(lean_object* v_x_1391_, lean_object* v_x_1392_){
_start:
{
lean_object* v_toConstantVal_1393_; uint8_t v_kind_1394_; lean_object* v_toConstantVal_1395_; uint8_t v_kind_1396_; uint8_t v___x_1397_; 
v_toConstantVal_1393_ = lean_ctor_get(v_x_1391_, 0);
v_kind_1394_ = lean_ctor_get_uint8(v_x_1391_, sizeof(void*)*1);
v_toConstantVal_1395_ = lean_ctor_get(v_x_1392_, 0);
v_kind_1396_ = lean_ctor_get_uint8(v_x_1392_, sizeof(void*)*1);
v___x_1397_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1393_, v_toConstantVal_1395_);
if (v___x_1397_ == 0)
{
return v___x_1397_;
}
else
{
uint8_t v___x_1398_; 
v___x_1398_ = l_Lean_instBEqQuotKind_beq(v_kind_1394_, v_kind_1396_);
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqQuotVal_beq___boxed(lean_object* v_x_1399_, lean_object* v_x_1400_){
_start:
{
uint8_t v_res_1401_; lean_object* v_r_1402_; 
v_res_1401_ = l_Lean_instBEqQuotVal_beq(v_x_1399_, v_x_1400_);
lean_dec_ref(v_x_1400_);
lean_dec_ref(v_x_1399_);
v_r_1402_ = lean_box(v_res_1401_);
return v_r_1402_;
}
}
LEAN_EXPORT lean_object* lean_mk_quot_val(lean_object* v_name_1405_, lean_object* v_levelParams_1406_, lean_object* v_type_1407_, uint8_t v_kind_1408_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1409_, 0, v_name_1405_);
lean_ctor_set(v___x_1409_, 1, v_levelParams_1406_);
lean_ctor_set(v___x_1409_, 2, v_type_1407_);
v___x_1410_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set_uint8(v___x_1410_, sizeof(void*)*1, v_kind_1408_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkQuotValEx___boxed(lean_object* v_name_1411_, lean_object* v_levelParams_1412_, lean_object* v_type_1413_, lean_object* v_kind_1414_){
_start:
{
uint8_t v_kind_boxed_1415_; lean_object* v_res_1416_; 
v_kind_boxed_1415_ = lean_unbox(v_kind_1414_);
v_res_1416_ = lean_mk_quot_val(v_name_1411_, v_levelParams_1412_, v_type_1413_, v_kind_boxed_1415_);
return v_res_1416_;
}
}
LEAN_EXPORT uint8_t lean_quot_val_kind(lean_object* v_v_1417_){
_start:
{
uint8_t v_kind_1418_; 
v_kind_1418_ = lean_ctor_get_uint8(v_v_1417_, sizeof(void*)*1);
lean_dec_ref(v_v_1417_);
return v_kind_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotVal_kindEx___boxed(lean_object* v_v_1419_){
_start:
{
uint8_t v_res_1420_; lean_object* v_r_1421_; 
v_res_1420_ = lean_quot_val_kind(v_v_1419_);
v_r_1421_ = lean_box(v_res_1420_);
return v_r_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx(lean_object* v_x_1422_){
_start:
{
switch(lean_obj_tag(v_x_1422_))
{
case 0:
{
lean_object* v___x_1423_; 
v___x_1423_ = lean_unsigned_to_nat(0u);
return v___x_1423_;
}
case 1:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_unsigned_to_nat(1u);
return v___x_1424_;
}
case 2:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_unsigned_to_nat(2u);
return v___x_1425_;
}
case 3:
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_unsigned_to_nat(3u);
return v___x_1426_;
}
case 4:
{
lean_object* v___x_1427_; 
v___x_1427_ = lean_unsigned_to_nat(4u);
return v___x_1427_;
}
case 5:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_unsigned_to_nat(5u);
return v___x_1428_;
}
case 6:
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_unsigned_to_nat(6u);
return v___x_1429_;
}
default: 
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_unsigned_to_nat(7u);
return v___x_1430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___boxed(lean_object* v_x_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_ConstantInfo_ctorIdx(v_x_1431_);
lean_dec_ref(v_x_1431_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___redArg(lean_object* v_t_1433_, lean_object* v_k_1434_){
_start:
{
lean_object* v_val_1435_; lean_object* v___x_1436_; 
v_val_1435_ = lean_ctor_get(v_t_1433_, 0);
lean_inc_ref(v_val_1435_);
lean_dec_ref(v_t_1433_);
v___x_1436_ = lean_apply_1(v_k_1434_, v_val_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim(lean_object* v_motive_1437_, lean_object* v_ctorIdx_1438_, lean_object* v_t_1439_, lean_object* v_h_1440_, lean_object* v_k_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1439_, v_k_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___boxed(lean_object* v_motive_1443_, lean_object* v_ctorIdx_1444_, lean_object* v_t_1445_, lean_object* v_h_1446_, lean_object* v_k_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_Lean_ConstantInfo_ctorElim(v_motive_1443_, v_ctorIdx_1444_, v_t_1445_, v_h_1446_, v_k_1447_);
lean_dec(v_ctorIdx_1444_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim___redArg(lean_object* v_t_1449_, lean_object* v_axiomInfo_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1449_, v_axiomInfo_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim(lean_object* v_motive_1452_, lean_object* v_t_1453_, lean_object* v_h_1454_, lean_object* v_axiomInfo_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1453_, v_axiomInfo_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim___redArg(lean_object* v_t_1457_, lean_object* v_defnInfo_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1457_, v_defnInfo_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim(lean_object* v_motive_1460_, lean_object* v_t_1461_, lean_object* v_h_1462_, lean_object* v_defnInfo_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1461_, v_defnInfo_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim___redArg(lean_object* v_t_1465_, lean_object* v_thmInfo_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1465_, v_thmInfo_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim(lean_object* v_motive_1468_, lean_object* v_t_1469_, lean_object* v_h_1470_, lean_object* v_thmInfo_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1469_, v_thmInfo_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim___redArg(lean_object* v_t_1473_, lean_object* v_opaqueInfo_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1473_, v_opaqueInfo_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim(lean_object* v_motive_1476_, lean_object* v_t_1477_, lean_object* v_h_1478_, lean_object* v_opaqueInfo_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1477_, v_opaqueInfo_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim___redArg(lean_object* v_t_1481_, lean_object* v_quotInfo_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1481_, v_quotInfo_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim(lean_object* v_motive_1484_, lean_object* v_t_1485_, lean_object* v_h_1486_, lean_object* v_quotInfo_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1485_, v_quotInfo_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim___redArg(lean_object* v_t_1489_, lean_object* v_inductInfo_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1489_, v_inductInfo_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim(lean_object* v_motive_1492_, lean_object* v_t_1493_, lean_object* v_h_1494_, lean_object* v_inductInfo_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1493_, v_inductInfo_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim___redArg(lean_object* v_t_1497_, lean_object* v_ctorInfo_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1497_, v_ctorInfo_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim(lean_object* v_motive_1500_, lean_object* v_t_1501_, lean_object* v_h_1502_, lean_object* v_ctorInfo_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1501_, v_ctorInfo_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim___redArg(lean_object* v_t_1505_, lean_object* v_recInfo_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1505_, v_recInfo_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim(lean_object* v_motive_1508_, lean_object* v_t_1509_, lean_object* v_h_1510_, lean_object* v_recInfo_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1509_, v_recInfo_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default___closed__0(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = l_Lean_instInhabitedAxiomVal_default;
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default(void){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_obj_once(&l_Lean_instInhabitedConstantInfo_default___closed__0, &l_Lean_instInhabitedConstantInfo_default___closed__0_once, _init_l_Lean_instInhabitedConstantInfo_default___closed__0);
return v___x_1515_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo(void){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_instInhabitedConstantInfo_default;
return v___x_1516_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstantInfo_beq(lean_object* v_x_1517_, lean_object* v_x_1518_){
_start:
{
switch(lean_obj_tag(v_x_1517_))
{
case 0:
{
if (lean_obj_tag(v_x_1518_) == 0)
{
lean_object* v_val_1519_; lean_object* v_val_1520_; uint8_t v___x_1521_; 
v_val_1519_ = lean_ctor_get(v_x_1517_, 0);
v_val_1520_ = lean_ctor_get(v_x_1518_, 0);
v___x_1521_ = l_Lean_instBEqAxiomVal_beq(v_val_1519_, v_val_1520_);
return v___x_1521_;
}
else
{
uint8_t v___x_1522_; 
v___x_1522_ = 0;
return v___x_1522_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1518_) == 1)
{
lean_object* v_val_1523_; lean_object* v_val_1524_; uint8_t v___x_1525_; 
v_val_1523_ = lean_ctor_get(v_x_1517_, 0);
v_val_1524_ = lean_ctor_get(v_x_1518_, 0);
v___x_1525_ = l_Lean_instBEqDefinitionVal_beq(v_val_1523_, v_val_1524_);
return v___x_1525_;
}
else
{
uint8_t v___x_1526_; 
v___x_1526_ = 0;
return v___x_1526_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1518_) == 2)
{
lean_object* v_val_1527_; lean_object* v_val_1528_; uint8_t v___x_1529_; 
v_val_1527_ = lean_ctor_get(v_x_1517_, 0);
v_val_1528_ = lean_ctor_get(v_x_1518_, 0);
v___x_1529_ = l_Lean_instBEqTheoremVal_beq(v_val_1527_, v_val_1528_);
return v___x_1529_;
}
else
{
uint8_t v___x_1530_; 
v___x_1530_ = 0;
return v___x_1530_;
}
}
case 3:
{
if (lean_obj_tag(v_x_1518_) == 3)
{
lean_object* v_val_1531_; lean_object* v_val_1532_; uint8_t v___x_1533_; 
v_val_1531_ = lean_ctor_get(v_x_1517_, 0);
v_val_1532_ = lean_ctor_get(v_x_1518_, 0);
v___x_1533_ = l_Lean_instBEqOpaqueVal_beq(v_val_1531_, v_val_1532_);
return v___x_1533_;
}
else
{
uint8_t v___x_1534_; 
v___x_1534_ = 0;
return v___x_1534_;
}
}
case 4:
{
if (lean_obj_tag(v_x_1518_) == 4)
{
lean_object* v_val_1535_; lean_object* v_val_1536_; uint8_t v___x_1537_; 
v_val_1535_ = lean_ctor_get(v_x_1517_, 0);
v_val_1536_ = lean_ctor_get(v_x_1518_, 0);
v___x_1537_ = l_Lean_instBEqQuotVal_beq(v_val_1535_, v_val_1536_);
return v___x_1537_;
}
else
{
uint8_t v___x_1538_; 
v___x_1538_ = 0;
return v___x_1538_;
}
}
case 5:
{
if (lean_obj_tag(v_x_1518_) == 5)
{
lean_object* v_val_1539_; lean_object* v_val_1540_; uint8_t v___x_1541_; 
v_val_1539_ = lean_ctor_get(v_x_1517_, 0);
v_val_1540_ = lean_ctor_get(v_x_1518_, 0);
v___x_1541_ = l_Lean_instBEqInductiveVal_beq(v_val_1539_, v_val_1540_);
return v___x_1541_;
}
else
{
uint8_t v___x_1542_; 
v___x_1542_ = 0;
return v___x_1542_;
}
}
case 6:
{
if (lean_obj_tag(v_x_1518_) == 6)
{
lean_object* v_val_1543_; lean_object* v_val_1544_; uint8_t v___x_1545_; 
v_val_1543_ = lean_ctor_get(v_x_1517_, 0);
v_val_1544_ = lean_ctor_get(v_x_1518_, 0);
v___x_1545_ = l_Lean_instBEqConstructorVal_beq(v_val_1543_, v_val_1544_);
return v___x_1545_;
}
else
{
uint8_t v___x_1546_; 
v___x_1546_ = 0;
return v___x_1546_;
}
}
default: 
{
if (lean_obj_tag(v_x_1518_) == 7)
{
lean_object* v_val_1547_; lean_object* v_val_1548_; uint8_t v___x_1549_; 
v_val_1547_ = lean_ctor_get(v_x_1517_, 0);
v_val_1548_ = lean_ctor_get(v_x_1518_, 0);
v___x_1549_ = l_Lean_instBEqRecursorVal_beq(v_val_1547_, v_val_1548_);
return v___x_1549_;
}
else
{
uint8_t v___x_1550_; 
v___x_1550_ = 0;
return v___x_1550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstantInfo_beq___boxed(lean_object* v_x_1551_, lean_object* v_x_1552_){
_start:
{
uint8_t v_res_1553_; lean_object* v_r_1554_; 
v_res_1553_ = l_Lean_instBEqConstantInfo_beq(v_x_1551_, v_x_1552_);
lean_dec_ref(v_x_1552_);
lean_dec_ref(v_x_1551_);
v_r_1554_ = lean_box(v_res_1553_);
return v_r_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object* v_x_1557_){
_start:
{
lean_object* v_val_1558_; lean_object* v_toConstantVal_1559_; 
v_val_1558_ = lean_ctor_get(v_x_1557_, 0);
v_toConstantVal_1559_ = lean_ctor_get(v_val_1558_, 0);
lean_inc_ref(v_toConstantVal_1559_);
return v_toConstantVal_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object* v_x_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_ConstantInfo_toConstantVal(v_x_1560_);
lean_dec_ref(v_x_1560_);
return v_res_1561_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object* v_x_1562_){
_start:
{
switch(lean_obj_tag(v_x_1562_))
{
case 0:
{
lean_object* v_val_1563_; uint8_t v_isUnsafe_1564_; 
v_val_1563_ = lean_ctor_get(v_x_1562_, 0);
v_isUnsafe_1564_ = lean_ctor_get_uint8(v_val_1563_, sizeof(void*)*1);
return v_isUnsafe_1564_;
}
case 1:
{
lean_object* v_val_1565_; uint8_t v_safety_1566_; uint8_t v___x_1567_; uint8_t v___x_1568_; 
v_val_1565_ = lean_ctor_get(v_x_1562_, 0);
v_safety_1566_ = lean_ctor_get_uint8(v_val_1565_, sizeof(void*)*4);
v___x_1567_ = 0;
v___x_1568_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1566_, v___x_1567_);
return v___x_1568_;
}
case 3:
{
lean_object* v_val_1569_; uint8_t v_isUnsafe_1570_; 
v_val_1569_ = lean_ctor_get(v_x_1562_, 0);
v_isUnsafe_1570_ = lean_ctor_get_uint8(v_val_1569_, sizeof(void*)*3);
return v_isUnsafe_1570_;
}
case 5:
{
lean_object* v_val_1571_; uint8_t v_isUnsafe_1572_; 
v_val_1571_ = lean_ctor_get(v_x_1562_, 0);
v_isUnsafe_1572_ = lean_ctor_get_uint8(v_val_1571_, sizeof(void*)*6 + 1);
return v_isUnsafe_1572_;
}
case 6:
{
lean_object* v_val_1573_; uint8_t v_isUnsafe_1574_; 
v_val_1573_ = lean_ctor_get(v_x_1562_, 0);
v_isUnsafe_1574_ = lean_ctor_get_uint8(v_val_1573_, sizeof(void*)*5);
return v_isUnsafe_1574_;
}
case 7:
{
lean_object* v_val_1575_; uint8_t v_isUnsafe_1576_; 
v_val_1575_ = lean_ctor_get(v_x_1562_, 0);
v_isUnsafe_1576_ = lean_ctor_get_uint8(v_val_1575_, sizeof(void*)*7 + 1);
return v_isUnsafe_1576_;
}
default: 
{
uint8_t v___x_1577_; 
v___x_1577_ = 0;
return v___x_1577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isUnsafe___boxed(lean_object* v_x_1578_){
_start:
{
uint8_t v_res_1579_; lean_object* v_r_1580_; 
v_res_1579_ = l_Lean_ConstantInfo_isUnsafe(v_x_1578_);
lean_dec_ref(v_x_1578_);
v_r_1580_ = lean_box(v_res_1579_);
return v_r_1580_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isPartial(lean_object* v_x_1581_){
_start:
{
if (lean_obj_tag(v_x_1581_) == 1)
{
lean_object* v_val_1582_; uint8_t v_safety_1583_; uint8_t v___x_1584_; uint8_t v___x_1585_; 
v_val_1582_ = lean_ctor_get(v_x_1581_, 0);
v_safety_1583_ = lean_ctor_get_uint8(v_val_1582_, sizeof(void*)*4);
v___x_1584_ = 2;
v___x_1585_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1583_, v___x_1584_);
return v___x_1585_;
}
else
{
uint8_t v___x_1586_; 
v___x_1586_ = 0;
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isPartial___boxed(lean_object* v_x_1587_){
_start:
{
uint8_t v_res_1588_; lean_object* v_r_1589_; 
v_res_1588_ = l_Lean_ConstantInfo_isPartial(v_x_1587_);
lean_dec_ref(v_x_1587_);
v_r_1589_ = lean_box(v_res_1588_);
return v_r_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name(lean_object* v_d_1590_){
_start:
{
lean_object* v___x_1591_; lean_object* v_name_1592_; 
v___x_1591_ = l_Lean_ConstantInfo_toConstantVal(v_d_1590_);
v_name_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_name_1592_);
lean_dec_ref(v___x_1591_);
return v_name_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name___boxed(lean_object* v_d_1593_){
_start:
{
lean_object* v_res_1594_; 
v_res_1594_ = l_Lean_ConstantInfo_name(v_d_1593_);
lean_dec_ref(v_d_1593_);
return v_res_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams(lean_object* v_d_1595_){
_start:
{
lean_object* v___x_1596_; lean_object* v_levelParams_1597_; 
v___x_1596_ = l_Lean_ConstantInfo_toConstantVal(v_d_1595_);
v_levelParams_1597_ = lean_ctor_get(v___x_1596_, 1);
lean_inc(v_levelParams_1597_);
lean_dec_ref(v___x_1596_);
return v_levelParams_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams___boxed(lean_object* v_d_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_ConstantInfo_levelParams(v_d_1598_);
lean_dec_ref(v_d_1598_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object* v_d_1600_){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = l_Lean_ConstantInfo_levelParams(v_d_1600_);
v___x_1602_ = l_List_lengthTR___redArg(v___x_1601_);
lean_dec(v___x_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams___boxed(lean_object* v_d_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_ConstantInfo_numLevelParams(v_d_1603_);
lean_dec_ref(v_d_1603_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type(lean_object* v_d_1605_){
_start:
{
lean_object* v___x_1606_; lean_object* v_type_1607_; 
v___x_1606_ = l_Lean_ConstantInfo_toConstantVal(v_d_1605_);
v_type_1607_ = lean_ctor_get(v___x_1606_, 2);
lean_inc_ref(v_type_1607_);
lean_dec_ref(v___x_1606_);
return v_type_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type___boxed(lean_object* v_d_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_ConstantInfo_type(v_d_1608_);
lean_dec_ref(v_d_1608_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f(lean_object* v_info_1610_, uint8_t v_allowOpaque_1611_){
_start:
{
switch(lean_obj_tag(v_info_1610_))
{
case 1:
{
lean_object* v_val_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1620_; 
v_val_1612_ = lean_ctor_get(v_info_1610_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_info_1610_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1614_ = v_info_1610_;
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_val_1612_);
lean_dec(v_info_1610_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v_value_1616_; lean_object* v___x_1618_; 
v_value_1616_ = lean_ctor_get(v_val_1612_, 1);
lean_inc_ref(v_value_1616_);
lean_dec_ref(v_val_1612_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v_value_1616_);
v___x_1618_ = v___x_1614_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_value_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
case 2:
{
lean_object* v_val_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1630_; 
v_val_1621_ = lean_ctor_get(v_info_1610_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_info_1610_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1623_ = v_info_1610_;
v_isShared_1624_ = v_isSharedCheck_1630_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_val_1621_);
lean_dec(v_info_1610_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1630_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
if (v_allowOpaque_1611_ == 0)
{
lean_object* v___x_1625_; 
lean_del_object(v___x_1623_);
lean_dec_ref(v_val_1621_);
v___x_1625_ = lean_box(0);
return v___x_1625_;
}
else
{
lean_object* v_value_1626_; lean_object* v___x_1628_; 
v_value_1626_ = lean_ctor_get(v_val_1621_, 1);
lean_inc_ref(v_value_1626_);
lean_dec_ref(v_val_1621_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set_tag(v___x_1623_, 1);
lean_ctor_set(v___x_1623_, 0, v_value_1626_);
v___x_1628_ = v___x_1623_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_value_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
case 3:
{
lean_object* v_val_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1640_; 
v_val_1631_ = lean_ctor_get(v_info_1610_, 0);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_info_1610_);
if (v_isSharedCheck_1640_ == 0)
{
v___x_1633_ = v_info_1610_;
v_isShared_1634_ = v_isSharedCheck_1640_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_val_1631_);
lean_dec(v_info_1610_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1640_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
if (v_allowOpaque_1611_ == 0)
{
lean_object* v___x_1635_; 
lean_del_object(v___x_1633_);
lean_dec_ref(v_val_1631_);
v___x_1635_ = lean_box(0);
return v___x_1635_;
}
else
{
lean_object* v_value_1636_; lean_object* v___x_1638_; 
v_value_1636_ = lean_ctor_get(v_val_1631_, 1);
lean_inc_ref(v_value_1636_);
lean_dec_ref(v_val_1631_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set_tag(v___x_1633_, 1);
lean_ctor_set(v___x_1633_, 0, v_value_1636_);
v___x_1638_ = v___x_1633_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_value_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
default: 
{
lean_object* v___x_1641_; 
lean_dec_ref(v_info_1610_);
v___x_1641_ = lean_box(0);
return v___x_1641_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f___boxed(lean_object* v_info_1642_, lean_object* v_allowOpaque_1643_){
_start:
{
uint8_t v_allowOpaque_boxed_1644_; lean_object* v_res_1645_; 
v_allowOpaque_boxed_1644_ = lean_unbox(v_allowOpaque_1643_);
v_res_1645_ = l_Lean_ConstantInfo_value_x3f(v_info_1642_, v_allowOpaque_boxed_1644_);
return v_res_1645_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_hasValue(lean_object* v_info_1646_, uint8_t v_allowOpaque_1647_){
_start:
{
switch(lean_obj_tag(v_info_1646_))
{
case 1:
{
uint8_t v___x_1648_; 
v___x_1648_ = 1;
return v___x_1648_;
}
case 2:
{
return v_allowOpaque_1647_;
}
case 3:
{
return v_allowOpaque_1647_;
}
default: 
{
uint8_t v___x_1649_; 
v___x_1649_ = 0;
return v___x_1649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object* v_info_1650_, lean_object* v_allowOpaque_1651_){
_start:
{
uint8_t v_allowOpaque_boxed_1652_; uint8_t v_res_1653_; lean_object* v_r_1654_; 
v_allowOpaque_boxed_1652_ = lean_unbox(v_allowOpaque_1651_);
v_res_1653_ = l_Lean_ConstantInfo_hasValue(v_info_1650_, v_allowOpaque_boxed_1652_);
lean_dec_ref(v_info_1650_);
v_r_1654_ = lean_box(v_res_1653_);
return v_r_1654_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(lean_object* v_msg_1655_){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1656_ = l_Lean_instInhabitedExpr;
v___x_1657_ = lean_panic_fn_borrowed(v___x_1656_, v_msg_1655_);
return v___x_1657_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__2(void){
_start:
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1660_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1661_ = lean_unsigned_to_nat(62u);
v___x_1662_ = lean_unsigned_to_nat(509u);
v___x_1663_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1664_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1665_ = l_mkPanicMessageWithDecl(v___x_1664_, v___x_1663_, v___x_1662_, v___x_1661_, v___x_1660_);
return v___x_1665_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__3(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1666_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1667_ = lean_unsigned_to_nat(62u);
v___x_1668_ = lean_unsigned_to_nat(510u);
v___x_1669_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1670_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1671_ = l_mkPanicMessageWithDecl(v___x_1670_, v___x_1669_, v___x_1668_, v___x_1667_, v___x_1666_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21(lean_object* v_info_1674_, uint8_t v_allowOpaque_1675_){
_start:
{
switch(lean_obj_tag(v_info_1674_))
{
case 1:
{
lean_object* v_val_1676_; lean_object* v_value_1677_; 
v_val_1676_ = lean_ctor_get(v_info_1674_, 0);
v_value_1677_ = lean_ctor_get(v_val_1676_, 1);
lean_inc_ref(v_value_1677_);
return v_value_1677_;
}
case 2:
{
if (v_allowOpaque_1675_ == 0)
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__2, &l_Lean_ConstantInfo_value_x21___closed__2_once, _init_l_Lean_ConstantInfo_value_x21___closed__2);
v___x_1679_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1678_);
return v___x_1679_;
}
else
{
lean_object* v_val_1680_; lean_object* v_value_1681_; 
v_val_1680_ = lean_ctor_get(v_info_1674_, 0);
v_value_1681_ = lean_ctor_get(v_val_1680_, 1);
lean_inc_ref(v_value_1681_);
return v_value_1681_;
}
}
case 3:
{
if (v_allowOpaque_1675_ == 0)
{
lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1682_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__3, &l_Lean_ConstantInfo_value_x21___closed__3_once, _init_l_Lean_ConstantInfo_value_x21___closed__3);
v___x_1683_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1682_);
return v___x_1683_;
}
else
{
lean_object* v_val_1684_; lean_object* v_value_1685_; 
v_val_1684_ = lean_ctor_get(v_info_1674_, 0);
v_value_1685_ = lean_ctor_get(v_val_1684_, 1);
lean_inc_ref(v_value_1685_);
return v_value_1685_;
}
}
default: 
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1686_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1687_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1688_ = lean_unsigned_to_nat(511u);
v___x_1689_ = lean_unsigned_to_nat(31u);
v___x_1690_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__4));
v___x_1691_ = l_Lean_ConstantInfo_name(v_info_1674_);
v___x_1692_ = 1;
v___x_1693_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1691_, v___x_1692_);
v___x_1694_ = lean_string_append(v___x_1690_, v___x_1693_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__5));
v___x_1696_ = lean_string_append(v___x_1694_, v___x_1695_);
v___x_1697_ = l_mkPanicMessageWithDecl(v___x_1686_, v___x_1687_, v___x_1688_, v___x_1689_, v___x_1696_);
lean_dec_ref(v___x_1696_);
v___x_1698_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1697_);
return v___x_1698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21___boxed(lean_object* v_info_1699_, lean_object* v_allowOpaque_1700_){
_start:
{
uint8_t v_allowOpaque_boxed_1701_; lean_object* v_res_1702_; 
v_allowOpaque_boxed_1701_ = lean_unbox(v_allowOpaque_1700_);
v_res_1702_ = l_Lean_ConstantInfo_value_x21(v_info_1699_, v_allowOpaque_boxed_1701_);
lean_dec_ref(v_info_1699_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints(lean_object* v_x_1703_){
_start:
{
if (lean_obj_tag(v_x_1703_) == 1)
{
lean_object* v_val_1704_; lean_object* v_hints_1705_; 
v_val_1704_ = lean_ctor_get(v_x_1703_, 0);
v_hints_1705_ = lean_ctor_get(v_val_1704_, 2);
lean_inc(v_hints_1705_);
return v_hints_1705_;
}
else
{
lean_object* v___x_1706_; 
v___x_1706_ = lean_box(0);
return v___x_1706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object* v_x_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lean_ConstantInfo_hints(v_x_1707_);
lean_dec_ref(v_x_1707_);
return v_res_1708_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isCtor(lean_object* v_x_1709_){
_start:
{
if (lean_obj_tag(v_x_1709_) == 6)
{
uint8_t v___x_1710_; 
v___x_1710_ = 1;
return v___x_1710_;
}
else
{
uint8_t v___x_1711_; 
v___x_1711_ = 0;
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isCtor___boxed(lean_object* v_x_1712_){
_start:
{
uint8_t v_res_1713_; lean_object* v_r_1714_; 
v_res_1713_ = l_Lean_ConstantInfo_isCtor(v_x_1712_);
lean_dec_ref(v_x_1712_);
v_r_1714_ = lean_box(v_res_1713_);
return v_r_1714_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isAxiom(lean_object* v_x_1715_){
_start:
{
if (lean_obj_tag(v_x_1715_) == 0)
{
uint8_t v___x_1716_; 
v___x_1716_ = 1;
return v___x_1716_;
}
else
{
uint8_t v___x_1717_; 
v___x_1717_ = 0;
return v___x_1717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isAxiom___boxed(lean_object* v_x_1718_){
_start:
{
uint8_t v_res_1719_; lean_object* v_r_1720_; 
v_res_1719_ = l_Lean_ConstantInfo_isAxiom(v_x_1718_);
lean_dec_ref(v_x_1718_);
v_r_1720_ = lean_box(v_res_1719_);
return v_r_1720_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isInductive(lean_object* v_x_1721_){
_start:
{
if (lean_obj_tag(v_x_1721_) == 5)
{
uint8_t v___x_1722_; 
v___x_1722_ = 1;
return v___x_1722_;
}
else
{
uint8_t v___x_1723_; 
v___x_1723_ = 0;
return v___x_1723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isInductive___boxed(lean_object* v_x_1724_){
_start:
{
uint8_t v_res_1725_; lean_object* v_r_1726_; 
v_res_1725_ = l_Lean_ConstantInfo_isInductive(v_x_1724_);
lean_dec_ref(v_x_1724_);
v_r_1726_ = lean_box(v_res_1725_);
return v_r_1726_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isDefinition(lean_object* v_x_1727_){
_start:
{
if (lean_obj_tag(v_x_1727_) == 1)
{
uint8_t v___x_1728_; 
v___x_1728_ = 1;
return v___x_1728_;
}
else
{
uint8_t v___x_1729_; 
v___x_1729_ = 0;
return v___x_1729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isDefinition___boxed(lean_object* v_x_1730_){
_start:
{
uint8_t v_res_1731_; lean_object* v_r_1732_; 
v_res_1731_ = l_Lean_ConstantInfo_isDefinition(v_x_1730_);
lean_dec_ref(v_x_1730_);
v_r_1732_ = lean_box(v_res_1731_);
return v_r_1732_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isTheorem(lean_object* v_x_1733_){
_start:
{
if (lean_obj_tag(v_x_1733_) == 2)
{
uint8_t v___x_1734_; 
v___x_1734_ = 1;
return v___x_1734_;
}
else
{
uint8_t v___x_1735_; 
v___x_1735_ = 0;
return v___x_1735_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isTheorem___boxed(lean_object* v_x_1736_){
_start:
{
uint8_t v_res_1737_; lean_object* v_r_1738_; 
v_res_1737_ = l_Lean_ConstantInfo_isTheorem(v_x_1736_);
lean_dec_ref(v_x_1736_);
v_r_1738_ = lean_box(v_res_1737_);
return v_r_1738_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(lean_object* v_msg_1739_){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1740_ = l_Lean_instInhabitedInductiveVal_default;
v___x_1741_ = lean_panic_fn_borrowed(v___x_1740_, v_msg_1739_);
return v___x_1741_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1744_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__1));
v___x_1745_ = lean_unsigned_to_nat(9u);
v___x_1746_ = lean_unsigned_to_nat(539u);
v___x_1747_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__0));
v___x_1748_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1749_ = l_mkPanicMessageWithDecl(v___x_1748_, v___x_1747_, v___x_1746_, v___x_1745_, v___x_1744_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object* v_x_1750_){
_start:
{
if (lean_obj_tag(v_x_1750_) == 5)
{
lean_object* v_val_1751_; 
v_val_1751_ = lean_ctor_get(v_x_1750_, 0);
lean_inc_ref(v_val_1751_);
return v_val_1751_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1752_ = lean_obj_once(&l_Lean_ConstantInfo_inductiveVal_x21___closed__2, &l_Lean_ConstantInfo_inductiveVal_x21___closed__2_once, _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2);
v___x_1753_ = l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(v___x_1752_);
return v___x_1753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21___boxed(lean_object* v_x_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_ConstantInfo_inductiveVal_x21(v_x_1754_);
lean_dec_ref(v_x_1754_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all(lean_object* v_x_1756_){
_start:
{
switch(lean_obj_tag(v_x_1756_))
{
case 5:
{
lean_object* v_val_1757_; lean_object* v_all_1758_; 
v_val_1757_ = lean_ctor_get(v_x_1756_, 0);
v_all_1758_ = lean_ctor_get(v_val_1757_, 3);
lean_inc(v_all_1758_);
return v_all_1758_;
}
case 1:
{
lean_object* v_val_1759_; lean_object* v_all_1760_; 
v_val_1759_ = lean_ctor_get(v_x_1756_, 0);
v_all_1760_ = lean_ctor_get(v_val_1759_, 3);
lean_inc(v_all_1760_);
return v_all_1760_;
}
case 2:
{
lean_object* v_val_1761_; lean_object* v_all_1762_; 
v_val_1761_ = lean_ctor_get(v_x_1756_, 0);
v_all_1762_ = lean_ctor_get(v_val_1761_, 2);
lean_inc(v_all_1762_);
return v_all_1762_;
}
case 3:
{
lean_object* v_val_1763_; lean_object* v_all_1764_; 
v_val_1763_ = lean_ctor_get(v_x_1756_, 0);
v_all_1764_ = lean_ctor_get(v_val_1763_, 2);
lean_inc(v_all_1764_);
return v_all_1764_;
}
default: 
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1765_ = l_Lean_ConstantInfo_name(v_x_1756_);
v___x_1766_ = lean_box(0);
v___x_1767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1765_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
return v___x_1767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all___boxed(lean_object* v_x_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lean_ConstantInfo_all(v_x_1768_);
lean_dec_ref(v_x_1768_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecName(lean_object* v_declName_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1771_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0));
v___x_1772_ = l_Lean_Name_str___override(v_declName_1770_, v___x_1771_);
return v___x_1772_;
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
