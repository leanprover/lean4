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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_QuotKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_QuotKind_toCtorIdx___boxed(lean_object*);
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
static lean_once_cell_t l_Lean_instInhabitedQuotVal_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedQuotVal_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedQuotVal_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedQuotVal;
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
lean_dec_ref(v_h_98_);
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
v___x_196_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__3, &l_Lean_instInhabitedConstantVal_default___closed__3_once, _init_l_Lean_instInhabitedConstantVal_default___closed__3);
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
if (v_isUnsafe_203_ == 0)
{
if (v_isUnsafe_205_ == 0)
{
return v___x_206_;
}
else
{
return v_isUnsafe_203_;
}
}
else
{
return v_isUnsafe_205_;
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
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_toCtorIdx(uint8_t v_x_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_DefinitionSafety_ctorIdx(v_x_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_toCtorIdx___boxed(lean_object* v_x_239_){
_start:
{
uint8_t v_x_4__boxed_240_; lean_object* v_res_241_; 
v_x_4__boxed_240_ = lean_unbox(v_x_239_);
v_res_241_ = l_Lean_DefinitionSafety_toCtorIdx(v_x_4__boxed_240_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg(lean_object* v_k_242_){
_start:
{
lean_inc(v_k_242_);
return v_k_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg___boxed(lean_object* v_k_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_DefinitionSafety_ctorElim___redArg(v_k_243_);
lean_dec(v_k_243_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim(lean_object* v_motive_245_, lean_object* v_ctorIdx_246_, uint8_t v_t_247_, lean_object* v_h_248_, lean_object* v_k_249_){
_start:
{
lean_inc(v_k_249_);
return v_k_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___boxed(lean_object* v_motive_250_, lean_object* v_ctorIdx_251_, lean_object* v_t_252_, lean_object* v_h_253_, lean_object* v_k_254_){
_start:
{
uint8_t v_t_boxed_255_; lean_object* v_res_256_; 
v_t_boxed_255_ = lean_unbox(v_t_252_);
v_res_256_ = l_Lean_DefinitionSafety_ctorElim(v_motive_250_, v_ctorIdx_251_, v_t_boxed_255_, v_h_253_, v_k_254_);
lean_dec(v_k_254_);
lean_dec(v_ctorIdx_251_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___redArg(lean_object* v_unsafe_257_){
_start:
{
lean_inc(v_unsafe_257_);
return v_unsafe_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___redArg___boxed(lean_object* v_unsafe_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_DefinitionSafety_unsafe_elim___redArg(v_unsafe_258_);
lean_dec(v_unsafe_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim(lean_object* v_motive_260_, uint8_t v_t_261_, lean_object* v_h_262_, lean_object* v_unsafe_263_){
_start:
{
lean_inc(v_unsafe_263_);
return v_unsafe_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___boxed(lean_object* v_motive_264_, lean_object* v_t_265_, lean_object* v_h_266_, lean_object* v_unsafe_267_){
_start:
{
uint8_t v_t_boxed_268_; lean_object* v_res_269_; 
v_t_boxed_268_ = lean_unbox(v_t_265_);
v_res_269_ = l_Lean_DefinitionSafety_unsafe_elim(v_motive_264_, v_t_boxed_268_, v_h_266_, v_unsafe_267_);
lean_dec(v_unsafe_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg(lean_object* v_safe_270_){
_start:
{
lean_inc(v_safe_270_);
return v_safe_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg___boxed(lean_object* v_safe_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_DefinitionSafety_safe_elim___redArg(v_safe_271_);
lean_dec(v_safe_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim(lean_object* v_motive_273_, uint8_t v_t_274_, lean_object* v_h_275_, lean_object* v_safe_276_){
_start:
{
lean_inc(v_safe_276_);
return v_safe_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___boxed(lean_object* v_motive_277_, lean_object* v_t_278_, lean_object* v_h_279_, lean_object* v_safe_280_){
_start:
{
uint8_t v_t_boxed_281_; lean_object* v_res_282_; 
v_t_boxed_281_ = lean_unbox(v_t_278_);
v_res_282_ = l_Lean_DefinitionSafety_safe_elim(v_motive_277_, v_t_boxed_281_, v_h_279_, v_safe_280_);
lean_dec(v_safe_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg(lean_object* v_partial_283_){
_start:
{
lean_inc(v_partial_283_);
return v_partial_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg___boxed(lean_object* v_partial_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_DefinitionSafety_partial_elim___redArg(v_partial_284_);
lean_dec(v_partial_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim(lean_object* v_motive_286_, uint8_t v_t_287_, lean_object* v_h_288_, lean_object* v_partial_289_){
_start:
{
lean_inc(v_partial_289_);
return v_partial_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___boxed(lean_object* v_motive_290_, lean_object* v_t_291_, lean_object* v_h_292_, lean_object* v_partial_293_){
_start:
{
uint8_t v_t_boxed_294_; lean_object* v_res_295_; 
v_t_boxed_294_ = lean_unbox(v_t_291_);
v_res_295_ = l_Lean_DefinitionSafety_partial_elim(v_motive_290_, v_t_boxed_294_, v_h_292_, v_partial_293_);
lean_dec(v_partial_293_);
return v_res_295_;
}
}
static uint8_t _init_l_Lean_instInhabitedDefinitionSafety_default(void){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = 0;
return v___x_296_;
}
}
static uint8_t _init_l_Lean_instInhabitedDefinitionSafety(void){
_start:
{
uint8_t v___x_297_; 
v___x_297_ = 0;
return v___x_297_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t v_x_298_, uint8_t v_y_299_){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_300_ = l_Lean_DefinitionSafety_ctorIdx(v_x_298_);
v___x_301_ = l_Lean_DefinitionSafety_ctorIdx(v_y_299_);
v___x_302_ = lean_nat_dec_eq(v___x_300_, v___x_301_);
lean_dec(v___x_301_);
lean_dec(v___x_300_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionSafety_beq___boxed(lean_object* v_x_303_, lean_object* v_y_304_){
_start:
{
uint8_t v_x_17__boxed_305_; uint8_t v_y_18__boxed_306_; uint8_t v_res_307_; lean_object* v_r_308_; 
v_x_17__boxed_305_ = lean_unbox(v_x_303_);
v_y_18__boxed_306_ = lean_unbox(v_y_304_);
v_res_307_ = l_Lean_instBEqDefinitionSafety_beq(v_x_17__boxed_305_, v_y_18__boxed_306_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
static lean_object* _init_l_Lean_instReprDefinitionSafety_repr___closed__6(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_unsigned_to_nat(2u);
v___x_321_ = lean_nat_to_int(v___x_320_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_instReprDefinitionSafety_repr___closed__7(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_to_int(v___x_322_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDefinitionSafety_repr(uint8_t v_x_324_, lean_object* v_prec_325_){
_start:
{
lean_object* v___y_327_; lean_object* v___y_334_; lean_object* v___y_341_; 
switch(v_x_324_)
{
case 0:
{
lean_object* v___x_347_; uint8_t v___x_348_; 
v___x_347_ = lean_unsigned_to_nat(1024u);
v___x_348_ = lean_nat_dec_le(v___x_347_, v_prec_325_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; 
v___x_349_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_327_ = v___x_349_;
goto v___jp_326_;
}
else
{
lean_object* v___x_350_; 
v___x_350_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_327_ = v___x_350_;
goto v___jp_326_;
}
}
case 1:
{
lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_351_ = lean_unsigned_to_nat(1024u);
v___x_352_ = lean_nat_dec_le(v___x_351_, v_prec_325_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
v___x_353_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_334_ = v___x_353_;
goto v___jp_333_;
}
else
{
lean_object* v___x_354_; 
v___x_354_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_334_ = v___x_354_;
goto v___jp_333_;
}
}
default: 
{
lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_355_ = lean_unsigned_to_nat(1024u);
v___x_356_ = lean_nat_dec_le(v___x_355_, v_prec_325_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; 
v___x_357_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_341_ = v___x_357_;
goto v___jp_340_;
}
else
{
lean_object* v___x_358_; 
v___x_358_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_341_ = v___x_358_;
goto v___jp_340_;
}
}
}
v___jp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_328_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__1));
lean_inc(v___y_327_);
v___x_329_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_329_, 0, v___y_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = 0;
v___x_331_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*1, v___x_330_);
v___x_332_ = l_Repr_addAppParen(v___x_331_, v_prec_325_);
return v___x_332_;
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_335_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__3));
lean_inc(v___y_334_);
v___x_336_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_336_, 0, v___y_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = 0;
v___x_338_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*1, v___x_337_);
v___x_339_ = l_Repr_addAppParen(v___x_338_, v_prec_325_);
return v___x_339_;
}
v___jp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_342_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__5));
lean_inc(v___y_341_);
v___x_343_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_343_, 0, v___y_341_);
lean_ctor_set(v___x_343_, 1, v___x_342_);
v___x_344_ = 0;
v___x_345_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_345_, 0, v___x_343_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*1, v___x_344_);
v___x_346_ = l_Repr_addAppParen(v___x_345_, v_prec_325_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDefinitionSafety_repr___boxed(lean_object* v_x_359_, lean_object* v_prec_360_){
_start:
{
uint8_t v_x_177__boxed_361_; lean_object* v_res_362_; 
v_x_177__boxed_361_ = lean_unbox(v_x_359_);
v_res_362_ = l_Lean_instReprDefinitionSafety_repr(v_x_177__boxed_361_, v_prec_360_);
lean_dec(v_prec_360_);
return v_res_362_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default___closed__0(void){
_start:
{
lean_object* v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_365_ = lean_box(0);
v___x_366_ = 0;
v___x_367_ = lean_box(0);
v___x_368_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__2, &l_Lean_instInhabitedConstantVal_default___closed__2_once, _init_l_Lean_instInhabitedConstantVal_default___closed__2);
v___x_369_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__3, &l_Lean_instInhabitedConstantVal_default___closed__3_once, _init_l_Lean_instInhabitedConstantVal_default___closed__3);
v___x_370_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___x_368_);
lean_ctor_set(v___x_370_, 2, v___x_367_);
lean_ctor_set(v___x_370_, 3, v___x_365_);
lean_ctor_set_uint8(v___x_370_, sizeof(void*)*4, v___x_366_);
return v___x_370_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default(void){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_instInhabitedDefinitionVal_default;
return v___x_372_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDefinitionVal_beq(lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
lean_object* v_toConstantVal_375_; lean_object* v_value_376_; lean_object* v_hints_377_; uint8_t v_safety_378_; lean_object* v_all_379_; lean_object* v_toConstantVal_380_; lean_object* v_value_381_; lean_object* v_hints_382_; uint8_t v_safety_383_; lean_object* v_all_384_; uint8_t v___x_385_; 
v_toConstantVal_375_ = lean_ctor_get(v_x_373_, 0);
v_value_376_ = lean_ctor_get(v_x_373_, 1);
v_hints_377_ = lean_ctor_get(v_x_373_, 2);
v_safety_378_ = lean_ctor_get_uint8(v_x_373_, sizeof(void*)*4);
v_all_379_ = lean_ctor_get(v_x_373_, 3);
v_toConstantVal_380_ = lean_ctor_get(v_x_374_, 0);
v_value_381_ = lean_ctor_get(v_x_374_, 1);
v_hints_382_ = lean_ctor_get(v_x_374_, 2);
v_safety_383_ = lean_ctor_get_uint8(v_x_374_, sizeof(void*)*4);
v_all_384_ = lean_ctor_get(v_x_374_, 3);
v___x_385_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_375_, v_toConstantVal_380_);
if (v___x_385_ == 0)
{
return v___x_385_;
}
else
{
uint8_t v___x_386_; 
v___x_386_ = lean_expr_eqv(v_value_376_, v_value_381_);
if (v___x_386_ == 0)
{
return v___x_386_;
}
else
{
uint8_t v___x_387_; 
v___x_387_ = l_Lean_instBEqReducibilityHints_beq(v_hints_377_, v_hints_382_);
if (v___x_387_ == 0)
{
return v___x_387_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_378_, v_safety_383_);
if (v___x_388_ == 0)
{
return v___x_388_;
}
else
{
uint8_t v___x_389_; 
v___x_389_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_379_, v_all_384_);
return v___x_389_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionVal_beq___boxed(lean_object* v_x_390_, lean_object* v_x_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_Lean_instBEqDefinitionVal_beq(v_x_390_, v_x_391_);
lean_dec_ref(v_x_391_);
lean_dec_ref(v_x_390_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
LEAN_EXPORT lean_object* lean_mk_definition_val(lean_object* v_name_396_, lean_object* v_levelParams_397_, lean_object* v_type_398_, lean_object* v_value_399_, lean_object* v_hints_400_, uint8_t v_safety_401_, lean_object* v_all_402_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_403_, 0, v_name_396_);
lean_ctor_set(v___x_403_, 1, v_levelParams_397_);
lean_ctor_set(v___x_403_, 2, v_type_398_);
v___x_404_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_value_399_);
lean_ctor_set(v___x_404_, 2, v_hints_400_);
lean_ctor_set(v___x_404_, 3, v_all_402_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*4, v_safety_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValEx___boxed(lean_object* v_name_405_, lean_object* v_levelParams_406_, lean_object* v_type_407_, lean_object* v_value_408_, lean_object* v_hints_409_, lean_object* v_safety_410_, lean_object* v_all_411_){
_start:
{
uint8_t v_safety_boxed_412_; lean_object* v_res_413_; 
v_safety_boxed_412_ = lean_unbox(v_safety_410_);
v_res_413_ = lean_mk_definition_val(v_name_405_, v_levelParams_406_, v_type_407_, v_value_408_, v_hints_409_, v_safety_boxed_412_, v_all_411_);
return v_res_413_;
}
}
LEAN_EXPORT uint8_t lean_definition_val_get_safety(lean_object* v_v_414_){
_start:
{
uint8_t v_safety_415_; 
v_safety_415_ = lean_ctor_get_uint8(v_v_414_, sizeof(void*)*4);
lean_dec_ref(v_v_414_);
return v_safety_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionVal_getSafetyEx___boxed(lean_object* v_v_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = lean_definition_val_get_safety(v_v_416_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default___closed__0(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_419_ = lean_box(0);
v___x_420_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__2, &l_Lean_instInhabitedConstantVal_default___closed__2_once, _init_l_Lean_instInhabitedConstantVal_default___closed__2);
v___x_421_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__3, &l_Lean_instInhabitedConstantVal_default___closed__3_once, _init_l_Lean_instInhabitedConstantVal_default___closed__3);
v___x_422_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_422_, 0, v___x_421_);
lean_ctor_set(v___x_422_, 1, v___x_420_);
lean_ctor_set(v___x_422_, 2, v___x_419_);
return v___x_422_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default(void){
_start:
{
lean_object* v___x_423_; 
v___x_423_ = lean_obj_once(&l_Lean_instInhabitedTheoremVal_default___closed__0, &l_Lean_instInhabitedTheoremVal_default___closed__0_once, _init_l_Lean_instInhabitedTheoremVal_default___closed__0);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal(void){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Lean_instInhabitedTheoremVal_default;
return v___x_424_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqTheoremVal_beq(lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
lean_object* v_toConstantVal_427_; lean_object* v_value_428_; lean_object* v_all_429_; lean_object* v_toConstantVal_430_; lean_object* v_value_431_; lean_object* v_all_432_; uint8_t v___x_433_; 
v_toConstantVal_427_ = lean_ctor_get(v_x_425_, 0);
v_value_428_ = lean_ctor_get(v_x_425_, 1);
v_all_429_ = lean_ctor_get(v_x_425_, 2);
v_toConstantVal_430_ = lean_ctor_get(v_x_426_, 0);
v_value_431_ = lean_ctor_get(v_x_426_, 1);
v_all_432_ = lean_ctor_get(v_x_426_, 2);
v___x_433_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_427_, v_toConstantVal_430_);
if (v___x_433_ == 0)
{
return v___x_433_;
}
else
{
uint8_t v___x_434_; 
v___x_434_ = lean_expr_eqv(v_value_428_, v_value_431_);
if (v___x_434_ == 0)
{
return v___x_434_;
}
else
{
uint8_t v___x_435_; 
v___x_435_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_429_, v_all_432_);
return v___x_435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqTheoremVal_beq___boxed(lean_object* v_x_436_, lean_object* v_x_437_){
_start:
{
uint8_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Lean_instBEqTheoremVal_beq(v_x_436_, v_x_437_);
lean_dec_ref(v_x_437_);
lean_dec_ref(v_x_436_);
v_r_439_ = lean_box(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT lean_object* lean_mk_theorem_val(lean_object* v_name_442_, lean_object* v_levelParams_443_, lean_object* v_type_444_, lean_object* v_value_445_, lean_object* v_all_446_){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_447_, 0, v_name_442_);
lean_ctor_set(v___x_447_, 1, v_levelParams_443_);
lean_ctor_set(v___x_447_, 2, v_type_444_);
v___x_448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v_value_445_);
lean_ctor_set(v___x_448_, 2, v_all_446_);
return v___x_448_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default___closed__0(void){
_start:
{
lean_object* v___x_449_; uint8_t v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_449_ = lean_box(0);
v___x_450_ = 0;
v___x_451_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__2, &l_Lean_instInhabitedConstantVal_default___closed__2_once, _init_l_Lean_instInhabitedConstantVal_default___closed__2);
v___x_452_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__3, &l_Lean_instInhabitedConstantVal_default___closed__3_once, _init_l_Lean_instInhabitedConstantVal_default___closed__3);
v___x_453_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_449_);
lean_ctor_set_uint8(v___x_453_, sizeof(void*)*3, v___x_450_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default(void){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = lean_obj_once(&l_Lean_instInhabitedOpaqueVal_default___closed__0, &l_Lean_instInhabitedOpaqueVal_default___closed__0_once, _init_l_Lean_instInhabitedOpaqueVal_default___closed__0);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal(void){
_start:
{
lean_object* v___x_455_; 
v___x_455_ = l_Lean_instInhabitedOpaqueVal_default;
return v___x_455_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqOpaqueVal_beq(lean_object* v_x_456_, lean_object* v_x_457_){
_start:
{
lean_object* v_toConstantVal_458_; lean_object* v_value_459_; uint8_t v_isUnsafe_460_; lean_object* v_all_461_; lean_object* v_toConstantVal_462_; lean_object* v_value_463_; uint8_t v_isUnsafe_464_; lean_object* v_all_465_; uint8_t v___y_467_; uint8_t v___x_469_; 
v_toConstantVal_458_ = lean_ctor_get(v_x_456_, 0);
v_value_459_ = lean_ctor_get(v_x_456_, 1);
v_isUnsafe_460_ = lean_ctor_get_uint8(v_x_456_, sizeof(void*)*3);
v_all_461_ = lean_ctor_get(v_x_456_, 2);
v_toConstantVal_462_ = lean_ctor_get(v_x_457_, 0);
v_value_463_ = lean_ctor_get(v_x_457_, 1);
v_isUnsafe_464_ = lean_ctor_get_uint8(v_x_457_, sizeof(void*)*3);
v_all_465_ = lean_ctor_get(v_x_457_, 2);
v___x_469_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_458_, v_toConstantVal_462_);
if (v___x_469_ == 0)
{
return v___x_469_;
}
else
{
uint8_t v___x_470_; 
v___x_470_ = lean_expr_eqv(v_value_459_, v_value_463_);
if (v___x_470_ == 0)
{
return v___x_470_;
}
else
{
if (v_isUnsafe_460_ == 0)
{
if (v_isUnsafe_464_ == 0)
{
v___y_467_ = v___x_470_;
goto v___jp_466_;
}
else
{
return v_isUnsafe_460_;
}
}
else
{
v___y_467_ = v_isUnsafe_464_;
goto v___jp_466_;
}
}
}
v___jp_466_:
{
if (v___y_467_ == 0)
{
return v___y_467_;
}
else
{
uint8_t v___x_468_; 
v___x_468_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_461_, v_all_465_);
return v___x_468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqOpaqueVal_beq___boxed(lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
uint8_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = l_Lean_instBEqOpaqueVal_beq(v_x_471_, v_x_472_);
lean_dec_ref(v_x_472_);
lean_dec_ref(v_x_471_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
LEAN_EXPORT lean_object* lean_mk_opaque_val(lean_object* v_name_477_, lean_object* v_levelParams_478_, lean_object* v_type_479_, lean_object* v_value_480_, uint8_t v_isUnsafe_481_, lean_object* v_all_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_483_, 0, v_name_477_);
lean_ctor_set(v___x_483_, 1, v_levelParams_478_);
lean_ctor_set(v___x_483_, 2, v_type_479_);
v___x_484_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v_value_480_);
lean_ctor_set(v___x_484_, 2, v_all_482_);
lean_ctor_set_uint8(v___x_484_, sizeof(void*)*3, v_isUnsafe_481_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOpaqueValEx___boxed(lean_object* v_name_485_, lean_object* v_levelParams_486_, lean_object* v_type_487_, lean_object* v_value_488_, lean_object* v_isUnsafe_489_, lean_object* v_all_490_){
_start:
{
uint8_t v_isUnsafe_boxed_491_; lean_object* v_res_492_; 
v_isUnsafe_boxed_491_ = lean_unbox(v_isUnsafe_489_);
v_res_492_ = lean_mk_opaque_val(v_name_485_, v_levelParams_486_, v_type_487_, v_value_488_, v_isUnsafe_boxed_491_, v_all_490_);
return v_res_492_;
}
}
LEAN_EXPORT uint8_t lean_opaque_val_is_unsafe(lean_object* v_v_493_){
_start:
{
uint8_t v_isUnsafe_494_; 
v_isUnsafe_494_ = lean_ctor_get_uint8(v_v_493_, sizeof(void*)*3);
lean_dec_ref(v_v_493_);
return v_isUnsafe_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpaqueVal_isUnsafeEx___boxed(lean_object* v_v_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = lean_opaque_val_is_unsafe(v_v_495_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__0(void){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_498_ = lean_box(0);
v___x_499_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_500_ = l_Lean_Expr_const___override(v___x_499_, v___x_498_);
return v___x_500_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__1(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_502_ = lean_box(0);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v___x_501_);
return v___x_503_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default(void){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__1, &l_Lean_instInhabitedConstructor_default___closed__1_once, _init_l_Lean_instInhabitedConstructor_default___closed__1);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor(void){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_instInhabitedConstructor_default;
return v___x_505_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructor_beq(lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
lean_object* v_name_508_; lean_object* v_type_509_; lean_object* v_name_510_; lean_object* v_type_511_; uint8_t v___x_512_; 
v_name_508_ = lean_ctor_get(v_x_506_, 0);
v_type_509_ = lean_ctor_get(v_x_506_, 1);
v_name_510_ = lean_ctor_get(v_x_507_, 0);
v_type_511_ = lean_ctor_get(v_x_507_, 1);
v___x_512_ = lean_name_eq(v_name_508_, v_name_510_);
if (v___x_512_ == 0)
{
return v___x_512_;
}
else
{
uint8_t v___x_513_; 
v___x_513_ = lean_expr_eqv(v_type_509_, v_type_511_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructor_beq___boxed(lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
uint8_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l_Lean_instBEqConstructor_beq(v_x_514_, v_x_515_);
lean_dec_ref(v_x_515_);
lean_dec_ref(v_x_514_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default___closed__0(void){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_520_ = lean_box(0);
v___x_521_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_522_ = lean_box(0);
v___x_523_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v___x_521_);
lean_ctor_set(v___x_523_, 2, v___x_520_);
return v___x_523_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default(void){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = lean_obj_once(&l_Lean_instInhabitedInductiveType_default___closed__0, &l_Lean_instInhabitedInductiveType_default___closed__0_once, _init_l_Lean_instInhabitedInductiveType_default___closed__0);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType(void){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_instInhabitedInductiveType_default;
return v___x_525_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
if (lean_obj_tag(v_x_527_) == 0)
{
uint8_t v___x_528_; 
v___x_528_ = 1;
return v___x_528_;
}
else
{
uint8_t v___x_529_; 
v___x_529_ = 0;
return v___x_529_;
}
}
else
{
if (lean_obj_tag(v_x_527_) == 0)
{
uint8_t v___x_530_; 
v___x_530_ = 0;
return v___x_530_;
}
else
{
lean_object* v_head_531_; lean_object* v_tail_532_; lean_object* v_head_533_; lean_object* v_tail_534_; uint8_t v___x_535_; 
v_head_531_ = lean_ctor_get(v_x_526_, 0);
v_tail_532_ = lean_ctor_get(v_x_526_, 1);
v_head_533_ = lean_ctor_get(v_x_527_, 0);
v_tail_534_ = lean_ctor_get(v_x_527_, 1);
v___x_535_ = l_Lean_instBEqConstructor_beq(v_head_531_, v_head_533_);
if (v___x_535_ == 0)
{
return v___x_535_;
}
else
{
v_x_526_ = v_tail_532_;
v_x_527_ = v_tail_534_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0___boxed(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_x_537_, v_x_538_);
lean_dec(v_x_538_);
lean_dec(v_x_537_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveType_beq(lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v_name_543_; lean_object* v_type_544_; lean_object* v_ctors_545_; lean_object* v_name_546_; lean_object* v_type_547_; lean_object* v_ctors_548_; uint8_t v___x_549_; 
v_name_543_ = lean_ctor_get(v_x_541_, 0);
v_type_544_ = lean_ctor_get(v_x_541_, 1);
v_ctors_545_ = lean_ctor_get(v_x_541_, 2);
v_name_546_ = lean_ctor_get(v_x_542_, 0);
v_type_547_ = lean_ctor_get(v_x_542_, 1);
v_ctors_548_ = lean_ctor_get(v_x_542_, 2);
v___x_549_ = lean_name_eq(v_name_543_, v_name_546_);
if (v___x_549_ == 0)
{
return v___x_549_;
}
else
{
uint8_t v___x_550_; 
v___x_550_ = lean_expr_eqv(v_type_544_, v_type_547_);
if (v___x_550_ == 0)
{
return v___x_550_;
}
else
{
uint8_t v___x_551_; 
v___x_551_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_ctors_545_, v_ctors_548_);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveType_beq___boxed(lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l_Lean_instBEqInductiveType_beq(v_x_552_, v_x_553_);
lean_dec_ref(v_x_553_);
lean_dec_ref(v_x_552_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx(lean_object* v_x_558_){
_start:
{
switch(lean_obj_tag(v_x_558_))
{
case 0:
{
lean_object* v___x_559_; 
v___x_559_ = lean_unsigned_to_nat(0u);
return v___x_559_;
}
case 1:
{
lean_object* v___x_560_; 
v___x_560_ = lean_unsigned_to_nat(1u);
return v___x_560_;
}
case 2:
{
lean_object* v___x_561_; 
v___x_561_ = lean_unsigned_to_nat(2u);
return v___x_561_;
}
case 3:
{
lean_object* v___x_562_; 
v___x_562_ = lean_unsigned_to_nat(3u);
return v___x_562_;
}
case 4:
{
lean_object* v___x_563_; 
v___x_563_ = lean_unsigned_to_nat(4u);
return v___x_563_;
}
case 5:
{
lean_object* v___x_564_; 
v___x_564_ = lean_unsigned_to_nat(5u);
return v___x_564_;
}
default: 
{
lean_object* v___x_565_; 
v___x_565_ = lean_unsigned_to_nat(6u);
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___boxed(lean_object* v_x_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Declaration_ctorIdx(v_x_566_);
lean_dec(v_x_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___redArg(lean_object* v_t_568_, lean_object* v_k_569_){
_start:
{
switch(lean_obj_tag(v_t_568_))
{
case 4:
{
return v_k_569_;
}
case 5:
{
lean_object* v_defns_570_; lean_object* v___x_571_; 
v_defns_570_ = lean_ctor_get(v_t_568_, 0);
lean_inc(v_defns_570_);
lean_dec_ref(v_t_568_);
v___x_571_ = lean_apply_1(v_k_569_, v_defns_570_);
return v___x_571_;
}
case 6:
{
lean_object* v_lparams_572_; lean_object* v_nparams_573_; lean_object* v_types_574_; uint8_t v_isUnsafe_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_lparams_572_ = lean_ctor_get(v_t_568_, 0);
lean_inc(v_lparams_572_);
v_nparams_573_ = lean_ctor_get(v_t_568_, 1);
lean_inc(v_nparams_573_);
v_types_574_ = lean_ctor_get(v_t_568_, 2);
lean_inc(v_types_574_);
v_isUnsafe_575_ = lean_ctor_get_uint8(v_t_568_, sizeof(void*)*3);
lean_dec_ref(v_t_568_);
v___x_576_ = lean_box(v_isUnsafe_575_);
v___x_577_ = lean_apply_4(v_k_569_, v_lparams_572_, v_nparams_573_, v_types_574_, v___x_576_);
return v___x_577_;
}
default: 
{
lean_object* v_val_578_; lean_object* v___x_579_; 
v_val_578_ = lean_ctor_get(v_t_568_, 0);
lean_inc_ref(v_val_578_);
lean_dec(v_t_568_);
v___x_579_ = lean_apply_1(v_k_569_, v_val_578_);
return v___x_579_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim(lean_object* v_motive_580_, lean_object* v_ctorIdx_581_, lean_object* v_t_582_, lean_object* v_h_583_, lean_object* v_k_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Declaration_ctorElim___redArg(v_t_582_, v_k_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___boxed(lean_object* v_motive_586_, lean_object* v_ctorIdx_587_, lean_object* v_t_588_, lean_object* v_h_589_, lean_object* v_k_590_){
_start:
{
lean_object* v_res_591_; 
v_res_591_ = l_Lean_Declaration_ctorElim(v_motive_586_, v_ctorIdx_587_, v_t_588_, v_h_589_, v_k_590_);
lean_dec(v_ctorIdx_587_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim___redArg(lean_object* v_t_592_, lean_object* v_axiomDecl_593_){
_start:
{
lean_object* v___x_594_; 
v___x_594_ = l_Lean_Declaration_ctorElim___redArg(v_t_592_, v_axiomDecl_593_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim(lean_object* v_motive_595_, lean_object* v_t_596_, lean_object* v_h_597_, lean_object* v_axiomDecl_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_Declaration_ctorElim___redArg(v_t_596_, v_axiomDecl_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim___redArg(lean_object* v_t_600_, lean_object* v_defnDecl_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_Declaration_ctorElim___redArg(v_t_600_, v_defnDecl_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim(lean_object* v_motive_603_, lean_object* v_t_604_, lean_object* v_h_605_, lean_object* v_defnDecl_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_Declaration_ctorElim___redArg(v_t_604_, v_defnDecl_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim___redArg(lean_object* v_t_608_, lean_object* v_thmDecl_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Declaration_ctorElim___redArg(v_t_608_, v_thmDecl_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim(lean_object* v_motive_611_, lean_object* v_t_612_, lean_object* v_h_613_, lean_object* v_thmDecl_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_Declaration_ctorElim___redArg(v_t_612_, v_thmDecl_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim___redArg(lean_object* v_t_616_, lean_object* v_opaqueDecl_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_Declaration_ctorElim___redArg(v_t_616_, v_opaqueDecl_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim(lean_object* v_motive_619_, lean_object* v_t_620_, lean_object* v_h_621_, lean_object* v_opaqueDecl_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Declaration_ctorElim___redArg(v_t_620_, v_opaqueDecl_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim___redArg(lean_object* v_t_624_, lean_object* v_quotDecl_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Lean_Declaration_ctorElim___redArg(v_t_624_, v_quotDecl_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim(lean_object* v_motive_627_, lean_object* v_t_628_, lean_object* v_h_629_, lean_object* v_quotDecl_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Declaration_ctorElim___redArg(v_t_628_, v_quotDecl_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim___redArg(lean_object* v_t_632_, lean_object* v_mutualDefnDecl_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_Declaration_ctorElim___redArg(v_t_632_, v_mutualDefnDecl_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim(lean_object* v_motive_635_, lean_object* v_t_636_, lean_object* v_h_637_, lean_object* v_mutualDefnDecl_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_Declaration_ctorElim___redArg(v_t_636_, v_mutualDefnDecl_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim___redArg(lean_object* v_t_640_, lean_object* v_inductDecl_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Declaration_ctorElim___redArg(v_t_640_, v_inductDecl_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim(lean_object* v_motive_643_, lean_object* v_t_644_, lean_object* v_h_645_, lean_object* v_inductDecl_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Lean_Declaration_ctorElim___redArg(v_t_644_, v_inductDecl_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default___closed__0(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = l_Lean_instInhabitedAxiomVal_default;
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default(void){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = lean_obj_once(&l_Lean_instInhabitedDeclaration_default___closed__0, &l_Lean_instInhabitedDeclaration_default___closed__0_once, _init_l_Lean_instInhabitedDeclaration_default___closed__0);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration(void){
_start:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_instInhabitedDeclaration_default;
return v___x_651_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
if (lean_obj_tag(v_x_652_) == 0)
{
if (lean_obj_tag(v_x_653_) == 0)
{
uint8_t v___x_654_; 
v___x_654_ = 1;
return v___x_654_;
}
else
{
uint8_t v___x_655_; 
v___x_655_ = 0;
return v___x_655_;
}
}
else
{
if (lean_obj_tag(v_x_653_) == 0)
{
uint8_t v___x_656_; 
v___x_656_ = 0;
return v___x_656_;
}
else
{
lean_object* v_head_657_; lean_object* v_tail_658_; lean_object* v_head_659_; lean_object* v_tail_660_; uint8_t v___x_661_; 
v_head_657_ = lean_ctor_get(v_x_652_, 0);
v_tail_658_ = lean_ctor_get(v_x_652_, 1);
v_head_659_ = lean_ctor_get(v_x_653_, 0);
v_tail_660_ = lean_ctor_get(v_x_653_, 1);
v___x_661_ = l_Lean_instBEqDefinitionVal_beq(v_head_657_, v_head_659_);
if (v___x_661_ == 0)
{
return v___x_661_;
}
else
{
v_x_652_ = v_tail_658_;
v_x_653_ = v_tail_660_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0___boxed(lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_x_663_, v_x_664_);
lean_dec(v_x_664_);
lean_dec(v_x_663_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
if (lean_obj_tag(v_x_667_) == 0)
{
if (lean_obj_tag(v_x_668_) == 0)
{
uint8_t v___x_669_; 
v___x_669_ = 1;
return v___x_669_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = 0;
return v___x_670_;
}
}
else
{
if (lean_obj_tag(v_x_668_) == 0)
{
uint8_t v___x_671_; 
v___x_671_ = 0;
return v___x_671_;
}
else
{
lean_object* v_head_672_; lean_object* v_tail_673_; lean_object* v_head_674_; lean_object* v_tail_675_; uint8_t v___x_676_; 
v_head_672_ = lean_ctor_get(v_x_667_, 0);
v_tail_673_ = lean_ctor_get(v_x_667_, 1);
v_head_674_ = lean_ctor_get(v_x_668_, 0);
v_tail_675_ = lean_ctor_get(v_x_668_, 1);
v___x_676_ = l_Lean_instBEqInductiveType_beq(v_head_672_, v_head_674_);
if (v___x_676_ == 0)
{
return v___x_676_;
}
else
{
v_x_667_ = v_tail_673_;
v_x_668_ = v_tail_675_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1___boxed(lean_object* v_x_678_, lean_object* v_x_679_){
_start:
{
uint8_t v_res_680_; lean_object* v_r_681_; 
v_res_680_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_x_678_, v_x_679_);
lean_dec(v_x_679_);
lean_dec(v_x_678_);
v_r_681_ = lean_box(v_res_680_);
return v_r_681_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDeclaration_beq(lean_object* v_x_682_, lean_object* v_x_683_){
_start:
{
switch(lean_obj_tag(v_x_682_))
{
case 0:
{
if (lean_obj_tag(v_x_683_) == 0)
{
lean_object* v_val_684_; lean_object* v_val_685_; uint8_t v___x_686_; 
v_val_684_ = lean_ctor_get(v_x_682_, 0);
v_val_685_ = lean_ctor_get(v_x_683_, 0);
v___x_686_ = l_Lean_instBEqAxiomVal_beq(v_val_684_, v_val_685_);
return v___x_686_;
}
else
{
uint8_t v___x_687_; 
v___x_687_ = 0;
return v___x_687_;
}
}
case 1:
{
if (lean_obj_tag(v_x_683_) == 1)
{
lean_object* v_val_688_; lean_object* v_val_689_; uint8_t v___x_690_; 
v_val_688_ = lean_ctor_get(v_x_682_, 0);
v_val_689_ = lean_ctor_get(v_x_683_, 0);
v___x_690_ = l_Lean_instBEqDefinitionVal_beq(v_val_688_, v_val_689_);
return v___x_690_;
}
else
{
uint8_t v___x_691_; 
v___x_691_ = 0;
return v___x_691_;
}
}
case 2:
{
if (lean_obj_tag(v_x_683_) == 2)
{
lean_object* v_val_692_; lean_object* v_val_693_; uint8_t v___x_694_; 
v_val_692_ = lean_ctor_get(v_x_682_, 0);
v_val_693_ = lean_ctor_get(v_x_683_, 0);
v___x_694_ = l_Lean_instBEqTheoremVal_beq(v_val_692_, v_val_693_);
return v___x_694_;
}
else
{
uint8_t v___x_695_; 
v___x_695_ = 0;
return v___x_695_;
}
}
case 3:
{
if (lean_obj_tag(v_x_683_) == 3)
{
lean_object* v_val_696_; lean_object* v_val_697_; uint8_t v___x_698_; 
v_val_696_ = lean_ctor_get(v_x_682_, 0);
v_val_697_ = lean_ctor_get(v_x_683_, 0);
v___x_698_ = l_Lean_instBEqOpaqueVal_beq(v_val_696_, v_val_697_);
return v___x_698_;
}
else
{
uint8_t v___x_699_; 
v___x_699_ = 0;
return v___x_699_;
}
}
case 4:
{
if (lean_obj_tag(v_x_683_) == 4)
{
uint8_t v___x_700_; 
v___x_700_ = 1;
return v___x_700_;
}
else
{
uint8_t v___x_701_; 
v___x_701_ = 0;
return v___x_701_;
}
}
case 5:
{
if (lean_obj_tag(v_x_683_) == 5)
{
lean_object* v_defns_702_; lean_object* v_defns_703_; uint8_t v___x_704_; 
v_defns_702_ = lean_ctor_get(v_x_682_, 0);
v_defns_703_ = lean_ctor_get(v_x_683_, 0);
v___x_704_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_defns_702_, v_defns_703_);
return v___x_704_;
}
else
{
uint8_t v___x_705_; 
v___x_705_ = 0;
return v___x_705_;
}
}
default: 
{
if (lean_obj_tag(v_x_683_) == 6)
{
lean_object* v_lparams_706_; lean_object* v_nparams_707_; lean_object* v_types_708_; uint8_t v_isUnsafe_709_; lean_object* v_lparams_710_; lean_object* v_nparams_711_; lean_object* v_types_712_; uint8_t v_isUnsafe_713_; uint8_t v___x_714_; 
v_lparams_706_ = lean_ctor_get(v_x_682_, 0);
v_nparams_707_ = lean_ctor_get(v_x_682_, 1);
v_types_708_ = lean_ctor_get(v_x_682_, 2);
v_isUnsafe_709_ = lean_ctor_get_uint8(v_x_682_, sizeof(void*)*3);
v_lparams_710_ = lean_ctor_get(v_x_683_, 0);
v_nparams_711_ = lean_ctor_get(v_x_683_, 1);
v_types_712_ = lean_ctor_get(v_x_683_, 2);
v_isUnsafe_713_ = lean_ctor_get_uint8(v_x_683_, sizeof(void*)*3);
v___x_714_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_lparams_706_, v_lparams_710_);
if (v___x_714_ == 0)
{
return v___x_714_;
}
else
{
uint8_t v___x_715_; 
v___x_715_ = lean_nat_dec_eq(v_nparams_707_, v_nparams_711_);
if (v___x_715_ == 0)
{
return v___x_715_;
}
else
{
uint8_t v___x_716_; 
v___x_716_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_types_708_, v_types_712_);
if (v___x_716_ == 0)
{
return v___x_716_;
}
else
{
if (v_isUnsafe_709_ == 0)
{
if (v_isUnsafe_713_ == 0)
{
return v___x_716_;
}
else
{
return v_isUnsafe_709_;
}
}
else
{
return v_isUnsafe_713_;
}
}
}
}
}
else
{
uint8_t v___x_717_; 
v___x_717_ = 0;
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDeclaration_beq___boxed(lean_object* v_x_718_, lean_object* v_x_719_){
_start:
{
uint8_t v_res_720_; lean_object* v_r_721_; 
v_res_720_ = l_Lean_instBEqDeclaration_beq(v_x_718_, v_x_719_);
lean_dec(v_x_719_);
lean_dec(v_x_718_);
v_r_721_ = lean_box(v_res_720_);
return v_r_721_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_decl(lean_object* v_lparams_724_, lean_object* v_nparams_725_, lean_object* v_types_726_, uint8_t v_isUnsafe_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_728_, 0, v_lparams_724_);
lean_ctor_set(v___x_728_, 1, v_nparams_725_);
lean_ctor_set(v___x_728_, 2, v_types_726_);
lean_ctor_set_uint8(v___x_728_, sizeof(void*)*3, v_isUnsafe_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveDeclEs___boxed(lean_object* v_lparams_729_, lean_object* v_nparams_730_, lean_object* v_types_731_, lean_object* v_isUnsafe_732_){
_start:
{
uint8_t v_isUnsafe_boxed_733_; lean_object* v_res_734_; 
v_isUnsafe_boxed_733_ = lean_unbox(v_isUnsafe_732_);
v_res_734_ = lean_mk_inductive_decl(v_lparams_729_, v_nparams_730_, v_types_731_, v_isUnsafe_boxed_733_);
return v_res_734_;
}
}
LEAN_EXPORT uint8_t lean_is_unsafe_inductive_decl(lean_object* v_x_735_){
_start:
{
if (lean_obj_tag(v_x_735_) == 6)
{
uint8_t v_isUnsafe_736_; 
v_isUnsafe_736_ = lean_ctor_get_uint8(v_x_735_, sizeof(void*)*3);
lean_dec_ref(v_x_735_);
return v_isUnsafe_736_;
}
else
{
uint8_t v___x_737_; 
lean_dec(v_x_735_);
v___x_737_ = 0;
return v___x_737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_isUnsafeInductiveDeclEx___boxed(lean_object* v_x_738_){
_start:
{
uint8_t v_res_739_; lean_object* v_r_740_; 
v_res_739_ = lean_is_unsafe_inductive_decl(v_x_738_);
v_r_740_ = lean_box(v_res_739_);
return v_r_740_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(lean_object* v_msg_741_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = l_Lean_instInhabitedDefinitionVal_default;
v___x_743_ = lean_panic_fn_borrowed(v___x_742_, v_msg_741_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_Declaration_definitionVal_x21___closed__3(void){
_start:
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_747_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__2));
v___x_748_ = lean_unsigned_to_nat(9u);
v___x_749_ = lean_unsigned_to_nat(206u);
v___x_750_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__1));
v___x_751_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_752_ = l_mkPanicMessageWithDecl(v___x_751_, v___x_750_, v___x_749_, v___x_748_, v___x_747_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21(lean_object* v_x_753_){
_start:
{
if (lean_obj_tag(v_x_753_) == 1)
{
lean_object* v_val_754_; 
v_val_754_ = lean_ctor_get(v_x_753_, 0);
lean_inc_ref(v_val_754_);
return v_val_754_;
}
else
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_obj_once(&l_Lean_Declaration_definitionVal_x21___closed__3, &l_Lean_Declaration_definitionVal_x21___closed__3_once, _init_l_Lean_Declaration_definitionVal_x21___closed__3);
v___x_756_ = l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(v___x_755_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21___boxed(lean_object* v_x_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_Lean_Declaration_definitionVal_x21(v_x_757_);
lean_dec(v_x_757_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
if (lean_obj_tag(v_a_759_) == 0)
{
lean_object* v___x_761_; 
v___x_761_ = l_List_reverse___redArg(v_a_760_);
return v___x_761_;
}
else
{
lean_object* v_head_762_; lean_object* v_toConstantVal_763_; lean_object* v_tail_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_773_; 
v_head_762_ = lean_ctor_get(v_a_759_, 0);
v_toConstantVal_763_ = lean_ctor_get(v_head_762_, 0);
lean_inc_ref(v_toConstantVal_763_);
v_tail_764_ = lean_ctor_get(v_a_759_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_759_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_a_759_, 0);
lean_dec(v_unused_774_);
v___x_766_ = v_a_759_;
v_isShared_767_ = v_isSharedCheck_773_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_tail_764_);
lean_dec(v_a_759_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_773_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v_name_768_; lean_object* v___x_770_; 
v_name_768_ = lean_ctor_get(v_toConstantVal_763_, 0);
lean_inc(v_name_768_);
lean_dec_ref(v_toConstantVal_763_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v_a_760_);
lean_ctor_set(v___x_766_, 0, v_name_768_);
v___x_770_ = v___x_766_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_name_768_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_760_);
v___x_770_ = v_reuseFailAlloc_772_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
v_a_759_ = v_tail_764_;
v_a_760_ = v___x_770_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
if (lean_obj_tag(v_a_775_) == 0)
{
lean_object* v___x_777_; 
v___x_777_ = l_List_reverse___redArg(v_a_776_);
return v___x_777_;
}
else
{
lean_object* v_head_778_; lean_object* v_tail_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_788_; 
v_head_778_ = lean_ctor_get(v_a_775_, 0);
v_tail_779_ = lean_ctor_get(v_a_775_, 1);
v_isSharedCheck_788_ = !lean_is_exclusive(v_a_775_);
if (v_isSharedCheck_788_ == 0)
{
v___x_781_ = v_a_775_;
v_isShared_782_ = v_isSharedCheck_788_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_tail_779_);
lean_inc(v_head_778_);
lean_dec(v_a_775_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_788_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_name_783_; lean_object* v___x_785_; 
v_name_783_ = lean_ctor_get(v_head_778_, 0);
lean_inc(v_name_783_);
lean_dec(v_head_778_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v_a_776_);
lean_ctor_set(v___x_781_, 0, v_name_783_);
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_name_783_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_a_776_);
v___x_785_ = v_reuseFailAlloc_787_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
v_a_775_ = v_tail_779_;
v_a_776_ = v___x_785_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getTopLevelNames(lean_object* v_x_795_){
_start:
{
switch(lean_obj_tag(v_x_795_))
{
case 4:
{
lean_object* v___x_796_; 
v___x_796_ = ((lean_object*)(l_Lean_Declaration_getTopLevelNames___closed__2));
return v___x_796_;
}
case 5:
{
lean_object* v_defns_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_defns_797_ = lean_ctor_get(v_x_795_, 0);
lean_inc(v_defns_797_);
lean_dec_ref(v_x_795_);
v___x_798_ = lean_box(0);
v___x_799_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_797_, v___x_798_);
return v___x_799_;
}
case 6:
{
lean_object* v_types_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_types_800_ = lean_ctor_get(v_x_795_, 2);
lean_inc(v_types_800_);
lean_dec_ref(v_x_795_);
v___x_801_ = lean_box(0);
v___x_802_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(v_types_800_, v___x_801_);
return v___x_802_;
}
default: 
{
lean_object* v_val_803_; lean_object* v_toConstantVal_804_; lean_object* v_name_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_val_803_ = lean_ctor_get(v_x_795_, 0);
lean_inc_ref(v_val_803_);
lean_dec(v_x_795_);
v_toConstantVal_804_ = lean_ctor_get(v_val_803_, 0);
lean_inc_ref(v_toConstantVal_804_);
lean_dec_ref(v_val_803_);
v_name_805_ = lean_ctor_get(v_toConstantVal_804_, 0);
lean_inc(v_name_805_);
lean_dec_ref(v_toConstantVal_804_);
v___x_806_ = lean_box(0);
v___x_807_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_807_, 0, v_name_805_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
return v___x_807_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
if (lean_obj_tag(v_a_808_) == 0)
{
lean_object* v___x_810_; 
v___x_810_ = l_List_reverse___redArg(v_a_809_);
return v___x_810_;
}
else
{
lean_object* v_head_811_; lean_object* v_tail_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_821_; 
v_head_811_ = lean_ctor_get(v_a_808_, 0);
v_tail_812_ = lean_ctor_get(v_a_808_, 1);
v_isSharedCheck_821_ = !lean_is_exclusive(v_a_808_);
if (v_isSharedCheck_821_ == 0)
{
v___x_814_ = v_a_808_;
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_tail_812_);
lean_inc(v_head_811_);
lean_dec(v_a_808_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_821_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v_name_816_; lean_object* v___x_818_; 
v_name_816_ = lean_ctor_get(v_head_811_, 0);
lean_inc(v_name_816_);
lean_dec(v_head_811_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v_a_809_);
lean_ctor_set(v___x_814_, 0, v_name_816_);
v___x_818_ = v___x_814_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_name_816_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_a_809_);
v___x_818_ = v_reuseFailAlloc_820_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
v_a_808_ = v_tail_812_;
v_a_809_ = v___x_818_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(lean_object* v_a_825_, lean_object* v_a_826_){
_start:
{
if (lean_obj_tag(v_a_825_) == 0)
{
lean_object* v___x_827_; 
v___x_827_ = lean_array_to_list(v_a_826_);
return v___x_827_;
}
else
{
lean_object* v_head_828_; lean_object* v_tail_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_845_; 
v_head_828_ = lean_ctor_get(v_a_825_, 0);
v_tail_829_ = lean_ctor_get(v_a_825_, 1);
v_isSharedCheck_845_ = !lean_is_exclusive(v_a_825_);
if (v_isSharedCheck_845_ == 0)
{
v___x_831_ = v_a_825_;
v_isShared_832_ = v_isSharedCheck_845_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_tail_829_);
lean_inc(v_head_828_);
lean_dec(v_a_825_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_845_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v_name_833_; lean_object* v_ctors_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_840_; 
v_name_833_ = lean_ctor_get(v_head_828_, 0);
lean_inc(v_name_833_);
v_ctors_834_ = lean_ctor_get(v_head_828_, 2);
lean_inc(v_ctors_834_);
lean_dec(v_head_828_);
v___x_835_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1));
v___x_836_ = l_Lean_Name_appendCore(v_name_833_, v___x_835_);
v___x_837_ = lean_box(0);
v___x_838_ = l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(v_ctors_834_, v___x_837_);
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v___x_838_);
lean_ctor_set(v___x_831_, 0, v___x_836_);
v___x_840_ = v___x_831_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v___x_838_);
v___x_840_ = v_reuseFailAlloc_844_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_841_, 0, v_name_833_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_826_, v___x_841_);
v_a_825_ = v_tail_829_;
v_a_826_ = v___x_842_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getNames(lean_object* v_x_872_){
_start:
{
switch(lean_obj_tag(v_x_872_))
{
case 4:
{
lean_object* v___x_873_; 
v___x_873_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__9));
return v___x_873_;
}
case 5:
{
lean_object* v_defns_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_defns_874_ = lean_ctor_get(v_x_872_, 0);
lean_inc(v_defns_874_);
lean_dec_ref(v_x_872_);
v___x_875_ = lean_box(0);
v___x_876_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_874_, v___x_875_);
return v___x_876_;
}
case 6:
{
lean_object* v_types_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_types_877_ = lean_ctor_get(v_x_872_, 2);
lean_inc(v_types_877_);
lean_dec_ref(v_x_872_);
v___x_878_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__10));
v___x_879_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(v_types_877_, v___x_878_);
return v___x_879_;
}
default: 
{
lean_object* v_val_880_; lean_object* v_toConstantVal_881_; lean_object* v_name_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_val_880_ = lean_ctor_get(v_x_872_, 0);
lean_inc_ref(v_val_880_);
lean_dec(v_x_872_);
v_toConstantVal_881_ = lean_ctor_get(v_val_880_, 0);
lean_inc_ref(v_toConstantVal_881_);
lean_dec_ref(v_val_880_);
v_name_882_ = lean_ctor_get(v_toConstantVal_881_, 0);
lean_inc(v_name_882_);
lean_dec_ref(v_toConstantVal_881_);
v___x_883_ = lean_box(0);
v___x_884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_884_, 0, v_name_882_);
lean_ctor_set(v___x_884_, 1, v___x_883_);
return v___x_884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__0(lean_object* v_f_885_, lean_object* v_value_886_, lean_object* v_a_887_){
_start:
{
lean_object* v___x_888_; 
v___x_888_ = lean_apply_2(v_f_885_, v_a_887_, v_value_886_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__3(lean_object* v_f_889_, lean_object* v_value_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = lean_apply_2(v_f_889_, v_a_891_, v_value_890_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__1(lean_object* v_f_893_, lean_object* v_toBind_894_, lean_object* v_a_895_, lean_object* v_v_896_){
_start:
{
lean_object* v_toConstantVal_897_; lean_object* v_value_898_; lean_object* v_type_899_; lean_object* v___f_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_toConstantVal_897_ = lean_ctor_get(v_v_896_, 0);
lean_inc_ref(v_toConstantVal_897_);
v_value_898_ = lean_ctor_get(v_v_896_, 1);
lean_inc_ref(v_value_898_);
lean_dec_ref(v_v_896_);
v_type_899_ = lean_ctor_get(v_toConstantVal_897_, 2);
lean_inc_ref(v_type_899_);
lean_dec_ref(v_toConstantVal_897_);
lean_inc(v_f_893_);
v___f_900_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__3), 3, 2);
lean_closure_set(v___f_900_, 0, v_f_893_);
lean_closure_set(v___f_900_, 1, v_value_898_);
v___x_901_ = lean_apply_2(v_f_893_, v_a_895_, v_type_899_);
v___x_902_ = lean_apply_4(v_toBind_894_, lean_box(0), lean_box(0), v___x_901_, v___f_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__2(lean_object* v_f_903_, lean_object* v_a_904_, lean_object* v_ctor_905_){
_start:
{
lean_object* v_type_906_; lean_object* v___x_907_; 
v_type_906_ = lean_ctor_get(v_ctor_905_, 1);
lean_inc_ref(v_type_906_);
lean_dec_ref(v_ctor_905_);
v___x_907_ = lean_apply_2(v_f_903_, v_a_904_, v_type_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__4(lean_object* v_inst_908_, lean_object* v___f_909_, lean_object* v_ctors_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_List_foldlM___redArg(v_inst_908_, v___f_909_, v_a_911_, v_ctors_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__5(lean_object* v_inst_913_, lean_object* v___f_914_, lean_object* v_f_915_, lean_object* v_toBind_916_, lean_object* v_a_917_, lean_object* v_inductType_918_){
_start:
{
lean_object* v_type_919_; lean_object* v_ctors_920_; lean_object* v___f_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
v_type_919_ = lean_ctor_get(v_inductType_918_, 1);
lean_inc_ref(v_type_919_);
v_ctors_920_ = lean_ctor_get(v_inductType_918_, 2);
lean_inc(v_ctors_920_);
lean_dec_ref(v_inductType_918_);
v___f_921_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__4), 4, 3);
lean_closure_set(v___f_921_, 0, v_inst_913_);
lean_closure_set(v___f_921_, 1, v___f_914_);
lean_closure_set(v___f_921_, 2, v_ctors_920_);
v___x_922_ = lean_apply_2(v_f_915_, v_a_917_, v_type_919_);
v___x_923_ = lean_apply_4(v_toBind_916_, lean_box(0), lean_box(0), v___x_922_, v___f_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object* v_inst_924_, lean_object* v_d_925_, lean_object* v_f_926_, lean_object* v_a_927_){
_start:
{
switch(lean_obj_tag(v_d_925_))
{
case 0:
{
lean_object* v_val_928_; lean_object* v_toConstantVal_929_; lean_object* v_type_930_; lean_object* v___x_931_; 
lean_dec_ref(v_inst_924_);
v_val_928_ = lean_ctor_get(v_d_925_, 0);
lean_inc_ref(v_val_928_);
lean_dec_ref(v_d_925_);
v_toConstantVal_929_ = lean_ctor_get(v_val_928_, 0);
lean_inc_ref(v_toConstantVal_929_);
lean_dec_ref(v_val_928_);
v_type_930_ = lean_ctor_get(v_toConstantVal_929_, 2);
lean_inc_ref(v_type_930_);
lean_dec_ref(v_toConstantVal_929_);
v___x_931_ = lean_apply_2(v_f_926_, v_a_927_, v_type_930_);
return v___x_931_;
}
case 4:
{
lean_object* v_toApplicative_932_; lean_object* v_toPure_933_; lean_object* v___x_934_; 
v_toApplicative_932_ = lean_ctor_get(v_inst_924_, 0);
lean_inc_ref(v_toApplicative_932_);
lean_dec(v_f_926_);
lean_dec_ref(v_inst_924_);
v_toPure_933_ = lean_ctor_get(v_toApplicative_932_, 1);
lean_inc(v_toPure_933_);
lean_dec_ref(v_toApplicative_932_);
v___x_934_ = lean_apply_2(v_toPure_933_, lean_box(0), v_a_927_);
return v___x_934_;
}
case 5:
{
lean_object* v_toBind_935_; lean_object* v_defns_936_; lean_object* v___f_937_; lean_object* v___x_938_; 
v_toBind_935_ = lean_ctor_get(v_inst_924_, 1);
v_defns_936_ = lean_ctor_get(v_d_925_, 0);
lean_inc(v_defns_936_);
lean_dec_ref(v_d_925_);
lean_inc(v_toBind_935_);
v___f_937_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_937_, 0, v_f_926_);
lean_closure_set(v___f_937_, 1, v_toBind_935_);
v___x_938_ = l_List_foldlM___redArg(v_inst_924_, v___f_937_, v_a_927_, v_defns_936_);
return v___x_938_;
}
case 6:
{
lean_object* v_toBind_939_; lean_object* v_types_940_; lean_object* v___f_941_; lean_object* v___f_942_; lean_object* v___x_943_; 
v_toBind_939_ = lean_ctor_get(v_inst_924_, 1);
v_types_940_ = lean_ctor_get(v_d_925_, 2);
lean_inc(v_types_940_);
lean_dec_ref(v_d_925_);
lean_inc(v_f_926_);
v___f_941_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__2), 3, 1);
lean_closure_set(v___f_941_, 0, v_f_926_);
lean_inc(v_toBind_939_);
lean_inc_ref(v_inst_924_);
v___f_942_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__5), 6, 4);
lean_closure_set(v___f_942_, 0, v_inst_924_);
lean_closure_set(v___f_942_, 1, v___f_941_);
lean_closure_set(v___f_942_, 2, v_f_926_);
lean_closure_set(v___f_942_, 3, v_toBind_939_);
v___x_943_ = l_List_foldlM___redArg(v_inst_924_, v___f_942_, v_a_927_, v_types_940_);
return v___x_943_;
}
default: 
{
lean_object* v_val_944_; lean_object* v_toConstantVal_945_; lean_object* v_toBind_946_; lean_object* v_value_947_; lean_object* v_type_948_; lean_object* v___f_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v_val_944_ = lean_ctor_get(v_d_925_, 0);
lean_inc_ref(v_val_944_);
lean_dec(v_d_925_);
v_toConstantVal_945_ = lean_ctor_get(v_val_944_, 0);
lean_inc_ref(v_toConstantVal_945_);
v_toBind_946_ = lean_ctor_get(v_inst_924_, 1);
lean_inc(v_toBind_946_);
lean_dec_ref(v_inst_924_);
v_value_947_ = lean_ctor_get(v_val_944_, 1);
lean_inc_ref(v_value_947_);
lean_dec_ref(v_val_944_);
v_type_948_ = lean_ctor_get(v_toConstantVal_945_, 2);
lean_inc_ref(v_type_948_);
lean_dec_ref(v_toConstantVal_945_);
lean_inc(v_f_926_);
v___f_949_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_949_, 0, v_f_926_);
lean_closure_set(v___f_949_, 1, v_value_947_);
v___x_950_ = lean_apply_2(v_f_926_, v_a_927_, v_type_948_);
v___x_951_ = lean_apply_4(v_toBind_946_, lean_box(0), lean_box(0), v___x_950_, v___f_949_);
return v___x_951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM(lean_object* v_00_u03b1_952_, lean_object* v_m_953_, lean_object* v_inst_954_, lean_object* v_d_955_, lean_object* v_f_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_Declaration_foldExprM___redArg(v_inst_954_, v_d_955_, v_f_956_, v_a_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg___lam__0(lean_object* v_f_959_, lean_object* v_x_960_, lean_object* v_a_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = lean_apply_1(v_f_959_, v_a_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg(lean_object* v_inst_963_, lean_object* v_d_964_, lean_object* v_f_965_){
_start:
{
lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v___f_966_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_966_, 0, v_f_965_);
v___x_967_ = lean_box(0);
v___x_968_ = l_Lean_Declaration_foldExprM___redArg(v_inst_963_, v_d_964_, v___f_966_, v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM(lean_object* v_m_969_, lean_object* v_inst_970_, lean_object* v_d_971_, lean_object* v_f_972_){
_start:
{
lean_object* v___f_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___f_973_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_973_, 0, v_f_972_);
v___x_974_ = lean_box(0);
v___x_975_ = l_Lean_Declaration_foldExprM___redArg(v_inst_970_, v_d_971_, v___f_973_, v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default___closed__0(void){
_start:
{
uint8_t v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_976_ = 0;
v___x_977_ = lean_box(0);
v___x_978_ = lean_unsigned_to_nat(0u);
v___x_979_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__3, &l_Lean_instInhabitedConstantVal_default___closed__3_once, _init_l_Lean_instInhabitedConstantVal_default___closed__3);
v___x_980_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v___x_978_);
lean_ctor_set(v___x_980_, 2, v___x_978_);
lean_ctor_set(v___x_980_, 3, v___x_977_);
lean_ctor_set(v___x_980_, 4, v___x_977_);
lean_ctor_set(v___x_980_, 5, v___x_978_);
lean_ctor_set_uint8(v___x_980_, sizeof(void*)*6, v___x_976_);
lean_ctor_set_uint8(v___x_980_, sizeof(void*)*6 + 1, v___x_976_);
lean_ctor_set_uint8(v___x_980_, sizeof(void*)*6 + 2, v___x_976_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default(void){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = lean_obj_once(&l_Lean_instInhabitedInductiveVal_default___closed__0, &l_Lean_instInhabitedInductiveVal_default___closed__0_once, _init_l_Lean_instInhabitedInductiveVal_default___closed__0);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal(void){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_instInhabitedInductiveVal_default;
return v___x_982_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_val(lean_object* v_name_983_, lean_object* v_levelParams_984_, lean_object* v_type_985_, lean_object* v_numParams_986_, lean_object* v_numIndices_987_, lean_object* v_all_988_, lean_object* v_ctors_989_, lean_object* v_numNested_990_, uint8_t v_isRec_991_, uint8_t v_isUnsafe_992_, uint8_t v_isReflexive_993_){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_994_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_994_, 0, v_name_983_);
lean_ctor_set(v___x_994_, 1, v_levelParams_984_);
lean_ctor_set(v___x_994_, 2, v_type_985_);
v___x_995_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v_numParams_986_);
lean_ctor_set(v___x_995_, 2, v_numIndices_987_);
lean_ctor_set(v___x_995_, 3, v_all_988_);
lean_ctor_set(v___x_995_, 4, v_ctors_989_);
lean_ctor_set(v___x_995_, 5, v_numNested_990_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*6, v_isRec_991_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*6 + 1, v_isUnsafe_992_);
lean_ctor_set_uint8(v___x_995_, sizeof(void*)*6 + 2, v_isReflexive_993_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveValEx___boxed(lean_object* v_name_996_, lean_object* v_levelParams_997_, lean_object* v_type_998_, lean_object* v_numParams_999_, lean_object* v_numIndices_1000_, lean_object* v_all_1001_, lean_object* v_ctors_1002_, lean_object* v_numNested_1003_, lean_object* v_isRec_1004_, lean_object* v_isUnsafe_1005_, lean_object* v_isReflexive_1006_){
_start:
{
uint8_t v_isRec_boxed_1007_; uint8_t v_isUnsafe_boxed_1008_; uint8_t v_isReflexive_boxed_1009_; lean_object* v_res_1010_; 
v_isRec_boxed_1007_ = lean_unbox(v_isRec_1004_);
v_isUnsafe_boxed_1008_ = lean_unbox(v_isUnsafe_1005_);
v_isReflexive_boxed_1009_ = lean_unbox(v_isReflexive_1006_);
v_res_1010_ = lean_mk_inductive_val(v_name_996_, v_levelParams_997_, v_type_998_, v_numParams_999_, v_numIndices_1000_, v_all_1001_, v_ctors_1002_, v_numNested_1003_, v_isRec_boxed_1007_, v_isUnsafe_boxed_1008_, v_isReflexive_boxed_1009_);
return v_res_1010_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_rec(lean_object* v_v_1011_){
_start:
{
uint8_t v_isRec_1012_; 
v_isRec_1012_ = lean_ctor_get_uint8(v_v_1011_, sizeof(void*)*6);
lean_dec_ref(v_v_1011_);
return v_isRec_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isRecEx___boxed(lean_object* v_v_1013_){
_start:
{
uint8_t v_res_1014_; lean_object* v_r_1015_; 
v_res_1014_ = lean_inductive_val_is_rec(v_v_1013_);
v_r_1015_ = lean_box(v_res_1014_);
return v_r_1015_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_unsafe(lean_object* v_v_1016_){
_start:
{
uint8_t v_isUnsafe_1017_; 
v_isUnsafe_1017_ = lean_ctor_get_uint8(v_v_1016_, sizeof(void*)*6 + 1);
lean_dec_ref(v_v_1016_);
return v_isUnsafe_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isUnsafeEx___boxed(lean_object* v_v_1018_){
_start:
{
uint8_t v_res_1019_; lean_object* v_r_1020_; 
v_res_1019_ = lean_inductive_val_is_unsafe(v_v_1018_);
v_r_1020_ = lean_box(v_res_1019_);
return v_r_1020_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_reflexive(lean_object* v_v_1021_){
_start:
{
uint8_t v_isReflexive_1022_; 
v_isReflexive_1022_ = lean_ctor_get_uint8(v_v_1021_, sizeof(void*)*6 + 2);
lean_dec_ref(v_v_1021_);
return v_isReflexive_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isReflexiveEx___boxed(lean_object* v_v_1023_){
_start:
{
uint8_t v_res_1024_; lean_object* v_r_1025_; 
v_res_1024_ = lean_inductive_val_is_reflexive(v_v_1023_);
v_r_1025_ = lean_box(v_res_1024_);
return v_r_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors(lean_object* v_v_1026_){
_start:
{
lean_object* v_ctors_1027_; lean_object* v___x_1028_; 
v_ctors_1027_ = lean_ctor_get(v_v_1026_, 4);
v___x_1028_ = l_List_lengthTR___redArg(v_ctors_1027_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors___boxed(lean_object* v_v_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_InductiveVal_numCtors(v_v_1029_);
lean_dec_ref(v_v_1029_);
return v_res_1030_;
}
}
LEAN_EXPORT uint8_t l_Lean_InductiveVal_isNested(lean_object* v_v_1031_){
_start:
{
lean_object* v_numNested_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_numNested_1032_ = lean_ctor_get(v_v_1031_, 5);
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_nat_dec_lt(v___x_1033_, v_numNested_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isNested___boxed(lean_object* v_v_1035_){
_start:
{
uint8_t v_res_1036_; lean_object* v_r_1037_; 
v_res_1036_ = l_Lean_InductiveVal_isNested(v_v_1035_);
lean_dec_ref(v_v_1035_);
v_r_1037_ = lean_box(v_res_1036_);
return v_r_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object* v_v_1038_){
_start:
{
lean_object* v_all_1039_; lean_object* v_numNested_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_all_1039_ = lean_ctor_get(v_v_1038_, 3);
v_numNested_1040_ = lean_ctor_get(v_v_1038_, 5);
v___x_1041_ = l_List_lengthTR___redArg(v_all_1039_);
v___x_1042_ = lean_nat_add(v___x_1041_, v_numNested_1040_);
lean_dec(v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers___boxed(lean_object* v_v_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Lean_InductiveVal_numTypeFormers(v_v_1043_);
lean_dec_ref(v_v_1043_);
return v_res_1044_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___x_1045_ = 0;
v___x_1046_ = lean_unsigned_to_nat(0u);
v___x_1047_ = lean_box(0);
v___x_1048_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__3, &l_Lean_instInhabitedConstantVal_default___closed__3_once, _init_l_Lean_instInhabitedConstantVal_default___closed__3);
v___x_1049_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v___x_1047_);
lean_ctor_set(v___x_1049_, 2, v___x_1046_);
lean_ctor_set(v___x_1049_, 3, v___x_1046_);
lean_ctor_set(v___x_1049_, 4, v___x_1046_);
lean_ctor_set_uint8(v___x_1049_, sizeof(void*)*5, v___x_1045_);
return v___x_1049_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default(void){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_obj_once(&l_Lean_instInhabitedConstructorVal_default___closed__0, &l_Lean_instInhabitedConstructorVal_default___closed__0_once, _init_l_Lean_instInhabitedConstructorVal_default___closed__0);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal(void){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = l_Lean_instInhabitedConstructorVal_default;
return v___x_1051_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructorVal_beq(lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
lean_object* v_toConstantVal_1054_; lean_object* v_induct_1055_; lean_object* v_cidx_1056_; lean_object* v_numParams_1057_; lean_object* v_numFields_1058_; uint8_t v_isUnsafe_1059_; lean_object* v_toConstantVal_1060_; lean_object* v_induct_1061_; lean_object* v_cidx_1062_; lean_object* v_numParams_1063_; lean_object* v_numFields_1064_; uint8_t v_isUnsafe_1065_; uint8_t v___x_1066_; 
v_toConstantVal_1054_ = lean_ctor_get(v_x_1052_, 0);
v_induct_1055_ = lean_ctor_get(v_x_1052_, 1);
v_cidx_1056_ = lean_ctor_get(v_x_1052_, 2);
v_numParams_1057_ = lean_ctor_get(v_x_1052_, 3);
v_numFields_1058_ = lean_ctor_get(v_x_1052_, 4);
v_isUnsafe_1059_ = lean_ctor_get_uint8(v_x_1052_, sizeof(void*)*5);
v_toConstantVal_1060_ = lean_ctor_get(v_x_1053_, 0);
v_induct_1061_ = lean_ctor_get(v_x_1053_, 1);
v_cidx_1062_ = lean_ctor_get(v_x_1053_, 2);
v_numParams_1063_ = lean_ctor_get(v_x_1053_, 3);
v_numFields_1064_ = lean_ctor_get(v_x_1053_, 4);
v_isUnsafe_1065_ = lean_ctor_get_uint8(v_x_1053_, sizeof(void*)*5);
v___x_1066_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1054_, v_toConstantVal_1060_);
if (v___x_1066_ == 0)
{
return v___x_1066_;
}
else
{
uint8_t v___x_1067_; 
v___x_1067_ = lean_name_eq(v_induct_1055_, v_induct_1061_);
if (v___x_1067_ == 0)
{
return v___x_1067_;
}
else
{
uint8_t v___x_1068_; 
v___x_1068_ = lean_nat_dec_eq(v_cidx_1056_, v_cidx_1062_);
if (v___x_1068_ == 0)
{
return v___x_1068_;
}
else
{
uint8_t v___x_1069_; 
v___x_1069_ = lean_nat_dec_eq(v_numParams_1057_, v_numParams_1063_);
if (v___x_1069_ == 0)
{
return v___x_1069_;
}
else
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_nat_dec_eq(v_numFields_1058_, v_numFields_1064_);
if (v___x_1070_ == 0)
{
return v___x_1070_;
}
else
{
if (v_isUnsafe_1059_ == 0)
{
if (v_isUnsafe_1065_ == 0)
{
return v___x_1070_;
}
else
{
return v_isUnsafe_1059_;
}
}
else
{
return v_isUnsafe_1065_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructorVal_beq___boxed(lean_object* v_x_1071_, lean_object* v_x_1072_){
_start:
{
uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_res_1073_ = l_Lean_instBEqConstructorVal_beq(v_x_1071_, v_x_1072_);
lean_dec_ref(v_x_1072_);
lean_dec_ref(v_x_1071_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT lean_object* lean_mk_constructor_val(lean_object* v_name_1077_, lean_object* v_levelParams_1078_, lean_object* v_type_1079_, lean_object* v_induct_1080_, lean_object* v_cidx_1081_, lean_object* v_numParams_1082_, lean_object* v_numFields_1083_, uint8_t v_isUnsafe_1084_){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1085_, 0, v_name_1077_);
lean_ctor_set(v___x_1085_, 1, v_levelParams_1078_);
lean_ctor_set(v___x_1085_, 2, v_type_1079_);
v___x_1086_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
lean_ctor_set(v___x_1086_, 1, v_induct_1080_);
lean_ctor_set(v___x_1086_, 2, v_cidx_1081_);
lean_ctor_set(v___x_1086_, 3, v_numParams_1082_);
lean_ctor_set(v___x_1086_, 4, v_numFields_1083_);
lean_ctor_set_uint8(v___x_1086_, sizeof(void*)*5, v_isUnsafe_1084_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstructorValEx___boxed(lean_object* v_name_1087_, lean_object* v_levelParams_1088_, lean_object* v_type_1089_, lean_object* v_induct_1090_, lean_object* v_cidx_1091_, lean_object* v_numParams_1092_, lean_object* v_numFields_1093_, lean_object* v_isUnsafe_1094_){
_start:
{
uint8_t v_isUnsafe_boxed_1095_; lean_object* v_res_1096_; 
v_isUnsafe_boxed_1095_ = lean_unbox(v_isUnsafe_1094_);
v_res_1096_ = lean_mk_constructor_val(v_name_1087_, v_levelParams_1088_, v_type_1089_, v_induct_1090_, v_cidx_1091_, v_numParams_1092_, v_numFields_1093_, v_isUnsafe_boxed_1095_);
return v_res_1096_;
}
}
LEAN_EXPORT uint8_t lean_constructor_val_is_unsafe(lean_object* v_v_1097_){
_start:
{
uint8_t v_isUnsafe_1098_; 
v_isUnsafe_1098_ = lean_ctor_get_uint8(v_v_1097_, sizeof(void*)*5);
lean_dec_ref(v_v_1097_);
return v_isUnsafe_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstructorVal_isUnsafeEx___boxed(lean_object* v_v_1099_){
_start:
{
uint8_t v_res_1100_; lean_object* v_r_1101_; 
v_res_1100_ = lean_constructor_val_is_unsafe(v_v_1099_);
v_r_1101_ = lean_box(v_res_1100_);
return v_r_1101_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default___closed__0(void){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1102_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_1103_ = lean_unsigned_to_nat(0u);
v___x_1104_ = lean_box(0);
v___x_1105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1104_);
lean_ctor_set(v___x_1105_, 1, v___x_1103_);
lean_ctor_set(v___x_1105_, 2, v___x_1102_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default(void){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_obj_once(&l_Lean_instInhabitedRecursorRule_default___closed__0, &l_Lean_instInhabitedRecursorRule_default___closed__0_once, _init_l_Lean_instInhabitedRecursorRule_default___closed__0);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule(void){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Lean_instInhabitedRecursorRule_default;
return v___x_1107_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorRule_beq(lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
lean_object* v_ctor_1110_; lean_object* v_nfields_1111_; lean_object* v_rhs_1112_; lean_object* v_ctor_1113_; lean_object* v_nfields_1114_; lean_object* v_rhs_1115_; uint8_t v___x_1116_; 
v_ctor_1110_ = lean_ctor_get(v_x_1108_, 0);
v_nfields_1111_ = lean_ctor_get(v_x_1108_, 1);
v_rhs_1112_ = lean_ctor_get(v_x_1108_, 2);
v_ctor_1113_ = lean_ctor_get(v_x_1109_, 0);
v_nfields_1114_ = lean_ctor_get(v_x_1109_, 1);
v_rhs_1115_ = lean_ctor_get(v_x_1109_, 2);
v___x_1116_ = lean_name_eq(v_ctor_1110_, v_ctor_1113_);
if (v___x_1116_ == 0)
{
return v___x_1116_;
}
else
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_nat_dec_eq(v_nfields_1111_, v_nfields_1114_);
if (v___x_1117_ == 0)
{
return v___x_1117_;
}
else
{
uint8_t v___x_1118_; 
v___x_1118_ = lean_expr_eqv(v_rhs_1112_, v_rhs_1115_);
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorRule_beq___boxed(lean_object* v_x_1119_, lean_object* v_x_1120_){
_start:
{
uint8_t v_res_1121_; lean_object* v_r_1122_; 
v_res_1121_ = l_Lean_instBEqRecursorRule_beq(v_x_1119_, v_x_1120_);
lean_dec_ref(v_x_1120_);
lean_dec_ref(v_x_1119_);
v_r_1122_ = lean_box(v_res_1121_);
return v_r_1122_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1125_ = 0;
v___x_1126_ = lean_unsigned_to_nat(0u);
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__3, &l_Lean_instInhabitedConstantVal_default___closed__3_once, _init_l_Lean_instInhabitedConstantVal_default___closed__3);
v___x_1129_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
lean_ctor_set(v___x_1129_, 1, v___x_1127_);
lean_ctor_set(v___x_1129_, 2, v___x_1126_);
lean_ctor_set(v___x_1129_, 3, v___x_1126_);
lean_ctor_set(v___x_1129_, 4, v___x_1126_);
lean_ctor_set(v___x_1129_, 5, v___x_1126_);
lean_ctor_set(v___x_1129_, 6, v___x_1127_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*7, v___x_1125_);
lean_ctor_set_uint8(v___x_1129_, sizeof(void*)*7 + 1, v___x_1125_);
return v___x_1129_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default(void){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_obj_once(&l_Lean_instInhabitedRecursorVal_default___closed__0, &l_Lean_instInhabitedRecursorVal_default___closed__0_once, _init_l_Lean_instInhabitedRecursorVal_default___closed__0);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal(void){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_instInhabitedRecursorVal_default;
return v___x_1131_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(lean_object* v_x_1132_, lean_object* v_x_1133_){
_start:
{
if (lean_obj_tag(v_x_1132_) == 0)
{
if (lean_obj_tag(v_x_1133_) == 0)
{
uint8_t v___x_1134_; 
v___x_1134_ = 1;
return v___x_1134_;
}
else
{
uint8_t v___x_1135_; 
v___x_1135_ = 0;
return v___x_1135_;
}
}
else
{
if (lean_obj_tag(v_x_1133_) == 0)
{
uint8_t v___x_1136_; 
v___x_1136_ = 0;
return v___x_1136_;
}
else
{
lean_object* v_head_1137_; lean_object* v_tail_1138_; lean_object* v_head_1139_; lean_object* v_tail_1140_; uint8_t v___x_1141_; 
v_head_1137_ = lean_ctor_get(v_x_1132_, 0);
v_tail_1138_ = lean_ctor_get(v_x_1132_, 1);
v_head_1139_ = lean_ctor_get(v_x_1133_, 0);
v_tail_1140_ = lean_ctor_get(v_x_1133_, 1);
v___x_1141_ = l_Lean_instBEqRecursorRule_beq(v_head_1137_, v_head_1139_);
if (v___x_1141_ == 0)
{
return v___x_1141_;
}
else
{
v_x_1132_ = v_tail_1138_;
v_x_1133_ = v_tail_1140_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0___boxed(lean_object* v_x_1143_, lean_object* v_x_1144_){
_start:
{
uint8_t v_res_1145_; lean_object* v_r_1146_; 
v_res_1145_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_x_1143_, v_x_1144_);
lean_dec(v_x_1144_);
lean_dec(v_x_1143_);
v_r_1146_ = lean_box(v_res_1145_);
return v_r_1146_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorVal_beq(lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
lean_object* v_toConstantVal_1149_; lean_object* v_all_1150_; lean_object* v_numParams_1151_; lean_object* v_numIndices_1152_; lean_object* v_numMotives_1153_; lean_object* v_numMinors_1154_; lean_object* v_rules_1155_; uint8_t v_k_1156_; uint8_t v_isUnsafe_1157_; lean_object* v_toConstantVal_1158_; lean_object* v_all_1159_; lean_object* v_numParams_1160_; lean_object* v_numIndices_1161_; lean_object* v_numMotives_1162_; lean_object* v_numMinors_1163_; lean_object* v_rules_1164_; uint8_t v_k_1165_; uint8_t v_isUnsafe_1166_; uint8_t v___y_1168_; uint8_t v___x_1169_; 
v_toConstantVal_1149_ = lean_ctor_get(v_x_1147_, 0);
v_all_1150_ = lean_ctor_get(v_x_1147_, 1);
v_numParams_1151_ = lean_ctor_get(v_x_1147_, 2);
v_numIndices_1152_ = lean_ctor_get(v_x_1147_, 3);
v_numMotives_1153_ = lean_ctor_get(v_x_1147_, 4);
v_numMinors_1154_ = lean_ctor_get(v_x_1147_, 5);
v_rules_1155_ = lean_ctor_get(v_x_1147_, 6);
v_k_1156_ = lean_ctor_get_uint8(v_x_1147_, sizeof(void*)*7);
v_isUnsafe_1157_ = lean_ctor_get_uint8(v_x_1147_, sizeof(void*)*7 + 1);
v_toConstantVal_1158_ = lean_ctor_get(v_x_1148_, 0);
v_all_1159_ = lean_ctor_get(v_x_1148_, 1);
v_numParams_1160_ = lean_ctor_get(v_x_1148_, 2);
v_numIndices_1161_ = lean_ctor_get(v_x_1148_, 3);
v_numMotives_1162_ = lean_ctor_get(v_x_1148_, 4);
v_numMinors_1163_ = lean_ctor_get(v_x_1148_, 5);
v_rules_1164_ = lean_ctor_get(v_x_1148_, 6);
v_k_1165_ = lean_ctor_get_uint8(v_x_1148_, sizeof(void*)*7);
v_isUnsafe_1166_ = lean_ctor_get_uint8(v_x_1148_, sizeof(void*)*7 + 1);
v___x_1169_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1149_, v_toConstantVal_1158_);
if (v___x_1169_ == 0)
{
return v___x_1169_;
}
else
{
uint8_t v___x_1170_; 
v___x_1170_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_1150_, v_all_1159_);
if (v___x_1170_ == 0)
{
return v___x_1170_;
}
else
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_nat_dec_eq(v_numParams_1151_, v_numParams_1160_);
if (v___x_1171_ == 0)
{
return v___x_1171_;
}
else
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_nat_dec_eq(v_numIndices_1152_, v_numIndices_1161_);
if (v___x_1172_ == 0)
{
return v___x_1172_;
}
else
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_nat_dec_eq(v_numMotives_1153_, v_numMotives_1162_);
if (v___x_1173_ == 0)
{
return v___x_1173_;
}
else
{
uint8_t v___x_1174_; 
v___x_1174_ = lean_nat_dec_eq(v_numMinors_1154_, v_numMinors_1163_);
if (v___x_1174_ == 0)
{
return v___x_1174_;
}
else
{
uint8_t v___x_1175_; 
v___x_1175_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_rules_1155_, v_rules_1164_);
if (v___x_1175_ == 0)
{
return v___x_1175_;
}
else
{
if (v_k_1156_ == 0)
{
if (v_k_1165_ == 0)
{
v___y_1168_ = v___x_1175_;
goto v___jp_1167_;
}
else
{
return v_k_1156_;
}
}
else
{
v___y_1168_ = v_k_1165_;
goto v___jp_1167_;
}
}
}
}
}
}
}
}
v___jp_1167_:
{
if (v___y_1168_ == 0)
{
return v___y_1168_;
}
else
{
if (v_isUnsafe_1157_ == 0)
{
if (v_isUnsafe_1166_ == 0)
{
return v___y_1168_;
}
else
{
return v_isUnsafe_1157_;
}
}
else
{
return v_isUnsafe_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorVal_beq___boxed(lean_object* v_x_1176_, lean_object* v_x_1177_){
_start:
{
uint8_t v_res_1178_; lean_object* v_r_1179_; 
v_res_1178_ = l_Lean_instBEqRecursorVal_beq(v_x_1176_, v_x_1177_);
lean_dec_ref(v_x_1177_);
lean_dec_ref(v_x_1176_);
v_r_1179_ = lean_box(v_res_1178_);
return v_r_1179_;
}
}
LEAN_EXPORT lean_object* lean_mk_recursor_val(lean_object* v_name_1182_, lean_object* v_levelParams_1183_, lean_object* v_type_1184_, lean_object* v_all_1185_, lean_object* v_numParams_1186_, lean_object* v_numIndices_1187_, lean_object* v_numMotives_1188_, lean_object* v_numMinors_1189_, lean_object* v_rules_1190_, uint8_t v_k_1191_, uint8_t v_isUnsafe_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1193_, 0, v_name_1182_);
lean_ctor_set(v___x_1193_, 1, v_levelParams_1183_);
lean_ctor_set(v___x_1193_, 2, v_type_1184_);
v___x_1194_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v_all_1185_);
lean_ctor_set(v___x_1194_, 2, v_numParams_1186_);
lean_ctor_set(v___x_1194_, 3, v_numIndices_1187_);
lean_ctor_set(v___x_1194_, 4, v_numMotives_1188_);
lean_ctor_set(v___x_1194_, 5, v_numMinors_1189_);
lean_ctor_set(v___x_1194_, 6, v_rules_1190_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*7, v_k_1191_);
lean_ctor_set_uint8(v___x_1194_, sizeof(void*)*7 + 1, v_isUnsafe_1192_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecursorValEx___boxed(lean_object* v_name_1195_, lean_object* v_levelParams_1196_, lean_object* v_type_1197_, lean_object* v_all_1198_, lean_object* v_numParams_1199_, lean_object* v_numIndices_1200_, lean_object* v_numMotives_1201_, lean_object* v_numMinors_1202_, lean_object* v_rules_1203_, lean_object* v_k_1204_, lean_object* v_isUnsafe_1205_){
_start:
{
uint8_t v_k_boxed_1206_; uint8_t v_isUnsafe_boxed_1207_; lean_object* v_res_1208_; 
v_k_boxed_1206_ = lean_unbox(v_k_1204_);
v_isUnsafe_boxed_1207_ = lean_unbox(v_isUnsafe_1205_);
v_res_1208_ = lean_mk_recursor_val(v_name_1195_, v_levelParams_1196_, v_type_1197_, v_all_1198_, v_numParams_1199_, v_numIndices_1200_, v_numMotives_1201_, v_numMinors_1202_, v_rules_1203_, v_k_boxed_1206_, v_isUnsafe_boxed_1207_);
return v_res_1208_;
}
}
LEAN_EXPORT uint8_t lean_recursor_k(lean_object* v_v_1209_){
_start:
{
uint8_t v_k_1210_; 
v_k_1210_ = lean_ctor_get_uint8(v_v_1209_, sizeof(void*)*7);
lean_dec_ref(v_v_1209_);
return v_k_1210_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_kEx___boxed(lean_object* v_v_1211_){
_start:
{
uint8_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = lean_recursor_k(v_v_1211_);
v_r_1213_ = lean_box(v_res_1212_);
return v_r_1213_;
}
}
LEAN_EXPORT uint8_t lean_recursor_is_unsafe(lean_object* v_v_1214_){
_start:
{
uint8_t v_isUnsafe_1215_; 
v_isUnsafe_1215_ = lean_ctor_get_uint8(v_v_1214_, sizeof(void*)*7 + 1);
lean_dec_ref(v_v_1214_);
return v_isUnsafe_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_isUnsafeEx___boxed(lean_object* v_v_1216_){
_start:
{
uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_res_1217_ = lean_recursor_is_unsafe(v_v_1216_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object* v_v_1219_){
_start:
{
lean_object* v_numParams_1220_; lean_object* v_numIndices_1221_; lean_object* v_numMotives_1222_; lean_object* v_numMinors_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v_numParams_1220_ = lean_ctor_get(v_v_1219_, 2);
v_numIndices_1221_ = lean_ctor_get(v_v_1219_, 3);
v_numMotives_1222_ = lean_ctor_get(v_v_1219_, 4);
v_numMinors_1223_ = lean_ctor_get(v_v_1219_, 5);
v___x_1224_ = lean_nat_add(v_numParams_1220_, v_numMotives_1222_);
v___x_1225_ = lean_nat_add(v___x_1224_, v_numMinors_1223_);
lean_dec(v___x_1224_);
v___x_1226_ = lean_nat_add(v___x_1225_, v_numIndices_1221_);
lean_dec(v___x_1225_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx___boxed(lean_object* v_v_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_RecursorVal_getMajorIdx(v_v_1227_);
lean_dec_ref(v_v_1227_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx(lean_object* v_v_1229_){
_start:
{
lean_object* v_numParams_1230_; lean_object* v_numMotives_1231_; lean_object* v_numMinors_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_numParams_1230_ = lean_ctor_get(v_v_1229_, 2);
v_numMotives_1231_ = lean_ctor_get(v_v_1229_, 4);
v_numMinors_1232_ = lean_ctor_get(v_v_1229_, 5);
v___x_1233_ = lean_nat_add(v_numParams_1230_, v_numMotives_1231_);
v___x_1234_ = lean_nat_add(v___x_1233_, v_numMinors_1232_);
lean_dec(v___x_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx___boxed(lean_object* v_v_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_RecursorVal_getFirstIndexIdx(v_v_1235_);
lean_dec_ref(v_v_1235_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx(lean_object* v_v_1237_){
_start:
{
lean_object* v_numParams_1238_; lean_object* v_numMotives_1239_; lean_object* v___x_1240_; 
v_numParams_1238_ = lean_ctor_get(v_v_1237_, 2);
v_numMotives_1239_ = lean_ctor_get(v_v_1237_, 4);
v___x_1240_ = lean_nat_add(v_numParams_1238_, v_numMotives_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx___boxed(lean_object* v_v_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_RecursorVal_getFirstMinorIdx(v_v_1241_);
lean_dec_ref(v_v_1241_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(lean_object* v_x_1243_, lean_object* v_x_1244_){
_start:
{
lean_object* v_zero_1245_; uint8_t v_isZero_1246_; 
v_zero_1245_ = lean_unsigned_to_nat(0u);
v_isZero_1246_ = lean_nat_dec_eq(v_x_1243_, v_zero_1245_);
if (v_isZero_1246_ == 1)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
lean_dec(v_x_1243_);
v___x_1247_ = l_Lean_Expr_bindingDomain_x21(v_x_1244_);
lean_dec_ref(v_x_1244_);
v___x_1248_ = l_Lean_Expr_getAppFn(v___x_1247_);
lean_dec_ref(v___x_1247_);
v___x_1249_ = l_Lean_Expr_constName_x21(v___x_1248_);
lean_dec_ref(v___x_1248_);
return v___x_1249_;
}
else
{
lean_object* v_one_1250_; lean_object* v_n_1251_; lean_object* v___x_1252_; 
v_one_1250_ = lean_unsigned_to_nat(1u);
v_n_1251_ = lean_nat_sub(v_x_1243_, v_one_1250_);
lean_dec(v_x_1243_);
v___x_1252_ = l_Lean_Expr_bindingBody_x21(v_x_1244_);
lean_dec_ref(v_x_1244_);
v_x_1243_ = v_n_1251_;
v_x_1244_ = v___x_1252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorInduct(lean_object* v_v_1254_){
_start:
{
lean_object* v_toConstantVal_1255_; lean_object* v_type_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v_toConstantVal_1255_ = lean_ctor_get(v_v_1254_, 0);
v_type_1256_ = lean_ctor_get(v_toConstantVal_1255_, 2);
lean_inc_ref(v_type_1256_);
v___x_1257_ = l_Lean_RecursorVal_getMajorIdx(v_v_1254_);
lean_dec_ref(v_v_1254_);
v___x_1258_ = l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(v___x_1257_, v_type_1256_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx(uint8_t v_x_1259_){
_start:
{
switch(v_x_1259_)
{
case 0:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_unsigned_to_nat(0u);
return v___x_1260_;
}
case 1:
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_unsigned_to_nat(1u);
return v___x_1261_;
}
case 2:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_unsigned_to_nat(2u);
return v___x_1262_;
}
default: 
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_unsigned_to_nat(3u);
return v___x_1263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___boxed(lean_object* v_x_1264_){
_start:
{
uint8_t v_x_boxed_1265_; lean_object* v_res_1266_; 
v_x_boxed_1265_ = lean_unbox(v_x_1264_);
v_res_1266_ = l_Lean_QuotKind_ctorIdx(v_x_boxed_1265_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_toCtorIdx(uint8_t v_x_1267_){
_start:
{
lean_object* v___x_1268_; 
v___x_1268_ = l_Lean_QuotKind_ctorIdx(v_x_1267_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_toCtorIdx___boxed(lean_object* v_x_1269_){
_start:
{
uint8_t v_x_4__boxed_1270_; lean_object* v_res_1271_; 
v_x_4__boxed_1270_ = lean_unbox(v_x_1269_);
v_res_1271_ = l_Lean_QuotKind_toCtorIdx(v_x_4__boxed_1270_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg(lean_object* v_k_1272_){
_start:
{
lean_inc(v_k_1272_);
return v_k_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg___boxed(lean_object* v_k_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_QuotKind_ctorElim___redArg(v_k_1273_);
lean_dec(v_k_1273_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim(lean_object* v_motive_1275_, lean_object* v_ctorIdx_1276_, uint8_t v_t_1277_, lean_object* v_h_1278_, lean_object* v_k_1279_){
_start:
{
lean_inc(v_k_1279_);
return v_k_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___boxed(lean_object* v_motive_1280_, lean_object* v_ctorIdx_1281_, lean_object* v_t_1282_, lean_object* v_h_1283_, lean_object* v_k_1284_){
_start:
{
uint8_t v_t_boxed_1285_; lean_object* v_res_1286_; 
v_t_boxed_1285_ = lean_unbox(v_t_1282_);
v_res_1286_ = l_Lean_QuotKind_ctorElim(v_motive_1280_, v_ctorIdx_1281_, v_t_boxed_1285_, v_h_1283_, v_k_1284_);
lean_dec(v_k_1284_);
lean_dec(v_ctorIdx_1281_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg(lean_object* v_type_1287_){
_start:
{
lean_inc(v_type_1287_);
return v_type_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg___boxed(lean_object* v_type_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_QuotKind_type_elim___redArg(v_type_1288_);
lean_dec(v_type_1288_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim(lean_object* v_motive_1290_, uint8_t v_t_1291_, lean_object* v_h_1292_, lean_object* v_type_1293_){
_start:
{
lean_inc(v_type_1293_);
return v_type_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___boxed(lean_object* v_motive_1294_, lean_object* v_t_1295_, lean_object* v_h_1296_, lean_object* v_type_1297_){
_start:
{
uint8_t v_t_boxed_1298_; lean_object* v_res_1299_; 
v_t_boxed_1298_ = lean_unbox(v_t_1295_);
v_res_1299_ = l_Lean_QuotKind_type_elim(v_motive_1294_, v_t_boxed_1298_, v_h_1296_, v_type_1297_);
lean_dec(v_type_1297_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg(lean_object* v_ctor_1300_){
_start:
{
lean_inc(v_ctor_1300_);
return v_ctor_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg___boxed(lean_object* v_ctor_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Lean_QuotKind_ctor_elim___redArg(v_ctor_1301_);
lean_dec(v_ctor_1301_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim(lean_object* v_motive_1303_, uint8_t v_t_1304_, lean_object* v_h_1305_, lean_object* v_ctor_1306_){
_start:
{
lean_inc(v_ctor_1306_);
return v_ctor_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___boxed(lean_object* v_motive_1307_, lean_object* v_t_1308_, lean_object* v_h_1309_, lean_object* v_ctor_1310_){
_start:
{
uint8_t v_t_boxed_1311_; lean_object* v_res_1312_; 
v_t_boxed_1311_ = lean_unbox(v_t_1308_);
v_res_1312_ = l_Lean_QuotKind_ctor_elim(v_motive_1307_, v_t_boxed_1311_, v_h_1309_, v_ctor_1310_);
lean_dec(v_ctor_1310_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg(lean_object* v_lift_1313_){
_start:
{
lean_inc(v_lift_1313_);
return v_lift_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg___boxed(lean_object* v_lift_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_QuotKind_lift_elim___redArg(v_lift_1314_);
lean_dec(v_lift_1314_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim(lean_object* v_motive_1316_, uint8_t v_t_1317_, lean_object* v_h_1318_, lean_object* v_lift_1319_){
_start:
{
lean_inc(v_lift_1319_);
return v_lift_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___boxed(lean_object* v_motive_1320_, lean_object* v_t_1321_, lean_object* v_h_1322_, lean_object* v_lift_1323_){
_start:
{
uint8_t v_t_boxed_1324_; lean_object* v_res_1325_; 
v_t_boxed_1324_ = lean_unbox(v_t_1321_);
v_res_1325_ = l_Lean_QuotKind_lift_elim(v_motive_1320_, v_t_boxed_1324_, v_h_1322_, v_lift_1323_);
lean_dec(v_lift_1323_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg(lean_object* v_ind_1326_){
_start:
{
lean_inc(v_ind_1326_);
return v_ind_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg___boxed(lean_object* v_ind_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_QuotKind_ind_elim___redArg(v_ind_1327_);
lean_dec(v_ind_1327_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim(lean_object* v_motive_1329_, uint8_t v_t_1330_, lean_object* v_h_1331_, lean_object* v_ind_1332_){
_start:
{
lean_inc(v_ind_1332_);
return v_ind_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___boxed(lean_object* v_motive_1333_, lean_object* v_t_1334_, lean_object* v_h_1335_, lean_object* v_ind_1336_){
_start:
{
uint8_t v_t_boxed_1337_; lean_object* v_res_1338_; 
v_t_boxed_1337_ = lean_unbox(v_t_1334_);
v_res_1338_ = l_Lean_QuotKind_ind_elim(v_motive_1333_, v_t_boxed_1337_, v_h_1335_, v_ind_1336_);
lean_dec(v_ind_1336_);
return v_res_1338_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind_default(void){
_start:
{
uint8_t v___x_1339_; 
v___x_1339_ = 0;
return v___x_1339_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind(void){
_start:
{
uint8_t v___x_1340_; 
v___x_1340_ = 0;
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default___closed__0(void){
_start:
{
uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = 0;
v___x_1342_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__3, &l_Lean_instInhabitedConstantVal_default___closed__3_once, _init_l_Lean_instInhabitedConstantVal_default___closed__3);
v___x_1343_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set_uint8(v___x_1343_, sizeof(void*)*1, v___x_1341_);
return v___x_1343_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default(void){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = lean_obj_once(&l_Lean_instInhabitedQuotVal_default___closed__0, &l_Lean_instInhabitedQuotVal_default___closed__0_once, _init_l_Lean_instInhabitedQuotVal_default___closed__0);
return v___x_1344_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal(void){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Lean_instInhabitedQuotVal_default;
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* lean_mk_quot_val(lean_object* v_name_1346_, lean_object* v_levelParams_1347_, lean_object* v_type_1348_, uint8_t v_kind_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; 
v___x_1350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1350_, 0, v_name_1346_);
lean_ctor_set(v___x_1350_, 1, v_levelParams_1347_);
lean_ctor_set(v___x_1350_, 2, v_type_1348_);
v___x_1351_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*1, v_kind_1349_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkQuotValEx___boxed(lean_object* v_name_1352_, lean_object* v_levelParams_1353_, lean_object* v_type_1354_, lean_object* v_kind_1355_){
_start:
{
uint8_t v_kind_boxed_1356_; lean_object* v_res_1357_; 
v_kind_boxed_1356_ = lean_unbox(v_kind_1355_);
v_res_1357_ = lean_mk_quot_val(v_name_1352_, v_levelParams_1353_, v_type_1354_, v_kind_boxed_1356_);
return v_res_1357_;
}
}
LEAN_EXPORT uint8_t lean_quot_val_kind(lean_object* v_v_1358_){
_start:
{
uint8_t v_kind_1359_; 
v_kind_1359_ = lean_ctor_get_uint8(v_v_1358_, sizeof(void*)*1);
lean_dec_ref(v_v_1358_);
return v_kind_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotVal_kindEx___boxed(lean_object* v_v_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = lean_quot_val_kind(v_v_1360_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx(lean_object* v_x_1363_){
_start:
{
switch(lean_obj_tag(v_x_1363_))
{
case 0:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_unsigned_to_nat(0u);
return v___x_1364_;
}
case 1:
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_unsigned_to_nat(1u);
return v___x_1365_;
}
case 2:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_unsigned_to_nat(2u);
return v___x_1366_;
}
case 3:
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_unsigned_to_nat(3u);
return v___x_1367_;
}
case 4:
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_unsigned_to_nat(4u);
return v___x_1368_;
}
case 5:
{
lean_object* v___x_1369_; 
v___x_1369_ = lean_unsigned_to_nat(5u);
return v___x_1369_;
}
case 6:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_unsigned_to_nat(6u);
return v___x_1370_;
}
default: 
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_unsigned_to_nat(7u);
return v___x_1371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___boxed(lean_object* v_x_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_ConstantInfo_ctorIdx(v_x_1372_);
lean_dec_ref(v_x_1372_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___redArg(lean_object* v_t_1374_, lean_object* v_k_1375_){
_start:
{
lean_object* v_val_1376_; lean_object* v___x_1377_; 
v_val_1376_ = lean_ctor_get(v_t_1374_, 0);
lean_inc_ref(v_val_1376_);
lean_dec_ref(v_t_1374_);
v___x_1377_ = lean_apply_1(v_k_1375_, v_val_1376_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim(lean_object* v_motive_1378_, lean_object* v_ctorIdx_1379_, lean_object* v_t_1380_, lean_object* v_h_1381_, lean_object* v_k_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1380_, v_k_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___boxed(lean_object* v_motive_1384_, lean_object* v_ctorIdx_1385_, lean_object* v_t_1386_, lean_object* v_h_1387_, lean_object* v_k_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lean_ConstantInfo_ctorElim(v_motive_1384_, v_ctorIdx_1385_, v_t_1386_, v_h_1387_, v_k_1388_);
lean_dec(v_ctorIdx_1385_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim___redArg(lean_object* v_t_1390_, lean_object* v_axiomInfo_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1390_, v_axiomInfo_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim(lean_object* v_motive_1393_, lean_object* v_t_1394_, lean_object* v_h_1395_, lean_object* v_axiomInfo_1396_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1394_, v_axiomInfo_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim___redArg(lean_object* v_t_1398_, lean_object* v_defnInfo_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1398_, v_defnInfo_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim(lean_object* v_motive_1401_, lean_object* v_t_1402_, lean_object* v_h_1403_, lean_object* v_defnInfo_1404_){
_start:
{
lean_object* v___x_1405_; 
v___x_1405_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1402_, v_defnInfo_1404_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim___redArg(lean_object* v_t_1406_, lean_object* v_thmInfo_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1406_, v_thmInfo_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim(lean_object* v_motive_1409_, lean_object* v_t_1410_, lean_object* v_h_1411_, lean_object* v_thmInfo_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1410_, v_thmInfo_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim___redArg(lean_object* v_t_1414_, lean_object* v_opaqueInfo_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1414_, v_opaqueInfo_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim(lean_object* v_motive_1417_, lean_object* v_t_1418_, lean_object* v_h_1419_, lean_object* v_opaqueInfo_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1418_, v_opaqueInfo_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim___redArg(lean_object* v_t_1422_, lean_object* v_quotInfo_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1422_, v_quotInfo_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim(lean_object* v_motive_1425_, lean_object* v_t_1426_, lean_object* v_h_1427_, lean_object* v_quotInfo_1428_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1426_, v_quotInfo_1428_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim___redArg(lean_object* v_t_1430_, lean_object* v_inductInfo_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1430_, v_inductInfo_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim(lean_object* v_motive_1433_, lean_object* v_t_1434_, lean_object* v_h_1435_, lean_object* v_inductInfo_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1434_, v_inductInfo_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim___redArg(lean_object* v_t_1438_, lean_object* v_ctorInfo_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1438_, v_ctorInfo_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim(lean_object* v_motive_1441_, lean_object* v_t_1442_, lean_object* v_h_1443_, lean_object* v_ctorInfo_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1442_, v_ctorInfo_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim___redArg(lean_object* v_t_1446_, lean_object* v_recInfo_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1446_, v_recInfo_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim(lean_object* v_motive_1449_, lean_object* v_t_1450_, lean_object* v_h_1451_, lean_object* v_recInfo_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1450_, v_recInfo_1452_);
return v___x_1453_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default___closed__0(void){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = l_Lean_instInhabitedAxiomVal_default;
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default(void){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_obj_once(&l_Lean_instInhabitedConstantInfo_default___closed__0, &l_Lean_instInhabitedConstantInfo_default___closed__0_once, _init_l_Lean_instInhabitedConstantInfo_default___closed__0);
return v___x_1456_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo(void){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_instInhabitedConstantInfo_default;
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object* v_x_1458_){
_start:
{
lean_object* v_val_1459_; lean_object* v_toConstantVal_1460_; 
v_val_1459_ = lean_ctor_get(v_x_1458_, 0);
v_toConstantVal_1460_ = lean_ctor_get(v_val_1459_, 0);
lean_inc_ref(v_toConstantVal_1460_);
return v_toConstantVal_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object* v_x_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l_Lean_ConstantInfo_toConstantVal(v_x_1461_);
lean_dec_ref(v_x_1461_);
return v_res_1462_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object* v_x_1463_){
_start:
{
switch(lean_obj_tag(v_x_1463_))
{
case 0:
{
lean_object* v_val_1464_; uint8_t v_isUnsafe_1465_; 
v_val_1464_ = lean_ctor_get(v_x_1463_, 0);
v_isUnsafe_1465_ = lean_ctor_get_uint8(v_val_1464_, sizeof(void*)*1);
return v_isUnsafe_1465_;
}
case 1:
{
lean_object* v_val_1466_; uint8_t v_safety_1467_; uint8_t v___x_1468_; uint8_t v___x_1469_; 
v_val_1466_ = lean_ctor_get(v_x_1463_, 0);
v_safety_1467_ = lean_ctor_get_uint8(v_val_1466_, sizeof(void*)*4);
v___x_1468_ = 0;
v___x_1469_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1467_, v___x_1468_);
return v___x_1469_;
}
case 3:
{
lean_object* v_val_1470_; uint8_t v_isUnsafe_1471_; 
v_val_1470_ = lean_ctor_get(v_x_1463_, 0);
v_isUnsafe_1471_ = lean_ctor_get_uint8(v_val_1470_, sizeof(void*)*3);
return v_isUnsafe_1471_;
}
case 5:
{
lean_object* v_val_1472_; uint8_t v_isUnsafe_1473_; 
v_val_1472_ = lean_ctor_get(v_x_1463_, 0);
v_isUnsafe_1473_ = lean_ctor_get_uint8(v_val_1472_, sizeof(void*)*6 + 1);
return v_isUnsafe_1473_;
}
case 6:
{
lean_object* v_val_1474_; uint8_t v_isUnsafe_1475_; 
v_val_1474_ = lean_ctor_get(v_x_1463_, 0);
v_isUnsafe_1475_ = lean_ctor_get_uint8(v_val_1474_, sizeof(void*)*5);
return v_isUnsafe_1475_;
}
case 7:
{
lean_object* v_val_1476_; uint8_t v_isUnsafe_1477_; 
v_val_1476_ = lean_ctor_get(v_x_1463_, 0);
v_isUnsafe_1477_ = lean_ctor_get_uint8(v_val_1476_, sizeof(void*)*7 + 1);
return v_isUnsafe_1477_;
}
default: 
{
uint8_t v___x_1478_; 
v___x_1478_ = 0;
return v___x_1478_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isUnsafe___boxed(lean_object* v_x_1479_){
_start:
{
uint8_t v_res_1480_; lean_object* v_r_1481_; 
v_res_1480_ = l_Lean_ConstantInfo_isUnsafe(v_x_1479_);
lean_dec_ref(v_x_1479_);
v_r_1481_ = lean_box(v_res_1480_);
return v_r_1481_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isPartial(lean_object* v_x_1482_){
_start:
{
if (lean_obj_tag(v_x_1482_) == 1)
{
lean_object* v_val_1483_; uint8_t v_safety_1484_; uint8_t v___x_1485_; uint8_t v___x_1486_; 
v_val_1483_ = lean_ctor_get(v_x_1482_, 0);
v_safety_1484_ = lean_ctor_get_uint8(v_val_1483_, sizeof(void*)*4);
v___x_1485_ = 2;
v___x_1486_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1484_, v___x_1485_);
return v___x_1486_;
}
else
{
uint8_t v___x_1487_; 
v___x_1487_ = 0;
return v___x_1487_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isPartial___boxed(lean_object* v_x_1488_){
_start:
{
uint8_t v_res_1489_; lean_object* v_r_1490_; 
v_res_1489_ = l_Lean_ConstantInfo_isPartial(v_x_1488_);
lean_dec_ref(v_x_1488_);
v_r_1490_ = lean_box(v_res_1489_);
return v_r_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name(lean_object* v_d_1491_){
_start:
{
lean_object* v___x_1492_; lean_object* v_name_1493_; 
v___x_1492_ = l_Lean_ConstantInfo_toConstantVal(v_d_1491_);
v_name_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_name_1493_);
lean_dec_ref(v___x_1492_);
return v_name_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name___boxed(lean_object* v_d_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_ConstantInfo_name(v_d_1494_);
lean_dec_ref(v_d_1494_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams(lean_object* v_d_1496_){
_start:
{
lean_object* v___x_1497_; lean_object* v_levelParams_1498_; 
v___x_1497_ = l_Lean_ConstantInfo_toConstantVal(v_d_1496_);
v_levelParams_1498_ = lean_ctor_get(v___x_1497_, 1);
lean_inc(v_levelParams_1498_);
lean_dec_ref(v___x_1497_);
return v_levelParams_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams___boxed(lean_object* v_d_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_ConstantInfo_levelParams(v_d_1499_);
lean_dec_ref(v_d_1499_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object* v_d_1501_){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = l_Lean_ConstantInfo_levelParams(v_d_1501_);
v___x_1503_ = l_List_lengthTR___redArg(v___x_1502_);
lean_dec(v___x_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams___boxed(lean_object* v_d_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_ConstantInfo_numLevelParams(v_d_1504_);
lean_dec_ref(v_d_1504_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type(lean_object* v_d_1506_){
_start:
{
lean_object* v___x_1507_; lean_object* v_type_1508_; 
v___x_1507_ = l_Lean_ConstantInfo_toConstantVal(v_d_1506_);
v_type_1508_ = lean_ctor_get(v___x_1507_, 2);
lean_inc_ref(v_type_1508_);
lean_dec_ref(v___x_1507_);
return v_type_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type___boxed(lean_object* v_d_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_ConstantInfo_type(v_d_1509_);
lean_dec_ref(v_d_1509_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f(lean_object* v_info_1511_, uint8_t v_allowOpaque_1512_){
_start:
{
switch(lean_obj_tag(v_info_1511_))
{
case 1:
{
lean_object* v_val_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1521_; 
v_val_1513_ = lean_ctor_get(v_info_1511_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_info_1511_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1515_ = v_info_1511_;
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_val_1513_);
lean_dec(v_info_1511_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v_value_1517_; lean_object* v___x_1519_; 
v_value_1517_ = lean_ctor_get(v_val_1513_, 1);
lean_inc_ref(v_value_1517_);
lean_dec_ref(v_val_1513_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 0, v_value_1517_);
v___x_1519_ = v___x_1515_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_value_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
case 2:
{
lean_object* v_val_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1531_; 
v_val_1522_ = lean_ctor_get(v_info_1511_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v_info_1511_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1524_ = v_info_1511_;
v_isShared_1525_ = v_isSharedCheck_1531_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_val_1522_);
lean_dec(v_info_1511_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1531_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
if (v_allowOpaque_1512_ == 0)
{
lean_object* v___x_1526_; 
lean_del_object(v___x_1524_);
lean_dec_ref(v_val_1522_);
v___x_1526_ = lean_box(0);
return v___x_1526_;
}
else
{
lean_object* v_value_1527_; lean_object* v___x_1529_; 
v_value_1527_ = lean_ctor_get(v_val_1522_, 1);
lean_inc_ref(v_value_1527_);
lean_dec_ref(v_val_1522_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set_tag(v___x_1524_, 1);
lean_ctor_set(v___x_1524_, 0, v_value_1527_);
v___x_1529_ = v___x_1524_;
goto v_reusejp_1528_;
}
else
{
lean_object* v_reuseFailAlloc_1530_; 
v_reuseFailAlloc_1530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_value_1527_);
v___x_1529_ = v_reuseFailAlloc_1530_;
goto v_reusejp_1528_;
}
v_reusejp_1528_:
{
return v___x_1529_;
}
}
}
}
case 3:
{
lean_object* v_val_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1541_; 
v_val_1532_ = lean_ctor_get(v_info_1511_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_info_1511_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1534_ = v_info_1511_;
v_isShared_1535_ = v_isSharedCheck_1541_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_val_1532_);
lean_dec(v_info_1511_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1541_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
if (v_allowOpaque_1512_ == 0)
{
lean_object* v___x_1536_; 
lean_del_object(v___x_1534_);
lean_dec_ref(v_val_1532_);
v___x_1536_ = lean_box(0);
return v___x_1536_;
}
else
{
lean_object* v_value_1537_; lean_object* v___x_1539_; 
v_value_1537_ = lean_ctor_get(v_val_1532_, 1);
lean_inc_ref(v_value_1537_);
lean_dec_ref(v_val_1532_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set_tag(v___x_1534_, 1);
lean_ctor_set(v___x_1534_, 0, v_value_1537_);
v___x_1539_ = v___x_1534_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_value_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
default: 
{
lean_object* v___x_1542_; 
lean_dec_ref(v_info_1511_);
v___x_1542_ = lean_box(0);
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f___boxed(lean_object* v_info_1543_, lean_object* v_allowOpaque_1544_){
_start:
{
uint8_t v_allowOpaque_boxed_1545_; lean_object* v_res_1546_; 
v_allowOpaque_boxed_1545_ = lean_unbox(v_allowOpaque_1544_);
v_res_1546_ = l_Lean_ConstantInfo_value_x3f(v_info_1543_, v_allowOpaque_boxed_1545_);
return v_res_1546_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_hasValue(lean_object* v_info_1547_, uint8_t v_allowOpaque_1548_){
_start:
{
switch(lean_obj_tag(v_info_1547_))
{
case 1:
{
uint8_t v___x_1549_; 
v___x_1549_ = 1;
return v___x_1549_;
}
case 2:
{
return v_allowOpaque_1548_;
}
case 3:
{
return v_allowOpaque_1548_;
}
default: 
{
uint8_t v___x_1550_; 
v___x_1550_ = 0;
return v___x_1550_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object* v_info_1551_, lean_object* v_allowOpaque_1552_){
_start:
{
uint8_t v_allowOpaque_boxed_1553_; uint8_t v_res_1554_; lean_object* v_r_1555_; 
v_allowOpaque_boxed_1553_ = lean_unbox(v_allowOpaque_1552_);
v_res_1554_ = l_Lean_ConstantInfo_hasValue(v_info_1551_, v_allowOpaque_boxed_1553_);
lean_dec_ref(v_info_1551_);
v_r_1555_ = lean_box(v_res_1554_);
return v_r_1555_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(lean_object* v_msg_1556_){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1557_ = l_Lean_instInhabitedExpr;
v___x_1558_ = lean_panic_fn_borrowed(v___x_1557_, v_msg_1556_);
return v___x_1558_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__2(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1561_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1562_ = lean_unsigned_to_nat(62u);
v___x_1563_ = lean_unsigned_to_nat(508u);
v___x_1564_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1565_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1566_ = l_mkPanicMessageWithDecl(v___x_1565_, v___x_1564_, v___x_1563_, v___x_1562_, v___x_1561_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__3(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1567_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1568_ = lean_unsigned_to_nat(62u);
v___x_1569_ = lean_unsigned_to_nat(509u);
v___x_1570_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1571_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1572_ = l_mkPanicMessageWithDecl(v___x_1571_, v___x_1570_, v___x_1569_, v___x_1568_, v___x_1567_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21(lean_object* v_info_1575_, uint8_t v_allowOpaque_1576_){
_start:
{
switch(lean_obj_tag(v_info_1575_))
{
case 1:
{
lean_object* v_val_1577_; lean_object* v_value_1578_; 
v_val_1577_ = lean_ctor_get(v_info_1575_, 0);
v_value_1578_ = lean_ctor_get(v_val_1577_, 1);
lean_inc_ref(v_value_1578_);
return v_value_1578_;
}
case 2:
{
if (v_allowOpaque_1576_ == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__2, &l_Lean_ConstantInfo_value_x21___closed__2_once, _init_l_Lean_ConstantInfo_value_x21___closed__2);
v___x_1580_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1579_);
return v___x_1580_;
}
else
{
lean_object* v_val_1581_; lean_object* v_value_1582_; 
v_val_1581_ = lean_ctor_get(v_info_1575_, 0);
v_value_1582_ = lean_ctor_get(v_val_1581_, 1);
lean_inc_ref(v_value_1582_);
return v_value_1582_;
}
}
case 3:
{
if (v_allowOpaque_1576_ == 0)
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__3, &l_Lean_ConstantInfo_value_x21___closed__3_once, _init_l_Lean_ConstantInfo_value_x21___closed__3);
v___x_1584_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1583_);
return v___x_1584_;
}
else
{
lean_object* v_val_1585_; lean_object* v_value_1586_; 
v_val_1585_ = lean_ctor_get(v_info_1575_, 0);
v_value_1586_ = lean_ctor_get(v_val_1585_, 1);
lean_inc_ref(v_value_1586_);
return v_value_1586_;
}
}
default: 
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1587_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1588_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1589_ = lean_unsigned_to_nat(510u);
v___x_1590_ = lean_unsigned_to_nat(31u);
v___x_1591_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__4));
v___x_1592_ = l_Lean_ConstantInfo_name(v_info_1575_);
v___x_1593_ = 1;
v___x_1594_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1592_, v___x_1593_);
v___x_1595_ = lean_string_append(v___x_1591_, v___x_1594_);
lean_dec_ref(v___x_1594_);
v___x_1596_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__5));
v___x_1597_ = lean_string_append(v___x_1595_, v___x_1596_);
v___x_1598_ = l_mkPanicMessageWithDecl(v___x_1587_, v___x_1588_, v___x_1589_, v___x_1590_, v___x_1597_);
lean_dec_ref(v___x_1597_);
v___x_1599_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1598_);
return v___x_1599_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21___boxed(lean_object* v_info_1600_, lean_object* v_allowOpaque_1601_){
_start:
{
uint8_t v_allowOpaque_boxed_1602_; lean_object* v_res_1603_; 
v_allowOpaque_boxed_1602_ = lean_unbox(v_allowOpaque_1601_);
v_res_1603_ = l_Lean_ConstantInfo_value_x21(v_info_1600_, v_allowOpaque_boxed_1602_);
lean_dec_ref(v_info_1600_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints(lean_object* v_x_1604_){
_start:
{
if (lean_obj_tag(v_x_1604_) == 1)
{
lean_object* v_val_1605_; lean_object* v_hints_1606_; 
v_val_1605_ = lean_ctor_get(v_x_1604_, 0);
v_hints_1606_ = lean_ctor_get(v_val_1605_, 2);
lean_inc(v_hints_1606_);
return v_hints_1606_;
}
else
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_box(0);
return v___x_1607_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object* v_x_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Lean_ConstantInfo_hints(v_x_1608_);
lean_dec_ref(v_x_1608_);
return v_res_1609_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isCtor(lean_object* v_x_1610_){
_start:
{
if (lean_obj_tag(v_x_1610_) == 6)
{
uint8_t v___x_1611_; 
v___x_1611_ = 1;
return v___x_1611_;
}
else
{
uint8_t v___x_1612_; 
v___x_1612_ = 0;
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isCtor___boxed(lean_object* v_x_1613_){
_start:
{
uint8_t v_res_1614_; lean_object* v_r_1615_; 
v_res_1614_ = l_Lean_ConstantInfo_isCtor(v_x_1613_);
lean_dec_ref(v_x_1613_);
v_r_1615_ = lean_box(v_res_1614_);
return v_r_1615_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isAxiom(lean_object* v_x_1616_){
_start:
{
if (lean_obj_tag(v_x_1616_) == 0)
{
uint8_t v___x_1617_; 
v___x_1617_ = 1;
return v___x_1617_;
}
else
{
uint8_t v___x_1618_; 
v___x_1618_ = 0;
return v___x_1618_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isAxiom___boxed(lean_object* v_x_1619_){
_start:
{
uint8_t v_res_1620_; lean_object* v_r_1621_; 
v_res_1620_ = l_Lean_ConstantInfo_isAxiom(v_x_1619_);
lean_dec_ref(v_x_1619_);
v_r_1621_ = lean_box(v_res_1620_);
return v_r_1621_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isInductive(lean_object* v_x_1622_){
_start:
{
if (lean_obj_tag(v_x_1622_) == 5)
{
uint8_t v___x_1623_; 
v___x_1623_ = 1;
return v___x_1623_;
}
else
{
uint8_t v___x_1624_; 
v___x_1624_ = 0;
return v___x_1624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isInductive___boxed(lean_object* v_x_1625_){
_start:
{
uint8_t v_res_1626_; lean_object* v_r_1627_; 
v_res_1626_ = l_Lean_ConstantInfo_isInductive(v_x_1625_);
lean_dec_ref(v_x_1625_);
v_r_1627_ = lean_box(v_res_1626_);
return v_r_1627_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isDefinition(lean_object* v_x_1628_){
_start:
{
if (lean_obj_tag(v_x_1628_) == 1)
{
uint8_t v___x_1629_; 
v___x_1629_ = 1;
return v___x_1629_;
}
else
{
uint8_t v___x_1630_; 
v___x_1630_ = 0;
return v___x_1630_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isDefinition___boxed(lean_object* v_x_1631_){
_start:
{
uint8_t v_res_1632_; lean_object* v_r_1633_; 
v_res_1632_ = l_Lean_ConstantInfo_isDefinition(v_x_1631_);
lean_dec_ref(v_x_1631_);
v_r_1633_ = lean_box(v_res_1632_);
return v_r_1633_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isTheorem(lean_object* v_x_1634_){
_start:
{
if (lean_obj_tag(v_x_1634_) == 2)
{
uint8_t v___x_1635_; 
v___x_1635_ = 1;
return v___x_1635_;
}
else
{
uint8_t v___x_1636_; 
v___x_1636_ = 0;
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isTheorem___boxed(lean_object* v_x_1637_){
_start:
{
uint8_t v_res_1638_; lean_object* v_r_1639_; 
v_res_1638_ = l_Lean_ConstantInfo_isTheorem(v_x_1637_);
lean_dec_ref(v_x_1637_);
v_r_1639_ = lean_box(v_res_1638_);
return v_r_1639_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(lean_object* v_msg_1640_){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = l_Lean_instInhabitedInductiveVal_default;
v___x_1642_ = lean_panic_fn_borrowed(v___x_1641_, v_msg_1640_);
return v___x_1642_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1645_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__1));
v___x_1646_ = lean_unsigned_to_nat(9u);
v___x_1647_ = lean_unsigned_to_nat(538u);
v___x_1648_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__0));
v___x_1649_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1650_ = l_mkPanicMessageWithDecl(v___x_1649_, v___x_1648_, v___x_1647_, v___x_1646_, v___x_1645_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object* v_x_1651_){
_start:
{
if (lean_obj_tag(v_x_1651_) == 5)
{
lean_object* v_val_1652_; 
v_val_1652_ = lean_ctor_get(v_x_1651_, 0);
lean_inc_ref(v_val_1652_);
return v_val_1652_;
}
else
{
lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1653_ = lean_obj_once(&l_Lean_ConstantInfo_inductiveVal_x21___closed__2, &l_Lean_ConstantInfo_inductiveVal_x21___closed__2_once, _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2);
v___x_1654_ = l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(v___x_1653_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21___boxed(lean_object* v_x_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_Lean_ConstantInfo_inductiveVal_x21(v_x_1655_);
lean_dec_ref(v_x_1655_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all(lean_object* v_x_1657_){
_start:
{
switch(lean_obj_tag(v_x_1657_))
{
case 5:
{
lean_object* v_val_1658_; lean_object* v_all_1659_; 
v_val_1658_ = lean_ctor_get(v_x_1657_, 0);
v_all_1659_ = lean_ctor_get(v_val_1658_, 3);
lean_inc(v_all_1659_);
return v_all_1659_;
}
case 1:
{
lean_object* v_val_1660_; lean_object* v_all_1661_; 
v_val_1660_ = lean_ctor_get(v_x_1657_, 0);
v_all_1661_ = lean_ctor_get(v_val_1660_, 3);
lean_inc(v_all_1661_);
return v_all_1661_;
}
case 2:
{
lean_object* v_val_1662_; lean_object* v_all_1663_; 
v_val_1662_ = lean_ctor_get(v_x_1657_, 0);
v_all_1663_ = lean_ctor_get(v_val_1662_, 2);
lean_inc(v_all_1663_);
return v_all_1663_;
}
case 3:
{
lean_object* v_val_1664_; lean_object* v_all_1665_; 
v_val_1664_ = lean_ctor_get(v_x_1657_, 0);
v_all_1665_ = lean_ctor_get(v_val_1664_, 2);
lean_inc(v_all_1665_);
return v_all_1665_;
}
default: 
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = l_Lean_ConstantInfo_name(v_x_1657_);
v___x_1667_ = lean_box(0);
v___x_1668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1666_);
lean_ctor_set(v___x_1668_, 1, v___x_1667_);
return v___x_1668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all___boxed(lean_object* v_x_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lean_ConstantInfo_all(v_x_1669_);
lean_dec_ref(v_x_1669_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecName(lean_object* v_declName_1671_){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1672_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0));
v___x_1673_ = l_Lean_Name_str___override(v_declName_1671_, v___x_1672_);
return v___x_1673_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_UInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Declaration(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
