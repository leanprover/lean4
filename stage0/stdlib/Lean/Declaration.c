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
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_365_ = lean_box(0);
v___x_366_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_367_ = l_Lean_Expr_const___override(v___x_366_, v___x_365_);
return v___x_367_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default___closed__2(void){
_start:
{
lean_object* v___x_371_; uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_371_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_372_ = 0;
v___x_373_ = lean_box(0);
v___x_374_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_375_ = l_Lean_instInhabitedConstantVal_default;
v___x_376_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
lean_ctor_set(v___x_376_, 2, v___x_373_);
lean_ctor_set(v___x_376_, 3, v___x_371_);
lean_ctor_set_uint8(v___x_376_, sizeof(void*)*4, v___x_372_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default(void){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__2, &l_Lean_instInhabitedDefinitionVal_default___closed__2_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__2);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal(void){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_instInhabitedDefinitionVal_default;
return v___x_378_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDefinitionVal_beq(lean_object* v_x_379_, lean_object* v_x_380_){
_start:
{
lean_object* v_toConstantVal_381_; lean_object* v_value_382_; lean_object* v_hints_383_; uint8_t v_safety_384_; lean_object* v_all_385_; lean_object* v_toConstantVal_386_; lean_object* v_value_387_; lean_object* v_hints_388_; uint8_t v_safety_389_; lean_object* v_all_390_; uint8_t v___x_391_; 
v_toConstantVal_381_ = lean_ctor_get(v_x_379_, 0);
v_value_382_ = lean_ctor_get(v_x_379_, 1);
v_hints_383_ = lean_ctor_get(v_x_379_, 2);
v_safety_384_ = lean_ctor_get_uint8(v_x_379_, sizeof(void*)*4);
v_all_385_ = lean_ctor_get(v_x_379_, 3);
v_toConstantVal_386_ = lean_ctor_get(v_x_380_, 0);
v_value_387_ = lean_ctor_get(v_x_380_, 1);
v_hints_388_ = lean_ctor_get(v_x_380_, 2);
v_safety_389_ = lean_ctor_get_uint8(v_x_380_, sizeof(void*)*4);
v_all_390_ = lean_ctor_get(v_x_380_, 3);
v___x_391_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_381_, v_toConstantVal_386_);
if (v___x_391_ == 0)
{
return v___x_391_;
}
else
{
uint8_t v___x_392_; 
v___x_392_ = lean_expr_eqv(v_value_382_, v_value_387_);
if (v___x_392_ == 0)
{
return v___x_392_;
}
else
{
uint8_t v___x_393_; 
v___x_393_ = l_Lean_instBEqReducibilityHints_beq(v_hints_383_, v_hints_388_);
if (v___x_393_ == 0)
{
return v___x_393_;
}
else
{
uint8_t v___x_394_; 
v___x_394_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_384_, v_safety_389_);
if (v___x_394_ == 0)
{
return v___x_394_;
}
else
{
uint8_t v___x_395_; 
v___x_395_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_385_, v_all_390_);
return v___x_395_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionVal_beq___boxed(lean_object* v_x_396_, lean_object* v_x_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l_Lean_instBEqDefinitionVal_beq(v_x_396_, v_x_397_);
lean_dec_ref(v_x_397_);
lean_dec_ref(v_x_396_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* lean_mk_definition_val(lean_object* v_name_402_, lean_object* v_levelParams_403_, lean_object* v_type_404_, lean_object* v_value_405_, lean_object* v_hints_406_, uint8_t v_safety_407_, lean_object* v_all_408_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_409_, 0, v_name_402_);
lean_ctor_set(v___x_409_, 1, v_levelParams_403_);
lean_ctor_set(v___x_409_, 2, v_type_404_);
v___x_410_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v_value_405_);
lean_ctor_set(v___x_410_, 2, v_hints_406_);
lean_ctor_set(v___x_410_, 3, v_all_408_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*4, v_safety_407_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValEx___boxed(lean_object* v_name_411_, lean_object* v_levelParams_412_, lean_object* v_type_413_, lean_object* v_value_414_, lean_object* v_hints_415_, lean_object* v_safety_416_, lean_object* v_all_417_){
_start:
{
uint8_t v_safety_boxed_418_; lean_object* v_res_419_; 
v_safety_boxed_418_ = lean_unbox(v_safety_416_);
v_res_419_ = lean_mk_definition_val(v_name_411_, v_levelParams_412_, v_type_413_, v_value_414_, v_hints_415_, v_safety_boxed_418_, v_all_417_);
return v_res_419_;
}
}
LEAN_EXPORT uint8_t lean_definition_val_get_safety(lean_object* v_v_420_){
_start:
{
uint8_t v_safety_421_; 
v_safety_421_ = lean_ctor_get_uint8(v_v_420_, sizeof(void*)*4);
lean_dec_ref(v_v_420_);
return v_safety_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionVal_getSafetyEx___boxed(lean_object* v_v_422_){
_start:
{
uint8_t v_res_423_; lean_object* v_r_424_; 
v_res_423_ = lean_definition_val_get_safety(v_v_422_);
v_r_424_ = lean_box(v_res_423_);
return v_r_424_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default___closed__0(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_425_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_426_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_427_ = l_Lean_instInhabitedConstantVal_default;
v___x_428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_428_, 0, v___x_427_);
lean_ctor_set(v___x_428_, 1, v___x_426_);
lean_ctor_set(v___x_428_, 2, v___x_425_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default(void){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = lean_obj_once(&l_Lean_instInhabitedTheoremVal_default___closed__0, &l_Lean_instInhabitedTheoremVal_default___closed__0_once, _init_l_Lean_instInhabitedTheoremVal_default___closed__0);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal(void){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = l_Lean_instInhabitedTheoremVal_default;
return v___x_430_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqTheoremVal_beq(lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
lean_object* v_toConstantVal_433_; lean_object* v_value_434_; lean_object* v_all_435_; lean_object* v_toConstantVal_436_; lean_object* v_value_437_; lean_object* v_all_438_; uint8_t v___x_439_; 
v_toConstantVal_433_ = lean_ctor_get(v_x_431_, 0);
v_value_434_ = lean_ctor_get(v_x_431_, 1);
v_all_435_ = lean_ctor_get(v_x_431_, 2);
v_toConstantVal_436_ = lean_ctor_get(v_x_432_, 0);
v_value_437_ = lean_ctor_get(v_x_432_, 1);
v_all_438_ = lean_ctor_get(v_x_432_, 2);
v___x_439_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_433_, v_toConstantVal_436_);
if (v___x_439_ == 0)
{
return v___x_439_;
}
else
{
uint8_t v___x_440_; 
v___x_440_ = lean_expr_eqv(v_value_434_, v_value_437_);
if (v___x_440_ == 0)
{
return v___x_440_;
}
else
{
uint8_t v___x_441_; 
v___x_441_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_435_, v_all_438_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqTheoremVal_beq___boxed(lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Lean_instBEqTheoremVal_beq(v_x_442_, v_x_443_);
lean_dec_ref(v_x_443_);
lean_dec_ref(v_x_442_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
LEAN_EXPORT lean_object* lean_mk_theorem_val(lean_object* v_name_448_, lean_object* v_levelParams_449_, lean_object* v_type_450_, lean_object* v_value_451_, lean_object* v_all_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_453_, 0, v_name_448_);
lean_ctor_set(v___x_453_, 1, v_levelParams_449_);
lean_ctor_set(v___x_453_, 2, v_type_450_);
v___x_454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v_value_451_);
lean_ctor_set(v___x_454_, 2, v_all_452_);
return v___x_454_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default___closed__0(void){
_start:
{
lean_object* v___x_455_; uint8_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_455_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_456_ = 0;
v___x_457_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_458_ = l_Lean_instInhabitedConstantVal_default;
v___x_459_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_457_);
lean_ctor_set(v___x_459_, 2, v___x_455_);
lean_ctor_set_uint8(v___x_459_, sizeof(void*)*3, v___x_456_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default(void){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = lean_obj_once(&l_Lean_instInhabitedOpaqueVal_default___closed__0, &l_Lean_instInhabitedOpaqueVal_default___closed__0_once, _init_l_Lean_instInhabitedOpaqueVal_default___closed__0);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal(void){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_instInhabitedOpaqueVal_default;
return v___x_461_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqOpaqueVal_beq(lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_toConstantVal_464_; lean_object* v_value_465_; uint8_t v_isUnsafe_466_; lean_object* v_all_467_; lean_object* v_toConstantVal_468_; lean_object* v_value_469_; uint8_t v_isUnsafe_470_; lean_object* v_all_471_; uint8_t v___y_473_; uint8_t v___x_475_; 
v_toConstantVal_464_ = lean_ctor_get(v_x_462_, 0);
v_value_465_ = lean_ctor_get(v_x_462_, 1);
v_isUnsafe_466_ = lean_ctor_get_uint8(v_x_462_, sizeof(void*)*3);
v_all_467_ = lean_ctor_get(v_x_462_, 2);
v_toConstantVal_468_ = lean_ctor_get(v_x_463_, 0);
v_value_469_ = lean_ctor_get(v_x_463_, 1);
v_isUnsafe_470_ = lean_ctor_get_uint8(v_x_463_, sizeof(void*)*3);
v_all_471_ = lean_ctor_get(v_x_463_, 2);
v___x_475_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_464_, v_toConstantVal_468_);
if (v___x_475_ == 0)
{
return v___x_475_;
}
else
{
uint8_t v___x_476_; 
v___x_476_ = lean_expr_eqv(v_value_465_, v_value_469_);
if (v___x_476_ == 0)
{
return v___x_476_;
}
else
{
if (v_isUnsafe_466_ == 0)
{
if (v_isUnsafe_470_ == 0)
{
v___y_473_ = v___x_476_;
goto v___jp_472_;
}
else
{
return v_isUnsafe_466_;
}
}
else
{
v___y_473_ = v_isUnsafe_470_;
goto v___jp_472_;
}
}
}
v___jp_472_:
{
if (v___y_473_ == 0)
{
return v___y_473_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_467_, v_all_471_);
return v___x_474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqOpaqueVal_beq___boxed(lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = l_Lean_instBEqOpaqueVal_beq(v_x_477_, v_x_478_);
lean_dec_ref(v_x_478_);
lean_dec_ref(v_x_477_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT lean_object* lean_mk_opaque_val(lean_object* v_name_483_, lean_object* v_levelParams_484_, lean_object* v_type_485_, lean_object* v_value_486_, uint8_t v_isUnsafe_487_, lean_object* v_all_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_489_, 0, v_name_483_);
lean_ctor_set(v___x_489_, 1, v_levelParams_484_);
lean_ctor_set(v___x_489_, 2, v_type_485_);
v___x_490_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_value_486_);
lean_ctor_set(v___x_490_, 2, v_all_488_);
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*3, v_isUnsafe_487_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkOpaqueValEx___boxed(lean_object* v_name_491_, lean_object* v_levelParams_492_, lean_object* v_type_493_, lean_object* v_value_494_, lean_object* v_isUnsafe_495_, lean_object* v_all_496_){
_start:
{
uint8_t v_isUnsafe_boxed_497_; lean_object* v_res_498_; 
v_isUnsafe_boxed_497_ = lean_unbox(v_isUnsafe_495_);
v_res_498_ = lean_mk_opaque_val(v_name_491_, v_levelParams_492_, v_type_493_, v_value_494_, v_isUnsafe_boxed_497_, v_all_496_);
return v_res_498_;
}
}
LEAN_EXPORT uint8_t lean_opaque_val_is_unsafe(lean_object* v_v_499_){
_start:
{
uint8_t v_isUnsafe_500_; 
v_isUnsafe_500_ = lean_ctor_get_uint8(v_v_499_, sizeof(void*)*3);
lean_dec_ref(v_v_499_);
return v_isUnsafe_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpaqueVal_isUnsafeEx___boxed(lean_object* v_v_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = lean_opaque_val_is_unsafe(v_v_501_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__0(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_box(0);
v___x_505_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_506_ = l_Lean_Expr_const___override(v___x_505_, v___x_504_);
return v___x_506_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__1(void){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_508_ = lean_box(0);
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_508_);
lean_ctor_set(v___x_509_, 1, v___x_507_);
return v___x_509_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default(void){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__1, &l_Lean_instInhabitedConstructor_default___closed__1_once, _init_l_Lean_instInhabitedConstructor_default___closed__1);
return v___x_510_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor(void){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Lean_instInhabitedConstructor_default;
return v___x_511_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructor_beq(lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
lean_object* v_name_514_; lean_object* v_type_515_; lean_object* v_name_516_; lean_object* v_type_517_; uint8_t v___x_518_; 
v_name_514_ = lean_ctor_get(v_x_512_, 0);
v_type_515_ = lean_ctor_get(v_x_512_, 1);
v_name_516_ = lean_ctor_get(v_x_513_, 0);
v_type_517_ = lean_ctor_get(v_x_513_, 1);
v___x_518_ = lean_name_eq(v_name_514_, v_name_516_);
if (v___x_518_ == 0)
{
return v___x_518_;
}
else
{
uint8_t v___x_519_; 
v___x_519_ = lean_expr_eqv(v_type_515_, v_type_517_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructor_beq___boxed(lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
uint8_t v_res_522_; lean_object* v_r_523_; 
v_res_522_ = l_Lean_instBEqConstructor_beq(v_x_520_, v_x_521_);
lean_dec_ref(v_x_521_);
lean_dec_ref(v_x_520_);
v_r_523_ = lean_box(v_res_522_);
return v_r_523_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default___closed__0(void){
_start:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_526_ = lean_box(0);
v___x_527_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_528_ = lean_box(0);
v___x_529_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
lean_ctor_set(v___x_529_, 1, v___x_527_);
lean_ctor_set(v___x_529_, 2, v___x_526_);
return v___x_529_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default(void){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = lean_obj_once(&l_Lean_instInhabitedInductiveType_default___closed__0, &l_Lean_instInhabitedInductiveType_default___closed__0_once, _init_l_Lean_instInhabitedInductiveType_default___closed__0);
return v___x_530_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType(void){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_instInhabitedInductiveType_default;
return v___x_531_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
if (lean_obj_tag(v_x_532_) == 0)
{
if (lean_obj_tag(v_x_533_) == 0)
{
uint8_t v___x_534_; 
v___x_534_ = 1;
return v___x_534_;
}
else
{
uint8_t v___x_535_; 
v___x_535_ = 0;
return v___x_535_;
}
}
else
{
if (lean_obj_tag(v_x_533_) == 0)
{
uint8_t v___x_536_; 
v___x_536_ = 0;
return v___x_536_;
}
else
{
lean_object* v_head_537_; lean_object* v_tail_538_; lean_object* v_head_539_; lean_object* v_tail_540_; uint8_t v___x_541_; 
v_head_537_ = lean_ctor_get(v_x_532_, 0);
v_tail_538_ = lean_ctor_get(v_x_532_, 1);
v_head_539_ = lean_ctor_get(v_x_533_, 0);
v_tail_540_ = lean_ctor_get(v_x_533_, 1);
v___x_541_ = l_Lean_instBEqConstructor_beq(v_head_537_, v_head_539_);
if (v___x_541_ == 0)
{
return v___x_541_;
}
else
{
v_x_532_ = v_tail_538_;
v_x_533_ = v_tail_540_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0___boxed(lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
uint8_t v_res_545_; lean_object* v_r_546_; 
v_res_545_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_x_543_, v_x_544_);
lean_dec(v_x_544_);
lean_dec(v_x_543_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveType_beq(lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v_name_549_; lean_object* v_type_550_; lean_object* v_ctors_551_; lean_object* v_name_552_; lean_object* v_type_553_; lean_object* v_ctors_554_; uint8_t v___x_555_; 
v_name_549_ = lean_ctor_get(v_x_547_, 0);
v_type_550_ = lean_ctor_get(v_x_547_, 1);
v_ctors_551_ = lean_ctor_get(v_x_547_, 2);
v_name_552_ = lean_ctor_get(v_x_548_, 0);
v_type_553_ = lean_ctor_get(v_x_548_, 1);
v_ctors_554_ = lean_ctor_get(v_x_548_, 2);
v___x_555_ = lean_name_eq(v_name_549_, v_name_552_);
if (v___x_555_ == 0)
{
return v___x_555_;
}
else
{
uint8_t v___x_556_; 
v___x_556_ = lean_expr_eqv(v_type_550_, v_type_553_);
if (v___x_556_ == 0)
{
return v___x_556_;
}
else
{
uint8_t v___x_557_; 
v___x_557_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_ctors_551_, v_ctors_554_);
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveType_beq___boxed(lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_Lean_instBEqInductiveType_beq(v_x_558_, v_x_559_);
lean_dec_ref(v_x_559_);
lean_dec_ref(v_x_558_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx(lean_object* v_x_564_){
_start:
{
switch(lean_obj_tag(v_x_564_))
{
case 0:
{
lean_object* v___x_565_; 
v___x_565_ = lean_unsigned_to_nat(0u);
return v___x_565_;
}
case 1:
{
lean_object* v___x_566_; 
v___x_566_ = lean_unsigned_to_nat(1u);
return v___x_566_;
}
case 2:
{
lean_object* v___x_567_; 
v___x_567_ = lean_unsigned_to_nat(2u);
return v___x_567_;
}
case 3:
{
lean_object* v___x_568_; 
v___x_568_ = lean_unsigned_to_nat(3u);
return v___x_568_;
}
case 4:
{
lean_object* v___x_569_; 
v___x_569_ = lean_unsigned_to_nat(4u);
return v___x_569_;
}
case 5:
{
lean_object* v___x_570_; 
v___x_570_ = lean_unsigned_to_nat(5u);
return v___x_570_;
}
default: 
{
lean_object* v___x_571_; 
v___x_571_ = lean_unsigned_to_nat(6u);
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___boxed(lean_object* v_x_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_Declaration_ctorIdx(v_x_572_);
lean_dec(v_x_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___redArg(lean_object* v_t_574_, lean_object* v_k_575_){
_start:
{
switch(lean_obj_tag(v_t_574_))
{
case 4:
{
return v_k_575_;
}
case 5:
{
lean_object* v_defns_576_; lean_object* v___x_577_; 
v_defns_576_ = lean_ctor_get(v_t_574_, 0);
lean_inc(v_defns_576_);
lean_dec_ref(v_t_574_);
v___x_577_ = lean_apply_1(v_k_575_, v_defns_576_);
return v___x_577_;
}
case 6:
{
lean_object* v_lparams_578_; lean_object* v_nparams_579_; lean_object* v_types_580_; uint8_t v_isUnsafe_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_lparams_578_ = lean_ctor_get(v_t_574_, 0);
lean_inc(v_lparams_578_);
v_nparams_579_ = lean_ctor_get(v_t_574_, 1);
lean_inc(v_nparams_579_);
v_types_580_ = lean_ctor_get(v_t_574_, 2);
lean_inc(v_types_580_);
v_isUnsafe_581_ = lean_ctor_get_uint8(v_t_574_, sizeof(void*)*3);
lean_dec_ref(v_t_574_);
v___x_582_ = lean_box(v_isUnsafe_581_);
v___x_583_ = lean_apply_4(v_k_575_, v_lparams_578_, v_nparams_579_, v_types_580_, v___x_582_);
return v___x_583_;
}
default: 
{
lean_object* v_val_584_; lean_object* v___x_585_; 
v_val_584_ = lean_ctor_get(v_t_574_, 0);
lean_inc_ref(v_val_584_);
lean_dec(v_t_574_);
v___x_585_ = lean_apply_1(v_k_575_, v_val_584_);
return v___x_585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim(lean_object* v_motive_586_, lean_object* v_ctorIdx_587_, lean_object* v_t_588_, lean_object* v_h_589_, lean_object* v_k_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_Declaration_ctorElim___redArg(v_t_588_, v_k_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___boxed(lean_object* v_motive_592_, lean_object* v_ctorIdx_593_, lean_object* v_t_594_, lean_object* v_h_595_, lean_object* v_k_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Declaration_ctorElim(v_motive_592_, v_ctorIdx_593_, v_t_594_, v_h_595_, v_k_596_);
lean_dec(v_ctorIdx_593_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim___redArg(lean_object* v_t_598_, lean_object* v_axiomDecl_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Declaration_ctorElim___redArg(v_t_598_, v_axiomDecl_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim(lean_object* v_motive_601_, lean_object* v_t_602_, lean_object* v_h_603_, lean_object* v_axiomDecl_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_Declaration_ctorElim___redArg(v_t_602_, v_axiomDecl_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim___redArg(lean_object* v_t_606_, lean_object* v_defnDecl_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Declaration_ctorElim___redArg(v_t_606_, v_defnDecl_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim(lean_object* v_motive_609_, lean_object* v_t_610_, lean_object* v_h_611_, lean_object* v_defnDecl_612_){
_start:
{
lean_object* v___x_613_; 
v___x_613_ = l_Lean_Declaration_ctorElim___redArg(v_t_610_, v_defnDecl_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim___redArg(lean_object* v_t_614_, lean_object* v_thmDecl_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_Declaration_ctorElim___redArg(v_t_614_, v_thmDecl_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim(lean_object* v_motive_617_, lean_object* v_t_618_, lean_object* v_h_619_, lean_object* v_thmDecl_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Lean_Declaration_ctorElim___redArg(v_t_618_, v_thmDecl_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim___redArg(lean_object* v_t_622_, lean_object* v_opaqueDecl_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_Declaration_ctorElim___redArg(v_t_622_, v_opaqueDecl_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim(lean_object* v_motive_625_, lean_object* v_t_626_, lean_object* v_h_627_, lean_object* v_opaqueDecl_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Declaration_ctorElim___redArg(v_t_626_, v_opaqueDecl_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim___redArg(lean_object* v_t_630_, lean_object* v_quotDecl_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_Declaration_ctorElim___redArg(v_t_630_, v_quotDecl_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim(lean_object* v_motive_633_, lean_object* v_t_634_, lean_object* v_h_635_, lean_object* v_quotDecl_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_Declaration_ctorElim___redArg(v_t_634_, v_quotDecl_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim___redArg(lean_object* v_t_638_, lean_object* v_mutualDefnDecl_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Declaration_ctorElim___redArg(v_t_638_, v_mutualDefnDecl_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim(lean_object* v_motive_641_, lean_object* v_t_642_, lean_object* v_h_643_, lean_object* v_mutualDefnDecl_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_Declaration_ctorElim___redArg(v_t_642_, v_mutualDefnDecl_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim___redArg(lean_object* v_t_646_, lean_object* v_inductDecl_647_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Declaration_ctorElim___redArg(v_t_646_, v_inductDecl_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim(lean_object* v_motive_649_, lean_object* v_t_650_, lean_object* v_h_651_, lean_object* v_inductDecl_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Declaration_ctorElim___redArg(v_t_650_, v_inductDecl_652_);
return v___x_653_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default___closed__0(void){
_start:
{
lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_654_ = l_Lean_instInhabitedAxiomVal_default;
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
return v___x_655_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default(void){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = lean_obj_once(&l_Lean_instInhabitedDeclaration_default___closed__0, &l_Lean_instInhabitedDeclaration_default___closed__0_once, _init_l_Lean_instInhabitedDeclaration_default___closed__0);
return v___x_656_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration(void){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_instInhabitedDeclaration_default;
return v___x_657_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
if (lean_obj_tag(v_x_658_) == 0)
{
if (lean_obj_tag(v_x_659_) == 0)
{
uint8_t v___x_660_; 
v___x_660_ = 1;
return v___x_660_;
}
else
{
uint8_t v___x_661_; 
v___x_661_ = 0;
return v___x_661_;
}
}
else
{
if (lean_obj_tag(v_x_659_) == 0)
{
uint8_t v___x_662_; 
v___x_662_ = 0;
return v___x_662_;
}
else
{
lean_object* v_head_663_; lean_object* v_tail_664_; lean_object* v_head_665_; lean_object* v_tail_666_; uint8_t v___x_667_; 
v_head_663_ = lean_ctor_get(v_x_658_, 0);
v_tail_664_ = lean_ctor_get(v_x_658_, 1);
v_head_665_ = lean_ctor_get(v_x_659_, 0);
v_tail_666_ = lean_ctor_get(v_x_659_, 1);
v___x_667_ = l_Lean_instBEqDefinitionVal_beq(v_head_663_, v_head_665_);
if (v___x_667_ == 0)
{
return v___x_667_;
}
else
{
v_x_658_ = v_tail_664_;
v_x_659_ = v_tail_666_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0___boxed(lean_object* v_x_669_, lean_object* v_x_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_x_669_, v_x_670_);
lean_dec(v_x_670_);
lean_dec(v_x_669_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
if (lean_obj_tag(v_x_673_) == 0)
{
if (lean_obj_tag(v_x_674_) == 0)
{
uint8_t v___x_675_; 
v___x_675_ = 1;
return v___x_675_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = 0;
return v___x_676_;
}
}
else
{
if (lean_obj_tag(v_x_674_) == 0)
{
uint8_t v___x_677_; 
v___x_677_ = 0;
return v___x_677_;
}
else
{
lean_object* v_head_678_; lean_object* v_tail_679_; lean_object* v_head_680_; lean_object* v_tail_681_; uint8_t v___x_682_; 
v_head_678_ = lean_ctor_get(v_x_673_, 0);
v_tail_679_ = lean_ctor_get(v_x_673_, 1);
v_head_680_ = lean_ctor_get(v_x_674_, 0);
v_tail_681_ = lean_ctor_get(v_x_674_, 1);
v___x_682_ = l_Lean_instBEqInductiveType_beq(v_head_678_, v_head_680_);
if (v___x_682_ == 0)
{
return v___x_682_;
}
else
{
v_x_673_ = v_tail_679_;
v_x_674_ = v_tail_681_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1___boxed(lean_object* v_x_684_, lean_object* v_x_685_){
_start:
{
uint8_t v_res_686_; lean_object* v_r_687_; 
v_res_686_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_x_684_, v_x_685_);
lean_dec(v_x_685_);
lean_dec(v_x_684_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDeclaration_beq(lean_object* v_x_688_, lean_object* v_x_689_){
_start:
{
switch(lean_obj_tag(v_x_688_))
{
case 0:
{
if (lean_obj_tag(v_x_689_) == 0)
{
lean_object* v_val_690_; lean_object* v_val_691_; uint8_t v___x_692_; 
v_val_690_ = lean_ctor_get(v_x_688_, 0);
v_val_691_ = lean_ctor_get(v_x_689_, 0);
v___x_692_ = l_Lean_instBEqAxiomVal_beq(v_val_690_, v_val_691_);
return v___x_692_;
}
else
{
uint8_t v___x_693_; 
v___x_693_ = 0;
return v___x_693_;
}
}
case 1:
{
if (lean_obj_tag(v_x_689_) == 1)
{
lean_object* v_val_694_; lean_object* v_val_695_; uint8_t v___x_696_; 
v_val_694_ = lean_ctor_get(v_x_688_, 0);
v_val_695_ = lean_ctor_get(v_x_689_, 0);
v___x_696_ = l_Lean_instBEqDefinitionVal_beq(v_val_694_, v_val_695_);
return v___x_696_;
}
else
{
uint8_t v___x_697_; 
v___x_697_ = 0;
return v___x_697_;
}
}
case 2:
{
if (lean_obj_tag(v_x_689_) == 2)
{
lean_object* v_val_698_; lean_object* v_val_699_; uint8_t v___x_700_; 
v_val_698_ = lean_ctor_get(v_x_688_, 0);
v_val_699_ = lean_ctor_get(v_x_689_, 0);
v___x_700_ = l_Lean_instBEqTheoremVal_beq(v_val_698_, v_val_699_);
return v___x_700_;
}
else
{
uint8_t v___x_701_; 
v___x_701_ = 0;
return v___x_701_;
}
}
case 3:
{
if (lean_obj_tag(v_x_689_) == 3)
{
lean_object* v_val_702_; lean_object* v_val_703_; uint8_t v___x_704_; 
v_val_702_ = lean_ctor_get(v_x_688_, 0);
v_val_703_ = lean_ctor_get(v_x_689_, 0);
v___x_704_ = l_Lean_instBEqOpaqueVal_beq(v_val_702_, v_val_703_);
return v___x_704_;
}
else
{
uint8_t v___x_705_; 
v___x_705_ = 0;
return v___x_705_;
}
}
case 4:
{
if (lean_obj_tag(v_x_689_) == 4)
{
uint8_t v___x_706_; 
v___x_706_ = 1;
return v___x_706_;
}
else
{
uint8_t v___x_707_; 
v___x_707_ = 0;
return v___x_707_;
}
}
case 5:
{
if (lean_obj_tag(v_x_689_) == 5)
{
lean_object* v_defns_708_; lean_object* v_defns_709_; uint8_t v___x_710_; 
v_defns_708_ = lean_ctor_get(v_x_688_, 0);
v_defns_709_ = lean_ctor_get(v_x_689_, 0);
v___x_710_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_defns_708_, v_defns_709_);
return v___x_710_;
}
else
{
uint8_t v___x_711_; 
v___x_711_ = 0;
return v___x_711_;
}
}
default: 
{
if (lean_obj_tag(v_x_689_) == 6)
{
lean_object* v_lparams_712_; lean_object* v_nparams_713_; lean_object* v_types_714_; uint8_t v_isUnsafe_715_; lean_object* v_lparams_716_; lean_object* v_nparams_717_; lean_object* v_types_718_; uint8_t v_isUnsafe_719_; uint8_t v___x_720_; 
v_lparams_712_ = lean_ctor_get(v_x_688_, 0);
v_nparams_713_ = lean_ctor_get(v_x_688_, 1);
v_types_714_ = lean_ctor_get(v_x_688_, 2);
v_isUnsafe_715_ = lean_ctor_get_uint8(v_x_688_, sizeof(void*)*3);
v_lparams_716_ = lean_ctor_get(v_x_689_, 0);
v_nparams_717_ = lean_ctor_get(v_x_689_, 1);
v_types_718_ = lean_ctor_get(v_x_689_, 2);
v_isUnsafe_719_ = lean_ctor_get_uint8(v_x_689_, sizeof(void*)*3);
v___x_720_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_lparams_712_, v_lparams_716_);
if (v___x_720_ == 0)
{
return v___x_720_;
}
else
{
uint8_t v___x_721_; 
v___x_721_ = lean_nat_dec_eq(v_nparams_713_, v_nparams_717_);
if (v___x_721_ == 0)
{
return v___x_721_;
}
else
{
uint8_t v___x_722_; 
v___x_722_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_types_714_, v_types_718_);
if (v___x_722_ == 0)
{
return v___x_722_;
}
else
{
if (v_isUnsafe_715_ == 0)
{
if (v_isUnsafe_719_ == 0)
{
return v___x_722_;
}
else
{
return v_isUnsafe_715_;
}
}
else
{
return v_isUnsafe_719_;
}
}
}
}
}
else
{
uint8_t v___x_723_; 
v___x_723_ = 0;
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDeclaration_beq___boxed(lean_object* v_x_724_, lean_object* v_x_725_){
_start:
{
uint8_t v_res_726_; lean_object* v_r_727_; 
v_res_726_ = l_Lean_instBEqDeclaration_beq(v_x_724_, v_x_725_);
lean_dec(v_x_725_);
lean_dec(v_x_724_);
v_r_727_ = lean_box(v_res_726_);
return v_r_727_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_decl(lean_object* v_lparams_730_, lean_object* v_nparams_731_, lean_object* v_types_732_, uint8_t v_isUnsafe_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_734_, 0, v_lparams_730_);
lean_ctor_set(v___x_734_, 1, v_nparams_731_);
lean_ctor_set(v___x_734_, 2, v_types_732_);
lean_ctor_set_uint8(v___x_734_, sizeof(void*)*3, v_isUnsafe_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveDeclEs___boxed(lean_object* v_lparams_735_, lean_object* v_nparams_736_, lean_object* v_types_737_, lean_object* v_isUnsafe_738_){
_start:
{
uint8_t v_isUnsafe_boxed_739_; lean_object* v_res_740_; 
v_isUnsafe_boxed_739_ = lean_unbox(v_isUnsafe_738_);
v_res_740_ = lean_mk_inductive_decl(v_lparams_735_, v_nparams_736_, v_types_737_, v_isUnsafe_boxed_739_);
return v_res_740_;
}
}
LEAN_EXPORT uint8_t lean_is_unsafe_inductive_decl(lean_object* v_x_741_){
_start:
{
if (lean_obj_tag(v_x_741_) == 6)
{
uint8_t v_isUnsafe_742_; 
v_isUnsafe_742_ = lean_ctor_get_uint8(v_x_741_, sizeof(void*)*3);
lean_dec_ref(v_x_741_);
return v_isUnsafe_742_;
}
else
{
uint8_t v___x_743_; 
lean_dec(v_x_741_);
v___x_743_ = 0;
return v___x_743_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_isUnsafeInductiveDeclEx___boxed(lean_object* v_x_744_){
_start:
{
uint8_t v_res_745_; lean_object* v_r_746_; 
v_res_745_ = lean_is_unsafe_inductive_decl(v_x_744_);
v_r_746_ = lean_box(v_res_745_);
return v_r_746_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(lean_object* v_msg_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = l_Lean_instInhabitedDefinitionVal_default;
v___x_749_ = lean_panic_fn_borrowed(v___x_748_, v_msg_747_);
return v___x_749_;
}
}
static lean_object* _init_l_Lean_Declaration_definitionVal_x21___closed__3(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_753_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__2));
v___x_754_ = lean_unsigned_to_nat(9u);
v___x_755_ = lean_unsigned_to_nat(206u);
v___x_756_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__1));
v___x_757_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_758_ = l_mkPanicMessageWithDecl(v___x_757_, v___x_756_, v___x_755_, v___x_754_, v___x_753_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21(lean_object* v_x_759_){
_start:
{
if (lean_obj_tag(v_x_759_) == 1)
{
lean_object* v_val_760_; 
v_val_760_ = lean_ctor_get(v_x_759_, 0);
lean_inc_ref(v_val_760_);
return v_val_760_;
}
else
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = lean_obj_once(&l_Lean_Declaration_definitionVal_x21___closed__3, &l_Lean_Declaration_definitionVal_x21___closed__3_once, _init_l_Lean_Declaration_definitionVal_x21___closed__3);
v___x_762_ = l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(v___x_761_);
return v___x_762_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21___boxed(lean_object* v_x_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Declaration_definitionVal_x21(v_x_763_);
lean_dec(v_x_763_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
if (lean_obj_tag(v_a_765_) == 0)
{
lean_object* v___x_767_; 
v___x_767_ = l_List_reverse___redArg(v_a_766_);
return v___x_767_;
}
else
{
lean_object* v_head_768_; lean_object* v_toConstantVal_769_; lean_object* v_tail_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_779_; 
v_head_768_ = lean_ctor_get(v_a_765_, 0);
v_toConstantVal_769_ = lean_ctor_get(v_head_768_, 0);
lean_inc_ref(v_toConstantVal_769_);
v_tail_770_ = lean_ctor_get(v_a_765_, 1);
v_isSharedCheck_779_ = !lean_is_exclusive(v_a_765_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v_a_765_, 0);
lean_dec(v_unused_780_);
v___x_772_ = v_a_765_;
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_tail_770_);
lean_dec(v_a_765_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v_name_774_; lean_object* v___x_776_; 
v_name_774_ = lean_ctor_get(v_toConstantVal_769_, 0);
lean_inc(v_name_774_);
lean_dec_ref(v_toConstantVal_769_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v_a_766_);
lean_ctor_set(v___x_772_, 0, v_name_774_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_name_774_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_a_766_);
v___x_776_ = v_reuseFailAlloc_778_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
v_a_765_ = v_tail_770_;
v_a_766_ = v___x_776_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
if (lean_obj_tag(v_a_781_) == 0)
{
lean_object* v___x_783_; 
v___x_783_ = l_List_reverse___redArg(v_a_782_);
return v___x_783_;
}
else
{
lean_object* v_head_784_; lean_object* v_tail_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_794_; 
v_head_784_ = lean_ctor_get(v_a_781_, 0);
v_tail_785_ = lean_ctor_get(v_a_781_, 1);
v_isSharedCheck_794_ = !lean_is_exclusive(v_a_781_);
if (v_isSharedCheck_794_ == 0)
{
v___x_787_ = v_a_781_;
v_isShared_788_ = v_isSharedCheck_794_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_tail_785_);
lean_inc(v_head_784_);
lean_dec(v_a_781_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_794_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v_name_789_; lean_object* v___x_791_; 
v_name_789_ = lean_ctor_get(v_head_784_, 0);
lean_inc(v_name_789_);
lean_dec(v_head_784_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v_a_782_);
lean_ctor_set(v___x_787_, 0, v_name_789_);
v___x_791_ = v___x_787_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_name_789_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_a_782_);
v___x_791_ = v_reuseFailAlloc_793_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
v_a_781_ = v_tail_785_;
v_a_782_ = v___x_791_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getTopLevelNames(lean_object* v_x_801_){
_start:
{
switch(lean_obj_tag(v_x_801_))
{
case 4:
{
lean_object* v___x_802_; 
v___x_802_ = ((lean_object*)(l_Lean_Declaration_getTopLevelNames___closed__2));
return v___x_802_;
}
case 5:
{
lean_object* v_defns_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v_defns_803_ = lean_ctor_get(v_x_801_, 0);
lean_inc(v_defns_803_);
lean_dec_ref(v_x_801_);
v___x_804_ = lean_box(0);
v___x_805_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_803_, v___x_804_);
return v___x_805_;
}
case 6:
{
lean_object* v_types_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_types_806_ = lean_ctor_get(v_x_801_, 2);
lean_inc(v_types_806_);
lean_dec_ref(v_x_801_);
v___x_807_ = lean_box(0);
v___x_808_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(v_types_806_, v___x_807_);
return v___x_808_;
}
default: 
{
lean_object* v_val_809_; lean_object* v_toConstantVal_810_; lean_object* v_name_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_val_809_ = lean_ctor_get(v_x_801_, 0);
lean_inc_ref(v_val_809_);
lean_dec(v_x_801_);
v_toConstantVal_810_ = lean_ctor_get(v_val_809_, 0);
lean_inc_ref(v_toConstantVal_810_);
lean_dec_ref(v_val_809_);
v_name_811_ = lean_ctor_get(v_toConstantVal_810_, 0);
lean_inc(v_name_811_);
lean_dec_ref(v_toConstantVal_810_);
v___x_812_ = lean_box(0);
v___x_813_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_813_, 0, v_name_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
return v___x_813_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
if (lean_obj_tag(v_a_814_) == 0)
{
lean_object* v___x_816_; 
v___x_816_ = l_List_reverse___redArg(v_a_815_);
return v___x_816_;
}
else
{
lean_object* v_head_817_; lean_object* v_tail_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_827_; 
v_head_817_ = lean_ctor_get(v_a_814_, 0);
v_tail_818_ = lean_ctor_get(v_a_814_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_a_814_);
if (v_isSharedCheck_827_ == 0)
{
v___x_820_ = v_a_814_;
v_isShared_821_ = v_isSharedCheck_827_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_tail_818_);
lean_inc(v_head_817_);
lean_dec(v_a_814_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_827_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v_name_822_; lean_object* v___x_824_; 
v_name_822_ = lean_ctor_get(v_head_817_, 0);
lean_inc(v_name_822_);
lean_dec(v_head_817_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v_a_815_);
lean_ctor_set(v___x_820_, 0, v_name_822_);
v___x_824_ = v___x_820_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_name_822_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_a_815_);
v___x_824_ = v_reuseFailAlloc_826_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
v_a_814_ = v_tail_818_;
v_a_815_ = v___x_824_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
if (lean_obj_tag(v_a_831_) == 0)
{
lean_object* v___x_833_; 
v___x_833_ = lean_array_to_list(v_a_832_);
return v___x_833_;
}
else
{
lean_object* v_head_834_; lean_object* v_tail_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_851_; 
v_head_834_ = lean_ctor_get(v_a_831_, 0);
v_tail_835_ = lean_ctor_get(v_a_831_, 1);
v_isSharedCheck_851_ = !lean_is_exclusive(v_a_831_);
if (v_isSharedCheck_851_ == 0)
{
v___x_837_ = v_a_831_;
v_isShared_838_ = v_isSharedCheck_851_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_tail_835_);
lean_inc(v_head_834_);
lean_dec(v_a_831_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_851_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v_name_839_; lean_object* v_ctors_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_846_; 
v_name_839_ = lean_ctor_get(v_head_834_, 0);
lean_inc(v_name_839_);
v_ctors_840_ = lean_ctor_get(v_head_834_, 2);
lean_inc(v_ctors_840_);
lean_dec(v_head_834_);
v___x_841_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1));
v___x_842_ = l_Lean_Name_appendCore(v_name_839_, v___x_841_);
v___x_843_ = lean_box(0);
v___x_844_ = l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(v_ctors_840_, v___x_843_);
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 1, v___x_844_);
lean_ctor_set(v___x_837_, 0, v___x_842_);
v___x_846_ = v___x_837_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_844_);
v___x_846_ = v_reuseFailAlloc_850_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_847_, 0, v_name_839_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_832_, v___x_847_);
v_a_831_ = v_tail_835_;
v_a_832_ = v___x_848_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getNames(lean_object* v_x_878_){
_start:
{
switch(lean_obj_tag(v_x_878_))
{
case 4:
{
lean_object* v___x_879_; 
v___x_879_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__9));
return v___x_879_;
}
case 5:
{
lean_object* v_defns_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v_defns_880_ = lean_ctor_get(v_x_878_, 0);
lean_inc(v_defns_880_);
lean_dec_ref(v_x_878_);
v___x_881_ = lean_box(0);
v___x_882_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_880_, v___x_881_);
return v___x_882_;
}
case 6:
{
lean_object* v_types_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_types_883_ = lean_ctor_get(v_x_878_, 2);
lean_inc(v_types_883_);
lean_dec_ref(v_x_878_);
v___x_884_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__10));
v___x_885_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(v_types_883_, v___x_884_);
return v___x_885_;
}
default: 
{
lean_object* v_val_886_; lean_object* v_toConstantVal_887_; lean_object* v_name_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_val_886_ = lean_ctor_get(v_x_878_, 0);
lean_inc_ref(v_val_886_);
lean_dec(v_x_878_);
v_toConstantVal_887_ = lean_ctor_get(v_val_886_, 0);
lean_inc_ref(v_toConstantVal_887_);
lean_dec_ref(v_val_886_);
v_name_888_ = lean_ctor_get(v_toConstantVal_887_, 0);
lean_inc(v_name_888_);
lean_dec_ref(v_toConstantVal_887_);
v___x_889_ = lean_box(0);
v___x_890_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_890_, 0, v_name_888_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
return v___x_890_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__0(lean_object* v_f_891_, lean_object* v_value_892_, lean_object* v_a_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = lean_apply_2(v_f_891_, v_a_893_, v_value_892_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__3(lean_object* v_f_895_, lean_object* v_value_896_, lean_object* v_a_897_){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = lean_apply_2(v_f_895_, v_a_897_, v_value_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__1(lean_object* v_f_899_, lean_object* v_toBind_900_, lean_object* v_a_901_, lean_object* v_v_902_){
_start:
{
lean_object* v_toConstantVal_903_; lean_object* v_value_904_; lean_object* v_type_905_; lean_object* v___f_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_toConstantVal_903_ = lean_ctor_get(v_v_902_, 0);
lean_inc_ref(v_toConstantVal_903_);
v_value_904_ = lean_ctor_get(v_v_902_, 1);
lean_inc_ref(v_value_904_);
lean_dec_ref(v_v_902_);
v_type_905_ = lean_ctor_get(v_toConstantVal_903_, 2);
lean_inc_ref(v_type_905_);
lean_dec_ref(v_toConstantVal_903_);
lean_inc(v_f_899_);
v___f_906_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__3), 3, 2);
lean_closure_set(v___f_906_, 0, v_f_899_);
lean_closure_set(v___f_906_, 1, v_value_904_);
v___x_907_ = lean_apply_2(v_f_899_, v_a_901_, v_type_905_);
v___x_908_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_907_, v___f_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__2(lean_object* v_f_909_, lean_object* v_a_910_, lean_object* v_ctor_911_){
_start:
{
lean_object* v_type_912_; lean_object* v___x_913_; 
v_type_912_ = lean_ctor_get(v_ctor_911_, 1);
lean_inc_ref(v_type_912_);
lean_dec_ref(v_ctor_911_);
v___x_913_ = lean_apply_2(v_f_909_, v_a_910_, v_type_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__4(lean_object* v_inst_914_, lean_object* v___f_915_, lean_object* v_ctors_916_, lean_object* v_a_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_List_foldlM___redArg(v_inst_914_, v___f_915_, v_a_917_, v_ctors_916_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__5(lean_object* v_inst_919_, lean_object* v___f_920_, lean_object* v_f_921_, lean_object* v_toBind_922_, lean_object* v_a_923_, lean_object* v_inductType_924_){
_start:
{
lean_object* v_type_925_; lean_object* v_ctors_926_; lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_type_925_ = lean_ctor_get(v_inductType_924_, 1);
lean_inc_ref(v_type_925_);
v_ctors_926_ = lean_ctor_get(v_inductType_924_, 2);
lean_inc(v_ctors_926_);
lean_dec_ref(v_inductType_924_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__4), 4, 3);
lean_closure_set(v___f_927_, 0, v_inst_919_);
lean_closure_set(v___f_927_, 1, v___f_920_);
lean_closure_set(v___f_927_, 2, v_ctors_926_);
v___x_928_ = lean_apply_2(v_f_921_, v_a_923_, v_type_925_);
v___x_929_ = lean_apply_4(v_toBind_922_, lean_box(0), lean_box(0), v___x_928_, v___f_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object* v_inst_930_, lean_object* v_d_931_, lean_object* v_f_932_, lean_object* v_a_933_){
_start:
{
switch(lean_obj_tag(v_d_931_))
{
case 0:
{
lean_object* v_val_934_; lean_object* v_toConstantVal_935_; lean_object* v_type_936_; lean_object* v___x_937_; 
lean_dec_ref(v_inst_930_);
v_val_934_ = lean_ctor_get(v_d_931_, 0);
lean_inc_ref(v_val_934_);
lean_dec_ref(v_d_931_);
v_toConstantVal_935_ = lean_ctor_get(v_val_934_, 0);
lean_inc_ref(v_toConstantVal_935_);
lean_dec_ref(v_val_934_);
v_type_936_ = lean_ctor_get(v_toConstantVal_935_, 2);
lean_inc_ref(v_type_936_);
lean_dec_ref(v_toConstantVal_935_);
v___x_937_ = lean_apply_2(v_f_932_, v_a_933_, v_type_936_);
return v___x_937_;
}
case 4:
{
lean_object* v_toApplicative_938_; lean_object* v_toPure_939_; lean_object* v___x_940_; 
v_toApplicative_938_ = lean_ctor_get(v_inst_930_, 0);
lean_inc_ref(v_toApplicative_938_);
lean_dec(v_f_932_);
lean_dec_ref(v_inst_930_);
v_toPure_939_ = lean_ctor_get(v_toApplicative_938_, 1);
lean_inc(v_toPure_939_);
lean_dec_ref(v_toApplicative_938_);
v___x_940_ = lean_apply_2(v_toPure_939_, lean_box(0), v_a_933_);
return v___x_940_;
}
case 5:
{
lean_object* v_toBind_941_; lean_object* v_defns_942_; lean_object* v___f_943_; lean_object* v___x_944_; 
v_toBind_941_ = lean_ctor_get(v_inst_930_, 1);
v_defns_942_ = lean_ctor_get(v_d_931_, 0);
lean_inc(v_defns_942_);
lean_dec_ref(v_d_931_);
lean_inc(v_toBind_941_);
v___f_943_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_943_, 0, v_f_932_);
lean_closure_set(v___f_943_, 1, v_toBind_941_);
v___x_944_ = l_List_foldlM___redArg(v_inst_930_, v___f_943_, v_a_933_, v_defns_942_);
return v___x_944_;
}
case 6:
{
lean_object* v_toBind_945_; lean_object* v_types_946_; lean_object* v___f_947_; lean_object* v___f_948_; lean_object* v___x_949_; 
v_toBind_945_ = lean_ctor_get(v_inst_930_, 1);
v_types_946_ = lean_ctor_get(v_d_931_, 2);
lean_inc(v_types_946_);
lean_dec_ref(v_d_931_);
lean_inc(v_f_932_);
v___f_947_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__2), 3, 1);
lean_closure_set(v___f_947_, 0, v_f_932_);
lean_inc(v_toBind_945_);
lean_inc_ref(v_inst_930_);
v___f_948_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__5), 6, 4);
lean_closure_set(v___f_948_, 0, v_inst_930_);
lean_closure_set(v___f_948_, 1, v___f_947_);
lean_closure_set(v___f_948_, 2, v_f_932_);
lean_closure_set(v___f_948_, 3, v_toBind_945_);
v___x_949_ = l_List_foldlM___redArg(v_inst_930_, v___f_948_, v_a_933_, v_types_946_);
return v___x_949_;
}
default: 
{
lean_object* v_val_950_; lean_object* v_toConstantVal_951_; lean_object* v_toBind_952_; lean_object* v_value_953_; lean_object* v_type_954_; lean_object* v___f_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_val_950_ = lean_ctor_get(v_d_931_, 0);
lean_inc_ref(v_val_950_);
lean_dec(v_d_931_);
v_toConstantVal_951_ = lean_ctor_get(v_val_950_, 0);
lean_inc_ref(v_toConstantVal_951_);
v_toBind_952_ = lean_ctor_get(v_inst_930_, 1);
lean_inc(v_toBind_952_);
lean_dec_ref(v_inst_930_);
v_value_953_ = lean_ctor_get(v_val_950_, 1);
lean_inc_ref(v_value_953_);
lean_dec_ref(v_val_950_);
v_type_954_ = lean_ctor_get(v_toConstantVal_951_, 2);
lean_inc_ref(v_type_954_);
lean_dec_ref(v_toConstantVal_951_);
lean_inc(v_f_932_);
v___f_955_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_955_, 0, v_f_932_);
lean_closure_set(v___f_955_, 1, v_value_953_);
v___x_956_ = lean_apply_2(v_f_932_, v_a_933_, v_type_954_);
v___x_957_ = lean_apply_4(v_toBind_952_, lean_box(0), lean_box(0), v___x_956_, v___f_955_);
return v___x_957_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM(lean_object* v_00_u03b1_958_, lean_object* v_m_959_, lean_object* v_inst_960_, lean_object* v_d_961_, lean_object* v_f_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_Declaration_foldExprM___redArg(v_inst_960_, v_d_961_, v_f_962_, v_a_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg___lam__0(lean_object* v_f_965_, lean_object* v_x_966_, lean_object* v_a_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = lean_apply_1(v_f_965_, v_a_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg(lean_object* v_inst_969_, lean_object* v_d_970_, lean_object* v_f_971_){
_start:
{
lean_object* v___f_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___f_972_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_972_, 0, v_f_971_);
v___x_973_ = lean_box(0);
v___x_974_ = l_Lean_Declaration_foldExprM___redArg(v_inst_969_, v_d_970_, v___f_972_, v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM(lean_object* v_m_975_, lean_object* v_inst_976_, lean_object* v_d_977_, lean_object* v_f_978_){
_start:
{
lean_object* v___f_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___f_979_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_979_, 0, v_f_978_);
v___x_980_ = lean_box(0);
v___x_981_ = l_Lean_Declaration_foldExprM___redArg(v_inst_976_, v_d_977_, v___f_979_, v___x_980_);
return v___x_981_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default___closed__0(void){
_start:
{
uint8_t v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_982_ = 0;
v___x_983_ = lean_box(0);
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = l_Lean_instInhabitedConstantVal_default;
v___x_986_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_986_, 0, v___x_985_);
lean_ctor_set(v___x_986_, 1, v___x_984_);
lean_ctor_set(v___x_986_, 2, v___x_984_);
lean_ctor_set(v___x_986_, 3, v___x_983_);
lean_ctor_set(v___x_986_, 4, v___x_983_);
lean_ctor_set(v___x_986_, 5, v___x_984_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*6, v___x_982_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*6 + 1, v___x_982_);
lean_ctor_set_uint8(v___x_986_, sizeof(void*)*6 + 2, v___x_982_);
return v___x_986_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default(void){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_obj_once(&l_Lean_instInhabitedInductiveVal_default___closed__0, &l_Lean_instInhabitedInductiveVal_default___closed__0_once, _init_l_Lean_instInhabitedInductiveVal_default___closed__0);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal(void){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l_Lean_instInhabitedInductiveVal_default;
return v___x_988_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_val(lean_object* v_name_989_, lean_object* v_levelParams_990_, lean_object* v_type_991_, lean_object* v_numParams_992_, lean_object* v_numIndices_993_, lean_object* v_all_994_, lean_object* v_ctors_995_, lean_object* v_numNested_996_, uint8_t v_isRec_997_, uint8_t v_isUnsafe_998_, uint8_t v_isReflexive_999_){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1000_, 0, v_name_989_);
lean_ctor_set(v___x_1000_, 1, v_levelParams_990_);
lean_ctor_set(v___x_1000_, 2, v_type_991_);
v___x_1001_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v_numParams_992_);
lean_ctor_set(v___x_1001_, 2, v_numIndices_993_);
lean_ctor_set(v___x_1001_, 3, v_all_994_);
lean_ctor_set(v___x_1001_, 4, v_ctors_995_);
lean_ctor_set(v___x_1001_, 5, v_numNested_996_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*6, v_isRec_997_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*6 + 1, v_isUnsafe_998_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*6 + 2, v_isReflexive_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveValEx___boxed(lean_object* v_name_1002_, lean_object* v_levelParams_1003_, lean_object* v_type_1004_, lean_object* v_numParams_1005_, lean_object* v_numIndices_1006_, lean_object* v_all_1007_, lean_object* v_ctors_1008_, lean_object* v_numNested_1009_, lean_object* v_isRec_1010_, lean_object* v_isUnsafe_1011_, lean_object* v_isReflexive_1012_){
_start:
{
uint8_t v_isRec_boxed_1013_; uint8_t v_isUnsafe_boxed_1014_; uint8_t v_isReflexive_boxed_1015_; lean_object* v_res_1016_; 
v_isRec_boxed_1013_ = lean_unbox(v_isRec_1010_);
v_isUnsafe_boxed_1014_ = lean_unbox(v_isUnsafe_1011_);
v_isReflexive_boxed_1015_ = lean_unbox(v_isReflexive_1012_);
v_res_1016_ = lean_mk_inductive_val(v_name_1002_, v_levelParams_1003_, v_type_1004_, v_numParams_1005_, v_numIndices_1006_, v_all_1007_, v_ctors_1008_, v_numNested_1009_, v_isRec_boxed_1013_, v_isUnsafe_boxed_1014_, v_isReflexive_boxed_1015_);
return v_res_1016_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_rec(lean_object* v_v_1017_){
_start:
{
uint8_t v_isRec_1018_; 
v_isRec_1018_ = lean_ctor_get_uint8(v_v_1017_, sizeof(void*)*6);
lean_dec_ref(v_v_1017_);
return v_isRec_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isRecEx___boxed(lean_object* v_v_1019_){
_start:
{
uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_res_1020_ = lean_inductive_val_is_rec(v_v_1019_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_unsafe(lean_object* v_v_1022_){
_start:
{
uint8_t v_isUnsafe_1023_; 
v_isUnsafe_1023_ = lean_ctor_get_uint8(v_v_1022_, sizeof(void*)*6 + 1);
lean_dec_ref(v_v_1022_);
return v_isUnsafe_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isUnsafeEx___boxed(lean_object* v_v_1024_){
_start:
{
uint8_t v_res_1025_; lean_object* v_r_1026_; 
v_res_1025_ = lean_inductive_val_is_unsafe(v_v_1024_);
v_r_1026_ = lean_box(v_res_1025_);
return v_r_1026_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_reflexive(lean_object* v_v_1027_){
_start:
{
uint8_t v_isReflexive_1028_; 
v_isReflexive_1028_ = lean_ctor_get_uint8(v_v_1027_, sizeof(void*)*6 + 2);
lean_dec_ref(v_v_1027_);
return v_isReflexive_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isReflexiveEx___boxed(lean_object* v_v_1029_){
_start:
{
uint8_t v_res_1030_; lean_object* v_r_1031_; 
v_res_1030_ = lean_inductive_val_is_reflexive(v_v_1029_);
v_r_1031_ = lean_box(v_res_1030_);
return v_r_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors(lean_object* v_v_1032_){
_start:
{
lean_object* v_ctors_1033_; lean_object* v___x_1034_; 
v_ctors_1033_ = lean_ctor_get(v_v_1032_, 4);
v___x_1034_ = l_List_lengthTR___redArg(v_ctors_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors___boxed(lean_object* v_v_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_InductiveVal_numCtors(v_v_1035_);
lean_dec_ref(v_v_1035_);
return v_res_1036_;
}
}
LEAN_EXPORT uint8_t l_Lean_InductiveVal_isNested(lean_object* v_v_1037_){
_start:
{
lean_object* v_numNested_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_numNested_1038_ = lean_ctor_get(v_v_1037_, 5);
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_nat_dec_lt(v___x_1039_, v_numNested_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isNested___boxed(lean_object* v_v_1041_){
_start:
{
uint8_t v_res_1042_; lean_object* v_r_1043_; 
v_res_1042_ = l_Lean_InductiveVal_isNested(v_v_1041_);
lean_dec_ref(v_v_1041_);
v_r_1043_ = lean_box(v_res_1042_);
return v_r_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object* v_v_1044_){
_start:
{
lean_object* v_all_1045_; lean_object* v_numNested_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v_all_1045_ = lean_ctor_get(v_v_1044_, 3);
v_numNested_1046_ = lean_ctor_get(v_v_1044_, 5);
v___x_1047_ = l_List_lengthTR___redArg(v_all_1045_);
v___x_1048_ = lean_nat_add(v___x_1047_, v_numNested_1046_);
lean_dec(v___x_1047_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers___boxed(lean_object* v_v_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Lean_InductiveVal_numTypeFormers(v_v_1049_);
lean_dec_ref(v_v_1049_);
return v_res_1050_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1051_ = 0;
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = lean_box(0);
v___x_1054_ = l_Lean_instInhabitedConstantVal_default;
v___x_1055_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v___x_1053_);
lean_ctor_set(v___x_1055_, 2, v___x_1052_);
lean_ctor_set(v___x_1055_, 3, v___x_1052_);
lean_ctor_set(v___x_1055_, 4, v___x_1052_);
lean_ctor_set_uint8(v___x_1055_, sizeof(void*)*5, v___x_1051_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default(void){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_obj_once(&l_Lean_instInhabitedConstructorVal_default___closed__0, &l_Lean_instInhabitedConstructorVal_default___closed__0_once, _init_l_Lean_instInhabitedConstructorVal_default___closed__0);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal(void){
_start:
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_instInhabitedConstructorVal_default;
return v___x_1057_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructorVal_beq(lean_object* v_x_1058_, lean_object* v_x_1059_){
_start:
{
lean_object* v_toConstantVal_1060_; lean_object* v_induct_1061_; lean_object* v_cidx_1062_; lean_object* v_numParams_1063_; lean_object* v_numFields_1064_; uint8_t v_isUnsafe_1065_; lean_object* v_toConstantVal_1066_; lean_object* v_induct_1067_; lean_object* v_cidx_1068_; lean_object* v_numParams_1069_; lean_object* v_numFields_1070_; uint8_t v_isUnsafe_1071_; uint8_t v___x_1072_; 
v_toConstantVal_1060_ = lean_ctor_get(v_x_1058_, 0);
v_induct_1061_ = lean_ctor_get(v_x_1058_, 1);
v_cidx_1062_ = lean_ctor_get(v_x_1058_, 2);
v_numParams_1063_ = lean_ctor_get(v_x_1058_, 3);
v_numFields_1064_ = lean_ctor_get(v_x_1058_, 4);
v_isUnsafe_1065_ = lean_ctor_get_uint8(v_x_1058_, sizeof(void*)*5);
v_toConstantVal_1066_ = lean_ctor_get(v_x_1059_, 0);
v_induct_1067_ = lean_ctor_get(v_x_1059_, 1);
v_cidx_1068_ = lean_ctor_get(v_x_1059_, 2);
v_numParams_1069_ = lean_ctor_get(v_x_1059_, 3);
v_numFields_1070_ = lean_ctor_get(v_x_1059_, 4);
v_isUnsafe_1071_ = lean_ctor_get_uint8(v_x_1059_, sizeof(void*)*5);
v___x_1072_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1060_, v_toConstantVal_1066_);
if (v___x_1072_ == 0)
{
return v___x_1072_;
}
else
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_name_eq(v_induct_1061_, v_induct_1067_);
if (v___x_1073_ == 0)
{
return v___x_1073_;
}
else
{
uint8_t v___x_1074_; 
v___x_1074_ = lean_nat_dec_eq(v_cidx_1062_, v_cidx_1068_);
if (v___x_1074_ == 0)
{
return v___x_1074_;
}
else
{
uint8_t v___x_1075_; 
v___x_1075_ = lean_nat_dec_eq(v_numParams_1063_, v_numParams_1069_);
if (v___x_1075_ == 0)
{
return v___x_1075_;
}
else
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_nat_dec_eq(v_numFields_1064_, v_numFields_1070_);
if (v___x_1076_ == 0)
{
return v___x_1076_;
}
else
{
if (v_isUnsafe_1065_ == 0)
{
if (v_isUnsafe_1071_ == 0)
{
return v___x_1076_;
}
else
{
return v_isUnsafe_1065_;
}
}
else
{
return v_isUnsafe_1071_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructorVal_beq___boxed(lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
uint8_t v_res_1079_; lean_object* v_r_1080_; 
v_res_1079_ = l_Lean_instBEqConstructorVal_beq(v_x_1077_, v_x_1078_);
lean_dec_ref(v_x_1078_);
lean_dec_ref(v_x_1077_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
}
}
LEAN_EXPORT lean_object* lean_mk_constructor_val(lean_object* v_name_1083_, lean_object* v_levelParams_1084_, lean_object* v_type_1085_, lean_object* v_induct_1086_, lean_object* v_cidx_1087_, lean_object* v_numParams_1088_, lean_object* v_numFields_1089_, uint8_t v_isUnsafe_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
v___x_1091_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1091_, 0, v_name_1083_);
lean_ctor_set(v___x_1091_, 1, v_levelParams_1084_);
lean_ctor_set(v___x_1091_, 2, v_type_1085_);
v___x_1092_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
lean_ctor_set(v___x_1092_, 1, v_induct_1086_);
lean_ctor_set(v___x_1092_, 2, v_cidx_1087_);
lean_ctor_set(v___x_1092_, 3, v_numParams_1088_);
lean_ctor_set(v___x_1092_, 4, v_numFields_1089_);
lean_ctor_set_uint8(v___x_1092_, sizeof(void*)*5, v_isUnsafe_1090_);
return v___x_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstructorValEx___boxed(lean_object* v_name_1093_, lean_object* v_levelParams_1094_, lean_object* v_type_1095_, lean_object* v_induct_1096_, lean_object* v_cidx_1097_, lean_object* v_numParams_1098_, lean_object* v_numFields_1099_, lean_object* v_isUnsafe_1100_){
_start:
{
uint8_t v_isUnsafe_boxed_1101_; lean_object* v_res_1102_; 
v_isUnsafe_boxed_1101_ = lean_unbox(v_isUnsafe_1100_);
v_res_1102_ = lean_mk_constructor_val(v_name_1093_, v_levelParams_1094_, v_type_1095_, v_induct_1096_, v_cidx_1097_, v_numParams_1098_, v_numFields_1099_, v_isUnsafe_boxed_1101_);
return v_res_1102_;
}
}
LEAN_EXPORT uint8_t lean_constructor_val_is_unsafe(lean_object* v_v_1103_){
_start:
{
uint8_t v_isUnsafe_1104_; 
v_isUnsafe_1104_ = lean_ctor_get_uint8(v_v_1103_, sizeof(void*)*5);
lean_dec_ref(v_v_1103_);
return v_isUnsafe_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstructorVal_isUnsafeEx___boxed(lean_object* v_v_1105_){
_start:
{
uint8_t v_res_1106_; lean_object* v_r_1107_; 
v_res_1106_ = lean_constructor_val_is_unsafe(v_v_1105_);
v_r_1107_ = lean_box(v_res_1106_);
return v_r_1107_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default___closed__0(void){
_start:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1108_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = lean_box(0);
v___x_1111_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v___x_1109_);
lean_ctor_set(v___x_1111_, 2, v___x_1108_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default(void){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_obj_once(&l_Lean_instInhabitedRecursorRule_default___closed__0, &l_Lean_instInhabitedRecursorRule_default___closed__0_once, _init_l_Lean_instInhabitedRecursorRule_default___closed__0);
return v___x_1112_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule(void){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Lean_instInhabitedRecursorRule_default;
return v___x_1113_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorRule_beq(lean_object* v_x_1114_, lean_object* v_x_1115_){
_start:
{
lean_object* v_ctor_1116_; lean_object* v_nfields_1117_; lean_object* v_rhs_1118_; lean_object* v_ctor_1119_; lean_object* v_nfields_1120_; lean_object* v_rhs_1121_; uint8_t v___x_1122_; 
v_ctor_1116_ = lean_ctor_get(v_x_1114_, 0);
v_nfields_1117_ = lean_ctor_get(v_x_1114_, 1);
v_rhs_1118_ = lean_ctor_get(v_x_1114_, 2);
v_ctor_1119_ = lean_ctor_get(v_x_1115_, 0);
v_nfields_1120_ = lean_ctor_get(v_x_1115_, 1);
v_rhs_1121_ = lean_ctor_get(v_x_1115_, 2);
v___x_1122_ = lean_name_eq(v_ctor_1116_, v_ctor_1119_);
if (v___x_1122_ == 0)
{
return v___x_1122_;
}
else
{
uint8_t v___x_1123_; 
v___x_1123_ = lean_nat_dec_eq(v_nfields_1117_, v_nfields_1120_);
if (v___x_1123_ == 0)
{
return v___x_1123_;
}
else
{
uint8_t v___x_1124_; 
v___x_1124_ = lean_expr_eqv(v_rhs_1118_, v_rhs_1121_);
return v___x_1124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorRule_beq___boxed(lean_object* v_x_1125_, lean_object* v_x_1126_){
_start:
{
uint8_t v_res_1127_; lean_object* v_r_1128_; 
v_res_1127_ = l_Lean_instBEqRecursorRule_beq(v_x_1125_, v_x_1126_);
lean_dec_ref(v_x_1126_);
lean_dec_ref(v_x_1125_);
v_r_1128_ = lean_box(v_res_1127_);
return v_r_1128_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1131_ = 0;
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_box(0);
v___x_1134_ = l_Lean_instInhabitedConstantVal_default;
v___x_1135_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v___x_1133_);
lean_ctor_set(v___x_1135_, 2, v___x_1132_);
lean_ctor_set(v___x_1135_, 3, v___x_1132_);
lean_ctor_set(v___x_1135_, 4, v___x_1132_);
lean_ctor_set(v___x_1135_, 5, v___x_1132_);
lean_ctor_set(v___x_1135_, 6, v___x_1133_);
lean_ctor_set_uint8(v___x_1135_, sizeof(void*)*7, v___x_1131_);
lean_ctor_set_uint8(v___x_1135_, sizeof(void*)*7 + 1, v___x_1131_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default(void){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_obj_once(&l_Lean_instInhabitedRecursorVal_default___closed__0, &l_Lean_instInhabitedRecursorVal_default___closed__0_once, _init_l_Lean_instInhabitedRecursorVal_default___closed__0);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal(void){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_instInhabitedRecursorVal_default;
return v___x_1137_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
if (lean_obj_tag(v_x_1138_) == 0)
{
if (lean_obj_tag(v_x_1139_) == 0)
{
uint8_t v___x_1140_; 
v___x_1140_ = 1;
return v___x_1140_;
}
else
{
uint8_t v___x_1141_; 
v___x_1141_ = 0;
return v___x_1141_;
}
}
else
{
if (lean_obj_tag(v_x_1139_) == 0)
{
uint8_t v___x_1142_; 
v___x_1142_ = 0;
return v___x_1142_;
}
else
{
lean_object* v_head_1143_; lean_object* v_tail_1144_; lean_object* v_head_1145_; lean_object* v_tail_1146_; uint8_t v___x_1147_; 
v_head_1143_ = lean_ctor_get(v_x_1138_, 0);
v_tail_1144_ = lean_ctor_get(v_x_1138_, 1);
v_head_1145_ = lean_ctor_get(v_x_1139_, 0);
v_tail_1146_ = lean_ctor_get(v_x_1139_, 1);
v___x_1147_ = l_Lean_instBEqRecursorRule_beq(v_head_1143_, v_head_1145_);
if (v___x_1147_ == 0)
{
return v___x_1147_;
}
else
{
v_x_1138_ = v_tail_1144_;
v_x_1139_ = v_tail_1146_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0___boxed(lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
uint8_t v_res_1151_; lean_object* v_r_1152_; 
v_res_1151_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_x_1149_, v_x_1150_);
lean_dec(v_x_1150_);
lean_dec(v_x_1149_);
v_r_1152_ = lean_box(v_res_1151_);
return v_r_1152_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorVal_beq(lean_object* v_x_1153_, lean_object* v_x_1154_){
_start:
{
lean_object* v_toConstantVal_1155_; lean_object* v_all_1156_; lean_object* v_numParams_1157_; lean_object* v_numIndices_1158_; lean_object* v_numMotives_1159_; lean_object* v_numMinors_1160_; lean_object* v_rules_1161_; uint8_t v_k_1162_; uint8_t v_isUnsafe_1163_; lean_object* v_toConstantVal_1164_; lean_object* v_all_1165_; lean_object* v_numParams_1166_; lean_object* v_numIndices_1167_; lean_object* v_numMotives_1168_; lean_object* v_numMinors_1169_; lean_object* v_rules_1170_; uint8_t v_k_1171_; uint8_t v_isUnsafe_1172_; uint8_t v___y_1174_; uint8_t v___x_1175_; 
v_toConstantVal_1155_ = lean_ctor_get(v_x_1153_, 0);
v_all_1156_ = lean_ctor_get(v_x_1153_, 1);
v_numParams_1157_ = lean_ctor_get(v_x_1153_, 2);
v_numIndices_1158_ = lean_ctor_get(v_x_1153_, 3);
v_numMotives_1159_ = lean_ctor_get(v_x_1153_, 4);
v_numMinors_1160_ = lean_ctor_get(v_x_1153_, 5);
v_rules_1161_ = lean_ctor_get(v_x_1153_, 6);
v_k_1162_ = lean_ctor_get_uint8(v_x_1153_, sizeof(void*)*7);
v_isUnsafe_1163_ = lean_ctor_get_uint8(v_x_1153_, sizeof(void*)*7 + 1);
v_toConstantVal_1164_ = lean_ctor_get(v_x_1154_, 0);
v_all_1165_ = lean_ctor_get(v_x_1154_, 1);
v_numParams_1166_ = lean_ctor_get(v_x_1154_, 2);
v_numIndices_1167_ = lean_ctor_get(v_x_1154_, 3);
v_numMotives_1168_ = lean_ctor_get(v_x_1154_, 4);
v_numMinors_1169_ = lean_ctor_get(v_x_1154_, 5);
v_rules_1170_ = lean_ctor_get(v_x_1154_, 6);
v_k_1171_ = lean_ctor_get_uint8(v_x_1154_, sizeof(void*)*7);
v_isUnsafe_1172_ = lean_ctor_get_uint8(v_x_1154_, sizeof(void*)*7 + 1);
v___x_1175_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1155_, v_toConstantVal_1164_);
if (v___x_1175_ == 0)
{
return v___x_1175_;
}
else
{
uint8_t v___x_1176_; 
v___x_1176_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_1156_, v_all_1165_);
if (v___x_1176_ == 0)
{
return v___x_1176_;
}
else
{
uint8_t v___x_1177_; 
v___x_1177_ = lean_nat_dec_eq(v_numParams_1157_, v_numParams_1166_);
if (v___x_1177_ == 0)
{
return v___x_1177_;
}
else
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_nat_dec_eq(v_numIndices_1158_, v_numIndices_1167_);
if (v___x_1178_ == 0)
{
return v___x_1178_;
}
else
{
uint8_t v___x_1179_; 
v___x_1179_ = lean_nat_dec_eq(v_numMotives_1159_, v_numMotives_1168_);
if (v___x_1179_ == 0)
{
return v___x_1179_;
}
else
{
uint8_t v___x_1180_; 
v___x_1180_ = lean_nat_dec_eq(v_numMinors_1160_, v_numMinors_1169_);
if (v___x_1180_ == 0)
{
return v___x_1180_;
}
else
{
uint8_t v___x_1181_; 
v___x_1181_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_rules_1161_, v_rules_1170_);
if (v___x_1181_ == 0)
{
return v___x_1181_;
}
else
{
if (v_k_1162_ == 0)
{
if (v_k_1171_ == 0)
{
v___y_1174_ = v___x_1181_;
goto v___jp_1173_;
}
else
{
return v_k_1162_;
}
}
else
{
v___y_1174_ = v_k_1171_;
goto v___jp_1173_;
}
}
}
}
}
}
}
}
v___jp_1173_:
{
if (v___y_1174_ == 0)
{
return v___y_1174_;
}
else
{
if (v_isUnsafe_1163_ == 0)
{
if (v_isUnsafe_1172_ == 0)
{
return v___y_1174_;
}
else
{
return v_isUnsafe_1163_;
}
}
else
{
return v_isUnsafe_1172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorVal_beq___boxed(lean_object* v_x_1182_, lean_object* v_x_1183_){
_start:
{
uint8_t v_res_1184_; lean_object* v_r_1185_; 
v_res_1184_ = l_Lean_instBEqRecursorVal_beq(v_x_1182_, v_x_1183_);
lean_dec_ref(v_x_1183_);
lean_dec_ref(v_x_1182_);
v_r_1185_ = lean_box(v_res_1184_);
return v_r_1185_;
}
}
LEAN_EXPORT lean_object* lean_mk_recursor_val(lean_object* v_name_1188_, lean_object* v_levelParams_1189_, lean_object* v_type_1190_, lean_object* v_all_1191_, lean_object* v_numParams_1192_, lean_object* v_numIndices_1193_, lean_object* v_numMotives_1194_, lean_object* v_numMinors_1195_, lean_object* v_rules_1196_, uint8_t v_k_1197_, uint8_t v_isUnsafe_1198_){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1199_, 0, v_name_1188_);
lean_ctor_set(v___x_1199_, 1, v_levelParams_1189_);
lean_ctor_set(v___x_1199_, 2, v_type_1190_);
v___x_1200_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1200_, 0, v___x_1199_);
lean_ctor_set(v___x_1200_, 1, v_all_1191_);
lean_ctor_set(v___x_1200_, 2, v_numParams_1192_);
lean_ctor_set(v___x_1200_, 3, v_numIndices_1193_);
lean_ctor_set(v___x_1200_, 4, v_numMotives_1194_);
lean_ctor_set(v___x_1200_, 5, v_numMinors_1195_);
lean_ctor_set(v___x_1200_, 6, v_rules_1196_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*7, v_k_1197_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*7 + 1, v_isUnsafe_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecursorValEx___boxed(lean_object* v_name_1201_, lean_object* v_levelParams_1202_, lean_object* v_type_1203_, lean_object* v_all_1204_, lean_object* v_numParams_1205_, lean_object* v_numIndices_1206_, lean_object* v_numMotives_1207_, lean_object* v_numMinors_1208_, lean_object* v_rules_1209_, lean_object* v_k_1210_, lean_object* v_isUnsafe_1211_){
_start:
{
uint8_t v_k_boxed_1212_; uint8_t v_isUnsafe_boxed_1213_; lean_object* v_res_1214_; 
v_k_boxed_1212_ = lean_unbox(v_k_1210_);
v_isUnsafe_boxed_1213_ = lean_unbox(v_isUnsafe_1211_);
v_res_1214_ = lean_mk_recursor_val(v_name_1201_, v_levelParams_1202_, v_type_1203_, v_all_1204_, v_numParams_1205_, v_numIndices_1206_, v_numMotives_1207_, v_numMinors_1208_, v_rules_1209_, v_k_boxed_1212_, v_isUnsafe_boxed_1213_);
return v_res_1214_;
}
}
LEAN_EXPORT uint8_t lean_recursor_k(lean_object* v_v_1215_){
_start:
{
uint8_t v_k_1216_; 
v_k_1216_ = lean_ctor_get_uint8(v_v_1215_, sizeof(void*)*7);
lean_dec_ref(v_v_1215_);
return v_k_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_kEx___boxed(lean_object* v_v_1217_){
_start:
{
uint8_t v_res_1218_; lean_object* v_r_1219_; 
v_res_1218_ = lean_recursor_k(v_v_1217_);
v_r_1219_ = lean_box(v_res_1218_);
return v_r_1219_;
}
}
LEAN_EXPORT uint8_t lean_recursor_is_unsafe(lean_object* v_v_1220_){
_start:
{
uint8_t v_isUnsafe_1221_; 
v_isUnsafe_1221_ = lean_ctor_get_uint8(v_v_1220_, sizeof(void*)*7 + 1);
lean_dec_ref(v_v_1220_);
return v_isUnsafe_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_isUnsafeEx___boxed(lean_object* v_v_1222_){
_start:
{
uint8_t v_res_1223_; lean_object* v_r_1224_; 
v_res_1223_ = lean_recursor_is_unsafe(v_v_1222_);
v_r_1224_ = lean_box(v_res_1223_);
return v_r_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object* v_v_1225_){
_start:
{
lean_object* v_numParams_1226_; lean_object* v_numIndices_1227_; lean_object* v_numMotives_1228_; lean_object* v_numMinors_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v_numParams_1226_ = lean_ctor_get(v_v_1225_, 2);
v_numIndices_1227_ = lean_ctor_get(v_v_1225_, 3);
v_numMotives_1228_ = lean_ctor_get(v_v_1225_, 4);
v_numMinors_1229_ = lean_ctor_get(v_v_1225_, 5);
v___x_1230_ = lean_nat_add(v_numParams_1226_, v_numMotives_1228_);
v___x_1231_ = lean_nat_add(v___x_1230_, v_numMinors_1229_);
lean_dec(v___x_1230_);
v___x_1232_ = lean_nat_add(v___x_1231_, v_numIndices_1227_);
lean_dec(v___x_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx___boxed(lean_object* v_v_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_RecursorVal_getMajorIdx(v_v_1233_);
lean_dec_ref(v_v_1233_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx(lean_object* v_v_1235_){
_start:
{
lean_object* v_numParams_1236_; lean_object* v_numMotives_1237_; lean_object* v_numMinors_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_numParams_1236_ = lean_ctor_get(v_v_1235_, 2);
v_numMotives_1237_ = lean_ctor_get(v_v_1235_, 4);
v_numMinors_1238_ = lean_ctor_get(v_v_1235_, 5);
v___x_1239_ = lean_nat_add(v_numParams_1236_, v_numMotives_1237_);
v___x_1240_ = lean_nat_add(v___x_1239_, v_numMinors_1238_);
lean_dec(v___x_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx___boxed(lean_object* v_v_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l_Lean_RecursorVal_getFirstIndexIdx(v_v_1241_);
lean_dec_ref(v_v_1241_);
return v_res_1242_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx(lean_object* v_v_1243_){
_start:
{
lean_object* v_numParams_1244_; lean_object* v_numMotives_1245_; lean_object* v___x_1246_; 
v_numParams_1244_ = lean_ctor_get(v_v_1243_, 2);
v_numMotives_1245_ = lean_ctor_get(v_v_1243_, 4);
v___x_1246_ = lean_nat_add(v_numParams_1244_, v_numMotives_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx___boxed(lean_object* v_v_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Lean_RecursorVal_getFirstMinorIdx(v_v_1247_);
lean_dec_ref(v_v_1247_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(lean_object* v_x_1249_, lean_object* v_x_1250_){
_start:
{
lean_object* v_zero_1251_; uint8_t v_isZero_1252_; 
v_zero_1251_ = lean_unsigned_to_nat(0u);
v_isZero_1252_ = lean_nat_dec_eq(v_x_1249_, v_zero_1251_);
if (v_isZero_1252_ == 1)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
lean_dec(v_x_1249_);
v___x_1253_ = l_Lean_Expr_bindingDomain_x21(v_x_1250_);
lean_dec_ref(v_x_1250_);
v___x_1254_ = l_Lean_Expr_getAppFn(v___x_1253_);
lean_dec_ref(v___x_1253_);
v___x_1255_ = l_Lean_Expr_constName_x21(v___x_1254_);
lean_dec_ref(v___x_1254_);
return v___x_1255_;
}
else
{
lean_object* v_one_1256_; lean_object* v_n_1257_; lean_object* v___x_1258_; 
v_one_1256_ = lean_unsigned_to_nat(1u);
v_n_1257_ = lean_nat_sub(v_x_1249_, v_one_1256_);
lean_dec(v_x_1249_);
v___x_1258_ = l_Lean_Expr_bindingBody_x21(v_x_1250_);
lean_dec_ref(v_x_1250_);
v_x_1249_ = v_n_1257_;
v_x_1250_ = v___x_1258_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorInduct(lean_object* v_v_1260_){
_start:
{
lean_object* v_toConstantVal_1261_; lean_object* v_type_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v_toConstantVal_1261_ = lean_ctor_get(v_v_1260_, 0);
v_type_1262_ = lean_ctor_get(v_toConstantVal_1261_, 2);
lean_inc_ref(v_type_1262_);
v___x_1263_ = l_Lean_RecursorVal_getMajorIdx(v_v_1260_);
lean_dec_ref(v_v_1260_);
v___x_1264_ = l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(v___x_1263_, v_type_1262_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx(uint8_t v_x_1265_){
_start:
{
switch(v_x_1265_)
{
case 0:
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_unsigned_to_nat(0u);
return v___x_1266_;
}
case 1:
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_unsigned_to_nat(1u);
return v___x_1267_;
}
case 2:
{
lean_object* v___x_1268_; 
v___x_1268_ = lean_unsigned_to_nat(2u);
return v___x_1268_;
}
default: 
{
lean_object* v___x_1269_; 
v___x_1269_ = lean_unsigned_to_nat(3u);
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___boxed(lean_object* v_x_1270_){
_start:
{
uint8_t v_x_boxed_1271_; lean_object* v_res_1272_; 
v_x_boxed_1271_ = lean_unbox(v_x_1270_);
v_res_1272_ = l_Lean_QuotKind_ctorIdx(v_x_boxed_1271_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_toCtorIdx(uint8_t v_x_1273_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_QuotKind_ctorIdx(v_x_1273_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_toCtorIdx___boxed(lean_object* v_x_1275_){
_start:
{
uint8_t v_x_4__boxed_1276_; lean_object* v_res_1277_; 
v_x_4__boxed_1276_ = lean_unbox(v_x_1275_);
v_res_1277_ = l_Lean_QuotKind_toCtorIdx(v_x_4__boxed_1276_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg(lean_object* v_k_1278_){
_start:
{
lean_inc(v_k_1278_);
return v_k_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg___boxed(lean_object* v_k_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_QuotKind_ctorElim___redArg(v_k_1279_);
lean_dec(v_k_1279_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim(lean_object* v_motive_1281_, lean_object* v_ctorIdx_1282_, uint8_t v_t_1283_, lean_object* v_h_1284_, lean_object* v_k_1285_){
_start:
{
lean_inc(v_k_1285_);
return v_k_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___boxed(lean_object* v_motive_1286_, lean_object* v_ctorIdx_1287_, lean_object* v_t_1288_, lean_object* v_h_1289_, lean_object* v_k_1290_){
_start:
{
uint8_t v_t_boxed_1291_; lean_object* v_res_1292_; 
v_t_boxed_1291_ = lean_unbox(v_t_1288_);
v_res_1292_ = l_Lean_QuotKind_ctorElim(v_motive_1286_, v_ctorIdx_1287_, v_t_boxed_1291_, v_h_1289_, v_k_1290_);
lean_dec(v_k_1290_);
lean_dec(v_ctorIdx_1287_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg(lean_object* v_type_1293_){
_start:
{
lean_inc(v_type_1293_);
return v_type_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg___boxed(lean_object* v_type_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_QuotKind_type_elim___redArg(v_type_1294_);
lean_dec(v_type_1294_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim(lean_object* v_motive_1296_, uint8_t v_t_1297_, lean_object* v_h_1298_, lean_object* v_type_1299_){
_start:
{
lean_inc(v_type_1299_);
return v_type_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___boxed(lean_object* v_motive_1300_, lean_object* v_t_1301_, lean_object* v_h_1302_, lean_object* v_type_1303_){
_start:
{
uint8_t v_t_boxed_1304_; lean_object* v_res_1305_; 
v_t_boxed_1304_ = lean_unbox(v_t_1301_);
v_res_1305_ = l_Lean_QuotKind_type_elim(v_motive_1300_, v_t_boxed_1304_, v_h_1302_, v_type_1303_);
lean_dec(v_type_1303_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg(lean_object* v_ctor_1306_){
_start:
{
lean_inc(v_ctor_1306_);
return v_ctor_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg___boxed(lean_object* v_ctor_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Lean_QuotKind_ctor_elim___redArg(v_ctor_1307_);
lean_dec(v_ctor_1307_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim(lean_object* v_motive_1309_, uint8_t v_t_1310_, lean_object* v_h_1311_, lean_object* v_ctor_1312_){
_start:
{
lean_inc(v_ctor_1312_);
return v_ctor_1312_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___boxed(lean_object* v_motive_1313_, lean_object* v_t_1314_, lean_object* v_h_1315_, lean_object* v_ctor_1316_){
_start:
{
uint8_t v_t_boxed_1317_; lean_object* v_res_1318_; 
v_t_boxed_1317_ = lean_unbox(v_t_1314_);
v_res_1318_ = l_Lean_QuotKind_ctor_elim(v_motive_1313_, v_t_boxed_1317_, v_h_1315_, v_ctor_1316_);
lean_dec(v_ctor_1316_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg(lean_object* v_lift_1319_){
_start:
{
lean_inc(v_lift_1319_);
return v_lift_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg___boxed(lean_object* v_lift_1320_){
_start:
{
lean_object* v_res_1321_; 
v_res_1321_ = l_Lean_QuotKind_lift_elim___redArg(v_lift_1320_);
lean_dec(v_lift_1320_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim(lean_object* v_motive_1322_, uint8_t v_t_1323_, lean_object* v_h_1324_, lean_object* v_lift_1325_){
_start:
{
lean_inc(v_lift_1325_);
return v_lift_1325_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___boxed(lean_object* v_motive_1326_, lean_object* v_t_1327_, lean_object* v_h_1328_, lean_object* v_lift_1329_){
_start:
{
uint8_t v_t_boxed_1330_; lean_object* v_res_1331_; 
v_t_boxed_1330_ = lean_unbox(v_t_1327_);
v_res_1331_ = l_Lean_QuotKind_lift_elim(v_motive_1326_, v_t_boxed_1330_, v_h_1328_, v_lift_1329_);
lean_dec(v_lift_1329_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg(lean_object* v_ind_1332_){
_start:
{
lean_inc(v_ind_1332_);
return v_ind_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg___boxed(lean_object* v_ind_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Lean_QuotKind_ind_elim___redArg(v_ind_1333_);
lean_dec(v_ind_1333_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim(lean_object* v_motive_1335_, uint8_t v_t_1336_, lean_object* v_h_1337_, lean_object* v_ind_1338_){
_start:
{
lean_inc(v_ind_1338_);
return v_ind_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___boxed(lean_object* v_motive_1339_, lean_object* v_t_1340_, lean_object* v_h_1341_, lean_object* v_ind_1342_){
_start:
{
uint8_t v_t_boxed_1343_; lean_object* v_res_1344_; 
v_t_boxed_1343_ = lean_unbox(v_t_1340_);
v_res_1344_ = l_Lean_QuotKind_ind_elim(v_motive_1339_, v_t_boxed_1343_, v_h_1341_, v_ind_1342_);
lean_dec(v_ind_1342_);
return v_res_1344_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind_default(void){
_start:
{
uint8_t v___x_1345_; 
v___x_1345_ = 0;
return v___x_1345_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind(void){
_start:
{
uint8_t v___x_1346_; 
v___x_1346_ = 0;
return v___x_1346_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default___closed__0(void){
_start:
{
uint8_t v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___x_1347_ = 0;
v___x_1348_ = l_Lean_instInhabitedConstantVal_default;
v___x_1349_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*1, v___x_1347_);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default(void){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_obj_once(&l_Lean_instInhabitedQuotVal_default___closed__0, &l_Lean_instInhabitedQuotVal_default___closed__0_once, _init_l_Lean_instInhabitedQuotVal_default___closed__0);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal(void){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_instInhabitedQuotVal_default;
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* lean_mk_quot_val(lean_object* v_name_1352_, lean_object* v_levelParams_1353_, lean_object* v_type_1354_, uint8_t v_kind_1355_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1356_, 0, v_name_1352_);
lean_ctor_set(v___x_1356_, 1, v_levelParams_1353_);
lean_ctor_set(v___x_1356_, 2, v_type_1354_);
v___x_1357_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set_uint8(v___x_1357_, sizeof(void*)*1, v_kind_1355_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkQuotValEx___boxed(lean_object* v_name_1358_, lean_object* v_levelParams_1359_, lean_object* v_type_1360_, lean_object* v_kind_1361_){
_start:
{
uint8_t v_kind_boxed_1362_; lean_object* v_res_1363_; 
v_kind_boxed_1362_ = lean_unbox(v_kind_1361_);
v_res_1363_ = lean_mk_quot_val(v_name_1358_, v_levelParams_1359_, v_type_1360_, v_kind_boxed_1362_);
return v_res_1363_;
}
}
LEAN_EXPORT uint8_t lean_quot_val_kind(lean_object* v_v_1364_){
_start:
{
uint8_t v_kind_1365_; 
v_kind_1365_ = lean_ctor_get_uint8(v_v_1364_, sizeof(void*)*1);
lean_dec_ref(v_v_1364_);
return v_kind_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotVal_kindEx___boxed(lean_object* v_v_1366_){
_start:
{
uint8_t v_res_1367_; lean_object* v_r_1368_; 
v_res_1367_ = lean_quot_val_kind(v_v_1366_);
v_r_1368_ = lean_box(v_res_1367_);
return v_r_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx(lean_object* v_x_1369_){
_start:
{
switch(lean_obj_tag(v_x_1369_))
{
case 0:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_unsigned_to_nat(0u);
return v___x_1370_;
}
case 1:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_unsigned_to_nat(1u);
return v___x_1371_;
}
case 2:
{
lean_object* v___x_1372_; 
v___x_1372_ = lean_unsigned_to_nat(2u);
return v___x_1372_;
}
case 3:
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_unsigned_to_nat(3u);
return v___x_1373_;
}
case 4:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_unsigned_to_nat(4u);
return v___x_1374_;
}
case 5:
{
lean_object* v___x_1375_; 
v___x_1375_ = lean_unsigned_to_nat(5u);
return v___x_1375_;
}
case 6:
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_unsigned_to_nat(6u);
return v___x_1376_;
}
default: 
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_unsigned_to_nat(7u);
return v___x_1377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___boxed(lean_object* v_x_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_ConstantInfo_ctorIdx(v_x_1378_);
lean_dec_ref(v_x_1378_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___redArg(lean_object* v_t_1380_, lean_object* v_k_1381_){
_start:
{
lean_object* v_val_1382_; lean_object* v___x_1383_; 
v_val_1382_ = lean_ctor_get(v_t_1380_, 0);
lean_inc_ref(v_val_1382_);
lean_dec_ref(v_t_1380_);
v___x_1383_ = lean_apply_1(v_k_1381_, v_val_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim(lean_object* v_motive_1384_, lean_object* v_ctorIdx_1385_, lean_object* v_t_1386_, lean_object* v_h_1387_, lean_object* v_k_1388_){
_start:
{
lean_object* v___x_1389_; 
v___x_1389_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1386_, v_k_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___boxed(lean_object* v_motive_1390_, lean_object* v_ctorIdx_1391_, lean_object* v_t_1392_, lean_object* v_h_1393_, lean_object* v_k_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_ConstantInfo_ctorElim(v_motive_1390_, v_ctorIdx_1391_, v_t_1392_, v_h_1393_, v_k_1394_);
lean_dec(v_ctorIdx_1391_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim___redArg(lean_object* v_t_1396_, lean_object* v_axiomInfo_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1396_, v_axiomInfo_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim(lean_object* v_motive_1399_, lean_object* v_t_1400_, lean_object* v_h_1401_, lean_object* v_axiomInfo_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1400_, v_axiomInfo_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim___redArg(lean_object* v_t_1404_, lean_object* v_defnInfo_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1404_, v_defnInfo_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim(lean_object* v_motive_1407_, lean_object* v_t_1408_, lean_object* v_h_1409_, lean_object* v_defnInfo_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1408_, v_defnInfo_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim___redArg(lean_object* v_t_1412_, lean_object* v_thmInfo_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1412_, v_thmInfo_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim(lean_object* v_motive_1415_, lean_object* v_t_1416_, lean_object* v_h_1417_, lean_object* v_thmInfo_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1416_, v_thmInfo_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim___redArg(lean_object* v_t_1420_, lean_object* v_opaqueInfo_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1420_, v_opaqueInfo_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim(lean_object* v_motive_1423_, lean_object* v_t_1424_, lean_object* v_h_1425_, lean_object* v_opaqueInfo_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1424_, v_opaqueInfo_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim___redArg(lean_object* v_t_1428_, lean_object* v_quotInfo_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1428_, v_quotInfo_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim(lean_object* v_motive_1431_, lean_object* v_t_1432_, lean_object* v_h_1433_, lean_object* v_quotInfo_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1432_, v_quotInfo_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim___redArg(lean_object* v_t_1436_, lean_object* v_inductInfo_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1436_, v_inductInfo_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim(lean_object* v_motive_1439_, lean_object* v_t_1440_, lean_object* v_h_1441_, lean_object* v_inductInfo_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1440_, v_inductInfo_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim___redArg(lean_object* v_t_1444_, lean_object* v_ctorInfo_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1444_, v_ctorInfo_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim(lean_object* v_motive_1447_, lean_object* v_t_1448_, lean_object* v_h_1449_, lean_object* v_ctorInfo_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1448_, v_ctorInfo_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim___redArg(lean_object* v_t_1452_, lean_object* v_recInfo_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1452_, v_recInfo_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim(lean_object* v_motive_1455_, lean_object* v_t_1456_, lean_object* v_h_1457_, lean_object* v_recInfo_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1456_, v_recInfo_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default___closed__0(void){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = l_Lean_instInhabitedAxiomVal_default;
v___x_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
return v___x_1461_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default(void){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = lean_obj_once(&l_Lean_instInhabitedConstantInfo_default___closed__0, &l_Lean_instInhabitedConstantInfo_default___closed__0_once, _init_l_Lean_instInhabitedConstantInfo_default___closed__0);
return v___x_1462_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo(void){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_instInhabitedConstantInfo_default;
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object* v_x_1464_){
_start:
{
lean_object* v_val_1465_; lean_object* v_toConstantVal_1466_; 
v_val_1465_ = lean_ctor_get(v_x_1464_, 0);
v_toConstantVal_1466_ = lean_ctor_get(v_val_1465_, 0);
lean_inc_ref(v_toConstantVal_1466_);
return v_toConstantVal_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object* v_x_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lean_ConstantInfo_toConstantVal(v_x_1467_);
lean_dec_ref(v_x_1467_);
return v_res_1468_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object* v_x_1469_){
_start:
{
switch(lean_obj_tag(v_x_1469_))
{
case 0:
{
lean_object* v_val_1470_; uint8_t v_isUnsafe_1471_; 
v_val_1470_ = lean_ctor_get(v_x_1469_, 0);
v_isUnsafe_1471_ = lean_ctor_get_uint8(v_val_1470_, sizeof(void*)*1);
return v_isUnsafe_1471_;
}
case 1:
{
lean_object* v_val_1472_; uint8_t v_safety_1473_; uint8_t v___x_1474_; uint8_t v___x_1475_; 
v_val_1472_ = lean_ctor_get(v_x_1469_, 0);
v_safety_1473_ = lean_ctor_get_uint8(v_val_1472_, sizeof(void*)*4);
v___x_1474_ = 0;
v___x_1475_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1473_, v___x_1474_);
return v___x_1475_;
}
case 3:
{
lean_object* v_val_1476_; uint8_t v_isUnsafe_1477_; 
v_val_1476_ = lean_ctor_get(v_x_1469_, 0);
v_isUnsafe_1477_ = lean_ctor_get_uint8(v_val_1476_, sizeof(void*)*3);
return v_isUnsafe_1477_;
}
case 5:
{
lean_object* v_val_1478_; uint8_t v_isUnsafe_1479_; 
v_val_1478_ = lean_ctor_get(v_x_1469_, 0);
v_isUnsafe_1479_ = lean_ctor_get_uint8(v_val_1478_, sizeof(void*)*6 + 1);
return v_isUnsafe_1479_;
}
case 6:
{
lean_object* v_val_1480_; uint8_t v_isUnsafe_1481_; 
v_val_1480_ = lean_ctor_get(v_x_1469_, 0);
v_isUnsafe_1481_ = lean_ctor_get_uint8(v_val_1480_, sizeof(void*)*5);
return v_isUnsafe_1481_;
}
case 7:
{
lean_object* v_val_1482_; uint8_t v_isUnsafe_1483_; 
v_val_1482_ = lean_ctor_get(v_x_1469_, 0);
v_isUnsafe_1483_ = lean_ctor_get_uint8(v_val_1482_, sizeof(void*)*7 + 1);
return v_isUnsafe_1483_;
}
default: 
{
uint8_t v___x_1484_; 
v___x_1484_ = 0;
return v___x_1484_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isUnsafe___boxed(lean_object* v_x_1485_){
_start:
{
uint8_t v_res_1486_; lean_object* v_r_1487_; 
v_res_1486_ = l_Lean_ConstantInfo_isUnsafe(v_x_1485_);
lean_dec_ref(v_x_1485_);
v_r_1487_ = lean_box(v_res_1486_);
return v_r_1487_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isPartial(lean_object* v_x_1488_){
_start:
{
if (lean_obj_tag(v_x_1488_) == 1)
{
lean_object* v_val_1489_; uint8_t v_safety_1490_; uint8_t v___x_1491_; uint8_t v___x_1492_; 
v_val_1489_ = lean_ctor_get(v_x_1488_, 0);
v_safety_1490_ = lean_ctor_get_uint8(v_val_1489_, sizeof(void*)*4);
v___x_1491_ = 2;
v___x_1492_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1490_, v___x_1491_);
return v___x_1492_;
}
else
{
uint8_t v___x_1493_; 
v___x_1493_ = 0;
return v___x_1493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isPartial___boxed(lean_object* v_x_1494_){
_start:
{
uint8_t v_res_1495_; lean_object* v_r_1496_; 
v_res_1495_ = l_Lean_ConstantInfo_isPartial(v_x_1494_);
lean_dec_ref(v_x_1494_);
v_r_1496_ = lean_box(v_res_1495_);
return v_r_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name(lean_object* v_d_1497_){
_start:
{
lean_object* v___x_1498_; lean_object* v_name_1499_; 
v___x_1498_ = l_Lean_ConstantInfo_toConstantVal(v_d_1497_);
v_name_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_name_1499_);
lean_dec_ref(v___x_1498_);
return v_name_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name___boxed(lean_object* v_d_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_ConstantInfo_name(v_d_1500_);
lean_dec_ref(v_d_1500_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams(lean_object* v_d_1502_){
_start:
{
lean_object* v___x_1503_; lean_object* v_levelParams_1504_; 
v___x_1503_ = l_Lean_ConstantInfo_toConstantVal(v_d_1502_);
v_levelParams_1504_ = lean_ctor_get(v___x_1503_, 1);
lean_inc(v_levelParams_1504_);
lean_dec_ref(v___x_1503_);
return v_levelParams_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams___boxed(lean_object* v_d_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_ConstantInfo_levelParams(v_d_1505_);
lean_dec_ref(v_d_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object* v_d_1507_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = l_Lean_ConstantInfo_levelParams(v_d_1507_);
v___x_1509_ = l_List_lengthTR___redArg(v___x_1508_);
lean_dec(v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams___boxed(lean_object* v_d_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_ConstantInfo_numLevelParams(v_d_1510_);
lean_dec_ref(v_d_1510_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type(lean_object* v_d_1512_){
_start:
{
lean_object* v___x_1513_; lean_object* v_type_1514_; 
v___x_1513_ = l_Lean_ConstantInfo_toConstantVal(v_d_1512_);
v_type_1514_ = lean_ctor_get(v___x_1513_, 2);
lean_inc_ref(v_type_1514_);
lean_dec_ref(v___x_1513_);
return v_type_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type___boxed(lean_object* v_d_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_ConstantInfo_type(v_d_1515_);
lean_dec_ref(v_d_1515_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f(lean_object* v_info_1517_, uint8_t v_allowOpaque_1518_){
_start:
{
switch(lean_obj_tag(v_info_1517_))
{
case 1:
{
lean_object* v_val_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1527_; 
v_val_1519_ = lean_ctor_get(v_info_1517_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_info_1517_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1521_ = v_info_1517_;
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_val_1519_);
lean_dec(v_info_1517_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1527_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v_value_1523_; lean_object* v___x_1525_; 
v_value_1523_ = lean_ctor_get(v_val_1519_, 1);
lean_inc_ref(v_value_1523_);
lean_dec_ref(v_val_1519_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 0, v_value_1523_);
v___x_1525_ = v___x_1521_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_value_1523_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
}
}
}
case 2:
{
lean_object* v_val_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1537_; 
v_val_1528_ = lean_ctor_get(v_info_1517_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_info_1517_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1530_ = v_info_1517_;
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_val_1528_);
lean_dec(v_info_1517_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
if (v_allowOpaque_1518_ == 0)
{
lean_object* v___x_1532_; 
lean_del_object(v___x_1530_);
lean_dec_ref(v_val_1528_);
v___x_1532_ = lean_box(0);
return v___x_1532_;
}
else
{
lean_object* v_value_1533_; lean_object* v___x_1535_; 
v_value_1533_ = lean_ctor_get(v_val_1528_, 1);
lean_inc_ref(v_value_1533_);
lean_dec_ref(v_val_1528_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set_tag(v___x_1530_, 1);
lean_ctor_set(v___x_1530_, 0, v_value_1533_);
v___x_1535_ = v___x_1530_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_value_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
case 3:
{
lean_object* v_val_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1547_; 
v_val_1538_ = lean_ctor_get(v_info_1517_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_info_1517_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1540_ = v_info_1517_;
v_isShared_1541_ = v_isSharedCheck_1547_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_val_1538_);
lean_dec(v_info_1517_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1547_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
if (v_allowOpaque_1518_ == 0)
{
lean_object* v___x_1542_; 
lean_del_object(v___x_1540_);
lean_dec_ref(v_val_1538_);
v___x_1542_ = lean_box(0);
return v___x_1542_;
}
else
{
lean_object* v_value_1543_; lean_object* v___x_1545_; 
v_value_1543_ = lean_ctor_get(v_val_1538_, 1);
lean_inc_ref(v_value_1543_);
lean_dec_ref(v_val_1538_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set_tag(v___x_1540_, 1);
lean_ctor_set(v___x_1540_, 0, v_value_1543_);
v___x_1545_ = v___x_1540_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_value_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
default: 
{
lean_object* v___x_1548_; 
lean_dec_ref(v_info_1517_);
v___x_1548_ = lean_box(0);
return v___x_1548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f___boxed(lean_object* v_info_1549_, lean_object* v_allowOpaque_1550_){
_start:
{
uint8_t v_allowOpaque_boxed_1551_; lean_object* v_res_1552_; 
v_allowOpaque_boxed_1551_ = lean_unbox(v_allowOpaque_1550_);
v_res_1552_ = l_Lean_ConstantInfo_value_x3f(v_info_1549_, v_allowOpaque_boxed_1551_);
return v_res_1552_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_hasValue(lean_object* v_info_1553_, uint8_t v_allowOpaque_1554_){
_start:
{
switch(lean_obj_tag(v_info_1553_))
{
case 1:
{
uint8_t v___x_1555_; 
v___x_1555_ = 1;
return v___x_1555_;
}
case 2:
{
return v_allowOpaque_1554_;
}
case 3:
{
return v_allowOpaque_1554_;
}
default: 
{
uint8_t v___x_1556_; 
v___x_1556_ = 0;
return v___x_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object* v_info_1557_, lean_object* v_allowOpaque_1558_){
_start:
{
uint8_t v_allowOpaque_boxed_1559_; uint8_t v_res_1560_; lean_object* v_r_1561_; 
v_allowOpaque_boxed_1559_ = lean_unbox(v_allowOpaque_1558_);
v_res_1560_ = l_Lean_ConstantInfo_hasValue(v_info_1557_, v_allowOpaque_boxed_1559_);
lean_dec_ref(v_info_1557_);
v_r_1561_ = lean_box(v_res_1560_);
return v_r_1561_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(lean_object* v_msg_1562_){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = l_Lean_instInhabitedExpr;
v___x_1564_ = lean_panic_fn_borrowed(v___x_1563_, v_msg_1562_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__2(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1567_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1568_ = lean_unsigned_to_nat(62u);
v___x_1569_ = lean_unsigned_to_nat(508u);
v___x_1570_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1571_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1572_ = l_mkPanicMessageWithDecl(v___x_1571_, v___x_1570_, v___x_1569_, v___x_1568_, v___x_1567_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__3(void){
_start:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1573_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1574_ = lean_unsigned_to_nat(62u);
v___x_1575_ = lean_unsigned_to_nat(509u);
v___x_1576_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1577_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1578_ = l_mkPanicMessageWithDecl(v___x_1577_, v___x_1576_, v___x_1575_, v___x_1574_, v___x_1573_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21(lean_object* v_info_1581_, uint8_t v_allowOpaque_1582_){
_start:
{
switch(lean_obj_tag(v_info_1581_))
{
case 1:
{
lean_object* v_val_1583_; lean_object* v_value_1584_; 
v_val_1583_ = lean_ctor_get(v_info_1581_, 0);
v_value_1584_ = lean_ctor_get(v_val_1583_, 1);
lean_inc_ref(v_value_1584_);
return v_value_1584_;
}
case 2:
{
if (v_allowOpaque_1582_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__2, &l_Lean_ConstantInfo_value_x21___closed__2_once, _init_l_Lean_ConstantInfo_value_x21___closed__2);
v___x_1586_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1585_);
return v___x_1586_;
}
else
{
lean_object* v_val_1587_; lean_object* v_value_1588_; 
v_val_1587_ = lean_ctor_get(v_info_1581_, 0);
v_value_1588_ = lean_ctor_get(v_val_1587_, 1);
lean_inc_ref(v_value_1588_);
return v_value_1588_;
}
}
case 3:
{
if (v_allowOpaque_1582_ == 0)
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__3, &l_Lean_ConstantInfo_value_x21___closed__3_once, _init_l_Lean_ConstantInfo_value_x21___closed__3);
v___x_1590_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1589_);
return v___x_1590_;
}
else
{
lean_object* v_val_1591_; lean_object* v_value_1592_; 
v_val_1591_ = lean_ctor_get(v_info_1581_, 0);
v_value_1592_ = lean_ctor_get(v_val_1591_, 1);
lean_inc_ref(v_value_1592_);
return v_value_1592_;
}
}
default: 
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1593_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1594_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1595_ = lean_unsigned_to_nat(510u);
v___x_1596_ = lean_unsigned_to_nat(31u);
v___x_1597_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__4));
v___x_1598_ = l_Lean_ConstantInfo_name(v_info_1581_);
v___x_1599_ = 1;
v___x_1600_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1598_, v___x_1599_);
v___x_1601_ = lean_string_append(v___x_1597_, v___x_1600_);
lean_dec_ref(v___x_1600_);
v___x_1602_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__5));
v___x_1603_ = lean_string_append(v___x_1601_, v___x_1602_);
v___x_1604_ = l_mkPanicMessageWithDecl(v___x_1593_, v___x_1594_, v___x_1595_, v___x_1596_, v___x_1603_);
lean_dec_ref(v___x_1603_);
v___x_1605_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1604_);
return v___x_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21___boxed(lean_object* v_info_1606_, lean_object* v_allowOpaque_1607_){
_start:
{
uint8_t v_allowOpaque_boxed_1608_; lean_object* v_res_1609_; 
v_allowOpaque_boxed_1608_ = lean_unbox(v_allowOpaque_1607_);
v_res_1609_ = l_Lean_ConstantInfo_value_x21(v_info_1606_, v_allowOpaque_boxed_1608_);
lean_dec_ref(v_info_1606_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints(lean_object* v_x_1610_){
_start:
{
if (lean_obj_tag(v_x_1610_) == 1)
{
lean_object* v_val_1611_; lean_object* v_hints_1612_; 
v_val_1611_ = lean_ctor_get(v_x_1610_, 0);
v_hints_1612_ = lean_ctor_get(v_val_1611_, 2);
lean_inc(v_hints_1612_);
return v_hints_1612_;
}
else
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_box(0);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object* v_x_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lean_ConstantInfo_hints(v_x_1614_);
lean_dec_ref(v_x_1614_);
return v_res_1615_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isCtor(lean_object* v_x_1616_){
_start:
{
if (lean_obj_tag(v_x_1616_) == 6)
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
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isCtor___boxed(lean_object* v_x_1619_){
_start:
{
uint8_t v_res_1620_; lean_object* v_r_1621_; 
v_res_1620_ = l_Lean_ConstantInfo_isCtor(v_x_1619_);
lean_dec_ref(v_x_1619_);
v_r_1621_ = lean_box(v_res_1620_);
return v_r_1621_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isAxiom(lean_object* v_x_1622_){
_start:
{
if (lean_obj_tag(v_x_1622_) == 0)
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
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isAxiom___boxed(lean_object* v_x_1625_){
_start:
{
uint8_t v_res_1626_; lean_object* v_r_1627_; 
v_res_1626_ = l_Lean_ConstantInfo_isAxiom(v_x_1625_);
lean_dec_ref(v_x_1625_);
v_r_1627_ = lean_box(v_res_1626_);
return v_r_1627_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isInductive(lean_object* v_x_1628_){
_start:
{
if (lean_obj_tag(v_x_1628_) == 5)
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
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isInductive___boxed(lean_object* v_x_1631_){
_start:
{
uint8_t v_res_1632_; lean_object* v_r_1633_; 
v_res_1632_ = l_Lean_ConstantInfo_isInductive(v_x_1631_);
lean_dec_ref(v_x_1631_);
v_r_1633_ = lean_box(v_res_1632_);
return v_r_1633_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isDefinition(lean_object* v_x_1634_){
_start:
{
if (lean_obj_tag(v_x_1634_) == 1)
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
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isDefinition___boxed(lean_object* v_x_1637_){
_start:
{
uint8_t v_res_1638_; lean_object* v_r_1639_; 
v_res_1638_ = l_Lean_ConstantInfo_isDefinition(v_x_1637_);
lean_dec_ref(v_x_1637_);
v_r_1639_ = lean_box(v_res_1638_);
return v_r_1639_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isTheorem(lean_object* v_x_1640_){
_start:
{
if (lean_obj_tag(v_x_1640_) == 2)
{
uint8_t v___x_1641_; 
v___x_1641_ = 1;
return v___x_1641_;
}
else
{
uint8_t v___x_1642_; 
v___x_1642_ = 0;
return v___x_1642_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isTheorem___boxed(lean_object* v_x_1643_){
_start:
{
uint8_t v_res_1644_; lean_object* v_r_1645_; 
v_res_1644_ = l_Lean_ConstantInfo_isTheorem(v_x_1643_);
lean_dec_ref(v_x_1643_);
v_r_1645_ = lean_box(v_res_1644_);
return v_r_1645_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(lean_object* v_msg_1646_){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1647_ = l_Lean_instInhabitedInductiveVal_default;
v___x_1648_ = lean_panic_fn_borrowed(v___x_1647_, v_msg_1646_);
return v___x_1648_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1651_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__1));
v___x_1652_ = lean_unsigned_to_nat(9u);
v___x_1653_ = lean_unsigned_to_nat(538u);
v___x_1654_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__0));
v___x_1655_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1656_ = l_mkPanicMessageWithDecl(v___x_1655_, v___x_1654_, v___x_1653_, v___x_1652_, v___x_1651_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object* v_x_1657_){
_start:
{
if (lean_obj_tag(v_x_1657_) == 5)
{
lean_object* v_val_1658_; 
v_val_1658_ = lean_ctor_get(v_x_1657_, 0);
lean_inc_ref(v_val_1658_);
return v_val_1658_;
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1659_ = lean_obj_once(&l_Lean_ConstantInfo_inductiveVal_x21___closed__2, &l_Lean_ConstantInfo_inductiveVal_x21___closed__2_once, _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2);
v___x_1660_ = l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(v___x_1659_);
return v___x_1660_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21___boxed(lean_object* v_x_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lean_ConstantInfo_inductiveVal_x21(v_x_1661_);
lean_dec_ref(v_x_1661_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all(lean_object* v_x_1663_){
_start:
{
switch(lean_obj_tag(v_x_1663_))
{
case 5:
{
lean_object* v_val_1664_; lean_object* v_all_1665_; 
v_val_1664_ = lean_ctor_get(v_x_1663_, 0);
v_all_1665_ = lean_ctor_get(v_val_1664_, 3);
lean_inc(v_all_1665_);
return v_all_1665_;
}
case 1:
{
lean_object* v_val_1666_; lean_object* v_all_1667_; 
v_val_1666_ = lean_ctor_get(v_x_1663_, 0);
v_all_1667_ = lean_ctor_get(v_val_1666_, 3);
lean_inc(v_all_1667_);
return v_all_1667_;
}
case 2:
{
lean_object* v_val_1668_; lean_object* v_all_1669_; 
v_val_1668_ = lean_ctor_get(v_x_1663_, 0);
v_all_1669_ = lean_ctor_get(v_val_1668_, 2);
lean_inc(v_all_1669_);
return v_all_1669_;
}
case 3:
{
lean_object* v_val_1670_; lean_object* v_all_1671_; 
v_val_1670_ = lean_ctor_get(v_x_1663_, 0);
v_all_1671_ = lean_ctor_get(v_val_1670_, 2);
lean_inc(v_all_1671_);
return v_all_1671_;
}
default: 
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = l_Lean_ConstantInfo_name(v_x_1663_);
v___x_1673_ = lean_box(0);
v___x_1674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1672_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
return v___x_1674_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all___boxed(lean_object* v_x_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Lean_ConstantInfo_all(v_x_1675_);
lean_dec_ref(v_x_1675_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecName(lean_object* v_declName_1677_){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; 
v___x_1678_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0));
v___x_1679_ = l_Lean_Name_str___override(v_declName_1677_, v___x_1678_);
return v___x_1679_;
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
