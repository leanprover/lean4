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
uint8_t v_x_17__boxed_300_; uint8_t v_y_18__boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v_x_17__boxed_300_ = lean_unbox(v_x_298_);
v_y_18__boxed_301_ = lean_unbox(v_y_299_);
v_res_302_ = l_Lean_instBEqDefinitionSafety_beq(v_x_17__boxed_300_, v_y_18__boxed_301_);
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
uint8_t v_x_177__boxed_356_; lean_object* v_res_357_; 
v_x_177__boxed_356_ = lean_unbox(v_x_354_);
v_res_357_ = l_Lean_instReprDefinitionSafety_repr(v_x_177__boxed_356_, v_prec_355_);
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
if (v_isUnsafe_461_ == 0)
{
if (v_isUnsafe_465_ == 0)
{
v___y_468_ = v___x_471_;
goto v___jp_467_;
}
else
{
return v_isUnsafe_461_;
}
}
else
{
v___y_468_ = v_isUnsafe_465_;
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
if (v_isUnsafe_710_ == 0)
{
if (v_isUnsafe_714_ == 0)
{
return v___x_717_;
}
else
{
return v_isUnsafe_710_;
}
}
else
{
return v_isUnsafe_714_;
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
if (v_isUnsafe_1060_ == 0)
{
if (v_isUnsafe_1066_ == 0)
{
return v___x_1071_;
}
else
{
return v_isUnsafe_1060_;
}
}
else
{
return v_isUnsafe_1066_;
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
if (v_k_1157_ == 0)
{
if (v_k_1166_ == 0)
{
v___y_1169_ = v___x_1176_;
goto v___jp_1168_;
}
else
{
return v_k_1157_;
}
}
else
{
v___y_1169_ = v_k_1166_;
goto v___jp_1168_;
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
if (v___y_1169_ == 0)
{
return v___y_1169_;
}
else
{
if (v_isUnsafe_1158_ == 0)
{
if (v_isUnsafe_1167_ == 0)
{
return v___y_1169_;
}
else
{
return v_isUnsafe_1158_;
}
}
else
{
return v_isUnsafe_1167_;
}
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
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx(uint8_t v_x_1260_){
_start:
{
switch(v_x_1260_)
{
case 0:
{
lean_object* v___x_1261_; 
v___x_1261_ = lean_unsigned_to_nat(0u);
return v___x_1261_;
}
case 1:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_unsigned_to_nat(1u);
return v___x_1262_;
}
case 2:
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_unsigned_to_nat(2u);
return v___x_1263_;
}
default: 
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_unsigned_to_nat(3u);
return v___x_1264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___boxed(lean_object* v_x_1265_){
_start:
{
uint8_t v_x_boxed_1266_; lean_object* v_res_1267_; 
v_x_boxed_1266_ = lean_unbox(v_x_1265_);
v_res_1267_ = l_Lean_QuotKind_ctorIdx(v_x_boxed_1266_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg(lean_object* v_k_1268_){
_start:
{
lean_inc(v_k_1268_);
return v_k_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg___boxed(lean_object* v_k_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_QuotKind_ctorElim___redArg(v_k_1269_);
lean_dec(v_k_1269_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim(lean_object* v_motive_1271_, lean_object* v_ctorIdx_1272_, uint8_t v_t_1273_, lean_object* v_h_1274_, lean_object* v_k_1275_){
_start:
{
lean_inc(v_k_1275_);
return v_k_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___boxed(lean_object* v_motive_1276_, lean_object* v_ctorIdx_1277_, lean_object* v_t_1278_, lean_object* v_h_1279_, lean_object* v_k_1280_){
_start:
{
uint8_t v_t_boxed_1281_; lean_object* v_res_1282_; 
v_t_boxed_1281_ = lean_unbox(v_t_1278_);
v_res_1282_ = l_Lean_QuotKind_ctorElim(v_motive_1276_, v_ctorIdx_1277_, v_t_boxed_1281_, v_h_1279_, v_k_1280_);
lean_dec(v_k_1280_);
lean_dec(v_ctorIdx_1277_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg(lean_object* v_type_1283_){
_start:
{
lean_inc(v_type_1283_);
return v_type_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg___boxed(lean_object* v_type_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_QuotKind_type_elim___redArg(v_type_1284_);
lean_dec(v_type_1284_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim(lean_object* v_motive_1286_, uint8_t v_t_1287_, lean_object* v_h_1288_, lean_object* v_type_1289_){
_start:
{
lean_inc(v_type_1289_);
return v_type_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___boxed(lean_object* v_motive_1290_, lean_object* v_t_1291_, lean_object* v_h_1292_, lean_object* v_type_1293_){
_start:
{
uint8_t v_t_boxed_1294_; lean_object* v_res_1295_; 
v_t_boxed_1294_ = lean_unbox(v_t_1291_);
v_res_1295_ = l_Lean_QuotKind_type_elim(v_motive_1290_, v_t_boxed_1294_, v_h_1292_, v_type_1293_);
lean_dec(v_type_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg(lean_object* v_ctor_1296_){
_start:
{
lean_inc(v_ctor_1296_);
return v_ctor_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg___boxed(lean_object* v_ctor_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_QuotKind_ctor_elim___redArg(v_ctor_1297_);
lean_dec(v_ctor_1297_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim(lean_object* v_motive_1299_, uint8_t v_t_1300_, lean_object* v_h_1301_, lean_object* v_ctor_1302_){
_start:
{
lean_inc(v_ctor_1302_);
return v_ctor_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___boxed(lean_object* v_motive_1303_, lean_object* v_t_1304_, lean_object* v_h_1305_, lean_object* v_ctor_1306_){
_start:
{
uint8_t v_t_boxed_1307_; lean_object* v_res_1308_; 
v_t_boxed_1307_ = lean_unbox(v_t_1304_);
v_res_1308_ = l_Lean_QuotKind_ctor_elim(v_motive_1303_, v_t_boxed_1307_, v_h_1305_, v_ctor_1306_);
lean_dec(v_ctor_1306_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg(lean_object* v_lift_1309_){
_start:
{
lean_inc(v_lift_1309_);
return v_lift_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg___boxed(lean_object* v_lift_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_QuotKind_lift_elim___redArg(v_lift_1310_);
lean_dec(v_lift_1310_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim(lean_object* v_motive_1312_, uint8_t v_t_1313_, lean_object* v_h_1314_, lean_object* v_lift_1315_){
_start:
{
lean_inc(v_lift_1315_);
return v_lift_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___boxed(lean_object* v_motive_1316_, lean_object* v_t_1317_, lean_object* v_h_1318_, lean_object* v_lift_1319_){
_start:
{
uint8_t v_t_boxed_1320_; lean_object* v_res_1321_; 
v_t_boxed_1320_ = lean_unbox(v_t_1317_);
v_res_1321_ = l_Lean_QuotKind_lift_elim(v_motive_1316_, v_t_boxed_1320_, v_h_1318_, v_lift_1319_);
lean_dec(v_lift_1319_);
return v_res_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg(lean_object* v_ind_1322_){
_start:
{
lean_inc(v_ind_1322_);
return v_ind_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg___boxed(lean_object* v_ind_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_Lean_QuotKind_ind_elim___redArg(v_ind_1323_);
lean_dec(v_ind_1323_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim(lean_object* v_motive_1325_, uint8_t v_t_1326_, lean_object* v_h_1327_, lean_object* v_ind_1328_){
_start:
{
lean_inc(v_ind_1328_);
return v_ind_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___boxed(lean_object* v_motive_1329_, lean_object* v_t_1330_, lean_object* v_h_1331_, lean_object* v_ind_1332_){
_start:
{
uint8_t v_t_boxed_1333_; lean_object* v_res_1334_; 
v_t_boxed_1333_ = lean_unbox(v_t_1330_);
v_res_1334_ = l_Lean_QuotKind_ind_elim(v_motive_1329_, v_t_boxed_1333_, v_h_1331_, v_ind_1332_);
lean_dec(v_ind_1332_);
return v_res_1334_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind_default(void){
_start:
{
uint8_t v___x_1335_; 
v___x_1335_ = 0;
return v___x_1335_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind(void){
_start:
{
uint8_t v___x_1336_; 
v___x_1336_ = 0;
return v___x_1336_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default___closed__0(void){
_start:
{
uint8_t v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1337_ = 0;
v___x_1338_ = l_Lean_instInhabitedConstantVal_default;
v___x_1339_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set_uint8(v___x_1339_, sizeof(void*)*1, v___x_1337_);
return v___x_1339_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default(void){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = lean_obj_once(&l_Lean_instInhabitedQuotVal_default___closed__0, &l_Lean_instInhabitedQuotVal_default___closed__0_once, _init_l_Lean_instInhabitedQuotVal_default___closed__0);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal(void){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Lean_instInhabitedQuotVal_default;
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* lean_mk_quot_val(lean_object* v_name_1342_, lean_object* v_levelParams_1343_, lean_object* v_type_1344_, uint8_t v_kind_1345_){
_start:
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1346_, 0, v_name_1342_);
lean_ctor_set(v___x_1346_, 1, v_levelParams_1343_);
lean_ctor_set(v___x_1346_, 2, v_type_1344_);
v___x_1347_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
lean_ctor_set_uint8(v___x_1347_, sizeof(void*)*1, v_kind_1345_);
return v___x_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkQuotValEx___boxed(lean_object* v_name_1348_, lean_object* v_levelParams_1349_, lean_object* v_type_1350_, lean_object* v_kind_1351_){
_start:
{
uint8_t v_kind_boxed_1352_; lean_object* v_res_1353_; 
v_kind_boxed_1352_ = lean_unbox(v_kind_1351_);
v_res_1353_ = lean_mk_quot_val(v_name_1348_, v_levelParams_1349_, v_type_1350_, v_kind_boxed_1352_);
return v_res_1353_;
}
}
LEAN_EXPORT uint8_t lean_quot_val_kind(lean_object* v_v_1354_){
_start:
{
uint8_t v_kind_1355_; 
v_kind_1355_ = lean_ctor_get_uint8(v_v_1354_, sizeof(void*)*1);
lean_dec_ref(v_v_1354_);
return v_kind_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotVal_kindEx___boxed(lean_object* v_v_1356_){
_start:
{
uint8_t v_res_1357_; lean_object* v_r_1358_; 
v_res_1357_ = lean_quot_val_kind(v_v_1356_);
v_r_1358_ = lean_box(v_res_1357_);
return v_r_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx(lean_object* v_x_1359_){
_start:
{
switch(lean_obj_tag(v_x_1359_))
{
case 0:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_unsigned_to_nat(0u);
return v___x_1360_;
}
case 1:
{
lean_object* v___x_1361_; 
v___x_1361_ = lean_unsigned_to_nat(1u);
return v___x_1361_;
}
case 2:
{
lean_object* v___x_1362_; 
v___x_1362_ = lean_unsigned_to_nat(2u);
return v___x_1362_;
}
case 3:
{
lean_object* v___x_1363_; 
v___x_1363_ = lean_unsigned_to_nat(3u);
return v___x_1363_;
}
case 4:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_unsigned_to_nat(4u);
return v___x_1364_;
}
case 5:
{
lean_object* v___x_1365_; 
v___x_1365_ = lean_unsigned_to_nat(5u);
return v___x_1365_;
}
case 6:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_unsigned_to_nat(6u);
return v___x_1366_;
}
default: 
{
lean_object* v___x_1367_; 
v___x_1367_ = lean_unsigned_to_nat(7u);
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___boxed(lean_object* v_x_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_ConstantInfo_ctorIdx(v_x_1368_);
lean_dec_ref(v_x_1368_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___redArg(lean_object* v_t_1370_, lean_object* v_k_1371_){
_start:
{
lean_object* v_val_1372_; lean_object* v___x_1373_; 
v_val_1372_ = lean_ctor_get(v_t_1370_, 0);
lean_inc_ref(v_val_1372_);
lean_dec_ref(v_t_1370_);
v___x_1373_ = lean_apply_1(v_k_1371_, v_val_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim(lean_object* v_motive_1374_, lean_object* v_ctorIdx_1375_, lean_object* v_t_1376_, lean_object* v_h_1377_, lean_object* v_k_1378_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1376_, v_k_1378_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___boxed(lean_object* v_motive_1380_, lean_object* v_ctorIdx_1381_, lean_object* v_t_1382_, lean_object* v_h_1383_, lean_object* v_k_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_ConstantInfo_ctorElim(v_motive_1380_, v_ctorIdx_1381_, v_t_1382_, v_h_1383_, v_k_1384_);
lean_dec(v_ctorIdx_1381_);
return v_res_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim___redArg(lean_object* v_t_1386_, lean_object* v_axiomInfo_1387_){
_start:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1386_, v_axiomInfo_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim(lean_object* v_motive_1389_, lean_object* v_t_1390_, lean_object* v_h_1391_, lean_object* v_axiomInfo_1392_){
_start:
{
lean_object* v___x_1393_; 
v___x_1393_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1390_, v_axiomInfo_1392_);
return v___x_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim___redArg(lean_object* v_t_1394_, lean_object* v_defnInfo_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1394_, v_defnInfo_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim(lean_object* v_motive_1397_, lean_object* v_t_1398_, lean_object* v_h_1399_, lean_object* v_defnInfo_1400_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1398_, v_defnInfo_1400_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim___redArg(lean_object* v_t_1402_, lean_object* v_thmInfo_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1402_, v_thmInfo_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim(lean_object* v_motive_1405_, lean_object* v_t_1406_, lean_object* v_h_1407_, lean_object* v_thmInfo_1408_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1406_, v_thmInfo_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim___redArg(lean_object* v_t_1410_, lean_object* v_opaqueInfo_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1410_, v_opaqueInfo_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim(lean_object* v_motive_1413_, lean_object* v_t_1414_, lean_object* v_h_1415_, lean_object* v_opaqueInfo_1416_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1414_, v_opaqueInfo_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim___redArg(lean_object* v_t_1418_, lean_object* v_quotInfo_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1418_, v_quotInfo_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim(lean_object* v_motive_1421_, lean_object* v_t_1422_, lean_object* v_h_1423_, lean_object* v_quotInfo_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1422_, v_quotInfo_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim___redArg(lean_object* v_t_1426_, lean_object* v_inductInfo_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1426_, v_inductInfo_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim(lean_object* v_motive_1429_, lean_object* v_t_1430_, lean_object* v_h_1431_, lean_object* v_inductInfo_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1430_, v_inductInfo_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim___redArg(lean_object* v_t_1434_, lean_object* v_ctorInfo_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1434_, v_ctorInfo_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim(lean_object* v_motive_1437_, lean_object* v_t_1438_, lean_object* v_h_1439_, lean_object* v_ctorInfo_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1438_, v_ctorInfo_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim___redArg(lean_object* v_t_1442_, lean_object* v_recInfo_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1442_, v_recInfo_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim(lean_object* v_motive_1445_, lean_object* v_t_1446_, lean_object* v_h_1447_, lean_object* v_recInfo_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1446_, v_recInfo_1448_);
return v___x_1449_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default___closed__0(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = l_Lean_instInhabitedAxiomVal_default;
v___x_1451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1451_, 0, v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default(void){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = lean_obj_once(&l_Lean_instInhabitedConstantInfo_default___closed__0, &l_Lean_instInhabitedConstantInfo_default___closed__0_once, _init_l_Lean_instInhabitedConstantInfo_default___closed__0);
return v___x_1452_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo(void){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_instInhabitedConstantInfo_default;
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object* v_x_1454_){
_start:
{
lean_object* v_val_1455_; lean_object* v_toConstantVal_1456_; 
v_val_1455_ = lean_ctor_get(v_x_1454_, 0);
v_toConstantVal_1456_ = lean_ctor_get(v_val_1455_, 0);
lean_inc_ref(v_toConstantVal_1456_);
return v_toConstantVal_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object* v_x_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Lean_ConstantInfo_toConstantVal(v_x_1457_);
lean_dec_ref(v_x_1457_);
return v_res_1458_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object* v_x_1459_){
_start:
{
switch(lean_obj_tag(v_x_1459_))
{
case 0:
{
lean_object* v_val_1460_; uint8_t v_isUnsafe_1461_; 
v_val_1460_ = lean_ctor_get(v_x_1459_, 0);
v_isUnsafe_1461_ = lean_ctor_get_uint8(v_val_1460_, sizeof(void*)*1);
return v_isUnsafe_1461_;
}
case 1:
{
lean_object* v_val_1462_; uint8_t v_safety_1463_; uint8_t v___x_1464_; uint8_t v___x_1465_; 
v_val_1462_ = lean_ctor_get(v_x_1459_, 0);
v_safety_1463_ = lean_ctor_get_uint8(v_val_1462_, sizeof(void*)*4);
v___x_1464_ = 0;
v___x_1465_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1463_, v___x_1464_);
return v___x_1465_;
}
case 3:
{
lean_object* v_val_1466_; uint8_t v_isUnsafe_1467_; 
v_val_1466_ = lean_ctor_get(v_x_1459_, 0);
v_isUnsafe_1467_ = lean_ctor_get_uint8(v_val_1466_, sizeof(void*)*3);
return v_isUnsafe_1467_;
}
case 5:
{
lean_object* v_val_1468_; uint8_t v_isUnsafe_1469_; 
v_val_1468_ = lean_ctor_get(v_x_1459_, 0);
v_isUnsafe_1469_ = lean_ctor_get_uint8(v_val_1468_, sizeof(void*)*6 + 1);
return v_isUnsafe_1469_;
}
case 6:
{
lean_object* v_val_1470_; uint8_t v_isUnsafe_1471_; 
v_val_1470_ = lean_ctor_get(v_x_1459_, 0);
v_isUnsafe_1471_ = lean_ctor_get_uint8(v_val_1470_, sizeof(void*)*5);
return v_isUnsafe_1471_;
}
case 7:
{
lean_object* v_val_1472_; uint8_t v_isUnsafe_1473_; 
v_val_1472_ = lean_ctor_get(v_x_1459_, 0);
v_isUnsafe_1473_ = lean_ctor_get_uint8(v_val_1472_, sizeof(void*)*7 + 1);
return v_isUnsafe_1473_;
}
default: 
{
uint8_t v___x_1474_; 
v___x_1474_ = 0;
return v___x_1474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isUnsafe___boxed(lean_object* v_x_1475_){
_start:
{
uint8_t v_res_1476_; lean_object* v_r_1477_; 
v_res_1476_ = l_Lean_ConstantInfo_isUnsafe(v_x_1475_);
lean_dec_ref(v_x_1475_);
v_r_1477_ = lean_box(v_res_1476_);
return v_r_1477_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isPartial(lean_object* v_x_1478_){
_start:
{
if (lean_obj_tag(v_x_1478_) == 1)
{
lean_object* v_val_1479_; uint8_t v_safety_1480_; uint8_t v___x_1481_; uint8_t v___x_1482_; 
v_val_1479_ = lean_ctor_get(v_x_1478_, 0);
v_safety_1480_ = lean_ctor_get_uint8(v_val_1479_, sizeof(void*)*4);
v___x_1481_ = 2;
v___x_1482_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1480_, v___x_1481_);
return v___x_1482_;
}
else
{
uint8_t v___x_1483_; 
v___x_1483_ = 0;
return v___x_1483_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isPartial___boxed(lean_object* v_x_1484_){
_start:
{
uint8_t v_res_1485_; lean_object* v_r_1486_; 
v_res_1485_ = l_Lean_ConstantInfo_isPartial(v_x_1484_);
lean_dec_ref(v_x_1484_);
v_r_1486_ = lean_box(v_res_1485_);
return v_r_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name(lean_object* v_d_1487_){
_start:
{
lean_object* v___x_1488_; lean_object* v_name_1489_; 
v___x_1488_ = l_Lean_ConstantInfo_toConstantVal(v_d_1487_);
v_name_1489_ = lean_ctor_get(v___x_1488_, 0);
lean_inc(v_name_1489_);
lean_dec_ref(v___x_1488_);
return v_name_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name___boxed(lean_object* v_d_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_ConstantInfo_name(v_d_1490_);
lean_dec_ref(v_d_1490_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams(lean_object* v_d_1492_){
_start:
{
lean_object* v___x_1493_; lean_object* v_levelParams_1494_; 
v___x_1493_ = l_Lean_ConstantInfo_toConstantVal(v_d_1492_);
v_levelParams_1494_ = lean_ctor_get(v___x_1493_, 1);
lean_inc(v_levelParams_1494_);
lean_dec_ref(v___x_1493_);
return v_levelParams_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams___boxed(lean_object* v_d_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_ConstantInfo_levelParams(v_d_1495_);
lean_dec_ref(v_d_1495_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object* v_d_1497_){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = l_Lean_ConstantInfo_levelParams(v_d_1497_);
v___x_1499_ = l_List_lengthTR___redArg(v___x_1498_);
lean_dec(v___x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams___boxed(lean_object* v_d_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_ConstantInfo_numLevelParams(v_d_1500_);
lean_dec_ref(v_d_1500_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type(lean_object* v_d_1502_){
_start:
{
lean_object* v___x_1503_; lean_object* v_type_1504_; 
v___x_1503_ = l_Lean_ConstantInfo_toConstantVal(v_d_1502_);
v_type_1504_ = lean_ctor_get(v___x_1503_, 2);
lean_inc_ref(v_type_1504_);
lean_dec_ref(v___x_1503_);
return v_type_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type___boxed(lean_object* v_d_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Lean_ConstantInfo_type(v_d_1505_);
lean_dec_ref(v_d_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f(lean_object* v_info_1507_, uint8_t v_allowOpaque_1508_){
_start:
{
switch(lean_obj_tag(v_info_1507_))
{
case 1:
{
lean_object* v_val_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1517_; 
v_val_1509_ = lean_ctor_get(v_info_1507_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v_info_1507_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1511_ = v_info_1507_;
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_val_1509_);
lean_dec(v_info_1507_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1517_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v_value_1513_; lean_object* v___x_1515_; 
v_value_1513_ = lean_ctor_get(v_val_1509_, 1);
lean_inc_ref(v_value_1513_);
lean_dec_ref(v_val_1509_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v_value_1513_);
v___x_1515_ = v___x_1511_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_value_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
case 2:
{
lean_object* v_val_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1527_; 
v_val_1518_ = lean_ctor_get(v_info_1507_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_info_1507_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1520_ = v_info_1507_;
v_isShared_1521_ = v_isSharedCheck_1527_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_val_1518_);
lean_dec(v_info_1507_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1527_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
if (v_allowOpaque_1508_ == 0)
{
lean_object* v___x_1522_; 
lean_del_object(v___x_1520_);
lean_dec_ref(v_val_1518_);
v___x_1522_ = lean_box(0);
return v___x_1522_;
}
else
{
lean_object* v_value_1523_; lean_object* v___x_1525_; 
v_value_1523_ = lean_ctor_get(v_val_1518_, 1);
lean_inc_ref(v_value_1523_);
lean_dec_ref(v_val_1518_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set_tag(v___x_1520_, 1);
lean_ctor_set(v___x_1520_, 0, v_value_1523_);
v___x_1525_ = v___x_1520_;
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
}
case 3:
{
lean_object* v_val_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1537_; 
v_val_1528_ = lean_ctor_get(v_info_1507_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_info_1507_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1530_ = v_info_1507_;
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_val_1528_);
lean_dec(v_info_1507_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1537_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
if (v_allowOpaque_1508_ == 0)
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
default: 
{
lean_object* v___x_1538_; 
lean_dec_ref(v_info_1507_);
v___x_1538_ = lean_box(0);
return v___x_1538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f___boxed(lean_object* v_info_1539_, lean_object* v_allowOpaque_1540_){
_start:
{
uint8_t v_allowOpaque_boxed_1541_; lean_object* v_res_1542_; 
v_allowOpaque_boxed_1541_ = lean_unbox(v_allowOpaque_1540_);
v_res_1542_ = l_Lean_ConstantInfo_value_x3f(v_info_1539_, v_allowOpaque_boxed_1541_);
return v_res_1542_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_hasValue(lean_object* v_info_1543_, uint8_t v_allowOpaque_1544_){
_start:
{
switch(lean_obj_tag(v_info_1543_))
{
case 1:
{
uint8_t v___x_1545_; 
v___x_1545_ = 1;
return v___x_1545_;
}
case 2:
{
return v_allowOpaque_1544_;
}
case 3:
{
return v_allowOpaque_1544_;
}
default: 
{
uint8_t v___x_1546_; 
v___x_1546_ = 0;
return v___x_1546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object* v_info_1547_, lean_object* v_allowOpaque_1548_){
_start:
{
uint8_t v_allowOpaque_boxed_1549_; uint8_t v_res_1550_; lean_object* v_r_1551_; 
v_allowOpaque_boxed_1549_ = lean_unbox(v_allowOpaque_1548_);
v_res_1550_ = l_Lean_ConstantInfo_hasValue(v_info_1547_, v_allowOpaque_boxed_1549_);
lean_dec_ref(v_info_1547_);
v_r_1551_ = lean_box(v_res_1550_);
return v_r_1551_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(lean_object* v_msg_1552_){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = l_Lean_instInhabitedExpr;
v___x_1554_ = lean_panic_fn_borrowed(v___x_1553_, v_msg_1552_);
return v___x_1554_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__2(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1557_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1558_ = lean_unsigned_to_nat(62u);
v___x_1559_ = lean_unsigned_to_nat(509u);
v___x_1560_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1561_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1562_ = l_mkPanicMessageWithDecl(v___x_1561_, v___x_1560_, v___x_1559_, v___x_1558_, v___x_1557_);
return v___x_1562_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__3(void){
_start:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1563_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1564_ = lean_unsigned_to_nat(62u);
v___x_1565_ = lean_unsigned_to_nat(510u);
v___x_1566_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1567_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1568_ = l_mkPanicMessageWithDecl(v___x_1567_, v___x_1566_, v___x_1565_, v___x_1564_, v___x_1563_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21(lean_object* v_info_1571_, uint8_t v_allowOpaque_1572_){
_start:
{
switch(lean_obj_tag(v_info_1571_))
{
case 1:
{
lean_object* v_val_1573_; lean_object* v_value_1574_; 
v_val_1573_ = lean_ctor_get(v_info_1571_, 0);
v_value_1574_ = lean_ctor_get(v_val_1573_, 1);
lean_inc_ref(v_value_1574_);
return v_value_1574_;
}
case 2:
{
if (v_allowOpaque_1572_ == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__2, &l_Lean_ConstantInfo_value_x21___closed__2_once, _init_l_Lean_ConstantInfo_value_x21___closed__2);
v___x_1576_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1575_);
return v___x_1576_;
}
else
{
lean_object* v_val_1577_; lean_object* v_value_1578_; 
v_val_1577_ = lean_ctor_get(v_info_1571_, 0);
v_value_1578_ = lean_ctor_get(v_val_1577_, 1);
lean_inc_ref(v_value_1578_);
return v_value_1578_;
}
}
case 3:
{
if (v_allowOpaque_1572_ == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__3, &l_Lean_ConstantInfo_value_x21___closed__3_once, _init_l_Lean_ConstantInfo_value_x21___closed__3);
v___x_1580_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1579_);
return v___x_1580_;
}
else
{
lean_object* v_val_1581_; lean_object* v_value_1582_; 
v_val_1581_ = lean_ctor_get(v_info_1571_, 0);
v_value_1582_ = lean_ctor_get(v_val_1581_, 1);
lean_inc_ref(v_value_1582_);
return v_value_1582_;
}
}
default: 
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1583_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1584_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1585_ = lean_unsigned_to_nat(511u);
v___x_1586_ = lean_unsigned_to_nat(31u);
v___x_1587_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__4));
v___x_1588_ = l_Lean_ConstantInfo_name(v_info_1571_);
v___x_1589_ = 1;
v___x_1590_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1588_, v___x_1589_);
v___x_1591_ = lean_string_append(v___x_1587_, v___x_1590_);
lean_dec_ref(v___x_1590_);
v___x_1592_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__5));
v___x_1593_ = lean_string_append(v___x_1591_, v___x_1592_);
v___x_1594_ = l_mkPanicMessageWithDecl(v___x_1583_, v___x_1584_, v___x_1585_, v___x_1586_, v___x_1593_);
lean_dec_ref(v___x_1593_);
v___x_1595_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1594_);
return v___x_1595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21___boxed(lean_object* v_info_1596_, lean_object* v_allowOpaque_1597_){
_start:
{
uint8_t v_allowOpaque_boxed_1598_; lean_object* v_res_1599_; 
v_allowOpaque_boxed_1598_ = lean_unbox(v_allowOpaque_1597_);
v_res_1599_ = l_Lean_ConstantInfo_value_x21(v_info_1596_, v_allowOpaque_boxed_1598_);
lean_dec_ref(v_info_1596_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints(lean_object* v_x_1600_){
_start:
{
if (lean_obj_tag(v_x_1600_) == 1)
{
lean_object* v_val_1601_; lean_object* v_hints_1602_; 
v_val_1601_ = lean_ctor_get(v_x_1600_, 0);
v_hints_1602_ = lean_ctor_get(v_val_1601_, 2);
lean_inc(v_hints_1602_);
return v_hints_1602_;
}
else
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_box(0);
return v___x_1603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object* v_x_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_ConstantInfo_hints(v_x_1604_);
lean_dec_ref(v_x_1604_);
return v_res_1605_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isCtor(lean_object* v_x_1606_){
_start:
{
if (lean_obj_tag(v_x_1606_) == 6)
{
uint8_t v___x_1607_; 
v___x_1607_ = 1;
return v___x_1607_;
}
else
{
uint8_t v___x_1608_; 
v___x_1608_ = 0;
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isCtor___boxed(lean_object* v_x_1609_){
_start:
{
uint8_t v_res_1610_; lean_object* v_r_1611_; 
v_res_1610_ = l_Lean_ConstantInfo_isCtor(v_x_1609_);
lean_dec_ref(v_x_1609_);
v_r_1611_ = lean_box(v_res_1610_);
return v_r_1611_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isAxiom(lean_object* v_x_1612_){
_start:
{
if (lean_obj_tag(v_x_1612_) == 0)
{
uint8_t v___x_1613_; 
v___x_1613_ = 1;
return v___x_1613_;
}
else
{
uint8_t v___x_1614_; 
v___x_1614_ = 0;
return v___x_1614_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isAxiom___boxed(lean_object* v_x_1615_){
_start:
{
uint8_t v_res_1616_; lean_object* v_r_1617_; 
v_res_1616_ = l_Lean_ConstantInfo_isAxiom(v_x_1615_);
lean_dec_ref(v_x_1615_);
v_r_1617_ = lean_box(v_res_1616_);
return v_r_1617_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isInductive(lean_object* v_x_1618_){
_start:
{
if (lean_obj_tag(v_x_1618_) == 5)
{
uint8_t v___x_1619_; 
v___x_1619_ = 1;
return v___x_1619_;
}
else
{
uint8_t v___x_1620_; 
v___x_1620_ = 0;
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isInductive___boxed(lean_object* v_x_1621_){
_start:
{
uint8_t v_res_1622_; lean_object* v_r_1623_; 
v_res_1622_ = l_Lean_ConstantInfo_isInductive(v_x_1621_);
lean_dec_ref(v_x_1621_);
v_r_1623_ = lean_box(v_res_1622_);
return v_r_1623_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isDefinition(lean_object* v_x_1624_){
_start:
{
if (lean_obj_tag(v_x_1624_) == 1)
{
uint8_t v___x_1625_; 
v___x_1625_ = 1;
return v___x_1625_;
}
else
{
uint8_t v___x_1626_; 
v___x_1626_ = 0;
return v___x_1626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isDefinition___boxed(lean_object* v_x_1627_){
_start:
{
uint8_t v_res_1628_; lean_object* v_r_1629_; 
v_res_1628_ = l_Lean_ConstantInfo_isDefinition(v_x_1627_);
lean_dec_ref(v_x_1627_);
v_r_1629_ = lean_box(v_res_1628_);
return v_r_1629_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isTheorem(lean_object* v_x_1630_){
_start:
{
if (lean_obj_tag(v_x_1630_) == 2)
{
uint8_t v___x_1631_; 
v___x_1631_ = 1;
return v___x_1631_;
}
else
{
uint8_t v___x_1632_; 
v___x_1632_ = 0;
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isTheorem___boxed(lean_object* v_x_1633_){
_start:
{
uint8_t v_res_1634_; lean_object* v_r_1635_; 
v_res_1634_ = l_Lean_ConstantInfo_isTheorem(v_x_1633_);
lean_dec_ref(v_x_1633_);
v_r_1635_ = lean_box(v_res_1634_);
return v_r_1635_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(lean_object* v_msg_1636_){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = l_Lean_instInhabitedInductiveVal_default;
v___x_1638_ = lean_panic_fn_borrowed(v___x_1637_, v_msg_1636_);
return v___x_1638_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1641_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__1));
v___x_1642_ = lean_unsigned_to_nat(9u);
v___x_1643_ = lean_unsigned_to_nat(539u);
v___x_1644_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__0));
v___x_1645_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1646_ = l_mkPanicMessageWithDecl(v___x_1645_, v___x_1644_, v___x_1643_, v___x_1642_, v___x_1641_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object* v_x_1647_){
_start:
{
if (lean_obj_tag(v_x_1647_) == 5)
{
lean_object* v_val_1648_; 
v_val_1648_ = lean_ctor_get(v_x_1647_, 0);
lean_inc_ref(v_val_1648_);
return v_val_1648_;
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1649_ = lean_obj_once(&l_Lean_ConstantInfo_inductiveVal_x21___closed__2, &l_Lean_ConstantInfo_inductiveVal_x21___closed__2_once, _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2);
v___x_1650_ = l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(v___x_1649_);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21___boxed(lean_object* v_x_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_ConstantInfo_inductiveVal_x21(v_x_1651_);
lean_dec_ref(v_x_1651_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all(lean_object* v_x_1653_){
_start:
{
switch(lean_obj_tag(v_x_1653_))
{
case 5:
{
lean_object* v_val_1654_; lean_object* v_all_1655_; 
v_val_1654_ = lean_ctor_get(v_x_1653_, 0);
v_all_1655_ = lean_ctor_get(v_val_1654_, 3);
lean_inc(v_all_1655_);
return v_all_1655_;
}
case 1:
{
lean_object* v_val_1656_; lean_object* v_all_1657_; 
v_val_1656_ = lean_ctor_get(v_x_1653_, 0);
v_all_1657_ = lean_ctor_get(v_val_1656_, 3);
lean_inc(v_all_1657_);
return v_all_1657_;
}
case 2:
{
lean_object* v_val_1658_; lean_object* v_all_1659_; 
v_val_1658_ = lean_ctor_get(v_x_1653_, 0);
v_all_1659_ = lean_ctor_get(v_val_1658_, 2);
lean_inc(v_all_1659_);
return v_all_1659_;
}
case 3:
{
lean_object* v_val_1660_; lean_object* v_all_1661_; 
v_val_1660_ = lean_ctor_get(v_x_1653_, 0);
v_all_1661_ = lean_ctor_get(v_val_1660_, 2);
lean_inc(v_all_1661_);
return v_all_1661_;
}
default: 
{
lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v___x_1662_ = l_Lean_ConstantInfo_name(v_x_1653_);
v___x_1663_ = lean_box(0);
v___x_1664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1662_);
lean_ctor_set(v___x_1664_, 1, v___x_1663_);
return v___x_1664_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all___boxed(lean_object* v_x_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Lean_ConstantInfo_all(v_x_1665_);
lean_dec_ref(v_x_1665_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecName(lean_object* v_declName_1667_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; 
v___x_1668_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0));
v___x_1669_ = l_Lean_Name_str___override(v_declName_1667_, v___x_1668_);
return v___x_1669_;
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
