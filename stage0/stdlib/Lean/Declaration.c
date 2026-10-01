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
LEAN_EXPORT uint32_t lean_reducibility_hints_get_height(lean_object* v_h_93_){
_start:
{
if (lean_obj_tag(v_h_93_) == 2)
{
uint32_t v_a_94_; 
v_a_94_ = lean_ctor_get_uint32(v_h_93_, 0);
lean_dec_ref_known(v_h_93_, 0);
return v_a_94_;
}
else
{
uint32_t v___x_95_; 
lean_dec(v_h_93_);
v___x_95_ = 0;
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_getHeightEx___boxed(lean_object* v_h_96_){
_start:
{
uint32_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = lean_reducibility_hints_get_height(v_h_96_);
v_r_98_ = lean_box_uint32(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_lt(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
switch(lean_obj_tag(v_x_99_))
{
case 1:
{
if (lean_obj_tag(v_x_100_) == 1)
{
uint8_t v___x_101_; 
v___x_101_ = 0;
return v___x_101_;
}
else
{
uint8_t v___x_102_; 
v___x_102_ = 1;
return v___x_102_;
}
}
case 2:
{
switch(lean_obj_tag(v_x_100_))
{
case 2:
{
uint32_t v_a_103_; uint32_t v_a_104_; uint8_t v___x_105_; 
v_a_103_ = lean_ctor_get_uint32(v_x_99_, 0);
v_a_104_ = lean_ctor_get_uint32(v_x_100_, 0);
v___x_105_ = lean_uint32_dec_lt(v_a_104_, v_a_103_);
return v___x_105_;
}
case 0:
{
uint8_t v___x_106_; 
v___x_106_ = 1;
return v___x_106_;
}
default: 
{
uint8_t v___x_107_; 
v___x_107_ = 0;
return v___x_107_;
}
}
}
default: 
{
uint8_t v___x_108_; 
v___x_108_ = 0;
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_lt___boxed(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
uint8_t v_res_111_; lean_object* v_r_112_; 
v_res_111_ = l_Lean_ReducibilityHints_lt(v_x_109_, v_x_110_);
lean_dec(v_x_110_);
lean_dec(v_x_109_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_compare(lean_object* v_x_113_, lean_object* v_x_114_){
_start:
{
switch(lean_obj_tag(v_x_113_))
{
case 0:
{
if (lean_obj_tag(v_x_114_) == 0)
{
uint8_t v___x_115_; 
v___x_115_ = 1;
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = 2;
return v___x_116_;
}
}
case 1:
{
if (lean_obj_tag(v_x_114_) == 1)
{
uint8_t v___x_117_; 
v___x_117_ = 1;
return v___x_117_;
}
else
{
uint8_t v___x_118_; 
v___x_118_ = 0;
return v___x_118_;
}
}
default: 
{
switch(lean_obj_tag(v_x_114_))
{
case 0:
{
uint8_t v___x_119_; 
v___x_119_ = 0;
return v___x_119_;
}
case 1:
{
uint8_t v___x_120_; 
v___x_120_ = 2;
return v___x_120_;
}
default: 
{
uint32_t v_a_121_; uint32_t v_a_122_; uint8_t v___x_123_; 
v_a_121_ = lean_ctor_get_uint32(v_x_113_, 0);
v_a_122_ = lean_ctor_get_uint32(v_x_114_, 0);
v___x_123_ = lean_uint32_dec_lt(v_a_122_, v_a_121_);
if (v___x_123_ == 0)
{
uint8_t v___x_124_; 
v___x_124_ = lean_uint32_dec_eq(v_a_122_, v_a_121_);
if (v___x_124_ == 0)
{
uint8_t v___x_125_; 
v___x_125_ = 2;
return v___x_125_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 1;
return v___x_126_;
}
}
else
{
uint8_t v___x_127_; 
v___x_127_ = 0;
return v___x_127_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_compare___boxed(lean_object* v_x_128_, lean_object* v_x_129_){
_start:
{
uint8_t v_res_130_; lean_object* v_r_131_; 
v_res_130_ = l_Lean_ReducibilityHints_compare(v_x_128_, v_x_129_);
lean_dec(v_x_129_);
lean_dec(v_x_128_);
v_r_131_ = lean_box(v_res_130_);
return v_r_131_;
}
}
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_isAbbrev(lean_object* v_x_134_){
_start:
{
if (lean_obj_tag(v_x_134_) == 1)
{
uint8_t v___x_135_; 
v___x_135_ = 1;
return v___x_135_;
}
else
{
uint8_t v___x_136_; 
v___x_136_ = 0;
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_isAbbrev___boxed(lean_object* v_x_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Lean_ReducibilityHints_isAbbrev(v_x_137_);
lean_dec(v_x_137_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_isRegular(lean_object* v_x_140_){
_start:
{
if (lean_obj_tag(v_x_140_) == 2)
{
uint8_t v___x_141_; 
v___x_141_ = 1;
return v___x_141_;
}
else
{
uint8_t v___x_142_; 
v___x_142_ = 0;
return v___x_142_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_isRegular___boxed(lean_object* v_x_143_){
_start:
{
uint8_t v_res_144_; lean_object* v_r_145_; 
v_res_144_ = l_Lean_ReducibilityHints_isRegular(v_x_143_);
lean_dec(v_x_143_);
v_r_145_ = lean_box(v_res_144_);
return v_r_145_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal_default___closed__2(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_box(0);
v___x_150_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_151_ = l_Lean_Expr_const___override(v___x_150_, v___x_149_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal_default___closed__3(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_152_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__2, &l_Lean_instInhabitedConstantVal_default___closed__2_once, _init_l_Lean_instInhabitedConstantVal_default___closed__2);
v___x_153_ = lean_box(0);
v___x_154_ = lean_box(0);
v___x_155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v___x_153_);
lean_ctor_set(v___x_155_, 2, v___x_152_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal_default(void){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__3, &l_Lean_instInhabitedConstantVal_default___closed__3_once, _init_l_Lean_instInhabitedConstantVal_default___closed__3);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal(void){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_instInhabitedConstantVal_default;
return v___x_157_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
if (lean_obj_tag(v_x_159_) == 0)
{
uint8_t v___x_160_; 
v___x_160_ = 1;
return v___x_160_;
}
else
{
uint8_t v___x_161_; 
v___x_161_ = 0;
return v___x_161_;
}
}
else
{
if (lean_obj_tag(v_x_159_) == 0)
{
uint8_t v___x_162_; 
v___x_162_ = 0;
return v___x_162_;
}
else
{
lean_object* v_head_163_; lean_object* v_tail_164_; lean_object* v_head_165_; lean_object* v_tail_166_; uint8_t v___x_167_; 
v_head_163_ = lean_ctor_get(v_x_158_, 0);
v_tail_164_ = lean_ctor_get(v_x_158_, 1);
v_head_165_ = lean_ctor_get(v_x_159_, 0);
v_tail_166_ = lean_ctor_get(v_x_159_, 1);
v___x_167_ = lean_name_eq(v_head_163_, v_head_165_);
if (v___x_167_ == 0)
{
return v___x_167_;
}
else
{
v_x_158_ = v_tail_164_;
v_x_159_ = v_tail_166_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0___boxed(lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_x_169_, v_x_170_);
lean_dec(v_x_170_);
lean_dec(v_x_169_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstantVal_beq(lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
lean_object* v_name_175_; lean_object* v_levelParams_176_; lean_object* v_type_177_; lean_object* v_name_178_; lean_object* v_levelParams_179_; lean_object* v_type_180_; uint8_t v___x_181_; 
v_name_175_ = lean_ctor_get(v_x_173_, 0);
v_levelParams_176_ = lean_ctor_get(v_x_173_, 1);
v_type_177_ = lean_ctor_get(v_x_173_, 2);
v_name_178_ = lean_ctor_get(v_x_174_, 0);
v_levelParams_179_ = lean_ctor_get(v_x_174_, 1);
v_type_180_ = lean_ctor_get(v_x_174_, 2);
v___x_181_ = lean_name_eq(v_name_175_, v_name_178_);
if (v___x_181_ == 0)
{
return v___x_181_;
}
else
{
uint8_t v___x_182_; 
v___x_182_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_levelParams_176_, v_levelParams_179_);
if (v___x_182_ == 0)
{
return v___x_182_;
}
else
{
uint8_t v___x_183_; 
v___x_183_ = lean_expr_eqv(v_type_177_, v_type_180_);
return v___x_183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstantVal_beq___boxed(lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
uint8_t v_res_186_; lean_object* v_r_187_; 
v_res_186_ = l_Lean_instBEqConstantVal_beq(v_x_184_, v_x_185_);
lean_dec_ref(v_x_185_);
lean_dec_ref(v_x_184_);
v_r_187_ = lean_box(v_res_186_);
return v_r_187_;
}
}
static lean_object* _init_l_Lean_instInhabitedAxiomVal_default___closed__0(void){
_start:
{
uint8_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_190_ = 0;
v___x_191_ = l_Lean_instInhabitedConstantVal_default;
v___x_192_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set_uint8(v___x_192_, sizeof(void*)*1, v___x_190_);
return v___x_192_;
}
}
static lean_object* _init_l_Lean_instInhabitedAxiomVal_default(void){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = lean_obj_once(&l_Lean_instInhabitedAxiomVal_default___closed__0, &l_Lean_instInhabitedAxiomVal_default___closed__0_once, _init_l_Lean_instInhabitedAxiomVal_default___closed__0);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_instInhabitedAxiomVal(void){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_instInhabitedAxiomVal_default;
return v___x_194_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqAxiomVal_beq(lean_object* v_x_195_, lean_object* v_x_196_){
_start:
{
lean_object* v_toConstantVal_197_; uint8_t v_isUnsafe_198_; lean_object* v_toConstantVal_199_; uint8_t v_isUnsafe_200_; uint8_t v___x_201_; 
v_toConstantVal_197_ = lean_ctor_get(v_x_195_, 0);
v_isUnsafe_198_ = lean_ctor_get_uint8(v_x_195_, sizeof(void*)*1);
v_toConstantVal_199_ = lean_ctor_get(v_x_196_, 0);
v_isUnsafe_200_ = lean_ctor_get_uint8(v_x_196_, sizeof(void*)*1);
v___x_201_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_197_, v_toConstantVal_199_);
if (v___x_201_ == 0)
{
return v___x_201_;
}
else
{
if (v_isUnsafe_200_ == 0)
{
if (v_isUnsafe_198_ == 0)
{
return v___x_201_;
}
else
{
return v_isUnsafe_200_;
}
}
else
{
return v_isUnsafe_198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqAxiomVal_beq___boxed(lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
uint8_t v_res_204_; lean_object* v_r_205_; 
v_res_204_ = l_Lean_instBEqAxiomVal_beq(v_x_202_, v_x_203_);
lean_dec_ref(v_x_203_);
lean_dec_ref(v_x_202_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
LEAN_EXPORT uint8_t lean_axiom_val_is_unsafe(lean_object* v_v_208_){
_start:
{
uint8_t v_isUnsafe_209_; 
v_isUnsafe_209_ = lean_ctor_get_uint8(v_v_208_, sizeof(void*)*1);
lean_dec_ref(v_v_208_);
return v_isUnsafe_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_AxiomVal_isUnsafeEx___boxed(lean_object* v_v_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = lean_axiom_val_is_unsafe(v_v_210_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorIdx(uint8_t v_x_213_){
_start:
{
switch(v_x_213_)
{
case 0:
{
lean_object* v___x_214_; 
v___x_214_ = lean_unsigned_to_nat(0u);
return v___x_214_;
}
case 1:
{
lean_object* v___x_215_; 
v___x_215_ = lean_unsigned_to_nat(1u);
return v___x_215_;
}
default: 
{
lean_object* v___x_216_; 
v___x_216_ = lean_unsigned_to_nat(2u);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorIdx___boxed(lean_object* v_x_217_){
_start:
{
uint8_t v_x_boxed_218_; lean_object* v_res_219_; 
v_x_boxed_218_ = lean_unbox(v_x_217_);
v_res_219_ = l_Lean_DefinitionSafety_ctorIdx(v_x_boxed_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg(lean_object* v_k_220_){
_start:
{
lean_inc(v_k_220_);
return v_k_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg___boxed(lean_object* v_k_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_DefinitionSafety_ctorElim___redArg(v_k_221_);
lean_dec(v_k_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim(lean_object* v_motive_223_, lean_object* v_ctorIdx_224_, uint8_t v_t_225_, lean_object* v_h_226_, lean_object* v_k_227_){
_start:
{
lean_inc(v_k_227_);
return v_k_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___boxed(lean_object* v_motive_228_, lean_object* v_ctorIdx_229_, lean_object* v_t_230_, lean_object* v_h_231_, lean_object* v_k_232_){
_start:
{
uint8_t v_t_boxed_233_; lean_object* v_res_234_; 
v_t_boxed_233_ = lean_unbox(v_t_230_);
v_res_234_ = l_Lean_DefinitionSafety_ctorElim(v_motive_228_, v_ctorIdx_229_, v_t_boxed_233_, v_h_231_, v_k_232_);
lean_dec(v_k_232_);
lean_dec(v_ctorIdx_229_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___redArg(lean_object* v_unsafe_235_){
_start:
{
lean_inc(v_unsafe_235_);
return v_unsafe_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___redArg___boxed(lean_object* v_unsafe_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_DefinitionSafety_unsafe_elim___redArg(v_unsafe_236_);
lean_dec(v_unsafe_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim(lean_object* v_motive_238_, uint8_t v_t_239_, lean_object* v_h_240_, lean_object* v_unsafe_241_){
_start:
{
lean_inc(v_unsafe_241_);
return v_unsafe_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___boxed(lean_object* v_motive_242_, lean_object* v_t_243_, lean_object* v_h_244_, lean_object* v_unsafe_245_){
_start:
{
uint8_t v_t_boxed_246_; lean_object* v_res_247_; 
v_t_boxed_246_ = lean_unbox(v_t_243_);
v_res_247_ = l_Lean_DefinitionSafety_unsafe_elim(v_motive_242_, v_t_boxed_246_, v_h_244_, v_unsafe_245_);
lean_dec(v_unsafe_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg(lean_object* v_safe_248_){
_start:
{
lean_inc(v_safe_248_);
return v_safe_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg___boxed(lean_object* v_safe_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_DefinitionSafety_safe_elim___redArg(v_safe_249_);
lean_dec(v_safe_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim(lean_object* v_motive_251_, uint8_t v_t_252_, lean_object* v_h_253_, lean_object* v_safe_254_){
_start:
{
lean_inc(v_safe_254_);
return v_safe_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___boxed(lean_object* v_motive_255_, lean_object* v_t_256_, lean_object* v_h_257_, lean_object* v_safe_258_){
_start:
{
uint8_t v_t_boxed_259_; lean_object* v_res_260_; 
v_t_boxed_259_ = lean_unbox(v_t_256_);
v_res_260_ = l_Lean_DefinitionSafety_safe_elim(v_motive_255_, v_t_boxed_259_, v_h_257_, v_safe_258_);
lean_dec(v_safe_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg(lean_object* v_partial_261_){
_start:
{
lean_inc(v_partial_261_);
return v_partial_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg___boxed(lean_object* v_partial_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_DefinitionSafety_partial_elim___redArg(v_partial_262_);
lean_dec(v_partial_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim(lean_object* v_motive_264_, uint8_t v_t_265_, lean_object* v_h_266_, lean_object* v_partial_267_){
_start:
{
lean_inc(v_partial_267_);
return v_partial_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___boxed(lean_object* v_motive_268_, lean_object* v_t_269_, lean_object* v_h_270_, lean_object* v_partial_271_){
_start:
{
uint8_t v_t_boxed_272_; lean_object* v_res_273_; 
v_t_boxed_272_ = lean_unbox(v_t_269_);
v_res_273_ = l_Lean_DefinitionSafety_partial_elim(v_motive_268_, v_t_boxed_272_, v_h_270_, v_partial_271_);
lean_dec(v_partial_271_);
return v_res_273_;
}
}
static uint8_t _init_l_Lean_instInhabitedDefinitionSafety_default(void){
_start:
{
uint8_t v___x_274_; 
v___x_274_ = 0;
return v___x_274_;
}
}
static uint8_t _init_l_Lean_instInhabitedDefinitionSafety(void){
_start:
{
uint8_t v___x_275_; 
v___x_275_ = 0;
return v___x_275_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t v_x_276_, uint8_t v_y_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v___x_278_ = l_Lean_DefinitionSafety_ctorIdx(v_x_276_);
v___x_279_ = l_Lean_DefinitionSafety_ctorIdx(v_y_277_);
v___x_280_ = lean_nat_dec_eq(v___x_278_, v___x_279_);
lean_dec(v___x_279_);
lean_dec(v___x_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionSafety_beq___boxed(lean_object* v_x_281_, lean_object* v_y_282_){
_start:
{
uint8_t v_x_21__boxed_283_; uint8_t v_y_22__boxed_284_; uint8_t v_res_285_; lean_object* v_r_286_; 
v_x_21__boxed_283_ = lean_unbox(v_x_281_);
v_y_22__boxed_284_ = lean_unbox(v_y_282_);
v_res_285_ = l_Lean_instBEqDefinitionSafety_beq(v_x_21__boxed_283_, v_y_22__boxed_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
static lean_object* _init_l_Lean_instReprDefinitionSafety_repr___closed__6(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(2u);
v___x_299_ = lean_nat_to_int(v___x_298_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_instReprDefinitionSafety_repr___closed__7(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_to_int(v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDefinitionSafety_repr(uint8_t v_x_302_, lean_object* v_prec_303_){
_start:
{
lean_object* v___y_305_; lean_object* v___y_312_; lean_object* v___y_319_; 
switch(v_x_302_)
{
case 0:
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(1024u);
v___x_326_ = lean_nat_dec_le(v___x_325_, v_prec_303_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; 
v___x_327_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_305_ = v___x_327_;
goto v___jp_304_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_305_ = v___x_328_;
goto v___jp_304_;
}
}
case 1:
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(1024u);
v___x_330_ = lean_nat_dec_le(v___x_329_, v_prec_303_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
v___x_331_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_312_ = v___x_331_;
goto v___jp_311_;
}
else
{
lean_object* v___x_332_; 
v___x_332_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_312_ = v___x_332_;
goto v___jp_311_;
}
}
default: 
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = lean_unsigned_to_nat(1024u);
v___x_334_ = lean_nat_dec_le(v___x_333_, v_prec_303_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; 
v___x_335_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_319_ = v___x_335_;
goto v___jp_318_;
}
else
{
lean_object* v___x_336_; 
v___x_336_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_319_ = v___x_336_;
goto v___jp_318_;
}
}
}
v___jp_304_:
{
lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_306_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__1));
lean_inc(v___y_305_);
v___x_307_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_307_, 0, v___y_305_);
lean_ctor_set(v___x_307_, 1, v___x_306_);
v___x_308_ = 0;
v___x_309_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_309_, 0, v___x_307_);
lean_ctor_set_uint8(v___x_309_, sizeof(void*)*1, v___x_308_);
v___x_310_ = l_Repr_addAppParen(v___x_309_, v_prec_303_);
return v___x_310_;
}
v___jp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_313_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__3));
lean_inc(v___y_312_);
v___x_314_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_314_, 0, v___y_312_);
lean_ctor_set(v___x_314_, 1, v___x_313_);
v___x_315_ = 0;
v___x_316_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*1, v___x_315_);
v___x_317_ = l_Repr_addAppParen(v___x_316_, v_prec_303_);
return v___x_317_;
}
v___jp_318_:
{
lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_320_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__5));
lean_inc(v___y_319_);
v___x_321_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_321_, 0, v___y_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = 0;
v___x_323_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_323_, 0, v___x_321_);
lean_ctor_set_uint8(v___x_323_, sizeof(void*)*1, v___x_322_);
v___x_324_ = l_Repr_addAppParen(v___x_323_, v_prec_303_);
return v___x_324_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDefinitionSafety_repr___boxed(lean_object* v_x_337_, lean_object* v_prec_338_){
_start:
{
uint8_t v_x_171__boxed_339_; lean_object* v_res_340_; 
v_x_171__boxed_339_ = lean_unbox(v_x_337_);
v_res_340_ = l_Lean_instReprDefinitionSafety_repr(v_x_171__boxed_339_, v_prec_338_);
lean_dec(v_prec_338_);
return v_res_340_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default___closed__0(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_box(0);
v___x_344_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_345_ = l_Lean_Expr_const___override(v___x_344_, v___x_343_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default___closed__2(void){
_start:
{
lean_object* v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_349_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_350_ = 0;
v___x_351_ = lean_box(0);
v___x_352_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_353_ = l_Lean_instInhabitedConstantVal_default;
v___x_354_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_352_);
lean_ctor_set(v___x_354_, 2, v___x_351_);
lean_ctor_set(v___x_354_, 3, v___x_349_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*4, v___x_350_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default(void){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__2, &l_Lean_instInhabitedDefinitionVal_default___closed__2_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__2);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal(void){
_start:
{
lean_object* v___x_356_; 
v___x_356_ = l_Lean_instInhabitedDefinitionVal_default;
return v___x_356_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDefinitionVal_beq(lean_object* v_x_357_, lean_object* v_x_358_){
_start:
{
lean_object* v_toConstantVal_359_; lean_object* v_value_360_; lean_object* v_hints_361_; uint8_t v_safety_362_; lean_object* v_all_363_; lean_object* v_toConstantVal_364_; lean_object* v_value_365_; lean_object* v_hints_366_; uint8_t v_safety_367_; lean_object* v_all_368_; uint8_t v___x_369_; 
v_toConstantVal_359_ = lean_ctor_get(v_x_357_, 0);
v_value_360_ = lean_ctor_get(v_x_357_, 1);
v_hints_361_ = lean_ctor_get(v_x_357_, 2);
v_safety_362_ = lean_ctor_get_uint8(v_x_357_, sizeof(void*)*4);
v_all_363_ = lean_ctor_get(v_x_357_, 3);
v_toConstantVal_364_ = lean_ctor_get(v_x_358_, 0);
v_value_365_ = lean_ctor_get(v_x_358_, 1);
v_hints_366_ = lean_ctor_get(v_x_358_, 2);
v_safety_367_ = lean_ctor_get_uint8(v_x_358_, sizeof(void*)*4);
v_all_368_ = lean_ctor_get(v_x_358_, 3);
v___x_369_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_359_, v_toConstantVal_364_);
if (v___x_369_ == 0)
{
return v___x_369_;
}
else
{
uint8_t v___x_370_; 
v___x_370_ = lean_expr_eqv(v_value_360_, v_value_365_);
if (v___x_370_ == 0)
{
return v___x_370_;
}
else
{
uint8_t v___x_371_; 
v___x_371_ = l_Lean_instBEqReducibilityHints_beq(v_hints_361_, v_hints_366_);
if (v___x_371_ == 0)
{
return v___x_371_;
}
else
{
uint8_t v___x_372_; 
v___x_372_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_362_, v_safety_367_);
if (v___x_372_ == 0)
{
return v___x_372_;
}
else
{
uint8_t v___x_373_; 
v___x_373_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_363_, v_all_368_);
return v___x_373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionVal_beq___boxed(lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
uint8_t v_res_376_; lean_object* v_r_377_; 
v_res_376_ = l_Lean_instBEqDefinitionVal_beq(v_x_374_, v_x_375_);
lean_dec_ref(v_x_375_);
lean_dec_ref(v_x_374_);
v_r_377_ = lean_box(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT lean_object* lean_mk_definition_val(lean_object* v_name_380_, lean_object* v_levelParams_381_, lean_object* v_type_382_, lean_object* v_value_383_, lean_object* v_hints_384_, uint8_t v_safety_385_, lean_object* v_all_386_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_387_, 0, v_name_380_);
lean_ctor_set(v___x_387_, 1, v_levelParams_381_);
lean_ctor_set(v___x_387_, 2, v_type_382_);
v___x_388_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v_value_383_);
lean_ctor_set(v___x_388_, 2, v_hints_384_);
lean_ctor_set(v___x_388_, 3, v_all_386_);
lean_ctor_set_uint8(v___x_388_, sizeof(void*)*4, v_safety_385_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValEx___boxed(lean_object* v_name_389_, lean_object* v_levelParams_390_, lean_object* v_type_391_, lean_object* v_value_392_, lean_object* v_hints_393_, lean_object* v_safety_394_, lean_object* v_all_395_){
_start:
{
uint8_t v_safety_boxed_396_; lean_object* v_res_397_; 
v_safety_boxed_396_ = lean_unbox(v_safety_394_);
v_res_397_ = lean_mk_definition_val(v_name_389_, v_levelParams_390_, v_type_391_, v_value_392_, v_hints_393_, v_safety_boxed_396_, v_all_395_);
return v_res_397_;
}
}
LEAN_EXPORT uint8_t lean_definition_val_get_safety(lean_object* v_v_398_){
_start:
{
uint8_t v_safety_399_; 
v_safety_399_ = lean_ctor_get_uint8(v_v_398_, sizeof(void*)*4);
lean_dec_ref(v_v_398_);
return v_safety_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionVal_getSafetyEx___boxed(lean_object* v_v_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = lean_definition_val_get_safety(v_v_400_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default___closed__0(void){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_404_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_405_ = l_Lean_instInhabitedConstantVal_default;
v___x_406_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
lean_ctor_set(v___x_406_, 1, v___x_404_);
lean_ctor_set(v___x_406_, 2, v___x_403_);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default(void){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = lean_obj_once(&l_Lean_instInhabitedTheoremVal_default___closed__0, &l_Lean_instInhabitedTheoremVal_default___closed__0_once, _init_l_Lean_instInhabitedTheoremVal_default___closed__0);
return v___x_407_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal(void){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_instInhabitedTheoremVal_default;
return v___x_408_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqTheoremVal_beq(lean_object* v_x_409_, lean_object* v_x_410_){
_start:
{
lean_object* v_toConstantVal_411_; lean_object* v_value_412_; lean_object* v_all_413_; lean_object* v_toConstantVal_414_; lean_object* v_value_415_; lean_object* v_all_416_; uint8_t v___x_417_; 
v_toConstantVal_411_ = lean_ctor_get(v_x_409_, 0);
v_value_412_ = lean_ctor_get(v_x_409_, 1);
v_all_413_ = lean_ctor_get(v_x_409_, 2);
v_toConstantVal_414_ = lean_ctor_get(v_x_410_, 0);
v_value_415_ = lean_ctor_get(v_x_410_, 1);
v_all_416_ = lean_ctor_get(v_x_410_, 2);
v___x_417_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_411_, v_toConstantVal_414_);
if (v___x_417_ == 0)
{
return v___x_417_;
}
else
{
uint8_t v___x_418_; 
v___x_418_ = lean_expr_eqv(v_value_412_, v_value_415_);
if (v___x_418_ == 0)
{
return v___x_418_;
}
else
{
uint8_t v___x_419_; 
v___x_419_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_413_, v_all_416_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqTheoremVal_beq___boxed(lean_object* v_x_420_, lean_object* v_x_421_){
_start:
{
uint8_t v_res_422_; lean_object* v_r_423_; 
v_res_422_ = l_Lean_instBEqTheoremVal_beq(v_x_420_, v_x_421_);
lean_dec_ref(v_x_421_);
lean_dec_ref(v_x_420_);
v_r_423_ = lean_box(v_res_422_);
return v_r_423_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default___closed__0(void){
_start:
{
lean_object* v___x_426_; uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_426_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_427_ = 0;
v___x_428_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_429_ = l_Lean_instInhabitedConstantVal_default;
v___x_430_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
lean_ctor_set(v___x_430_, 2, v___x_426_);
lean_ctor_set_uint8(v___x_430_, sizeof(void*)*3, v___x_427_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default(void){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = lean_obj_once(&l_Lean_instInhabitedOpaqueVal_default___closed__0, &l_Lean_instInhabitedOpaqueVal_default___closed__0_once, _init_l_Lean_instInhabitedOpaqueVal_default___closed__0);
return v___x_431_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal(void){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_instInhabitedOpaqueVal_default;
return v___x_432_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqOpaqueVal_beq(lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v_toConstantVal_435_; lean_object* v_value_436_; uint8_t v_isUnsafe_437_; lean_object* v_all_438_; lean_object* v_toConstantVal_439_; lean_object* v_value_440_; uint8_t v_isUnsafe_441_; lean_object* v_all_442_; uint8_t v___y_444_; uint8_t v___x_446_; 
v_toConstantVal_435_ = lean_ctor_get(v_x_433_, 0);
v_value_436_ = lean_ctor_get(v_x_433_, 1);
v_isUnsafe_437_ = lean_ctor_get_uint8(v_x_433_, sizeof(void*)*3);
v_all_438_ = lean_ctor_get(v_x_433_, 2);
v_toConstantVal_439_ = lean_ctor_get(v_x_434_, 0);
v_value_440_ = lean_ctor_get(v_x_434_, 1);
v_isUnsafe_441_ = lean_ctor_get_uint8(v_x_434_, sizeof(void*)*3);
v_all_442_ = lean_ctor_get(v_x_434_, 2);
v___x_446_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_435_, v_toConstantVal_439_);
if (v___x_446_ == 0)
{
return v___x_446_;
}
else
{
uint8_t v___x_447_; 
v___x_447_ = lean_expr_eqv(v_value_436_, v_value_440_);
if (v___x_447_ == 0)
{
return v___x_447_;
}
else
{
if (v_isUnsafe_441_ == 0)
{
if (v_isUnsafe_437_ == 0)
{
v___y_444_ = v___x_447_;
goto v___jp_443_;
}
else
{
return v_isUnsafe_441_;
}
}
else
{
v___y_444_ = v_isUnsafe_437_;
goto v___jp_443_;
}
}
}
v___jp_443_:
{
if (v___y_444_ == 0)
{
return v___y_444_;
}
else
{
uint8_t v___x_445_; 
v___x_445_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_438_, v_all_442_);
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqOpaqueVal_beq___boxed(lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
uint8_t v_res_450_; lean_object* v_r_451_; 
v_res_450_ = l_Lean_instBEqOpaqueVal_beq(v_x_448_, v_x_449_);
lean_dec_ref(v_x_449_);
lean_dec_ref(v_x_448_);
v_r_451_ = lean_box(v_res_450_);
return v_r_451_;
}
}
LEAN_EXPORT uint8_t lean_opaque_val_is_unsafe(lean_object* v_v_454_){
_start:
{
uint8_t v_isUnsafe_455_; 
v_isUnsafe_455_ = lean_ctor_get_uint8(v_v_454_, sizeof(void*)*3);
lean_dec_ref(v_v_454_);
return v_isUnsafe_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpaqueVal_isUnsafeEx___boxed(lean_object* v_v_456_){
_start:
{
uint8_t v_res_457_; lean_object* v_r_458_; 
v_res_457_ = lean_opaque_val_is_unsafe(v_v_456_);
v_r_458_ = lean_box(v_res_457_);
return v_r_458_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__0(void){
_start:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_459_ = lean_box(0);
v___x_460_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_461_ = l_Lean_Expr_const___override(v___x_460_, v___x_459_);
return v___x_461_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__1(void){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_462_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_463_ = lean_box(0);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_462_);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default(void){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__1, &l_Lean_instInhabitedConstructor_default___closed__1_once, _init_l_Lean_instInhabitedConstructor_default___closed__1);
return v___x_465_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor(void){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Lean_instInhabitedConstructor_default;
return v___x_466_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructor_beq(lean_object* v_x_467_, lean_object* v_x_468_){
_start:
{
lean_object* v_name_469_; lean_object* v_type_470_; lean_object* v_name_471_; lean_object* v_type_472_; uint8_t v___x_473_; 
v_name_469_ = lean_ctor_get(v_x_467_, 0);
v_type_470_ = lean_ctor_get(v_x_467_, 1);
v_name_471_ = lean_ctor_get(v_x_468_, 0);
v_type_472_ = lean_ctor_get(v_x_468_, 1);
v___x_473_ = lean_name_eq(v_name_469_, v_name_471_);
if (v___x_473_ == 0)
{
return v___x_473_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = lean_expr_eqv(v_type_470_, v_type_472_);
return v___x_474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructor_beq___boxed(lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
uint8_t v_res_477_; lean_object* v_r_478_; 
v_res_477_ = l_Lean_instBEqConstructor_beq(v_x_475_, v_x_476_);
lean_dec_ref(v_x_476_);
lean_dec_ref(v_x_475_);
v_r_478_ = lean_box(v_res_477_);
return v_r_478_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default___closed__0(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_481_ = lean_box(0);
v___x_482_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_483_ = lean_box(0);
v___x_484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v___x_482_);
lean_ctor_set(v___x_484_, 2, v___x_481_);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default(void){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = lean_obj_once(&l_Lean_instInhabitedInductiveType_default___closed__0, &l_Lean_instInhabitedInductiveType_default___closed__0_once, _init_l_Lean_instInhabitedInductiveType_default___closed__0);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType(void){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_instInhabitedInductiveType_default;
return v___x_486_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
if (lean_obj_tag(v_x_487_) == 0)
{
if (lean_obj_tag(v_x_488_) == 0)
{
uint8_t v___x_489_; 
v___x_489_ = 1;
return v___x_489_;
}
else
{
uint8_t v___x_490_; 
v___x_490_ = 0;
return v___x_490_;
}
}
else
{
if (lean_obj_tag(v_x_488_) == 0)
{
uint8_t v___x_491_; 
v___x_491_ = 0;
return v___x_491_;
}
else
{
lean_object* v_head_492_; lean_object* v_tail_493_; lean_object* v_head_494_; lean_object* v_tail_495_; uint8_t v___x_496_; 
v_head_492_ = lean_ctor_get(v_x_487_, 0);
v_tail_493_ = lean_ctor_get(v_x_487_, 1);
v_head_494_ = lean_ctor_get(v_x_488_, 0);
v_tail_495_ = lean_ctor_get(v_x_488_, 1);
v___x_496_ = l_Lean_instBEqConstructor_beq(v_head_492_, v_head_494_);
if (v___x_496_ == 0)
{
return v___x_496_;
}
else
{
v_x_487_ = v_tail_493_;
v_x_488_ = v_tail_495_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0___boxed(lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_x_498_, v_x_499_);
lean_dec(v_x_499_);
lean_dec(v_x_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveType_beq(lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
lean_object* v_name_504_; lean_object* v_type_505_; lean_object* v_ctors_506_; lean_object* v_name_507_; lean_object* v_type_508_; lean_object* v_ctors_509_; uint8_t v___x_510_; 
v_name_504_ = lean_ctor_get(v_x_502_, 0);
v_type_505_ = lean_ctor_get(v_x_502_, 1);
v_ctors_506_ = lean_ctor_get(v_x_502_, 2);
v_name_507_ = lean_ctor_get(v_x_503_, 0);
v_type_508_ = lean_ctor_get(v_x_503_, 1);
v_ctors_509_ = lean_ctor_get(v_x_503_, 2);
v___x_510_ = lean_name_eq(v_name_504_, v_name_507_);
if (v___x_510_ == 0)
{
return v___x_510_;
}
else
{
uint8_t v___x_511_; 
v___x_511_ = lean_expr_eqv(v_type_505_, v_type_508_);
if (v___x_511_ == 0)
{
return v___x_511_;
}
else
{
uint8_t v___x_512_; 
v___x_512_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_ctors_506_, v_ctors_509_);
return v___x_512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveType_beq___boxed(lean_object* v_x_513_, lean_object* v_x_514_){
_start:
{
uint8_t v_res_515_; lean_object* v_r_516_; 
v_res_515_ = l_Lean_instBEqInductiveType_beq(v_x_513_, v_x_514_);
lean_dec_ref(v_x_514_);
lean_dec_ref(v_x_513_);
v_r_516_ = lean_box(v_res_515_);
return v_r_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx(lean_object* v_x_519_){
_start:
{
switch(lean_obj_tag(v_x_519_))
{
case 0:
{
lean_object* v___x_520_; 
v___x_520_ = lean_unsigned_to_nat(0u);
return v___x_520_;
}
case 1:
{
lean_object* v___x_521_; 
v___x_521_ = lean_unsigned_to_nat(1u);
return v___x_521_;
}
case 2:
{
lean_object* v___x_522_; 
v___x_522_ = lean_unsigned_to_nat(2u);
return v___x_522_;
}
case 3:
{
lean_object* v___x_523_; 
v___x_523_ = lean_unsigned_to_nat(3u);
return v___x_523_;
}
case 4:
{
lean_object* v___x_524_; 
v___x_524_ = lean_unsigned_to_nat(4u);
return v___x_524_;
}
case 5:
{
lean_object* v___x_525_; 
v___x_525_ = lean_unsigned_to_nat(5u);
return v___x_525_;
}
default: 
{
lean_object* v___x_526_; 
v___x_526_ = lean_unsigned_to_nat(6u);
return v___x_526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___boxed(lean_object* v_x_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l_Lean_Declaration_ctorIdx(v_x_527_);
lean_dec(v_x_527_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___redArg(lean_object* v_t_529_, lean_object* v_k_530_){
_start:
{
switch(lean_obj_tag(v_t_529_))
{
case 4:
{
return v_k_530_;
}
case 5:
{
lean_object* v_defns_531_; lean_object* v___x_532_; 
v_defns_531_ = lean_ctor_get(v_t_529_, 0);
lean_inc(v_defns_531_);
lean_dec_ref_known(v_t_529_, 1);
v___x_532_ = lean_apply_1(v_k_530_, v_defns_531_);
return v___x_532_;
}
case 6:
{
lean_object* v_lparams_533_; lean_object* v_nparams_534_; lean_object* v_types_535_; uint8_t v_isUnsafe_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_lparams_533_ = lean_ctor_get(v_t_529_, 0);
lean_inc(v_lparams_533_);
v_nparams_534_ = lean_ctor_get(v_t_529_, 1);
lean_inc(v_nparams_534_);
v_types_535_ = lean_ctor_get(v_t_529_, 2);
lean_inc(v_types_535_);
v_isUnsafe_536_ = lean_ctor_get_uint8(v_t_529_, sizeof(void*)*3);
lean_dec_ref_known(v_t_529_, 3);
v___x_537_ = lean_box(v_isUnsafe_536_);
v___x_538_ = lean_apply_4(v_k_530_, v_lparams_533_, v_nparams_534_, v_types_535_, v___x_537_);
return v___x_538_;
}
default: 
{
lean_object* v_val_539_; lean_object* v___x_540_; 
v_val_539_ = lean_ctor_get(v_t_529_, 0);
lean_inc_ref(v_val_539_);
lean_dec(v_t_529_);
v___x_540_ = lean_apply_1(v_k_530_, v_val_539_);
return v___x_540_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim(lean_object* v_motive_541_, lean_object* v_ctorIdx_542_, lean_object* v_t_543_, lean_object* v_h_544_, lean_object* v_k_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_Declaration_ctorElim___redArg(v_t_543_, v_k_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___boxed(lean_object* v_motive_547_, lean_object* v_ctorIdx_548_, lean_object* v_t_549_, lean_object* v_h_550_, lean_object* v_k_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Declaration_ctorElim(v_motive_547_, v_ctorIdx_548_, v_t_549_, v_h_550_, v_k_551_);
lean_dec(v_ctorIdx_548_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim___redArg(lean_object* v_t_553_, lean_object* v_axiomDecl_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Declaration_ctorElim___redArg(v_t_553_, v_axiomDecl_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim(lean_object* v_motive_556_, lean_object* v_t_557_, lean_object* v_h_558_, lean_object* v_axiomDecl_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Declaration_ctorElim___redArg(v_t_557_, v_axiomDecl_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim___redArg(lean_object* v_t_561_, lean_object* v_defnDecl_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Declaration_ctorElim___redArg(v_t_561_, v_defnDecl_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim(lean_object* v_motive_564_, lean_object* v_t_565_, lean_object* v_h_566_, lean_object* v_defnDecl_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Declaration_ctorElim___redArg(v_t_565_, v_defnDecl_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim___redArg(lean_object* v_t_569_, lean_object* v_thmDecl_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Declaration_ctorElim___redArg(v_t_569_, v_thmDecl_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim(lean_object* v_motive_572_, lean_object* v_t_573_, lean_object* v_h_574_, lean_object* v_thmDecl_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Declaration_ctorElim___redArg(v_t_573_, v_thmDecl_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim___redArg(lean_object* v_t_577_, lean_object* v_opaqueDecl_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Declaration_ctorElim___redArg(v_t_577_, v_opaqueDecl_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim(lean_object* v_motive_580_, lean_object* v_t_581_, lean_object* v_h_582_, lean_object* v_opaqueDecl_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Declaration_ctorElim___redArg(v_t_581_, v_opaqueDecl_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim___redArg(lean_object* v_t_585_, lean_object* v_quotDecl_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Declaration_ctorElim___redArg(v_t_585_, v_quotDecl_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim(lean_object* v_motive_588_, lean_object* v_t_589_, lean_object* v_h_590_, lean_object* v_quotDecl_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Declaration_ctorElim___redArg(v_t_589_, v_quotDecl_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim___redArg(lean_object* v_t_593_, lean_object* v_mutualDefnDecl_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Declaration_ctorElim___redArg(v_t_593_, v_mutualDefnDecl_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim(lean_object* v_motive_596_, lean_object* v_t_597_, lean_object* v_h_598_, lean_object* v_mutualDefnDecl_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Declaration_ctorElim___redArg(v_t_597_, v_mutualDefnDecl_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim___redArg(lean_object* v_t_601_, lean_object* v_inductDecl_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Declaration_ctorElim___redArg(v_t_601_, v_inductDecl_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim(lean_object* v_motive_604_, lean_object* v_t_605_, lean_object* v_h_606_, lean_object* v_inductDecl_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_Declaration_ctorElim___redArg(v_t_605_, v_inductDecl_607_);
return v___x_608_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default___closed__0(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = l_Lean_instInhabitedAxiomVal_default;
v___x_610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default(void){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = lean_obj_once(&l_Lean_instInhabitedDeclaration_default___closed__0, &l_Lean_instInhabitedDeclaration_default___closed__0_once, _init_l_Lean_instInhabitedDeclaration_default___closed__0);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration(void){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_instInhabitedDeclaration_default;
return v___x_612_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
if (lean_obj_tag(v_x_613_) == 0)
{
if (lean_obj_tag(v_x_614_) == 0)
{
uint8_t v___x_615_; 
v___x_615_ = 1;
return v___x_615_;
}
else
{
uint8_t v___x_616_; 
v___x_616_ = 0;
return v___x_616_;
}
}
else
{
if (lean_obj_tag(v_x_614_) == 0)
{
uint8_t v___x_617_; 
v___x_617_ = 0;
return v___x_617_;
}
else
{
lean_object* v_head_618_; lean_object* v_tail_619_; lean_object* v_head_620_; lean_object* v_tail_621_; uint8_t v___x_622_; 
v_head_618_ = lean_ctor_get(v_x_613_, 0);
v_tail_619_ = lean_ctor_get(v_x_613_, 1);
v_head_620_ = lean_ctor_get(v_x_614_, 0);
v_tail_621_ = lean_ctor_get(v_x_614_, 1);
v___x_622_ = l_Lean_instBEqDefinitionVal_beq(v_head_618_, v_head_620_);
if (v___x_622_ == 0)
{
return v___x_622_;
}
else
{
v_x_613_ = v_tail_619_;
v_x_614_ = v_tail_621_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0___boxed(lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
uint8_t v_res_626_; lean_object* v_r_627_; 
v_res_626_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_x_624_, v_x_625_);
lean_dec(v_x_625_);
lean_dec(v_x_624_);
v_r_627_ = lean_box(v_res_626_);
return v_r_627_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
if (lean_obj_tag(v_x_628_) == 0)
{
if (lean_obj_tag(v_x_629_) == 0)
{
uint8_t v___x_630_; 
v___x_630_ = 1;
return v___x_630_;
}
else
{
uint8_t v___x_631_; 
v___x_631_ = 0;
return v___x_631_;
}
}
else
{
if (lean_obj_tag(v_x_629_) == 0)
{
uint8_t v___x_632_; 
v___x_632_ = 0;
return v___x_632_;
}
else
{
lean_object* v_head_633_; lean_object* v_tail_634_; lean_object* v_head_635_; lean_object* v_tail_636_; uint8_t v___x_637_; 
v_head_633_ = lean_ctor_get(v_x_628_, 0);
v_tail_634_ = lean_ctor_get(v_x_628_, 1);
v_head_635_ = lean_ctor_get(v_x_629_, 0);
v_tail_636_ = lean_ctor_get(v_x_629_, 1);
v___x_637_ = l_Lean_instBEqInductiveType_beq(v_head_633_, v_head_635_);
if (v___x_637_ == 0)
{
return v___x_637_;
}
else
{
v_x_628_ = v_tail_634_;
v_x_629_ = v_tail_636_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1___boxed(lean_object* v_x_639_, lean_object* v_x_640_){
_start:
{
uint8_t v_res_641_; lean_object* v_r_642_; 
v_res_641_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_x_639_, v_x_640_);
lean_dec(v_x_640_);
lean_dec(v_x_639_);
v_r_642_ = lean_box(v_res_641_);
return v_r_642_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDeclaration_beq(lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
switch(lean_obj_tag(v_x_643_))
{
case 0:
{
if (lean_obj_tag(v_x_644_) == 0)
{
lean_object* v_val_645_; lean_object* v_val_646_; uint8_t v___x_647_; 
v_val_645_ = lean_ctor_get(v_x_643_, 0);
v_val_646_ = lean_ctor_get(v_x_644_, 0);
v___x_647_ = l_Lean_instBEqAxiomVal_beq(v_val_645_, v_val_646_);
return v___x_647_;
}
else
{
uint8_t v___x_648_; 
v___x_648_ = 0;
return v___x_648_;
}
}
case 1:
{
if (lean_obj_tag(v_x_644_) == 1)
{
lean_object* v_val_649_; lean_object* v_val_650_; uint8_t v___x_651_; 
v_val_649_ = lean_ctor_get(v_x_643_, 0);
v_val_650_ = lean_ctor_get(v_x_644_, 0);
v___x_651_ = l_Lean_instBEqDefinitionVal_beq(v_val_649_, v_val_650_);
return v___x_651_;
}
else
{
uint8_t v___x_652_; 
v___x_652_ = 0;
return v___x_652_;
}
}
case 2:
{
if (lean_obj_tag(v_x_644_) == 2)
{
lean_object* v_val_653_; lean_object* v_val_654_; uint8_t v___x_655_; 
v_val_653_ = lean_ctor_get(v_x_643_, 0);
v_val_654_ = lean_ctor_get(v_x_644_, 0);
v___x_655_ = l_Lean_instBEqTheoremVal_beq(v_val_653_, v_val_654_);
return v___x_655_;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = 0;
return v___x_656_;
}
}
case 3:
{
if (lean_obj_tag(v_x_644_) == 3)
{
lean_object* v_val_657_; lean_object* v_val_658_; uint8_t v___x_659_; 
v_val_657_ = lean_ctor_get(v_x_643_, 0);
v_val_658_ = lean_ctor_get(v_x_644_, 0);
v___x_659_ = l_Lean_instBEqOpaqueVal_beq(v_val_657_, v_val_658_);
return v___x_659_;
}
else
{
uint8_t v___x_660_; 
v___x_660_ = 0;
return v___x_660_;
}
}
case 4:
{
if (lean_obj_tag(v_x_644_) == 4)
{
uint8_t v___x_661_; 
v___x_661_ = 1;
return v___x_661_;
}
else
{
uint8_t v___x_662_; 
v___x_662_ = 0;
return v___x_662_;
}
}
case 5:
{
if (lean_obj_tag(v_x_644_) == 5)
{
lean_object* v_defns_663_; lean_object* v_defns_664_; uint8_t v___x_665_; 
v_defns_663_ = lean_ctor_get(v_x_643_, 0);
v_defns_664_ = lean_ctor_get(v_x_644_, 0);
v___x_665_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_defns_663_, v_defns_664_);
return v___x_665_;
}
else
{
uint8_t v___x_666_; 
v___x_666_ = 0;
return v___x_666_;
}
}
default: 
{
if (lean_obj_tag(v_x_644_) == 6)
{
lean_object* v_lparams_667_; lean_object* v_nparams_668_; lean_object* v_types_669_; uint8_t v_isUnsafe_670_; lean_object* v_lparams_671_; lean_object* v_nparams_672_; lean_object* v_types_673_; uint8_t v_isUnsafe_674_; uint8_t v___x_675_; 
v_lparams_667_ = lean_ctor_get(v_x_643_, 0);
v_nparams_668_ = lean_ctor_get(v_x_643_, 1);
v_types_669_ = lean_ctor_get(v_x_643_, 2);
v_isUnsafe_670_ = lean_ctor_get_uint8(v_x_643_, sizeof(void*)*3);
v_lparams_671_ = lean_ctor_get(v_x_644_, 0);
v_nparams_672_ = lean_ctor_get(v_x_644_, 1);
v_types_673_ = lean_ctor_get(v_x_644_, 2);
v_isUnsafe_674_ = lean_ctor_get_uint8(v_x_644_, sizeof(void*)*3);
v___x_675_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_lparams_667_, v_lparams_671_);
if (v___x_675_ == 0)
{
return v___x_675_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = lean_nat_dec_eq(v_nparams_668_, v_nparams_672_);
if (v___x_676_ == 0)
{
return v___x_676_;
}
else
{
uint8_t v___x_677_; 
v___x_677_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_types_669_, v_types_673_);
if (v___x_677_ == 0)
{
return v___x_677_;
}
else
{
if (v_isUnsafe_674_ == 0)
{
if (v_isUnsafe_670_ == 0)
{
return v___x_677_;
}
else
{
return v_isUnsafe_674_;
}
}
else
{
return v_isUnsafe_670_;
}
}
}
}
}
else
{
uint8_t v___x_678_; 
v___x_678_ = 0;
return v___x_678_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDeclaration_beq___boxed(lean_object* v_x_679_, lean_object* v_x_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Lean_instBEqDeclaration_beq(v_x_679_, v_x_680_);
lean_dec(v_x_680_);
lean_dec(v_x_679_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_decl(lean_object* v_lparams_685_, lean_object* v_nparams_686_, lean_object* v_types_687_, uint8_t v_isUnsafe_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_689_, 0, v_lparams_685_);
lean_ctor_set(v___x_689_, 1, v_nparams_686_);
lean_ctor_set(v___x_689_, 2, v_types_687_);
lean_ctor_set_uint8(v___x_689_, sizeof(void*)*3, v_isUnsafe_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveDeclEs___boxed(lean_object* v_lparams_690_, lean_object* v_nparams_691_, lean_object* v_types_692_, lean_object* v_isUnsafe_693_){
_start:
{
uint8_t v_isUnsafe_boxed_694_; lean_object* v_res_695_; 
v_isUnsafe_boxed_694_ = lean_unbox(v_isUnsafe_693_);
v_res_695_ = lean_mk_inductive_decl(v_lparams_690_, v_nparams_691_, v_types_692_, v_isUnsafe_boxed_694_);
return v_res_695_;
}
}
LEAN_EXPORT uint8_t lean_is_unsafe_inductive_decl(lean_object* v_x_696_){
_start:
{
if (lean_obj_tag(v_x_696_) == 6)
{
uint8_t v_isUnsafe_697_; 
v_isUnsafe_697_ = lean_ctor_get_uint8(v_x_696_, sizeof(void*)*3);
lean_dec_ref_known(v_x_696_, 3);
return v_isUnsafe_697_;
}
else
{
uint8_t v___x_698_; 
lean_dec(v_x_696_);
v___x_698_ = 0;
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_isUnsafeInductiveDeclEx___boxed(lean_object* v_x_699_){
_start:
{
uint8_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = lean_is_unsafe_inductive_decl(v_x_699_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(lean_object* v_msg_702_){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = l_Lean_instInhabitedDefinitionVal_default;
v___x_704_ = lean_panic_fn_borrowed(v___x_703_, v_msg_702_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Declaration_definitionVal_x21___closed__3(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_708_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__2));
v___x_709_ = lean_unsigned_to_nat(9u);
v___x_710_ = lean_unsigned_to_nat(184u);
v___x_711_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__1));
v___x_712_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_713_ = l_mkPanicMessageWithDecl(v___x_712_, v___x_711_, v___x_710_, v___x_709_, v___x_708_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21(lean_object* v_x_714_){
_start:
{
if (lean_obj_tag(v_x_714_) == 1)
{
lean_object* v_val_715_; 
v_val_715_ = lean_ctor_get(v_x_714_, 0);
lean_inc_ref(v_val_715_);
return v_val_715_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_obj_once(&l_Lean_Declaration_definitionVal_x21___closed__3, &l_Lean_Declaration_definitionVal_x21___closed__3_once, _init_l_Lean_Declaration_definitionVal_x21___closed__3);
v___x_717_ = l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(v___x_716_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21___boxed(lean_object* v_x_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Declaration_definitionVal_x21(v_x_718_);
lean_dec(v_x_718_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
if (lean_obj_tag(v_a_720_) == 0)
{
lean_object* v___x_722_; 
v___x_722_ = l_List_reverse___redArg(v_a_721_);
return v___x_722_;
}
else
{
lean_object* v_head_723_; lean_object* v_toConstantVal_724_; lean_object* v_tail_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_734_; 
v_head_723_ = lean_ctor_get(v_a_720_, 0);
v_toConstantVal_724_ = lean_ctor_get(v_head_723_, 0);
lean_inc_ref(v_toConstantVal_724_);
v_tail_725_ = lean_ctor_get(v_a_720_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_a_720_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v_a_720_, 0);
lean_dec(v_unused_735_);
v___x_727_ = v_a_720_;
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_tail_725_);
lean_dec(v_a_720_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_734_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v_name_729_; lean_object* v___x_731_; 
v_name_729_ = lean_ctor_get(v_toConstantVal_724_, 0);
lean_inc(v_name_729_);
lean_dec_ref(v_toConstantVal_724_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v_a_721_);
lean_ctor_set(v___x_727_, 0, v_name_729_);
v___x_731_ = v___x_727_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_name_729_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_a_721_);
v___x_731_ = v_reuseFailAlloc_733_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
v_a_720_ = v_tail_725_;
v_a_721_ = v___x_731_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
if (lean_obj_tag(v_a_736_) == 0)
{
lean_object* v___x_738_; 
v___x_738_ = l_List_reverse___redArg(v_a_737_);
return v___x_738_;
}
else
{
lean_object* v_head_739_; lean_object* v_tail_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_749_; 
v_head_739_ = lean_ctor_get(v_a_736_, 0);
v_tail_740_ = lean_ctor_get(v_a_736_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v_a_736_);
if (v_isSharedCheck_749_ == 0)
{
v___x_742_ = v_a_736_;
v_isShared_743_ = v_isSharedCheck_749_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_tail_740_);
lean_inc(v_head_739_);
lean_dec(v_a_736_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_749_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v_name_744_; lean_object* v___x_746_; 
v_name_744_ = lean_ctor_get(v_head_739_, 0);
lean_inc(v_name_744_);
lean_dec(v_head_739_);
if (v_isShared_743_ == 0)
{
lean_ctor_set(v___x_742_, 1, v_a_737_);
lean_ctor_set(v___x_742_, 0, v_name_744_);
v___x_746_ = v___x_742_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_name_744_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_a_737_);
v___x_746_ = v_reuseFailAlloc_748_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
v_a_736_ = v_tail_740_;
v_a_737_ = v___x_746_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getTopLevelNames(lean_object* v_x_756_){
_start:
{
switch(lean_obj_tag(v_x_756_))
{
case 4:
{
lean_object* v___x_757_; 
v___x_757_ = ((lean_object*)(l_Lean_Declaration_getTopLevelNames___closed__2));
return v___x_757_;
}
case 5:
{
lean_object* v_defns_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_defns_758_ = lean_ctor_get(v_x_756_, 0);
lean_inc(v_defns_758_);
lean_dec_ref_known(v_x_756_, 1);
v___x_759_ = lean_box(0);
v___x_760_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_758_, v___x_759_);
return v___x_760_;
}
case 6:
{
lean_object* v_types_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v_types_761_ = lean_ctor_get(v_x_756_, 2);
lean_inc(v_types_761_);
lean_dec_ref_known(v_x_756_, 3);
v___x_762_ = lean_box(0);
v___x_763_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(v_types_761_, v___x_762_);
return v___x_763_;
}
default: 
{
lean_object* v_val_764_; lean_object* v_toConstantVal_765_; lean_object* v_name_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v_val_764_ = lean_ctor_get(v_x_756_, 0);
lean_inc_ref(v_val_764_);
lean_dec(v_x_756_);
v_toConstantVal_765_ = lean_ctor_get(v_val_764_, 0);
lean_inc_ref(v_toConstantVal_765_);
lean_dec_ref(v_val_764_);
v_name_766_ = lean_ctor_get(v_toConstantVal_765_, 0);
lean_inc(v_name_766_);
lean_dec_ref(v_toConstantVal_765_);
v___x_767_ = lean_box(0);
v___x_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_768_, 0, v_name_766_);
lean_ctor_set(v___x_768_, 1, v___x_767_);
return v___x_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
if (lean_obj_tag(v_a_769_) == 0)
{
lean_object* v___x_771_; 
v___x_771_ = l_List_reverse___redArg(v_a_770_);
return v___x_771_;
}
else
{
lean_object* v_head_772_; lean_object* v_tail_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_782_; 
v_head_772_ = lean_ctor_get(v_a_769_, 0);
v_tail_773_ = lean_ctor_get(v_a_769_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v_a_769_);
if (v_isSharedCheck_782_ == 0)
{
v___x_775_ = v_a_769_;
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_tail_773_);
lean_inc(v_head_772_);
lean_dec(v_a_769_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v_name_777_; lean_object* v___x_779_; 
v_name_777_ = lean_ctor_get(v_head_772_, 0);
lean_inc(v_name_777_);
lean_dec(v_head_772_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 1, v_a_770_);
lean_ctor_set(v___x_775_, 0, v_name_777_);
v___x_779_ = v___x_775_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_name_777_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_a_770_);
v___x_779_ = v_reuseFailAlloc_781_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
v_a_769_ = v_tail_773_;
v_a_770_ = v___x_779_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
if (lean_obj_tag(v_a_786_) == 0)
{
lean_object* v___x_788_; 
v___x_788_ = lean_array_to_list(v_a_787_);
return v___x_788_;
}
else
{
lean_object* v_head_789_; lean_object* v_tail_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_806_; 
v_head_789_ = lean_ctor_get(v_a_786_, 0);
v_tail_790_ = lean_ctor_get(v_a_786_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_a_786_);
if (v_isSharedCheck_806_ == 0)
{
v___x_792_ = v_a_786_;
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_tail_790_);
lean_inc(v_head_789_);
lean_dec(v_a_786_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_806_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v_name_794_; lean_object* v_ctors_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_801_; 
v_name_794_ = lean_ctor_get(v_head_789_, 0);
lean_inc(v_name_794_);
v_ctors_795_ = lean_ctor_get(v_head_789_, 2);
lean_inc(v_ctors_795_);
lean_dec(v_head_789_);
v___x_796_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1));
v___x_797_ = l_Lean_Name_appendCore(v_name_794_, v___x_796_);
v___x_798_ = lean_box(0);
v___x_799_ = l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(v_ctors_795_, v___x_798_);
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 1, v___x_799_);
lean_ctor_set(v___x_792_, 0, v___x_797_);
v___x_801_ = v___x_792_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_799_);
v___x_801_ = v_reuseFailAlloc_805_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_802_, 0, v_name_794_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_787_, v___x_802_);
v_a_786_ = v_tail_790_;
v_a_787_ = v___x_803_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getNames(lean_object* v_x_833_){
_start:
{
switch(lean_obj_tag(v_x_833_))
{
case 4:
{
lean_object* v___x_834_; 
v___x_834_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__9));
return v___x_834_;
}
case 5:
{
lean_object* v_defns_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_defns_835_ = lean_ctor_get(v_x_833_, 0);
lean_inc(v_defns_835_);
lean_dec_ref_known(v_x_833_, 1);
v___x_836_ = lean_box(0);
v___x_837_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_835_, v___x_836_);
return v___x_837_;
}
case 6:
{
lean_object* v_types_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_types_838_ = lean_ctor_get(v_x_833_, 2);
lean_inc(v_types_838_);
lean_dec_ref_known(v_x_833_, 3);
v___x_839_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__10));
v___x_840_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(v_types_838_, v___x_839_);
return v___x_840_;
}
default: 
{
lean_object* v_val_841_; lean_object* v_toConstantVal_842_; lean_object* v_name_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v_val_841_ = lean_ctor_get(v_x_833_, 0);
lean_inc_ref(v_val_841_);
lean_dec(v_x_833_);
v_toConstantVal_842_ = lean_ctor_get(v_val_841_, 0);
lean_inc_ref(v_toConstantVal_842_);
lean_dec_ref(v_val_841_);
v_name_843_ = lean_ctor_get(v_toConstantVal_842_, 0);
lean_inc(v_name_843_);
lean_dec_ref(v_toConstantVal_842_);
v___x_844_ = lean_box(0);
v___x_845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_845_, 0, v_name_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
return v___x_845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__0(lean_object* v_f_846_, lean_object* v_value_847_, lean_object* v_a_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_apply_2(v_f_846_, v_a_848_, v_value_847_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__3(lean_object* v_f_850_, lean_object* v_value_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_apply_2(v_f_850_, v_a_852_, v_value_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__1(lean_object* v_f_854_, lean_object* v_toBind_855_, lean_object* v_a_856_, lean_object* v_v_857_){
_start:
{
lean_object* v_toConstantVal_858_; lean_object* v_value_859_; lean_object* v_type_860_; lean_object* v___f_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v_toConstantVal_858_ = lean_ctor_get(v_v_857_, 0);
lean_inc_ref(v_toConstantVal_858_);
v_value_859_ = lean_ctor_get(v_v_857_, 1);
lean_inc_ref(v_value_859_);
lean_dec_ref(v_v_857_);
v_type_860_ = lean_ctor_get(v_toConstantVal_858_, 2);
lean_inc_ref(v_type_860_);
lean_dec_ref(v_toConstantVal_858_);
lean_inc(v_f_854_);
v___f_861_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__3), 3, 2);
lean_closure_set(v___f_861_, 0, v_f_854_);
lean_closure_set(v___f_861_, 1, v_value_859_);
v___x_862_ = lean_apply_2(v_f_854_, v_a_856_, v_type_860_);
v___x_863_ = lean_apply_4(v_toBind_855_, lean_box(0), lean_box(0), v___x_862_, v___f_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__2(lean_object* v_f_864_, lean_object* v_a_865_, lean_object* v_ctor_866_){
_start:
{
lean_object* v_type_867_; lean_object* v___x_868_; 
v_type_867_ = lean_ctor_get(v_ctor_866_, 1);
lean_inc_ref(v_type_867_);
lean_dec_ref(v_ctor_866_);
v___x_868_ = lean_apply_2(v_f_864_, v_a_865_, v_type_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__4(lean_object* v_inst_869_, lean_object* v___f_870_, lean_object* v_ctors_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l_List_foldlM___redArg(v_inst_869_, v___f_870_, v_a_872_, v_ctors_871_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__5(lean_object* v_inst_874_, lean_object* v___f_875_, lean_object* v_f_876_, lean_object* v_toBind_877_, lean_object* v_a_878_, lean_object* v_inductType_879_){
_start:
{
lean_object* v_type_880_; lean_object* v_ctors_881_; lean_object* v___f_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_type_880_ = lean_ctor_get(v_inductType_879_, 1);
lean_inc_ref(v_type_880_);
v_ctors_881_ = lean_ctor_get(v_inductType_879_, 2);
lean_inc(v_ctors_881_);
lean_dec_ref(v_inductType_879_);
v___f_882_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__4), 4, 3);
lean_closure_set(v___f_882_, 0, v_inst_874_);
lean_closure_set(v___f_882_, 1, v___f_875_);
lean_closure_set(v___f_882_, 2, v_ctors_881_);
v___x_883_ = lean_apply_2(v_f_876_, v_a_878_, v_type_880_);
v___x_884_ = lean_apply_4(v_toBind_877_, lean_box(0), lean_box(0), v___x_883_, v___f_882_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object* v_inst_885_, lean_object* v_d_886_, lean_object* v_f_887_, lean_object* v_a_888_){
_start:
{
switch(lean_obj_tag(v_d_886_))
{
case 0:
{
lean_object* v_val_889_; lean_object* v_toConstantVal_890_; lean_object* v_type_891_; lean_object* v___x_892_; 
lean_dec_ref(v_inst_885_);
v_val_889_ = lean_ctor_get(v_d_886_, 0);
lean_inc_ref(v_val_889_);
lean_dec_ref_known(v_d_886_, 1);
v_toConstantVal_890_ = lean_ctor_get(v_val_889_, 0);
lean_inc_ref(v_toConstantVal_890_);
lean_dec_ref(v_val_889_);
v_type_891_ = lean_ctor_get(v_toConstantVal_890_, 2);
lean_inc_ref(v_type_891_);
lean_dec_ref(v_toConstantVal_890_);
v___x_892_ = lean_apply_2(v_f_887_, v_a_888_, v_type_891_);
return v___x_892_;
}
case 4:
{
lean_object* v_toApplicative_893_; lean_object* v_toPure_894_; lean_object* v___x_895_; 
v_toApplicative_893_ = lean_ctor_get(v_inst_885_, 0);
lean_inc_ref(v_toApplicative_893_);
lean_dec(v_f_887_);
lean_dec_ref(v_inst_885_);
v_toPure_894_ = lean_ctor_get(v_toApplicative_893_, 1);
lean_inc(v_toPure_894_);
lean_dec_ref(v_toApplicative_893_);
v___x_895_ = lean_apply_2(v_toPure_894_, lean_box(0), v_a_888_);
return v___x_895_;
}
case 5:
{
lean_object* v_toBind_896_; lean_object* v_defns_897_; lean_object* v___f_898_; lean_object* v___x_899_; 
v_toBind_896_ = lean_ctor_get(v_inst_885_, 1);
v_defns_897_ = lean_ctor_get(v_d_886_, 0);
lean_inc(v_defns_897_);
lean_dec_ref_known(v_d_886_, 1);
lean_inc(v_toBind_896_);
v___f_898_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_898_, 0, v_f_887_);
lean_closure_set(v___f_898_, 1, v_toBind_896_);
v___x_899_ = l_List_foldlM___redArg(v_inst_885_, v___f_898_, v_a_888_, v_defns_897_);
return v___x_899_;
}
case 6:
{
lean_object* v_toBind_900_; lean_object* v_types_901_; lean_object* v___f_902_; lean_object* v___f_903_; lean_object* v___x_904_; 
v_toBind_900_ = lean_ctor_get(v_inst_885_, 1);
v_types_901_ = lean_ctor_get(v_d_886_, 2);
lean_inc(v_types_901_);
lean_dec_ref_known(v_d_886_, 3);
lean_inc(v_f_887_);
v___f_902_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__2), 3, 1);
lean_closure_set(v___f_902_, 0, v_f_887_);
lean_inc(v_toBind_900_);
lean_inc_ref(v_inst_885_);
v___f_903_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__5), 6, 4);
lean_closure_set(v___f_903_, 0, v_inst_885_);
lean_closure_set(v___f_903_, 1, v___f_902_);
lean_closure_set(v___f_903_, 2, v_f_887_);
lean_closure_set(v___f_903_, 3, v_toBind_900_);
v___x_904_ = l_List_foldlM___redArg(v_inst_885_, v___f_903_, v_a_888_, v_types_901_);
return v___x_904_;
}
default: 
{
lean_object* v_val_905_; lean_object* v_toConstantVal_906_; lean_object* v_toBind_907_; lean_object* v_value_908_; lean_object* v_type_909_; lean_object* v___f_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_val_905_ = lean_ctor_get(v_d_886_, 0);
lean_inc_ref(v_val_905_);
lean_dec(v_d_886_);
v_toConstantVal_906_ = lean_ctor_get(v_val_905_, 0);
lean_inc_ref(v_toConstantVal_906_);
v_toBind_907_ = lean_ctor_get(v_inst_885_, 1);
lean_inc(v_toBind_907_);
lean_dec_ref(v_inst_885_);
v_value_908_ = lean_ctor_get(v_val_905_, 1);
lean_inc_ref(v_value_908_);
lean_dec_ref(v_val_905_);
v_type_909_ = lean_ctor_get(v_toConstantVal_906_, 2);
lean_inc_ref(v_type_909_);
lean_dec_ref(v_toConstantVal_906_);
lean_inc(v_f_887_);
v___f_910_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_910_, 0, v_f_887_);
lean_closure_set(v___f_910_, 1, v_value_908_);
v___x_911_ = lean_apply_2(v_f_887_, v_a_888_, v_type_909_);
v___x_912_ = lean_apply_4(v_toBind_907_, lean_box(0), lean_box(0), v___x_911_, v___f_910_);
return v___x_912_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM(lean_object* v_00_u03b1_913_, lean_object* v_m_914_, lean_object* v_inst_915_, lean_object* v_d_916_, lean_object* v_f_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_Declaration_foldExprM___redArg(v_inst_915_, v_d_916_, v_f_917_, v_a_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg___lam__0(lean_object* v_f_920_, lean_object* v_x_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = lean_apply_1(v_f_920_, v_a_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg(lean_object* v_inst_924_, lean_object* v_d_925_, lean_object* v_f_926_){
_start:
{
lean_object* v___f_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_927_, 0, v_f_926_);
v___x_928_ = lean_box(0);
v___x_929_ = l_Lean_Declaration_foldExprM___redArg(v_inst_924_, v_d_925_, v___f_927_, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM(lean_object* v_m_930_, lean_object* v_inst_931_, lean_object* v_d_932_, lean_object* v_f_933_){
_start:
{
lean_object* v___f_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___f_934_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_934_, 0, v_f_933_);
v___x_935_ = lean_box(0);
v___x_936_ = l_Lean_Declaration_foldExprM___redArg(v_inst_931_, v_d_932_, v___f_934_, v___x_935_);
return v___x_936_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default___closed__0(void){
_start:
{
uint8_t v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_937_ = 0;
v___x_938_ = lean_box(0);
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = l_Lean_instInhabitedConstantVal_default;
v___x_941_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v___x_939_);
lean_ctor_set(v___x_941_, 2, v___x_939_);
lean_ctor_set(v___x_941_, 3, v___x_938_);
lean_ctor_set(v___x_941_, 4, v___x_938_);
lean_ctor_set(v___x_941_, 5, v___x_939_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*6, v___x_937_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*6 + 1, v___x_937_);
lean_ctor_set_uint8(v___x_941_, sizeof(void*)*6 + 2, v___x_937_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default(void){
_start:
{
lean_object* v___x_942_; 
v___x_942_ = lean_obj_once(&l_Lean_instInhabitedInductiveVal_default___closed__0, &l_Lean_instInhabitedInductiveVal_default___closed__0_once, _init_l_Lean_instInhabitedInductiveVal_default___closed__0);
return v___x_942_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal(void){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_instInhabitedInductiveVal_default;
return v___x_943_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveVal_beq(lean_object* v_x_944_, lean_object* v_x_945_){
_start:
{
lean_object* v_toConstantVal_946_; lean_object* v_numParams_947_; lean_object* v_numIndices_948_; lean_object* v_all_949_; lean_object* v_ctors_950_; lean_object* v_numNested_951_; uint8_t v_isRec_952_; uint8_t v_isUnsafe_953_; uint8_t v_isReflexive_954_; lean_object* v_toConstantVal_955_; lean_object* v_numParams_956_; lean_object* v_numIndices_957_; lean_object* v_all_958_; lean_object* v_ctors_959_; lean_object* v_numNested_960_; uint8_t v_isRec_961_; uint8_t v_isUnsafe_962_; uint8_t v_isReflexive_963_; uint8_t v___y_965_; uint8_t v___y_967_; uint8_t v___x_968_; 
v_toConstantVal_946_ = lean_ctor_get(v_x_944_, 0);
v_numParams_947_ = lean_ctor_get(v_x_944_, 1);
v_numIndices_948_ = lean_ctor_get(v_x_944_, 2);
v_all_949_ = lean_ctor_get(v_x_944_, 3);
v_ctors_950_ = lean_ctor_get(v_x_944_, 4);
v_numNested_951_ = lean_ctor_get(v_x_944_, 5);
v_isRec_952_ = lean_ctor_get_uint8(v_x_944_, sizeof(void*)*6);
v_isUnsafe_953_ = lean_ctor_get_uint8(v_x_944_, sizeof(void*)*6 + 1);
v_isReflexive_954_ = lean_ctor_get_uint8(v_x_944_, sizeof(void*)*6 + 2);
v_toConstantVal_955_ = lean_ctor_get(v_x_945_, 0);
v_numParams_956_ = lean_ctor_get(v_x_945_, 1);
v_numIndices_957_ = lean_ctor_get(v_x_945_, 2);
v_all_958_ = lean_ctor_get(v_x_945_, 3);
v_ctors_959_ = lean_ctor_get(v_x_945_, 4);
v_numNested_960_ = lean_ctor_get(v_x_945_, 5);
v_isRec_961_ = lean_ctor_get_uint8(v_x_945_, sizeof(void*)*6);
v_isUnsafe_962_ = lean_ctor_get_uint8(v_x_945_, sizeof(void*)*6 + 1);
v_isReflexive_963_ = lean_ctor_get_uint8(v_x_945_, sizeof(void*)*6 + 2);
v___x_968_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_946_, v_toConstantVal_955_);
if (v___x_968_ == 0)
{
return v___x_968_;
}
else
{
uint8_t v___x_969_; 
v___x_969_ = lean_nat_dec_eq(v_numParams_947_, v_numParams_956_);
if (v___x_969_ == 0)
{
return v___x_969_;
}
else
{
uint8_t v___x_970_; 
v___x_970_ = lean_nat_dec_eq(v_numIndices_948_, v_numIndices_957_);
if (v___x_970_ == 0)
{
return v___x_970_;
}
else
{
uint8_t v___x_971_; 
v___x_971_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_949_, v_all_958_);
if (v___x_971_ == 0)
{
return v___x_971_;
}
else
{
uint8_t v___x_972_; 
v___x_972_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_ctors_950_, v_ctors_959_);
if (v___x_972_ == 0)
{
return v___x_972_;
}
else
{
uint8_t v___x_973_; 
v___x_973_ = lean_nat_dec_eq(v_numNested_951_, v_numNested_960_);
if (v___x_973_ == 0)
{
return v___x_973_;
}
else
{
if (v_isRec_961_ == 0)
{
if (v_isRec_952_ == 0)
{
v___y_967_ = v___x_973_;
goto v___jp_966_;
}
else
{
return v_isRec_961_;
}
}
else
{
v___y_967_ = v_isRec_952_;
goto v___jp_966_;
}
}
}
}
}
}
}
v___jp_964_:
{
if (v_isReflexive_963_ == 0)
{
if (v_isReflexive_954_ == 0)
{
return v___y_965_;
}
else
{
return v_isReflexive_963_;
}
}
else
{
return v_isReflexive_954_;
}
}
v___jp_966_:
{
if (v___y_967_ == 0)
{
return v___y_967_;
}
else
{
if (v_isUnsafe_962_ == 0)
{
if (v_isUnsafe_953_ == 0)
{
v___y_965_ = v___y_967_;
goto v___jp_964_;
}
else
{
return v_isUnsafe_962_;
}
}
else
{
if (v_isUnsafe_953_ == 0)
{
return v_isUnsafe_953_;
}
else
{
v___y_965_ = v_isUnsafe_953_;
goto v___jp_964_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveVal_beq___boxed(lean_object* v_x_974_, lean_object* v_x_975_){
_start:
{
uint8_t v_res_976_; lean_object* v_r_977_; 
v_res_976_ = l_Lean_instBEqInductiveVal_beq(v_x_974_, v_x_975_);
lean_dec_ref(v_x_975_);
lean_dec_ref(v_x_974_);
v_r_977_ = lean_box(v_res_976_);
return v_r_977_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_val(lean_object* v_name_980_, lean_object* v_levelParams_981_, lean_object* v_type_982_, lean_object* v_numParams_983_, lean_object* v_numIndices_984_, lean_object* v_all_985_, lean_object* v_ctors_986_, lean_object* v_numNested_987_, uint8_t v_isRec_988_, uint8_t v_isUnsafe_989_, uint8_t v_isReflexive_990_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_991_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_991_, 0, v_name_980_);
lean_ctor_set(v___x_991_, 1, v_levelParams_981_);
lean_ctor_set(v___x_991_, 2, v_type_982_);
v___x_992_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_992_, 0, v___x_991_);
lean_ctor_set(v___x_992_, 1, v_numParams_983_);
lean_ctor_set(v___x_992_, 2, v_numIndices_984_);
lean_ctor_set(v___x_992_, 3, v_all_985_);
lean_ctor_set(v___x_992_, 4, v_ctors_986_);
lean_ctor_set(v___x_992_, 5, v_numNested_987_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*6, v_isRec_988_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*6 + 1, v_isUnsafe_989_);
lean_ctor_set_uint8(v___x_992_, sizeof(void*)*6 + 2, v_isReflexive_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveValEx___boxed(lean_object* v_name_993_, lean_object* v_levelParams_994_, lean_object* v_type_995_, lean_object* v_numParams_996_, lean_object* v_numIndices_997_, lean_object* v_all_998_, lean_object* v_ctors_999_, lean_object* v_numNested_1000_, lean_object* v_isRec_1001_, lean_object* v_isUnsafe_1002_, lean_object* v_isReflexive_1003_){
_start:
{
uint8_t v_isRec_boxed_1004_; uint8_t v_isUnsafe_boxed_1005_; uint8_t v_isReflexive_boxed_1006_; lean_object* v_res_1007_; 
v_isRec_boxed_1004_ = lean_unbox(v_isRec_1001_);
v_isUnsafe_boxed_1005_ = lean_unbox(v_isUnsafe_1002_);
v_isReflexive_boxed_1006_ = lean_unbox(v_isReflexive_1003_);
v_res_1007_ = lean_mk_inductive_val(v_name_993_, v_levelParams_994_, v_type_995_, v_numParams_996_, v_numIndices_997_, v_all_998_, v_ctors_999_, v_numNested_1000_, v_isRec_boxed_1004_, v_isUnsafe_boxed_1005_, v_isReflexive_boxed_1006_);
return v_res_1007_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_rec(lean_object* v_v_1008_){
_start:
{
uint8_t v_isRec_1009_; 
v_isRec_1009_ = lean_ctor_get_uint8(v_v_1008_, sizeof(void*)*6);
lean_dec_ref(v_v_1008_);
return v_isRec_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isRecEx___boxed(lean_object* v_v_1010_){
_start:
{
uint8_t v_res_1011_; lean_object* v_r_1012_; 
v_res_1011_ = lean_inductive_val_is_rec(v_v_1010_);
v_r_1012_ = lean_box(v_res_1011_);
return v_r_1012_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_unsafe(lean_object* v_v_1013_){
_start:
{
uint8_t v_isUnsafe_1014_; 
v_isUnsafe_1014_ = lean_ctor_get_uint8(v_v_1013_, sizeof(void*)*6 + 1);
lean_dec_ref(v_v_1013_);
return v_isUnsafe_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isUnsafeEx___boxed(lean_object* v_v_1015_){
_start:
{
uint8_t v_res_1016_; lean_object* v_r_1017_; 
v_res_1016_ = lean_inductive_val_is_unsafe(v_v_1015_);
v_r_1017_ = lean_box(v_res_1016_);
return v_r_1017_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_reflexive(lean_object* v_v_1018_){
_start:
{
uint8_t v_isReflexive_1019_; 
v_isReflexive_1019_ = lean_ctor_get_uint8(v_v_1018_, sizeof(void*)*6 + 2);
lean_dec_ref(v_v_1018_);
return v_isReflexive_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isReflexiveEx___boxed(lean_object* v_v_1020_){
_start:
{
uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_res_1021_ = lean_inductive_val_is_reflexive(v_v_1020_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors(lean_object* v_v_1023_){
_start:
{
lean_object* v_ctors_1024_; lean_object* v___x_1025_; 
v_ctors_1024_ = lean_ctor_get(v_v_1023_, 4);
v___x_1025_ = l_List_lengthTR___redArg(v_ctors_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors___boxed(lean_object* v_v_1026_){
_start:
{
lean_object* v_res_1027_; 
v_res_1027_ = l_Lean_InductiveVal_numCtors(v_v_1026_);
lean_dec_ref(v_v_1026_);
return v_res_1027_;
}
}
LEAN_EXPORT uint8_t l_Lean_InductiveVal_isNested(lean_object* v_v_1028_){
_start:
{
lean_object* v_numNested_1029_; lean_object* v___x_1030_; uint8_t v___x_1031_; 
v_numNested_1029_ = lean_ctor_get(v_v_1028_, 5);
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1031_ = lean_nat_dec_lt(v___x_1030_, v_numNested_1029_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isNested___boxed(lean_object* v_v_1032_){
_start:
{
uint8_t v_res_1033_; lean_object* v_r_1034_; 
v_res_1033_ = l_Lean_InductiveVal_isNested(v_v_1032_);
lean_dec_ref(v_v_1032_);
v_r_1034_ = lean_box(v_res_1033_);
return v_r_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object* v_v_1035_){
_start:
{
lean_object* v_all_1036_; lean_object* v_numNested_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_all_1036_ = lean_ctor_get(v_v_1035_, 3);
v_numNested_1037_ = lean_ctor_get(v_v_1035_, 5);
v___x_1038_ = l_List_lengthTR___redArg(v_all_1036_);
v___x_1039_ = lean_nat_add(v___x_1038_, v_numNested_1037_);
lean_dec(v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers___boxed(lean_object* v_v_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_InductiveVal_numTypeFormers(v_v_1040_);
lean_dec_ref(v_v_1040_);
return v_res_1041_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1042_ = 0;
v___x_1043_ = lean_unsigned_to_nat(0u);
v___x_1044_ = lean_box(0);
v___x_1045_ = l_Lean_instInhabitedConstantVal_default;
v___x_1046_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v___x_1044_);
lean_ctor_set(v___x_1046_, 2, v___x_1043_);
lean_ctor_set(v___x_1046_, 3, v___x_1043_);
lean_ctor_set(v___x_1046_, 4, v___x_1043_);
lean_ctor_set_uint8(v___x_1046_, sizeof(void*)*5, v___x_1042_);
return v___x_1046_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default(void){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_obj_once(&l_Lean_instInhabitedConstructorVal_default___closed__0, &l_Lean_instInhabitedConstructorVal_default___closed__0_once, _init_l_Lean_instInhabitedConstructorVal_default___closed__0);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal(void){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = l_Lean_instInhabitedConstructorVal_default;
return v___x_1048_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructorVal_beq(lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
lean_object* v_toConstantVal_1051_; lean_object* v_induct_1052_; lean_object* v_cidx_1053_; lean_object* v_numParams_1054_; lean_object* v_numFields_1055_; uint8_t v_isUnsafe_1056_; lean_object* v_toConstantVal_1057_; lean_object* v_induct_1058_; lean_object* v_cidx_1059_; lean_object* v_numParams_1060_; lean_object* v_numFields_1061_; uint8_t v_isUnsafe_1062_; uint8_t v___x_1063_; 
v_toConstantVal_1051_ = lean_ctor_get(v_x_1049_, 0);
v_induct_1052_ = lean_ctor_get(v_x_1049_, 1);
v_cidx_1053_ = lean_ctor_get(v_x_1049_, 2);
v_numParams_1054_ = lean_ctor_get(v_x_1049_, 3);
v_numFields_1055_ = lean_ctor_get(v_x_1049_, 4);
v_isUnsafe_1056_ = lean_ctor_get_uint8(v_x_1049_, sizeof(void*)*5);
v_toConstantVal_1057_ = lean_ctor_get(v_x_1050_, 0);
v_induct_1058_ = lean_ctor_get(v_x_1050_, 1);
v_cidx_1059_ = lean_ctor_get(v_x_1050_, 2);
v_numParams_1060_ = lean_ctor_get(v_x_1050_, 3);
v_numFields_1061_ = lean_ctor_get(v_x_1050_, 4);
v_isUnsafe_1062_ = lean_ctor_get_uint8(v_x_1050_, sizeof(void*)*5);
v___x_1063_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1051_, v_toConstantVal_1057_);
if (v___x_1063_ == 0)
{
return v___x_1063_;
}
else
{
uint8_t v___x_1064_; 
v___x_1064_ = lean_name_eq(v_induct_1052_, v_induct_1058_);
if (v___x_1064_ == 0)
{
return v___x_1064_;
}
else
{
uint8_t v___x_1065_; 
v___x_1065_ = lean_nat_dec_eq(v_cidx_1053_, v_cidx_1059_);
if (v___x_1065_ == 0)
{
return v___x_1065_;
}
else
{
uint8_t v___x_1066_; 
v___x_1066_ = lean_nat_dec_eq(v_numParams_1054_, v_numParams_1060_);
if (v___x_1066_ == 0)
{
return v___x_1066_;
}
else
{
uint8_t v___x_1067_; 
v___x_1067_ = lean_nat_dec_eq(v_numFields_1055_, v_numFields_1061_);
if (v___x_1067_ == 0)
{
return v___x_1067_;
}
else
{
if (v_isUnsafe_1062_ == 0)
{
if (v_isUnsafe_1056_ == 0)
{
return v___x_1067_;
}
else
{
return v_isUnsafe_1062_;
}
}
else
{
return v_isUnsafe_1056_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructorVal_beq___boxed(lean_object* v_x_1068_, lean_object* v_x_1069_){
_start:
{
uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_res_1070_ = l_Lean_instBEqConstructorVal_beq(v_x_1068_, v_x_1069_);
lean_dec_ref(v_x_1069_);
lean_dec_ref(v_x_1068_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
}
}
LEAN_EXPORT lean_object* lean_mk_constructor_val(lean_object* v_name_1074_, lean_object* v_levelParams_1075_, lean_object* v_type_1076_, lean_object* v_induct_1077_, lean_object* v_cidx_1078_, lean_object* v_numParams_1079_, lean_object* v_numFields_1080_, uint8_t v_isUnsafe_1081_){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1082_, 0, v_name_1074_);
lean_ctor_set(v___x_1082_, 1, v_levelParams_1075_);
lean_ctor_set(v___x_1082_, 2, v_type_1076_);
v___x_1083_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v_induct_1077_);
lean_ctor_set(v___x_1083_, 2, v_cidx_1078_);
lean_ctor_set(v___x_1083_, 3, v_numParams_1079_);
lean_ctor_set(v___x_1083_, 4, v_numFields_1080_);
lean_ctor_set_uint8(v___x_1083_, sizeof(void*)*5, v_isUnsafe_1081_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstructorValEx___boxed(lean_object* v_name_1084_, lean_object* v_levelParams_1085_, lean_object* v_type_1086_, lean_object* v_induct_1087_, lean_object* v_cidx_1088_, lean_object* v_numParams_1089_, lean_object* v_numFields_1090_, lean_object* v_isUnsafe_1091_){
_start:
{
uint8_t v_isUnsafe_boxed_1092_; lean_object* v_res_1093_; 
v_isUnsafe_boxed_1092_ = lean_unbox(v_isUnsafe_1091_);
v_res_1093_ = lean_mk_constructor_val(v_name_1084_, v_levelParams_1085_, v_type_1086_, v_induct_1087_, v_cidx_1088_, v_numParams_1089_, v_numFields_1090_, v_isUnsafe_boxed_1092_);
return v_res_1093_;
}
}
LEAN_EXPORT uint8_t lean_constructor_val_is_unsafe(lean_object* v_v_1094_){
_start:
{
uint8_t v_isUnsafe_1095_; 
v_isUnsafe_1095_ = lean_ctor_get_uint8(v_v_1094_, sizeof(void*)*5);
lean_dec_ref(v_v_1094_);
return v_isUnsafe_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstructorVal_isUnsafeEx___boxed(lean_object* v_v_1096_){
_start:
{
uint8_t v_res_1097_; lean_object* v_r_1098_; 
v_res_1097_ = lean_constructor_val_is_unsafe(v_v_1096_);
v_r_1098_ = lean_box(v_res_1097_);
return v_r_1098_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default___closed__0(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1099_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v___x_1100_);
lean_ctor_set(v___x_1102_, 2, v___x_1099_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default(void){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_obj_once(&l_Lean_instInhabitedRecursorRule_default___closed__0, &l_Lean_instInhabitedRecursorRule_default___closed__0_once, _init_l_Lean_instInhabitedRecursorRule_default___closed__0);
return v___x_1103_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule(void){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_instInhabitedRecursorRule_default;
return v___x_1104_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorRule_beq(lean_object* v_x_1105_, lean_object* v_x_1106_){
_start:
{
lean_object* v_ctor_1107_; lean_object* v_nfields_1108_; lean_object* v_rhs_1109_; lean_object* v_ctor_1110_; lean_object* v_nfields_1111_; lean_object* v_rhs_1112_; uint8_t v___x_1113_; 
v_ctor_1107_ = lean_ctor_get(v_x_1105_, 0);
v_nfields_1108_ = lean_ctor_get(v_x_1105_, 1);
v_rhs_1109_ = lean_ctor_get(v_x_1105_, 2);
v_ctor_1110_ = lean_ctor_get(v_x_1106_, 0);
v_nfields_1111_ = lean_ctor_get(v_x_1106_, 1);
v_rhs_1112_ = lean_ctor_get(v_x_1106_, 2);
v___x_1113_ = lean_name_eq(v_ctor_1107_, v_ctor_1110_);
if (v___x_1113_ == 0)
{
return v___x_1113_;
}
else
{
uint8_t v___x_1114_; 
v___x_1114_ = lean_nat_dec_eq(v_nfields_1108_, v_nfields_1111_);
if (v___x_1114_ == 0)
{
return v___x_1114_;
}
else
{
uint8_t v___x_1115_; 
v___x_1115_ = lean_expr_eqv(v_rhs_1109_, v_rhs_1112_);
return v___x_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorRule_beq___boxed(lean_object* v_x_1116_, lean_object* v_x_1117_){
_start:
{
uint8_t v_res_1118_; lean_object* v_r_1119_; 
v_res_1118_ = l_Lean_instBEqRecursorRule_beq(v_x_1116_, v_x_1117_);
lean_dec_ref(v_x_1117_);
lean_dec_ref(v_x_1116_);
v_r_1119_ = lean_box(v_res_1118_);
return v_r_1119_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1122_ = 0;
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_box(0);
v___x_1125_ = l_Lean_instInhabitedConstantVal_default;
v___x_1126_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v___x_1124_);
lean_ctor_set(v___x_1126_, 2, v___x_1123_);
lean_ctor_set(v___x_1126_, 3, v___x_1123_);
lean_ctor_set(v___x_1126_, 4, v___x_1123_);
lean_ctor_set(v___x_1126_, 5, v___x_1123_);
lean_ctor_set(v___x_1126_, 6, v___x_1124_);
lean_ctor_set_uint8(v___x_1126_, sizeof(void*)*7, v___x_1122_);
lean_ctor_set_uint8(v___x_1126_, sizeof(void*)*7 + 1, v___x_1122_);
return v___x_1126_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default(void){
_start:
{
lean_object* v___x_1127_; 
v___x_1127_ = lean_obj_once(&l_Lean_instInhabitedRecursorVal_default___closed__0, &l_Lean_instInhabitedRecursorVal_default___closed__0_once, _init_l_Lean_instInhabitedRecursorVal_default___closed__0);
return v___x_1127_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal(void){
_start:
{
lean_object* v___x_1128_; 
v___x_1128_ = l_Lean_instInhabitedRecursorVal_default;
return v___x_1128_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(lean_object* v_x_1129_, lean_object* v_x_1130_){
_start:
{
if (lean_obj_tag(v_x_1129_) == 0)
{
if (lean_obj_tag(v_x_1130_) == 0)
{
uint8_t v___x_1131_; 
v___x_1131_ = 1;
return v___x_1131_;
}
else
{
uint8_t v___x_1132_; 
v___x_1132_ = 0;
return v___x_1132_;
}
}
else
{
if (lean_obj_tag(v_x_1130_) == 0)
{
uint8_t v___x_1133_; 
v___x_1133_ = 0;
return v___x_1133_;
}
else
{
lean_object* v_head_1134_; lean_object* v_tail_1135_; lean_object* v_head_1136_; lean_object* v_tail_1137_; uint8_t v___x_1138_; 
v_head_1134_ = lean_ctor_get(v_x_1129_, 0);
v_tail_1135_ = lean_ctor_get(v_x_1129_, 1);
v_head_1136_ = lean_ctor_get(v_x_1130_, 0);
v_tail_1137_ = lean_ctor_get(v_x_1130_, 1);
v___x_1138_ = l_Lean_instBEqRecursorRule_beq(v_head_1134_, v_head_1136_);
if (v___x_1138_ == 0)
{
return v___x_1138_;
}
else
{
v_x_1129_ = v_tail_1135_;
v_x_1130_ = v_tail_1137_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0___boxed(lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
uint8_t v_res_1142_; lean_object* v_r_1143_; 
v_res_1142_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_x_1140_, v_x_1141_);
lean_dec(v_x_1141_);
lean_dec(v_x_1140_);
v_r_1143_ = lean_box(v_res_1142_);
return v_r_1143_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorVal_beq(lean_object* v_x_1144_, lean_object* v_x_1145_){
_start:
{
lean_object* v_toConstantVal_1146_; lean_object* v_all_1147_; lean_object* v_numParams_1148_; lean_object* v_numIndices_1149_; lean_object* v_numMotives_1150_; lean_object* v_numMinors_1151_; lean_object* v_rules_1152_; uint8_t v_k_1153_; uint8_t v_isUnsafe_1154_; lean_object* v_toConstantVal_1155_; lean_object* v_all_1156_; lean_object* v_numParams_1157_; lean_object* v_numIndices_1158_; lean_object* v_numMotives_1159_; lean_object* v_numMinors_1160_; lean_object* v_rules_1161_; uint8_t v_k_1162_; uint8_t v_isUnsafe_1163_; uint8_t v___y_1165_; uint8_t v___x_1166_; 
v_toConstantVal_1146_ = lean_ctor_get(v_x_1144_, 0);
v_all_1147_ = lean_ctor_get(v_x_1144_, 1);
v_numParams_1148_ = lean_ctor_get(v_x_1144_, 2);
v_numIndices_1149_ = lean_ctor_get(v_x_1144_, 3);
v_numMotives_1150_ = lean_ctor_get(v_x_1144_, 4);
v_numMinors_1151_ = lean_ctor_get(v_x_1144_, 5);
v_rules_1152_ = lean_ctor_get(v_x_1144_, 6);
v_k_1153_ = lean_ctor_get_uint8(v_x_1144_, sizeof(void*)*7);
v_isUnsafe_1154_ = lean_ctor_get_uint8(v_x_1144_, sizeof(void*)*7 + 1);
v_toConstantVal_1155_ = lean_ctor_get(v_x_1145_, 0);
v_all_1156_ = lean_ctor_get(v_x_1145_, 1);
v_numParams_1157_ = lean_ctor_get(v_x_1145_, 2);
v_numIndices_1158_ = lean_ctor_get(v_x_1145_, 3);
v_numMotives_1159_ = lean_ctor_get(v_x_1145_, 4);
v_numMinors_1160_ = lean_ctor_get(v_x_1145_, 5);
v_rules_1161_ = lean_ctor_get(v_x_1145_, 6);
v_k_1162_ = lean_ctor_get_uint8(v_x_1145_, sizeof(void*)*7);
v_isUnsafe_1163_ = lean_ctor_get_uint8(v_x_1145_, sizeof(void*)*7 + 1);
v___x_1166_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1146_, v_toConstantVal_1155_);
if (v___x_1166_ == 0)
{
return v___x_1166_;
}
else
{
uint8_t v___x_1167_; 
v___x_1167_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_1147_, v_all_1156_);
if (v___x_1167_ == 0)
{
return v___x_1167_;
}
else
{
uint8_t v___x_1168_; 
v___x_1168_ = lean_nat_dec_eq(v_numParams_1148_, v_numParams_1157_);
if (v___x_1168_ == 0)
{
return v___x_1168_;
}
else
{
uint8_t v___x_1169_; 
v___x_1169_ = lean_nat_dec_eq(v_numIndices_1149_, v_numIndices_1158_);
if (v___x_1169_ == 0)
{
return v___x_1169_;
}
else
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_nat_dec_eq(v_numMotives_1150_, v_numMotives_1159_);
if (v___x_1170_ == 0)
{
return v___x_1170_;
}
else
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_nat_dec_eq(v_numMinors_1151_, v_numMinors_1160_);
if (v___x_1171_ == 0)
{
return v___x_1171_;
}
else
{
uint8_t v___x_1172_; 
v___x_1172_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_rules_1152_, v_rules_1161_);
if (v___x_1172_ == 0)
{
return v___x_1172_;
}
else
{
if (v_k_1162_ == 0)
{
if (v_k_1153_ == 0)
{
v___y_1165_ = v___x_1172_;
goto v___jp_1164_;
}
else
{
return v_k_1162_;
}
}
else
{
v___y_1165_ = v_k_1153_;
goto v___jp_1164_;
}
}
}
}
}
}
}
}
v___jp_1164_:
{
if (v___y_1165_ == 0)
{
return v___y_1165_;
}
else
{
if (v_isUnsafe_1163_ == 0)
{
if (v_isUnsafe_1154_ == 0)
{
return v___y_1165_;
}
else
{
return v_isUnsafe_1163_;
}
}
else
{
return v_isUnsafe_1154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorVal_beq___boxed(lean_object* v_x_1173_, lean_object* v_x_1174_){
_start:
{
uint8_t v_res_1175_; lean_object* v_r_1176_; 
v_res_1175_ = l_Lean_instBEqRecursorVal_beq(v_x_1173_, v_x_1174_);
lean_dec_ref(v_x_1174_);
lean_dec_ref(v_x_1173_);
v_r_1176_ = lean_box(v_res_1175_);
return v_r_1176_;
}
}
LEAN_EXPORT lean_object* lean_mk_recursor_val(lean_object* v_name_1179_, lean_object* v_levelParams_1180_, lean_object* v_type_1181_, lean_object* v_all_1182_, lean_object* v_numParams_1183_, lean_object* v_numIndices_1184_, lean_object* v_numMotives_1185_, lean_object* v_numMinors_1186_, lean_object* v_rules_1187_, uint8_t v_k_1188_, uint8_t v_isUnsafe_1189_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1190_, 0, v_name_1179_);
lean_ctor_set(v___x_1190_, 1, v_levelParams_1180_);
lean_ctor_set(v___x_1190_, 2, v_type_1181_);
v___x_1191_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1191_, 0, v___x_1190_);
lean_ctor_set(v___x_1191_, 1, v_all_1182_);
lean_ctor_set(v___x_1191_, 2, v_numParams_1183_);
lean_ctor_set(v___x_1191_, 3, v_numIndices_1184_);
lean_ctor_set(v___x_1191_, 4, v_numMotives_1185_);
lean_ctor_set(v___x_1191_, 5, v_numMinors_1186_);
lean_ctor_set(v___x_1191_, 6, v_rules_1187_);
lean_ctor_set_uint8(v___x_1191_, sizeof(void*)*7, v_k_1188_);
lean_ctor_set_uint8(v___x_1191_, sizeof(void*)*7 + 1, v_isUnsafe_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecursorValEx___boxed(lean_object* v_name_1192_, lean_object* v_levelParams_1193_, lean_object* v_type_1194_, lean_object* v_all_1195_, lean_object* v_numParams_1196_, lean_object* v_numIndices_1197_, lean_object* v_numMotives_1198_, lean_object* v_numMinors_1199_, lean_object* v_rules_1200_, lean_object* v_k_1201_, lean_object* v_isUnsafe_1202_){
_start:
{
uint8_t v_k_boxed_1203_; uint8_t v_isUnsafe_boxed_1204_; lean_object* v_res_1205_; 
v_k_boxed_1203_ = lean_unbox(v_k_1201_);
v_isUnsafe_boxed_1204_ = lean_unbox(v_isUnsafe_1202_);
v_res_1205_ = lean_mk_recursor_val(v_name_1192_, v_levelParams_1193_, v_type_1194_, v_all_1195_, v_numParams_1196_, v_numIndices_1197_, v_numMotives_1198_, v_numMinors_1199_, v_rules_1200_, v_k_boxed_1203_, v_isUnsafe_boxed_1204_);
return v_res_1205_;
}
}
LEAN_EXPORT uint8_t lean_recursor_k(lean_object* v_v_1206_){
_start:
{
uint8_t v_k_1207_; 
v_k_1207_ = lean_ctor_get_uint8(v_v_1206_, sizeof(void*)*7);
lean_dec_ref(v_v_1206_);
return v_k_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_kEx___boxed(lean_object* v_v_1208_){
_start:
{
uint8_t v_res_1209_; lean_object* v_r_1210_; 
v_res_1209_ = lean_recursor_k(v_v_1208_);
v_r_1210_ = lean_box(v_res_1209_);
return v_r_1210_;
}
}
LEAN_EXPORT uint8_t lean_recursor_is_unsafe(lean_object* v_v_1211_){
_start:
{
uint8_t v_isUnsafe_1212_; 
v_isUnsafe_1212_ = lean_ctor_get_uint8(v_v_1211_, sizeof(void*)*7 + 1);
lean_dec_ref(v_v_1211_);
return v_isUnsafe_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_isUnsafeEx___boxed(lean_object* v_v_1213_){
_start:
{
uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_res_1214_ = lean_recursor_is_unsafe(v_v_1213_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object* v_v_1216_){
_start:
{
lean_object* v_numParams_1217_; lean_object* v_numIndices_1218_; lean_object* v_numMotives_1219_; lean_object* v_numMinors_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_numParams_1217_ = lean_ctor_get(v_v_1216_, 2);
v_numIndices_1218_ = lean_ctor_get(v_v_1216_, 3);
v_numMotives_1219_ = lean_ctor_get(v_v_1216_, 4);
v_numMinors_1220_ = lean_ctor_get(v_v_1216_, 5);
v___x_1221_ = lean_nat_add(v_numParams_1217_, v_numMotives_1219_);
v___x_1222_ = lean_nat_add(v___x_1221_, v_numMinors_1220_);
lean_dec(v___x_1221_);
v___x_1223_ = lean_nat_add(v___x_1222_, v_numIndices_1218_);
lean_dec(v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx___boxed(lean_object* v_v_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_RecursorVal_getMajorIdx(v_v_1224_);
lean_dec_ref(v_v_1224_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx(lean_object* v_v_1226_){
_start:
{
lean_object* v_numParams_1227_; lean_object* v_numMotives_1228_; lean_object* v_numMinors_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v_numParams_1227_ = lean_ctor_get(v_v_1226_, 2);
v_numMotives_1228_ = lean_ctor_get(v_v_1226_, 4);
v_numMinors_1229_ = lean_ctor_get(v_v_1226_, 5);
v___x_1230_ = lean_nat_add(v_numParams_1227_, v_numMotives_1228_);
v___x_1231_ = lean_nat_add(v___x_1230_, v_numMinors_1229_);
lean_dec(v___x_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx___boxed(lean_object* v_v_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_RecursorVal_getFirstIndexIdx(v_v_1232_);
lean_dec_ref(v_v_1232_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx(lean_object* v_v_1234_){
_start:
{
lean_object* v_numParams_1235_; lean_object* v_numMotives_1236_; lean_object* v___x_1237_; 
v_numParams_1235_ = lean_ctor_get(v_v_1234_, 2);
v_numMotives_1236_ = lean_ctor_get(v_v_1234_, 4);
v___x_1237_ = lean_nat_add(v_numParams_1235_, v_numMotives_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx___boxed(lean_object* v_v_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Lean_RecursorVal_getFirstMinorIdx(v_v_1238_);
lean_dec_ref(v_v_1238_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(lean_object* v_x_1240_, lean_object* v_x_1241_){
_start:
{
lean_object* v_zero_1242_; uint8_t v_isZero_1243_; 
v_zero_1242_ = lean_unsigned_to_nat(0u);
v_isZero_1243_ = lean_nat_dec_eq(v_x_1240_, v_zero_1242_);
if (v_isZero_1243_ == 1)
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec(v_x_1240_);
v___x_1244_ = l_Lean_Expr_bindingDomain_x21(v_x_1241_);
lean_dec_ref(v_x_1241_);
v___x_1245_ = l_Lean_Expr_getAppFn(v___x_1244_);
lean_dec_ref(v___x_1244_);
v___x_1246_ = l_Lean_Expr_constName_x21(v___x_1245_);
lean_dec_ref(v___x_1245_);
return v___x_1246_;
}
else
{
lean_object* v_one_1247_; lean_object* v_n_1248_; lean_object* v___x_1249_; 
v_one_1247_ = lean_unsigned_to_nat(1u);
v_n_1248_ = lean_nat_sub(v_x_1240_, v_one_1247_);
lean_dec(v_x_1240_);
v___x_1249_ = l_Lean_Expr_bindingBody_x21(v_x_1241_);
lean_dec_ref(v_x_1241_);
v_x_1240_ = v_n_1248_;
v_x_1241_ = v___x_1249_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorInduct(lean_object* v_v_1251_){
_start:
{
lean_object* v_toConstantVal_1252_; lean_object* v_type_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; 
v_toConstantVal_1252_ = lean_ctor_get(v_v_1251_, 0);
v_type_1253_ = lean_ctor_get(v_toConstantVal_1252_, 2);
lean_inc_ref(v_type_1253_);
v___x_1254_ = l_Lean_RecursorVal_getMajorIdx(v_v_1251_);
lean_dec_ref(v_v_1251_);
v___x_1255_ = l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(v___x_1254_, v_type_1253_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx(uint8_t v_x_1256_){
_start:
{
switch(v_x_1256_)
{
case 0:
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_unsigned_to_nat(0u);
return v___x_1257_;
}
case 1:
{
lean_object* v___x_1258_; 
v___x_1258_ = lean_unsigned_to_nat(1u);
return v___x_1258_;
}
case 2:
{
lean_object* v___x_1259_; 
v___x_1259_ = lean_unsigned_to_nat(2u);
return v___x_1259_;
}
default: 
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_unsigned_to_nat(3u);
return v___x_1260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___boxed(lean_object* v_x_1261_){
_start:
{
uint8_t v_x_boxed_1262_; lean_object* v_res_1263_; 
v_x_boxed_1262_ = lean_unbox(v_x_1261_);
v_res_1263_ = l_Lean_QuotKind_ctorIdx(v_x_boxed_1262_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg(lean_object* v_k_1264_){
_start:
{
lean_inc(v_k_1264_);
return v_k_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg___boxed(lean_object* v_k_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Lean_QuotKind_ctorElim___redArg(v_k_1265_);
lean_dec(v_k_1265_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim(lean_object* v_motive_1267_, lean_object* v_ctorIdx_1268_, uint8_t v_t_1269_, lean_object* v_h_1270_, lean_object* v_k_1271_){
_start:
{
lean_inc(v_k_1271_);
return v_k_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___boxed(lean_object* v_motive_1272_, lean_object* v_ctorIdx_1273_, lean_object* v_t_1274_, lean_object* v_h_1275_, lean_object* v_k_1276_){
_start:
{
uint8_t v_t_boxed_1277_; lean_object* v_res_1278_; 
v_t_boxed_1277_ = lean_unbox(v_t_1274_);
v_res_1278_ = l_Lean_QuotKind_ctorElim(v_motive_1272_, v_ctorIdx_1273_, v_t_boxed_1277_, v_h_1275_, v_k_1276_);
lean_dec(v_k_1276_);
lean_dec(v_ctorIdx_1273_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg(lean_object* v_type_1279_){
_start:
{
lean_inc(v_type_1279_);
return v_type_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg___boxed(lean_object* v_type_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Lean_QuotKind_type_elim___redArg(v_type_1280_);
lean_dec(v_type_1280_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim(lean_object* v_motive_1282_, uint8_t v_t_1283_, lean_object* v_h_1284_, lean_object* v_type_1285_){
_start:
{
lean_inc(v_type_1285_);
return v_type_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___boxed(lean_object* v_motive_1286_, lean_object* v_t_1287_, lean_object* v_h_1288_, lean_object* v_type_1289_){
_start:
{
uint8_t v_t_boxed_1290_; lean_object* v_res_1291_; 
v_t_boxed_1290_ = lean_unbox(v_t_1287_);
v_res_1291_ = l_Lean_QuotKind_type_elim(v_motive_1286_, v_t_boxed_1290_, v_h_1288_, v_type_1289_);
lean_dec(v_type_1289_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg(lean_object* v_ctor_1292_){
_start:
{
lean_inc(v_ctor_1292_);
return v_ctor_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg___boxed(lean_object* v_ctor_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Lean_QuotKind_ctor_elim___redArg(v_ctor_1293_);
lean_dec(v_ctor_1293_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim(lean_object* v_motive_1295_, uint8_t v_t_1296_, lean_object* v_h_1297_, lean_object* v_ctor_1298_){
_start:
{
lean_inc(v_ctor_1298_);
return v_ctor_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___boxed(lean_object* v_motive_1299_, lean_object* v_t_1300_, lean_object* v_h_1301_, lean_object* v_ctor_1302_){
_start:
{
uint8_t v_t_boxed_1303_; lean_object* v_res_1304_; 
v_t_boxed_1303_ = lean_unbox(v_t_1300_);
v_res_1304_ = l_Lean_QuotKind_ctor_elim(v_motive_1299_, v_t_boxed_1303_, v_h_1301_, v_ctor_1302_);
lean_dec(v_ctor_1302_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg(lean_object* v_lift_1305_){
_start:
{
lean_inc(v_lift_1305_);
return v_lift_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg___boxed(lean_object* v_lift_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_QuotKind_lift_elim___redArg(v_lift_1306_);
lean_dec(v_lift_1306_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim(lean_object* v_motive_1308_, uint8_t v_t_1309_, lean_object* v_h_1310_, lean_object* v_lift_1311_){
_start:
{
lean_inc(v_lift_1311_);
return v_lift_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___boxed(lean_object* v_motive_1312_, lean_object* v_t_1313_, lean_object* v_h_1314_, lean_object* v_lift_1315_){
_start:
{
uint8_t v_t_boxed_1316_; lean_object* v_res_1317_; 
v_t_boxed_1316_ = lean_unbox(v_t_1313_);
v_res_1317_ = l_Lean_QuotKind_lift_elim(v_motive_1312_, v_t_boxed_1316_, v_h_1314_, v_lift_1315_);
lean_dec(v_lift_1315_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg(lean_object* v_ind_1318_){
_start:
{
lean_inc(v_ind_1318_);
return v_ind_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg___boxed(lean_object* v_ind_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_QuotKind_ind_elim___redArg(v_ind_1319_);
lean_dec(v_ind_1319_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim(lean_object* v_motive_1321_, uint8_t v_t_1322_, lean_object* v_h_1323_, lean_object* v_ind_1324_){
_start:
{
lean_inc(v_ind_1324_);
return v_ind_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___boxed(lean_object* v_motive_1325_, lean_object* v_t_1326_, lean_object* v_h_1327_, lean_object* v_ind_1328_){
_start:
{
uint8_t v_t_boxed_1329_; lean_object* v_res_1330_; 
v_t_boxed_1329_ = lean_unbox(v_t_1326_);
v_res_1330_ = l_Lean_QuotKind_ind_elim(v_motive_1325_, v_t_boxed_1329_, v_h_1327_, v_ind_1328_);
lean_dec(v_ind_1328_);
return v_res_1330_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind_default(void){
_start:
{
uint8_t v___x_1331_; 
v___x_1331_ = 0;
return v___x_1331_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind(void){
_start:
{
uint8_t v___x_1332_; 
v___x_1332_ = 0;
return v___x_1332_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqQuotKind_beq(uint8_t v_x_1333_, uint8_t v_y_1334_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1335_ = l_Lean_QuotKind_ctorIdx(v_x_1333_);
v___x_1336_ = l_Lean_QuotKind_ctorIdx(v_y_1334_);
v___x_1337_ = lean_nat_dec_eq(v___x_1335_, v___x_1336_);
lean_dec(v___x_1336_);
lean_dec(v___x_1335_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqQuotKind_beq___boxed(lean_object* v_x_1338_, lean_object* v_y_1339_){
_start:
{
uint8_t v_x_21__boxed_1340_; uint8_t v_y_22__boxed_1341_; uint8_t v_res_1342_; lean_object* v_r_1343_; 
v_x_21__boxed_1340_ = lean_unbox(v_x_1338_);
v_y_22__boxed_1341_ = lean_unbox(v_y_1339_);
v_res_1342_ = l_Lean_instBEqQuotKind_beq(v_x_21__boxed_1340_, v_y_22__boxed_1341_);
v_r_1343_ = lean_box(v_res_1342_);
return v_r_1343_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default___closed__0(void){
_start:
{
uint8_t v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1346_ = 0;
v___x_1347_ = l_Lean_instInhabitedConstantVal_default;
v___x_1348_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*1, v___x_1346_);
return v___x_1348_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default(void){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_obj_once(&l_Lean_instInhabitedQuotVal_default___closed__0, &l_Lean_instInhabitedQuotVal_default___closed__0_once, _init_l_Lean_instInhabitedQuotVal_default___closed__0);
return v___x_1349_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal(void){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_instInhabitedQuotVal_default;
return v___x_1350_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqQuotVal_beq(lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
lean_object* v_toConstantVal_1353_; uint8_t v_kind_1354_; lean_object* v_toConstantVal_1355_; uint8_t v_kind_1356_; uint8_t v___x_1357_; 
v_toConstantVal_1353_ = lean_ctor_get(v_x_1351_, 0);
v_kind_1354_ = lean_ctor_get_uint8(v_x_1351_, sizeof(void*)*1);
v_toConstantVal_1355_ = lean_ctor_get(v_x_1352_, 0);
v_kind_1356_ = lean_ctor_get_uint8(v_x_1352_, sizeof(void*)*1);
v___x_1357_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1353_, v_toConstantVal_1355_);
if (v___x_1357_ == 0)
{
return v___x_1357_;
}
else
{
uint8_t v___x_1358_; 
v___x_1358_ = l_Lean_instBEqQuotKind_beq(v_kind_1354_, v_kind_1356_);
return v___x_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqQuotVal_beq___boxed(lean_object* v_x_1359_, lean_object* v_x_1360_){
_start:
{
uint8_t v_res_1361_; lean_object* v_r_1362_; 
v_res_1361_ = l_Lean_instBEqQuotVal_beq(v_x_1359_, v_x_1360_);
lean_dec_ref(v_x_1360_);
lean_dec_ref(v_x_1359_);
v_r_1362_ = lean_box(v_res_1361_);
return v_r_1362_;
}
}
LEAN_EXPORT lean_object* lean_mk_quot_val(lean_object* v_name_1365_, lean_object* v_levelParams_1366_, lean_object* v_type_1367_, uint8_t v_kind_1368_){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1369_, 0, v_name_1365_);
lean_ctor_set(v___x_1369_, 1, v_levelParams_1366_);
lean_ctor_set(v___x_1369_, 2, v_type_1367_);
v___x_1370_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
lean_ctor_set_uint8(v___x_1370_, sizeof(void*)*1, v_kind_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkQuotValEx___boxed(lean_object* v_name_1371_, lean_object* v_levelParams_1372_, lean_object* v_type_1373_, lean_object* v_kind_1374_){
_start:
{
uint8_t v_kind_boxed_1375_; lean_object* v_res_1376_; 
v_kind_boxed_1375_ = lean_unbox(v_kind_1374_);
v_res_1376_ = lean_mk_quot_val(v_name_1371_, v_levelParams_1372_, v_type_1373_, v_kind_boxed_1375_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx(lean_object* v_x_1377_){
_start:
{
switch(lean_obj_tag(v_x_1377_))
{
case 0:
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_unsigned_to_nat(0u);
return v___x_1378_;
}
case 1:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_unsigned_to_nat(1u);
return v___x_1379_;
}
case 2:
{
lean_object* v___x_1380_; 
v___x_1380_ = lean_unsigned_to_nat(2u);
return v___x_1380_;
}
case 3:
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_unsigned_to_nat(3u);
return v___x_1381_;
}
case 4:
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_unsigned_to_nat(4u);
return v___x_1382_;
}
case 5:
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_unsigned_to_nat(5u);
return v___x_1383_;
}
case 6:
{
lean_object* v___x_1384_; 
v___x_1384_ = lean_unsigned_to_nat(6u);
return v___x_1384_;
}
default: 
{
lean_object* v___x_1385_; 
v___x_1385_ = lean_unsigned_to_nat(7u);
return v___x_1385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___boxed(lean_object* v_x_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_ConstantInfo_ctorIdx(v_x_1386_);
lean_dec_ref(v_x_1386_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___redArg(lean_object* v_t_1388_, lean_object* v_k_1389_){
_start:
{
lean_object* v_val_1390_; lean_object* v___x_1391_; 
v_val_1390_ = lean_ctor_get(v_t_1388_, 0);
lean_inc_ref(v_val_1390_);
lean_dec_ref(v_t_1388_);
v___x_1391_ = lean_apply_1(v_k_1389_, v_val_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim(lean_object* v_motive_1392_, lean_object* v_ctorIdx_1393_, lean_object* v_t_1394_, lean_object* v_h_1395_, lean_object* v_k_1396_){
_start:
{
lean_object* v___x_1397_; 
v___x_1397_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1394_, v_k_1396_);
return v___x_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___boxed(lean_object* v_motive_1398_, lean_object* v_ctorIdx_1399_, lean_object* v_t_1400_, lean_object* v_h_1401_, lean_object* v_k_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_ConstantInfo_ctorElim(v_motive_1398_, v_ctorIdx_1399_, v_t_1400_, v_h_1401_, v_k_1402_);
lean_dec(v_ctorIdx_1399_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim___redArg(lean_object* v_t_1404_, lean_object* v_axiomInfo_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1404_, v_axiomInfo_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim(lean_object* v_motive_1407_, lean_object* v_t_1408_, lean_object* v_h_1409_, lean_object* v_axiomInfo_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1408_, v_axiomInfo_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim___redArg(lean_object* v_t_1412_, lean_object* v_defnInfo_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1412_, v_defnInfo_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim(lean_object* v_motive_1415_, lean_object* v_t_1416_, lean_object* v_h_1417_, lean_object* v_defnInfo_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1416_, v_defnInfo_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim___redArg(lean_object* v_t_1420_, lean_object* v_thmInfo_1421_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1420_, v_thmInfo_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim(lean_object* v_motive_1423_, lean_object* v_t_1424_, lean_object* v_h_1425_, lean_object* v_thmInfo_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1424_, v_thmInfo_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim___redArg(lean_object* v_t_1428_, lean_object* v_opaqueInfo_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1428_, v_opaqueInfo_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim(lean_object* v_motive_1431_, lean_object* v_t_1432_, lean_object* v_h_1433_, lean_object* v_opaqueInfo_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1432_, v_opaqueInfo_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim___redArg(lean_object* v_t_1436_, lean_object* v_quotInfo_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1436_, v_quotInfo_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim(lean_object* v_motive_1439_, lean_object* v_t_1440_, lean_object* v_h_1441_, lean_object* v_quotInfo_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1440_, v_quotInfo_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim___redArg(lean_object* v_t_1444_, lean_object* v_inductInfo_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1444_, v_inductInfo_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim(lean_object* v_motive_1447_, lean_object* v_t_1448_, lean_object* v_h_1449_, lean_object* v_inductInfo_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1448_, v_inductInfo_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim___redArg(lean_object* v_t_1452_, lean_object* v_ctorInfo_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1452_, v_ctorInfo_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim(lean_object* v_motive_1455_, lean_object* v_t_1456_, lean_object* v_h_1457_, lean_object* v_ctorInfo_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1456_, v_ctorInfo_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim___redArg(lean_object* v_t_1460_, lean_object* v_recInfo_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1460_, v_recInfo_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim(lean_object* v_motive_1463_, lean_object* v_t_1464_, lean_object* v_h_1465_, lean_object* v_recInfo_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1464_, v_recInfo_1466_);
return v___x_1467_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default___closed__0(void){
_start:
{
lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1468_ = l_Lean_instInhabitedAxiomVal_default;
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1468_);
return v___x_1469_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default(void){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_obj_once(&l_Lean_instInhabitedConstantInfo_default___closed__0, &l_Lean_instInhabitedConstantInfo_default___closed__0_once, _init_l_Lean_instInhabitedConstantInfo_default___closed__0);
return v___x_1470_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo(void){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_instInhabitedConstantInfo_default;
return v___x_1471_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstantInfo_beq(lean_object* v_x_1472_, lean_object* v_x_1473_){
_start:
{
switch(lean_obj_tag(v_x_1472_))
{
case 0:
{
if (lean_obj_tag(v_x_1473_) == 0)
{
lean_object* v_val_1474_; lean_object* v_val_1475_; uint8_t v___x_1476_; 
v_val_1474_ = lean_ctor_get(v_x_1472_, 0);
v_val_1475_ = lean_ctor_get(v_x_1473_, 0);
v___x_1476_ = l_Lean_instBEqAxiomVal_beq(v_val_1474_, v_val_1475_);
return v___x_1476_;
}
else
{
uint8_t v___x_1477_; 
v___x_1477_ = 0;
return v___x_1477_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1473_) == 1)
{
lean_object* v_val_1478_; lean_object* v_val_1479_; uint8_t v___x_1480_; 
v_val_1478_ = lean_ctor_get(v_x_1472_, 0);
v_val_1479_ = lean_ctor_get(v_x_1473_, 0);
v___x_1480_ = l_Lean_instBEqDefinitionVal_beq(v_val_1478_, v_val_1479_);
return v___x_1480_;
}
else
{
uint8_t v___x_1481_; 
v___x_1481_ = 0;
return v___x_1481_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1473_) == 2)
{
lean_object* v_val_1482_; lean_object* v_val_1483_; uint8_t v___x_1484_; 
v_val_1482_ = lean_ctor_get(v_x_1472_, 0);
v_val_1483_ = lean_ctor_get(v_x_1473_, 0);
v___x_1484_ = l_Lean_instBEqTheoremVal_beq(v_val_1482_, v_val_1483_);
return v___x_1484_;
}
else
{
uint8_t v___x_1485_; 
v___x_1485_ = 0;
return v___x_1485_;
}
}
case 3:
{
if (lean_obj_tag(v_x_1473_) == 3)
{
lean_object* v_val_1486_; lean_object* v_val_1487_; uint8_t v___x_1488_; 
v_val_1486_ = lean_ctor_get(v_x_1472_, 0);
v_val_1487_ = lean_ctor_get(v_x_1473_, 0);
v___x_1488_ = l_Lean_instBEqOpaqueVal_beq(v_val_1486_, v_val_1487_);
return v___x_1488_;
}
else
{
uint8_t v___x_1489_; 
v___x_1489_ = 0;
return v___x_1489_;
}
}
case 4:
{
if (lean_obj_tag(v_x_1473_) == 4)
{
lean_object* v_val_1490_; lean_object* v_val_1491_; uint8_t v___x_1492_; 
v_val_1490_ = lean_ctor_get(v_x_1472_, 0);
v_val_1491_ = lean_ctor_get(v_x_1473_, 0);
v___x_1492_ = l_Lean_instBEqQuotVal_beq(v_val_1490_, v_val_1491_);
return v___x_1492_;
}
else
{
uint8_t v___x_1493_; 
v___x_1493_ = 0;
return v___x_1493_;
}
}
case 5:
{
if (lean_obj_tag(v_x_1473_) == 5)
{
lean_object* v_val_1494_; lean_object* v_val_1495_; uint8_t v___x_1496_; 
v_val_1494_ = lean_ctor_get(v_x_1472_, 0);
v_val_1495_ = lean_ctor_get(v_x_1473_, 0);
v___x_1496_ = l_Lean_instBEqInductiveVal_beq(v_val_1494_, v_val_1495_);
return v___x_1496_;
}
else
{
uint8_t v___x_1497_; 
v___x_1497_ = 0;
return v___x_1497_;
}
}
case 6:
{
if (lean_obj_tag(v_x_1473_) == 6)
{
lean_object* v_val_1498_; lean_object* v_val_1499_; uint8_t v___x_1500_; 
v_val_1498_ = lean_ctor_get(v_x_1472_, 0);
v_val_1499_ = lean_ctor_get(v_x_1473_, 0);
v___x_1500_ = l_Lean_instBEqConstructorVal_beq(v_val_1498_, v_val_1499_);
return v___x_1500_;
}
else
{
uint8_t v___x_1501_; 
v___x_1501_ = 0;
return v___x_1501_;
}
}
default: 
{
if (lean_obj_tag(v_x_1473_) == 7)
{
lean_object* v_val_1502_; lean_object* v_val_1503_; uint8_t v___x_1504_; 
v_val_1502_ = lean_ctor_get(v_x_1472_, 0);
v_val_1503_ = lean_ctor_get(v_x_1473_, 0);
v___x_1504_ = l_Lean_instBEqRecursorVal_beq(v_val_1502_, v_val_1503_);
return v___x_1504_;
}
else
{
uint8_t v___x_1505_; 
v___x_1505_ = 0;
return v___x_1505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstantInfo_beq___boxed(lean_object* v_x_1506_, lean_object* v_x_1507_){
_start:
{
uint8_t v_res_1508_; lean_object* v_r_1509_; 
v_res_1508_ = l_Lean_instBEqConstantInfo_beq(v_x_1506_, v_x_1507_);
lean_dec_ref(v_x_1507_);
lean_dec_ref(v_x_1506_);
v_r_1509_ = lean_box(v_res_1508_);
return v_r_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object* v_x_1512_){
_start:
{
lean_object* v_val_1513_; lean_object* v_toConstantVal_1514_; 
v_val_1513_ = lean_ctor_get(v_x_1512_, 0);
v_toConstantVal_1514_ = lean_ctor_get(v_val_1513_, 0);
lean_inc_ref(v_toConstantVal_1514_);
return v_toConstantVal_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object* v_x_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_ConstantInfo_toConstantVal(v_x_1515_);
lean_dec_ref(v_x_1515_);
return v_res_1516_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object* v_x_1517_){
_start:
{
switch(lean_obj_tag(v_x_1517_))
{
case 0:
{
lean_object* v_val_1518_; uint8_t v_isUnsafe_1519_; 
v_val_1518_ = lean_ctor_get(v_x_1517_, 0);
v_isUnsafe_1519_ = lean_ctor_get_uint8(v_val_1518_, sizeof(void*)*1);
return v_isUnsafe_1519_;
}
case 1:
{
lean_object* v_val_1520_; uint8_t v_safety_1521_; uint8_t v___x_1522_; uint8_t v___x_1523_; 
v_val_1520_ = lean_ctor_get(v_x_1517_, 0);
v_safety_1521_ = lean_ctor_get_uint8(v_val_1520_, sizeof(void*)*4);
v___x_1522_ = 0;
v___x_1523_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1521_, v___x_1522_);
return v___x_1523_;
}
case 3:
{
lean_object* v_val_1524_; uint8_t v_isUnsafe_1525_; 
v_val_1524_ = lean_ctor_get(v_x_1517_, 0);
v_isUnsafe_1525_ = lean_ctor_get_uint8(v_val_1524_, sizeof(void*)*3);
return v_isUnsafe_1525_;
}
case 5:
{
lean_object* v_val_1526_; uint8_t v_isUnsafe_1527_; 
v_val_1526_ = lean_ctor_get(v_x_1517_, 0);
v_isUnsafe_1527_ = lean_ctor_get_uint8(v_val_1526_, sizeof(void*)*6 + 1);
return v_isUnsafe_1527_;
}
case 6:
{
lean_object* v_val_1528_; uint8_t v_isUnsafe_1529_; 
v_val_1528_ = lean_ctor_get(v_x_1517_, 0);
v_isUnsafe_1529_ = lean_ctor_get_uint8(v_val_1528_, sizeof(void*)*5);
return v_isUnsafe_1529_;
}
case 7:
{
lean_object* v_val_1530_; uint8_t v_isUnsafe_1531_; 
v_val_1530_ = lean_ctor_get(v_x_1517_, 0);
v_isUnsafe_1531_ = lean_ctor_get_uint8(v_val_1530_, sizeof(void*)*7 + 1);
return v_isUnsafe_1531_;
}
default: 
{
uint8_t v___x_1532_; 
v___x_1532_ = 0;
return v___x_1532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isUnsafe___boxed(lean_object* v_x_1533_){
_start:
{
uint8_t v_res_1534_; lean_object* v_r_1535_; 
v_res_1534_ = l_Lean_ConstantInfo_isUnsafe(v_x_1533_);
lean_dec_ref(v_x_1533_);
v_r_1535_ = lean_box(v_res_1534_);
return v_r_1535_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isPartial(lean_object* v_x_1536_){
_start:
{
if (lean_obj_tag(v_x_1536_) == 1)
{
lean_object* v_val_1537_; uint8_t v_safety_1538_; uint8_t v___x_1539_; uint8_t v___x_1540_; 
v_val_1537_ = lean_ctor_get(v_x_1536_, 0);
v_safety_1538_ = lean_ctor_get_uint8(v_val_1537_, sizeof(void*)*4);
v___x_1539_ = 2;
v___x_1540_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1538_, v___x_1539_);
return v___x_1540_;
}
else
{
uint8_t v___x_1541_; 
v___x_1541_ = 0;
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isPartial___boxed(lean_object* v_x_1542_){
_start:
{
uint8_t v_res_1543_; lean_object* v_r_1544_; 
v_res_1543_ = l_Lean_ConstantInfo_isPartial(v_x_1542_);
lean_dec_ref(v_x_1542_);
v_r_1544_ = lean_box(v_res_1543_);
return v_r_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name(lean_object* v_d_1545_){
_start:
{
lean_object* v___x_1546_; lean_object* v_name_1547_; 
v___x_1546_ = l_Lean_ConstantInfo_toConstantVal(v_d_1545_);
v_name_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_name_1547_);
lean_dec_ref(v___x_1546_);
return v_name_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name___boxed(lean_object* v_d_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_ConstantInfo_name(v_d_1548_);
lean_dec_ref(v_d_1548_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams(lean_object* v_d_1550_){
_start:
{
lean_object* v___x_1551_; lean_object* v_levelParams_1552_; 
v___x_1551_ = l_Lean_ConstantInfo_toConstantVal(v_d_1550_);
v_levelParams_1552_ = lean_ctor_get(v___x_1551_, 1);
lean_inc(v_levelParams_1552_);
lean_dec_ref(v___x_1551_);
return v_levelParams_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams___boxed(lean_object* v_d_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_ConstantInfo_levelParams(v_d_1553_);
lean_dec_ref(v_d_1553_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object* v_d_1555_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = l_Lean_ConstantInfo_levelParams(v_d_1555_);
v___x_1557_ = l_List_lengthTR___redArg(v___x_1556_);
lean_dec(v___x_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams___boxed(lean_object* v_d_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l_Lean_ConstantInfo_numLevelParams(v_d_1558_);
lean_dec_ref(v_d_1558_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type(lean_object* v_d_1560_){
_start:
{
lean_object* v___x_1561_; lean_object* v_type_1562_; 
v___x_1561_ = l_Lean_ConstantInfo_toConstantVal(v_d_1560_);
v_type_1562_ = lean_ctor_get(v___x_1561_, 2);
lean_inc_ref(v_type_1562_);
lean_dec_ref(v___x_1561_);
return v_type_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type___boxed(lean_object* v_d_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Lean_ConstantInfo_type(v_d_1563_);
lean_dec_ref(v_d_1563_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f(lean_object* v_info_1565_, uint8_t v_allowOpaque_1566_){
_start:
{
switch(lean_obj_tag(v_info_1565_))
{
case 1:
{
lean_object* v_val_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1575_; 
v_val_1567_ = lean_ctor_get(v_info_1565_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_info_1565_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1569_ = v_info_1565_;
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_val_1567_);
lean_dec(v_info_1565_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v_value_1571_; lean_object* v___x_1573_; 
v_value_1571_ = lean_ctor_get(v_val_1567_, 1);
lean_inc_ref(v_value_1571_);
lean_dec_ref(v_val_1567_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v_value_1571_);
v___x_1573_ = v___x_1569_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_value_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
case 2:
{
lean_object* v_val_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1585_; 
v_val_1576_ = lean_ctor_get(v_info_1565_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_info_1565_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1578_ = v_info_1565_;
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_val_1576_);
lean_dec(v_info_1565_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1585_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
if (v_allowOpaque_1566_ == 0)
{
lean_object* v___x_1580_; 
lean_del_object(v___x_1578_);
lean_dec_ref(v_val_1576_);
v___x_1580_ = lean_box(0);
return v___x_1580_;
}
else
{
lean_object* v_value_1581_; lean_object* v___x_1583_; 
v_value_1581_ = lean_ctor_get(v_val_1576_, 1);
lean_inc_ref(v_value_1581_);
lean_dec_ref(v_val_1576_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set_tag(v___x_1578_, 1);
lean_ctor_set(v___x_1578_, 0, v_value_1581_);
v___x_1583_ = v___x_1578_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_value_1581_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
}
case 3:
{
lean_object* v_val_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1595_; 
v_val_1586_ = lean_ctor_get(v_info_1565_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_info_1565_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1588_ = v_info_1565_;
v_isShared_1589_ = v_isSharedCheck_1595_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_val_1586_);
lean_dec(v_info_1565_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1595_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
if (v_allowOpaque_1566_ == 0)
{
lean_object* v___x_1590_; 
lean_del_object(v___x_1588_);
lean_dec_ref(v_val_1586_);
v___x_1590_ = lean_box(0);
return v___x_1590_;
}
else
{
lean_object* v_value_1591_; lean_object* v___x_1593_; 
v_value_1591_ = lean_ctor_get(v_val_1586_, 1);
lean_inc_ref(v_value_1591_);
lean_dec_ref(v_val_1586_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set_tag(v___x_1588_, 1);
lean_ctor_set(v___x_1588_, 0, v_value_1591_);
v___x_1593_ = v___x_1588_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_value_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
default: 
{
lean_object* v___x_1596_; 
lean_dec_ref(v_info_1565_);
v___x_1596_ = lean_box(0);
return v___x_1596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f___boxed(lean_object* v_info_1597_, lean_object* v_allowOpaque_1598_){
_start:
{
uint8_t v_allowOpaque_boxed_1599_; lean_object* v_res_1600_; 
v_allowOpaque_boxed_1599_ = lean_unbox(v_allowOpaque_1598_);
v_res_1600_ = l_Lean_ConstantInfo_value_x3f(v_info_1597_, v_allowOpaque_boxed_1599_);
return v_res_1600_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_hasValue(lean_object* v_info_1601_, uint8_t v_allowOpaque_1602_){
_start:
{
switch(lean_obj_tag(v_info_1601_))
{
case 1:
{
uint8_t v___x_1603_; 
v___x_1603_ = 1;
return v___x_1603_;
}
case 2:
{
return v_allowOpaque_1602_;
}
case 3:
{
return v_allowOpaque_1602_;
}
default: 
{
uint8_t v___x_1604_; 
v___x_1604_ = 0;
return v___x_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object* v_info_1605_, lean_object* v_allowOpaque_1606_){
_start:
{
uint8_t v_allowOpaque_boxed_1607_; uint8_t v_res_1608_; lean_object* v_r_1609_; 
v_allowOpaque_boxed_1607_ = lean_unbox(v_allowOpaque_1606_);
v_res_1608_ = l_Lean_ConstantInfo_hasValue(v_info_1605_, v_allowOpaque_boxed_1607_);
lean_dec_ref(v_info_1605_);
v_r_1609_ = lean_box(v_res_1608_);
return v_r_1609_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(lean_object* v_msg_1610_){
_start:
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = l_Lean_instInhabitedExpr;
v___x_1612_ = lean_panic_fn_borrowed(v___x_1611_, v_msg_1610_);
return v___x_1612_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__2(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1615_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1616_ = lean_unsigned_to_nat(62u);
v___x_1617_ = lean_unsigned_to_nat(485u);
v___x_1618_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1619_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1620_ = l_mkPanicMessageWithDecl(v___x_1619_, v___x_1618_, v___x_1617_, v___x_1616_, v___x_1615_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__3(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1621_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1622_ = lean_unsigned_to_nat(62u);
v___x_1623_ = lean_unsigned_to_nat(486u);
v___x_1624_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1625_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1626_ = l_mkPanicMessageWithDecl(v___x_1625_, v___x_1624_, v___x_1623_, v___x_1622_, v___x_1621_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21(lean_object* v_info_1629_, uint8_t v_allowOpaque_1630_){
_start:
{
switch(lean_obj_tag(v_info_1629_))
{
case 1:
{
lean_object* v_val_1631_; lean_object* v_value_1632_; 
v_val_1631_ = lean_ctor_get(v_info_1629_, 0);
v_value_1632_ = lean_ctor_get(v_val_1631_, 1);
lean_inc_ref(v_value_1632_);
return v_value_1632_;
}
case 2:
{
if (v_allowOpaque_1630_ == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__2, &l_Lean_ConstantInfo_value_x21___closed__2_once, _init_l_Lean_ConstantInfo_value_x21___closed__2);
v___x_1634_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1633_);
return v___x_1634_;
}
else
{
lean_object* v_val_1635_; lean_object* v_value_1636_; 
v_val_1635_ = lean_ctor_get(v_info_1629_, 0);
v_value_1636_ = lean_ctor_get(v_val_1635_, 1);
lean_inc_ref(v_value_1636_);
return v_value_1636_;
}
}
case 3:
{
if (v_allowOpaque_1630_ == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1637_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__3, &l_Lean_ConstantInfo_value_x21___closed__3_once, _init_l_Lean_ConstantInfo_value_x21___closed__3);
v___x_1638_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1637_);
return v___x_1638_;
}
else
{
lean_object* v_val_1639_; lean_object* v_value_1640_; 
v_val_1639_ = lean_ctor_get(v_info_1629_, 0);
v_value_1640_ = lean_ctor_get(v_val_1639_, 1);
lean_inc_ref(v_value_1640_);
return v_value_1640_;
}
}
default: 
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1641_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1642_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1643_ = lean_unsigned_to_nat(487u);
v___x_1644_ = lean_unsigned_to_nat(31u);
v___x_1645_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__4));
v___x_1646_ = l_Lean_ConstantInfo_name(v_info_1629_);
v___x_1647_ = 1;
v___x_1648_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1646_, v___x_1647_);
v___x_1649_ = lean_string_append(v___x_1645_, v___x_1648_);
lean_dec_ref(v___x_1648_);
v___x_1650_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__5));
v___x_1651_ = lean_string_append(v___x_1649_, v___x_1650_);
v___x_1652_ = l_mkPanicMessageWithDecl(v___x_1641_, v___x_1642_, v___x_1643_, v___x_1644_, v___x_1651_);
lean_dec_ref(v___x_1651_);
v___x_1653_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1652_);
return v___x_1653_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21___boxed(lean_object* v_info_1654_, lean_object* v_allowOpaque_1655_){
_start:
{
uint8_t v_allowOpaque_boxed_1656_; lean_object* v_res_1657_; 
v_allowOpaque_boxed_1656_ = lean_unbox(v_allowOpaque_1655_);
v_res_1657_ = l_Lean_ConstantInfo_value_x21(v_info_1654_, v_allowOpaque_boxed_1656_);
lean_dec_ref(v_info_1654_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints(lean_object* v_x_1658_){
_start:
{
if (lean_obj_tag(v_x_1658_) == 1)
{
lean_object* v_val_1659_; lean_object* v_hints_1660_; 
v_val_1659_ = lean_ctor_get(v_x_1658_, 0);
v_hints_1660_ = lean_ctor_get(v_val_1659_, 2);
lean_inc(v_hints_1660_);
return v_hints_1660_;
}
else
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_box(0);
return v___x_1661_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object* v_x_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_ConstantInfo_hints(v_x_1662_);
lean_dec_ref(v_x_1662_);
return v_res_1663_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isCtor(lean_object* v_x_1664_){
_start:
{
if (lean_obj_tag(v_x_1664_) == 6)
{
uint8_t v___x_1665_; 
v___x_1665_ = 1;
return v___x_1665_;
}
else
{
uint8_t v___x_1666_; 
v___x_1666_ = 0;
return v___x_1666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isCtor___boxed(lean_object* v_x_1667_){
_start:
{
uint8_t v_res_1668_; lean_object* v_r_1669_; 
v_res_1668_ = l_Lean_ConstantInfo_isCtor(v_x_1667_);
lean_dec_ref(v_x_1667_);
v_r_1669_ = lean_box(v_res_1668_);
return v_r_1669_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isAxiom(lean_object* v_x_1670_){
_start:
{
if (lean_obj_tag(v_x_1670_) == 0)
{
uint8_t v___x_1671_; 
v___x_1671_ = 1;
return v___x_1671_;
}
else
{
uint8_t v___x_1672_; 
v___x_1672_ = 0;
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isAxiom___boxed(lean_object* v_x_1673_){
_start:
{
uint8_t v_res_1674_; lean_object* v_r_1675_; 
v_res_1674_ = l_Lean_ConstantInfo_isAxiom(v_x_1673_);
lean_dec_ref(v_x_1673_);
v_r_1675_ = lean_box(v_res_1674_);
return v_r_1675_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isInductive(lean_object* v_x_1676_){
_start:
{
if (lean_obj_tag(v_x_1676_) == 5)
{
uint8_t v___x_1677_; 
v___x_1677_ = 1;
return v___x_1677_;
}
else
{
uint8_t v___x_1678_; 
v___x_1678_ = 0;
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isInductive___boxed(lean_object* v_x_1679_){
_start:
{
uint8_t v_res_1680_; lean_object* v_r_1681_; 
v_res_1680_ = l_Lean_ConstantInfo_isInductive(v_x_1679_);
lean_dec_ref(v_x_1679_);
v_r_1681_ = lean_box(v_res_1680_);
return v_r_1681_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isDefinition(lean_object* v_x_1682_){
_start:
{
if (lean_obj_tag(v_x_1682_) == 1)
{
uint8_t v___x_1683_; 
v___x_1683_ = 1;
return v___x_1683_;
}
else
{
uint8_t v___x_1684_; 
v___x_1684_ = 0;
return v___x_1684_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isDefinition___boxed(lean_object* v_x_1685_){
_start:
{
uint8_t v_res_1686_; lean_object* v_r_1687_; 
v_res_1686_ = l_Lean_ConstantInfo_isDefinition(v_x_1685_);
lean_dec_ref(v_x_1685_);
v_r_1687_ = lean_box(v_res_1686_);
return v_r_1687_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isTheorem(lean_object* v_x_1688_){
_start:
{
if (lean_obj_tag(v_x_1688_) == 2)
{
uint8_t v___x_1689_; 
v___x_1689_ = 1;
return v___x_1689_;
}
else
{
uint8_t v___x_1690_; 
v___x_1690_ = 0;
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isTheorem___boxed(lean_object* v_x_1691_){
_start:
{
uint8_t v_res_1692_; lean_object* v_r_1693_; 
v_res_1692_ = l_Lean_ConstantInfo_isTheorem(v_x_1691_);
lean_dec_ref(v_x_1691_);
v_r_1693_ = lean_box(v_res_1692_);
return v_r_1693_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(lean_object* v_msg_1694_){
_start:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1695_ = l_Lean_instInhabitedInductiveVal_default;
v___x_1696_ = lean_panic_fn_borrowed(v___x_1695_, v_msg_1694_);
return v___x_1696_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1699_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__1));
v___x_1700_ = lean_unsigned_to_nat(9u);
v___x_1701_ = lean_unsigned_to_nat(515u);
v___x_1702_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__0));
v___x_1703_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1704_ = l_mkPanicMessageWithDecl(v___x_1703_, v___x_1702_, v___x_1701_, v___x_1700_, v___x_1699_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object* v_x_1705_){
_start:
{
if (lean_obj_tag(v_x_1705_) == 5)
{
lean_object* v_val_1706_; 
v_val_1706_ = lean_ctor_get(v_x_1705_, 0);
lean_inc_ref(v_val_1706_);
return v_val_1706_;
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_obj_once(&l_Lean_ConstantInfo_inductiveVal_x21___closed__2, &l_Lean_ConstantInfo_inductiveVal_x21___closed__2_once, _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2);
v___x_1708_ = l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(v___x_1707_);
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21___boxed(lean_object* v_x_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_ConstantInfo_inductiveVal_x21(v_x_1709_);
lean_dec_ref(v_x_1709_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all(lean_object* v_x_1711_){
_start:
{
switch(lean_obj_tag(v_x_1711_))
{
case 5:
{
lean_object* v_val_1712_; lean_object* v_all_1713_; 
v_val_1712_ = lean_ctor_get(v_x_1711_, 0);
v_all_1713_ = lean_ctor_get(v_val_1712_, 3);
lean_inc(v_all_1713_);
return v_all_1713_;
}
case 1:
{
lean_object* v_val_1714_; lean_object* v_all_1715_; 
v_val_1714_ = lean_ctor_get(v_x_1711_, 0);
v_all_1715_ = lean_ctor_get(v_val_1714_, 3);
lean_inc(v_all_1715_);
return v_all_1715_;
}
case 2:
{
lean_object* v_val_1716_; lean_object* v_all_1717_; 
v_val_1716_ = lean_ctor_get(v_x_1711_, 0);
v_all_1717_ = lean_ctor_get(v_val_1716_, 2);
lean_inc(v_all_1717_);
return v_all_1717_;
}
case 3:
{
lean_object* v_val_1718_; lean_object* v_all_1719_; 
v_val_1718_ = lean_ctor_get(v_x_1711_, 0);
v_all_1719_ = lean_ctor_get(v_val_1718_, 2);
lean_inc(v_all_1719_);
return v_all_1719_;
}
default: 
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = l_Lean_ConstantInfo_name(v_x_1711_);
v___x_1721_ = lean_box(0);
v___x_1722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1722_, 0, v___x_1720_);
lean_ctor_set(v___x_1722_, 1, v___x_1721_);
return v___x_1722_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all___boxed(lean_object* v_x_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Lean_ConstantInfo_all(v_x_1723_);
lean_dec_ref(v_x_1723_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecName(lean_object* v_declName_1725_){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0));
v___x_1727_ = l_Lean_Name_str___override(v_declName_1725_, v___x_1726_);
return v___x_1727_;
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
