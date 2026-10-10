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
uint8_t l_Lean_instBEqReducibilityHints_beq(lean_object* v_x_75_, lean_object* v_x_76_){
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
LEAN_EXPORT void l_Lean_instBEqReducibilityHints_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_75_ = stack[0].m_obj;
lean_object* v_x_76_ = stack[1].m_obj;
uint8_t v_res_85_;
v_res_85_ = l_Lean_instBEqReducibilityHints_beq(v_x_75_, v_x_76_);
stack->m_num = v_res_85_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqReducibilityHints_beq___boxed(lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Lean_instBEqReducibilityHints_beq(v_x_86_, v_x_87_);
lean_dec(v_x_87_);
lean_dec(v_x_86_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
uint32_t lean_reducibility_hints_get_height(lean_object* v_h_92_){
_start:
{
if (lean_obj_tag(v_h_92_) == 2)
{
uint32_t v_a_93_; 
v_a_93_ = lean_ctor_get_uint32(v_h_92_, 0);
lean_dec_ref_known(v_h_92_, 0);
return v_a_93_;
}
else
{
uint32_t v___x_94_; 
lean_dec(v_h_92_);
v___x_94_ = 0;
return v___x_94_;
}
}
}
LEAN_EXPORT void lean_reducibility_hints_get_height_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_92_ = stack[0].m_obj;
uint32_t v_res_95_;
v_res_95_ = lean_reducibility_hints_get_height(v_h_92_);
stack->m_num = v_res_95_;
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
uint8_t l_Lean_ReducibilityHints_lt(lean_object* v_x_99_, lean_object* v_x_100_){
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
LEAN_EXPORT void l_Lean_ReducibilityHints_lt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_99_ = stack[0].m_obj;
lean_object* v_x_100_ = stack[1].m_obj;
uint8_t v_res_109_;
v_res_109_ = l_Lean_ReducibilityHints_lt(v_x_99_, v_x_100_);
stack->m_num = v_res_109_;
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_lt___boxed(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
uint8_t v_res_112_; lean_object* v_r_113_; 
v_res_112_ = l_Lean_ReducibilityHints_lt(v_x_110_, v_x_111_);
lean_dec(v_x_111_);
lean_dec(v_x_110_);
v_r_113_ = lean_box(v_res_112_);
return v_r_113_;
}
}
uint8_t l_Lean_ReducibilityHints_compare(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
switch(lean_obj_tag(v_x_114_))
{
case 0:
{
if (lean_obj_tag(v_x_115_) == 0)
{
uint8_t v___x_116_; 
v___x_116_ = 1;
return v___x_116_;
}
else
{
uint8_t v___x_117_; 
v___x_117_ = 2;
return v___x_117_;
}
}
case 1:
{
if (lean_obj_tag(v_x_115_) == 1)
{
uint8_t v___x_118_; 
v___x_118_ = 1;
return v___x_118_;
}
else
{
uint8_t v___x_119_; 
v___x_119_ = 0;
return v___x_119_;
}
}
default: 
{
switch(lean_obj_tag(v_x_115_))
{
case 0:
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
case 1:
{
uint8_t v___x_121_; 
v___x_121_ = 2;
return v___x_121_;
}
default: 
{
uint32_t v_a_122_; uint32_t v_a_123_; uint8_t v___x_124_; 
v_a_122_ = lean_ctor_get_uint32(v_x_114_, 0);
v_a_123_ = lean_ctor_get_uint32(v_x_115_, 0);
v___x_124_ = lean_uint32_dec_lt(v_a_123_, v_a_122_);
if (v___x_124_ == 0)
{
uint8_t v___x_125_; 
v___x_125_ = lean_uint32_dec_eq(v_a_123_, v_a_122_);
if (v___x_125_ == 0)
{
uint8_t v___x_126_; 
v___x_126_ = 2;
return v___x_126_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = 1;
return v___x_127_;
}
}
else
{
uint8_t v___x_128_; 
v___x_128_ = 0;
return v___x_128_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_ReducibilityHints_compare_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_114_ = stack[0].m_obj;
lean_object* v_x_115_ = stack[1].m_obj;
uint8_t v_res_129_;
v_res_129_ = l_Lean_ReducibilityHints_compare(v_x_114_, v_x_115_);
stack->m_num = v_res_129_;
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_compare___boxed(lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
uint8_t v_res_132_; lean_object* v_r_133_; 
v_res_132_ = l_Lean_ReducibilityHints_compare(v_x_130_, v_x_131_);
lean_dec(v_x_131_);
lean_dec(v_x_130_);
v_r_133_ = lean_box(v_res_132_);
return v_r_133_;
}
}
uint8_t l_Lean_ReducibilityHints_isAbbrev(lean_object* v_x_136_){
_start:
{
if (lean_obj_tag(v_x_136_) == 1)
{
uint8_t v___x_137_; 
v___x_137_ = 1;
return v___x_137_;
}
else
{
uint8_t v___x_138_; 
v___x_138_ = 0;
return v___x_138_;
}
}
}
LEAN_EXPORT void l_Lean_ReducibilityHints_isAbbrev_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_136_ = stack[0].m_obj;
uint8_t v_res_139_;
v_res_139_ = l_Lean_ReducibilityHints_isAbbrev(v_x_136_);
stack->m_num = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_isAbbrev___boxed(lean_object* v_x_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = l_Lean_ReducibilityHints_isAbbrev(v_x_140_);
lean_dec(v_x_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
uint8_t l_Lean_ReducibilityHints_isRegular(lean_object* v_x_143_){
_start:
{
if (lean_obj_tag(v_x_143_) == 2)
{
uint8_t v___x_144_; 
v___x_144_ = 1;
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
}
LEAN_EXPORT void l_Lean_ReducibilityHints_isRegular_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_143_ = stack[0].m_obj;
uint8_t v_res_146_;
v_res_146_ = l_Lean_ReducibilityHints_isRegular(v_x_143_);
stack->m_num = v_res_146_;
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_isRegular___boxed(lean_object* v_x_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Lean_ReducibilityHints_isRegular(v_x_147_);
lean_dec(v_x_147_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal_default___closed__2(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = lean_box(0);
v___x_154_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_155_ = l_Lean_Expr_const___override(v___x_154_, v___x_153_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal_default___closed__3(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__2, &l_Lean_instInhabitedConstantVal_default___closed__2_once, _init_l_Lean_instInhabitedConstantVal_default___closed__2);
v___x_157_ = lean_box(0);
v___x_158_ = lean_box(0);
v___x_159_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_156_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal_default(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Lean_instInhabitedConstantVal_default___closed__3, &l_Lean_instInhabitedConstantVal_default___closed__3_once, _init_l_Lean_instInhabitedConstantVal_default___closed__3);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantVal(void){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_instInhabitedConstantVal_default;
return v___x_161_;
}
}
uint8_t l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(lean_object* v_x_162_, lean_object* v_x_163_){
_start:
{
if (lean_obj_tag(v_x_162_) == 0)
{
if (lean_obj_tag(v_x_163_) == 0)
{
uint8_t v___x_164_; 
v___x_164_ = 1;
return v___x_164_;
}
else
{
uint8_t v___x_165_; 
v___x_165_ = 0;
return v___x_165_;
}
}
else
{
if (lean_obj_tag(v_x_163_) == 0)
{
uint8_t v___x_166_; 
v___x_166_ = 0;
return v___x_166_;
}
else
{
lean_object* v_head_167_; lean_object* v_tail_168_; lean_object* v_head_169_; lean_object* v_tail_170_; uint8_t v___x_171_; 
v_head_167_ = lean_ctor_get(v_x_162_, 0);
v_tail_168_ = lean_ctor_get(v_x_162_, 1);
v_head_169_ = lean_ctor_get(v_x_163_, 0);
v_tail_170_ = lean_ctor_get(v_x_163_, 1);
v___x_171_ = lean_name_eq(v_head_167_, v_head_169_);
if (v___x_171_ == 0)
{
return v___x_171_;
}
else
{
v_x_162_ = v_tail_168_;
v_x_163_ = v_tail_170_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_162_ = stack[0].m_obj;
lean_object* v_x_163_ = stack[1].m_obj;
uint8_t v_res_173_;
v_res_173_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_x_162_, v_x_163_);
stack->m_num = v_res_173_;
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
uint8_t l_Lean_instBEqConstantVal_beq(lean_object* v_x_178_, lean_object* v_x_179_){
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
LEAN_EXPORT void l_Lean_instBEqConstantVal_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_178_ = stack[0].m_obj;
lean_object* v_x_179_ = stack[1].m_obj;
uint8_t v_res_189_;
v_res_189_ = l_Lean_instBEqConstantVal_beq(v_x_178_, v_x_179_);
stack->m_num = v_res_189_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstantVal_beq___boxed(lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = l_Lean_instBEqConstantVal_beq(v_x_190_, v_x_191_);
lean_dec_ref(v_x_191_);
lean_dec_ref(v_x_190_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
static lean_object* _init_l_Lean_instInhabitedAxiomVal_default___closed__0(void){
_start:
{
uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = 0;
v___x_197_ = l_Lean_instInhabitedConstantVal_default;
v___x_198_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set_uint8(v___x_198_, sizeof(void*)*1, v___x_196_);
return v___x_198_;
}
}
static lean_object* _init_l_Lean_instInhabitedAxiomVal_default(void){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_obj_once(&l_Lean_instInhabitedAxiomVal_default___closed__0, &l_Lean_instInhabitedAxiomVal_default___closed__0_once, _init_l_Lean_instInhabitedAxiomVal_default___closed__0);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_instInhabitedAxiomVal(void){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_instInhabitedAxiomVal_default;
return v___x_200_;
}
}
uint8_t l_Lean_instBEqAxiomVal_beq(lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
lean_object* v_toConstantVal_203_; uint8_t v_isUnsafe_204_; lean_object* v_toConstantVal_205_; uint8_t v_isUnsafe_206_; uint8_t v___x_207_; 
v_toConstantVal_203_ = lean_ctor_get(v_x_201_, 0);
v_isUnsafe_204_ = lean_ctor_get_uint8(v_x_201_, sizeof(void*)*1);
v_toConstantVal_205_ = lean_ctor_get(v_x_202_, 0);
v_isUnsafe_206_ = lean_ctor_get_uint8(v_x_202_, sizeof(void*)*1);
v___x_207_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_203_, v_toConstantVal_205_);
if (v___x_207_ == 0)
{
return v___x_207_;
}
else
{
if (v_isUnsafe_206_ == 0)
{
if (v_isUnsafe_204_ == 0)
{
return v___x_207_;
}
else
{
return v_isUnsafe_206_;
}
}
else
{
return v_isUnsafe_204_;
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqAxiomVal_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_201_ = stack[0].m_obj;
lean_object* v_x_202_ = stack[1].m_obj;
uint8_t v_res_208_;
v_res_208_ = l_Lean_instBEqAxiomVal_beq(v_x_201_, v_x_202_);
stack->m_num = v_res_208_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqAxiomVal_beq___boxed(lean_object* v_x_209_, lean_object* v_x_210_){
_start:
{
uint8_t v_res_211_; lean_object* v_r_212_; 
v_res_211_ = l_Lean_instBEqAxiomVal_beq(v_x_209_, v_x_210_);
lean_dec_ref(v_x_210_);
lean_dec_ref(v_x_209_);
v_r_212_ = lean_box(v_res_211_);
return v_r_212_;
}
}
uint8_t lean_axiom_val_is_unsafe(lean_object* v_v_215_){
_start:
{
uint8_t v_isUnsafe_216_; 
v_isUnsafe_216_ = lean_ctor_get_uint8(v_v_215_, sizeof(void*)*1);
lean_dec_ref(v_v_215_);
return v_isUnsafe_216_;
}
}
LEAN_EXPORT void lean_axiom_val_is_unsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_215_ = stack[0].m_obj;
uint8_t v_res_217_;
v_res_217_ = lean_axiom_val_is_unsafe(v_v_215_);
stack->m_num = v_res_217_;
}
LEAN_EXPORT lean_object* l_Lean_AxiomVal_isUnsafeEx___boxed(lean_object* v_v_218_){
_start:
{
uint8_t v_res_219_; lean_object* v_r_220_; 
v_res_219_ = lean_axiom_val_is_unsafe(v_v_218_);
v_r_220_ = lean_box(v_res_219_);
return v_r_220_;
}
}
lean_object* l_Lean_DefinitionSafety_ctorIdx___impl(uint8_t v_x_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_box(v_x_221_);
v___x_223_ = lean_obj_tag_nat(v___x_222_);
lean_dec(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT void l_Lean_DefinitionSafety_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_221_ = stack[0].m_num;
lean_object* v_res_224_;
v_res_224_ = l_Lean_DefinitionSafety_ctorIdx___impl(v_x_221_);
stack->m_obj
 = v_res_224_;
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorIdx___impl___boxed(lean_object* v_x_225_){
_start:
{
uint8_t v_x_4__boxed_226_; lean_object* v_res_227_; 
v_x_4__boxed_226_ = lean_unbox(v_x_225_);
v_res_227_ = l_Lean_DefinitionSafety_ctorIdx___impl(v_x_4__boxed_226_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg(lean_object* v_k_228_){
_start:
{
lean_inc(v_k_228_);
return v_k_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg___boxed(lean_object* v_k_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_DefinitionSafety_ctorElim___redArg(v_k_229_);
lean_dec(v_k_229_);
return v_res_230_;
}
}
lean_object* l_Lean_DefinitionSafety_ctorElim(lean_object* v_motive_231_, lean_object* v_ctorIdx_232_, uint8_t v_t_233_, lean_object* v_h_234_, lean_object* v_k_235_){
_start:
{
lean_inc(v_k_235_);
return v_k_235_;
}
}
LEAN_EXPORT void l_Lean_DefinitionSafety_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_232_ = stack[1].m_obj;
uint8_t v_t_233_ = stack[2].m_num;
lean_object* v_k_235_ = stack[4].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Lean_DefinitionSafety_ctorElim(lean_box(0), v_ctorIdx_232_, v_t_233_, lean_box(0), v_k_235_);
stack->m_obj
 = v_res_236_;
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
lean_object* l_Lean_DefinitionSafety_unsafe_elim(lean_object* v_motive_247_, uint8_t v_t_248_, lean_object* v_h_249_, lean_object* v_unsafe_250_){
_start:
{
lean_inc(v_unsafe_250_);
return v_unsafe_250_;
}
}
LEAN_EXPORT void l_Lean_DefinitionSafety_unsafe_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_248_ = stack[1].m_num;
lean_object* v_unsafe_250_ = stack[3].m_obj;
lean_object* v_res_251_;
v_res_251_ = l_Lean_DefinitionSafety_unsafe_elim(lean_box(0), v_t_248_, lean_box(0), v_unsafe_250_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___boxed(lean_object* v_motive_252_, lean_object* v_t_253_, lean_object* v_h_254_, lean_object* v_unsafe_255_){
_start:
{
uint8_t v_t_boxed_256_; lean_object* v_res_257_; 
v_t_boxed_256_ = lean_unbox(v_t_253_);
v_res_257_ = l_Lean_DefinitionSafety_unsafe_elim(v_motive_252_, v_t_boxed_256_, v_h_254_, v_unsafe_255_);
lean_dec(v_unsafe_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg(lean_object* v_safe_258_){
_start:
{
lean_inc(v_safe_258_);
return v_safe_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg___boxed(lean_object* v_safe_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_DefinitionSafety_safe_elim___redArg(v_safe_259_);
lean_dec(v_safe_259_);
return v_res_260_;
}
}
lean_object* l_Lean_DefinitionSafety_safe_elim(lean_object* v_motive_261_, uint8_t v_t_262_, lean_object* v_h_263_, lean_object* v_safe_264_){
_start:
{
lean_inc(v_safe_264_);
return v_safe_264_;
}
}
LEAN_EXPORT void l_Lean_DefinitionSafety_safe_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_262_ = stack[1].m_num;
lean_object* v_safe_264_ = stack[3].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_DefinitionSafety_safe_elim(lean_box(0), v_t_262_, lean_box(0), v_safe_264_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___boxed(lean_object* v_motive_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_safe_269_){
_start:
{
uint8_t v_t_boxed_270_; lean_object* v_res_271_; 
v_t_boxed_270_ = lean_unbox(v_t_267_);
v_res_271_ = l_Lean_DefinitionSafety_safe_elim(v_motive_266_, v_t_boxed_270_, v_h_268_, v_safe_269_);
lean_dec(v_safe_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg(lean_object* v_partial_272_){
_start:
{
lean_inc(v_partial_272_);
return v_partial_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg___boxed(lean_object* v_partial_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_DefinitionSafety_partial_elim___redArg(v_partial_273_);
lean_dec(v_partial_273_);
return v_res_274_;
}
}
lean_object* l_Lean_DefinitionSafety_partial_elim(lean_object* v_motive_275_, uint8_t v_t_276_, lean_object* v_h_277_, lean_object* v_partial_278_){
_start:
{
lean_inc(v_partial_278_);
return v_partial_278_;
}
}
LEAN_EXPORT void l_Lean_DefinitionSafety_partial_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_276_ = stack[1].m_num;
lean_object* v_partial_278_ = stack[3].m_obj;
lean_object* v_res_279_;
v_res_279_ = l_Lean_DefinitionSafety_partial_elim(lean_box(0), v_t_276_, lean_box(0), v_partial_278_);
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___boxed(lean_object* v_motive_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_partial_283_){
_start:
{
uint8_t v_t_boxed_284_; lean_object* v_res_285_; 
v_t_boxed_284_ = lean_unbox(v_t_281_);
v_res_285_ = l_Lean_DefinitionSafety_partial_elim(v_motive_280_, v_t_boxed_284_, v_h_282_, v_partial_283_);
lean_dec(v_partial_283_);
return v_res_285_;
}
}
static uint8_t _init_l_Lean_instInhabitedDefinitionSafety_default(void){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = 0;
return v___x_286_;
}
}
static uint8_t _init_l_Lean_instInhabitedDefinitionSafety(void){
_start:
{
uint8_t v___x_287_; 
v___x_287_ = 0;
return v___x_287_;
}
}
uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t v_x_288_, uint8_t v_y_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_290_ = lean_box(v_x_288_);
v___x_291_ = lean_obj_tag_nat(v___x_290_);
lean_dec(v___x_290_);
v___x_292_ = lean_box(v_y_289_);
v___x_293_ = lean_obj_tag_nat(v___x_292_);
lean_dec(v___x_292_);
v___x_294_ = lean_nat_dec_eq(v___x_291_, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT void l_Lean_instBEqDefinitionSafety_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_288_ = stack[0].m_num;
uint8_t v_y_289_ = stack[1].m_num;
uint8_t v_res_295_;
v_res_295_ = l_Lean_instBEqDefinitionSafety_beq(v_x_288_, v_y_289_);
stack->m_num = v_res_295_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionSafety_beq___boxed(lean_object* v_x_296_, lean_object* v_y_297_){
_start:
{
uint8_t v_x_24__boxed_298_; uint8_t v_y_25__boxed_299_; uint8_t v_res_300_; lean_object* v_r_301_; 
v_x_24__boxed_298_ = lean_unbox(v_x_296_);
v_y_25__boxed_299_ = lean_unbox(v_y_297_);
v_res_300_ = l_Lean_instBEqDefinitionSafety_beq(v_x_24__boxed_298_, v_y_25__boxed_299_);
v_r_301_ = lean_box(v_res_300_);
return v_r_301_;
}
}
static lean_object* _init_l_Lean_instReprDefinitionSafety_repr___closed__6(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_unsigned_to_nat(2u);
v___x_314_ = lean_nat_to_int(v___x_313_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_instReprDefinitionSafety_repr___closed__7(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_unsigned_to_nat(1u);
v___x_316_ = lean_nat_to_int(v___x_315_);
return v___x_316_;
}
}
lean_object* l_Lean_instReprDefinitionSafety_repr(uint8_t v_x_317_, lean_object* v_prec_318_){
_start:
{
lean_object* v___y_320_; lean_object* v___y_327_; lean_object* v___y_334_; 
switch(v_x_317_)
{
case 0:
{
lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_340_ = lean_unsigned_to_nat(1024u);
v___x_341_ = lean_nat_dec_le(v___x_340_, v_prec_318_);
if (v___x_341_ == 0)
{
lean_object* v___x_342_; 
v___x_342_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_320_ = v___x_342_;
goto v___jp_319_;
}
else
{
lean_object* v___x_343_; 
v___x_343_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_320_ = v___x_343_;
goto v___jp_319_;
}
}
case 1:
{
lean_object* v___x_344_; uint8_t v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(1024u);
v___x_345_ = lean_nat_dec_le(v___x_344_, v_prec_318_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
v___x_346_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_327_ = v___x_346_;
goto v___jp_326_;
}
else
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_327_ = v___x_347_;
goto v___jp_326_;
}
}
default: 
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_unsigned_to_nat(1024u);
v___x_349_ = lean_nat_dec_le(v___x_348_, v_prec_318_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; 
v___x_350_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_334_ = v___x_350_;
goto v___jp_333_;
}
else
{
lean_object* v___x_351_; 
v___x_351_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_334_ = v___x_351_;
goto v___jp_333_;
}
}
}
v___jp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_321_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__1));
lean_inc(v___y_320_);
v___x_322_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_322_, 0, v___y_320_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
v___x_323_ = 0;
v___x_324_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_324_, 0, v___x_322_);
lean_ctor_set_uint8(v___x_324_, sizeof(void*)*1, v___x_323_);
v___x_325_ = l_Repr_addAppParen(v___x_324_, v_prec_318_);
return v___x_325_;
}
v___jp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_328_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__3));
lean_inc(v___y_327_);
v___x_329_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_329_, 0, v___y_327_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
v___x_330_ = 0;
v___x_331_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*1, v___x_330_);
v___x_332_ = l_Repr_addAppParen(v___x_331_, v_prec_318_);
return v___x_332_;
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_335_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__5));
lean_inc(v___y_334_);
v___x_336_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_336_, 0, v___y_334_);
lean_ctor_set(v___x_336_, 1, v___x_335_);
v___x_337_ = 0;
v___x_338_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_338_, 0, v___x_336_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*1, v___x_337_);
v___x_339_ = l_Repr_addAppParen(v___x_338_, v_prec_318_);
return v___x_339_;
}
}
}
LEAN_EXPORT void l_Lean_instReprDefinitionSafety_repr_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_317_ = stack[0].m_num;
lean_object* v_prec_318_ = stack[1].m_obj;
lean_object* v_res_352_;
v_res_352_ = l_Lean_instReprDefinitionSafety_repr(v_x_317_, v_prec_318_);
stack->m_obj
 = v_res_352_;
}
LEAN_EXPORT lean_object* l_Lean_instReprDefinitionSafety_repr___boxed(lean_object* v_x_353_, lean_object* v_prec_354_){
_start:
{
uint8_t v_x_171__boxed_355_; lean_object* v_res_356_; 
v_x_171__boxed_355_ = lean_unbox(v_x_353_);
v_res_356_ = l_Lean_instReprDefinitionSafety_repr(v_x_171__boxed_355_, v_prec_354_);
lean_dec(v_prec_354_);
return v_res_356_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default___closed__0(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_359_ = lean_box(0);
v___x_360_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_361_ = l_Lean_Expr_const___override(v___x_360_, v___x_359_);
return v___x_361_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default___closed__2(void){
_start:
{
lean_object* v___x_365_; uint8_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_365_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_366_ = 0;
v___x_367_ = lean_box(0);
v___x_368_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_369_ = l_Lean_instInhabitedConstantVal_default;
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
v___x_371_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__2, &l_Lean_instInhabitedDefinitionVal_default___closed__2_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__2);
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
uint8_t l_Lean_instBEqDefinitionVal_beq(lean_object* v_x_373_, lean_object* v_x_374_){
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
LEAN_EXPORT void l_Lean_instBEqDefinitionVal_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_373_ = stack[0].m_obj;
lean_object* v_x_374_ = stack[1].m_obj;
uint8_t v_res_390_;
v_res_390_ = l_Lean_instBEqDefinitionVal_beq(v_x_373_, v_x_374_);
stack->m_num = v_res_390_;
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
lean_object* lean_mk_definition_val(lean_object* v_name_397_, lean_object* v_levelParams_398_, lean_object* v_type_399_, lean_object* v_value_400_, lean_object* v_hints_401_, uint8_t v_safety_402_, lean_object* v_all_403_){
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
LEAN_EXPORT void lean_mk_definition_val_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_397_ = stack[0].m_obj;
lean_object* v_levelParams_398_ = stack[1].m_obj;
lean_object* v_type_399_ = stack[2].m_obj;
lean_object* v_value_400_ = stack[3].m_obj;
lean_object* v_hints_401_ = stack[4].m_obj;
uint8_t v_safety_402_ = stack[5].m_num;
lean_object* v_all_403_ = stack[6].m_obj;
lean_object* v_res_406_;
v_res_406_ = lean_mk_definition_val(v_name_397_, v_levelParams_398_, v_type_399_, v_value_400_, v_hints_401_, v_safety_402_, v_all_403_);
stack->m_obj
 = v_res_406_;
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValEx___boxed(lean_object* v_name_407_, lean_object* v_levelParams_408_, lean_object* v_type_409_, lean_object* v_value_410_, lean_object* v_hints_411_, lean_object* v_safety_412_, lean_object* v_all_413_){
_start:
{
uint8_t v_safety_boxed_414_; lean_object* v_res_415_; 
v_safety_boxed_414_ = lean_unbox(v_safety_412_);
v_res_415_ = lean_mk_definition_val(v_name_407_, v_levelParams_408_, v_type_409_, v_value_410_, v_hints_411_, v_safety_boxed_414_, v_all_413_);
return v_res_415_;
}
}
uint8_t lean_definition_val_get_safety(lean_object* v_v_416_){
_start:
{
uint8_t v_safety_417_; 
v_safety_417_ = lean_ctor_get_uint8(v_v_416_, sizeof(void*)*4);
lean_dec_ref(v_v_416_);
return v_safety_417_;
}
}
LEAN_EXPORT void lean_definition_val_get_safety_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_416_ = stack[0].m_obj;
uint8_t v_res_418_;
v_res_418_ = lean_definition_val_get_safety(v_v_416_);
stack->m_num = v_res_418_;
}
LEAN_EXPORT lean_object* l_Lean_DefinitionVal_getSafetyEx___boxed(lean_object* v_v_419_){
_start:
{
uint8_t v_res_420_; lean_object* v_r_421_; 
v_res_420_ = lean_definition_val_get_safety(v_v_419_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default___closed__0(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_422_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_423_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_424_ = l_Lean_instInhabitedConstantVal_default;
v___x_425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
lean_ctor_set(v___x_425_, 2, v___x_422_);
return v___x_425_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default(void){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = lean_obj_once(&l_Lean_instInhabitedTheoremVal_default___closed__0, &l_Lean_instInhabitedTheoremVal_default___closed__0_once, _init_l_Lean_instInhabitedTheoremVal_default___closed__0);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal(void){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_instInhabitedTheoremVal_default;
return v___x_427_;
}
}
uint8_t l_Lean_instBEqTheoremVal_beq(lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
lean_object* v_toConstantVal_430_; lean_object* v_value_431_; lean_object* v_all_432_; lean_object* v_toConstantVal_433_; lean_object* v_value_434_; lean_object* v_all_435_; uint8_t v___x_436_; 
v_toConstantVal_430_ = lean_ctor_get(v_x_428_, 0);
v_value_431_ = lean_ctor_get(v_x_428_, 1);
v_all_432_ = lean_ctor_get(v_x_428_, 2);
v_toConstantVal_433_ = lean_ctor_get(v_x_429_, 0);
v_value_434_ = lean_ctor_get(v_x_429_, 1);
v_all_435_ = lean_ctor_get(v_x_429_, 2);
v___x_436_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_430_, v_toConstantVal_433_);
if (v___x_436_ == 0)
{
return v___x_436_;
}
else
{
uint8_t v___x_437_; 
v___x_437_ = lean_expr_eqv(v_value_431_, v_value_434_);
if (v___x_437_ == 0)
{
return v___x_437_;
}
else
{
uint8_t v___x_438_; 
v___x_438_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_432_, v_all_435_);
return v___x_438_;
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqTheoremVal_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_428_ = stack[0].m_obj;
lean_object* v_x_429_ = stack[1].m_obj;
uint8_t v_res_439_;
v_res_439_ = l_Lean_instBEqTheoremVal_beq(v_x_428_, v_x_429_);
stack->m_num = v_res_439_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqTheoremVal_beq___boxed(lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
uint8_t v_res_442_; lean_object* v_r_443_; 
v_res_442_ = l_Lean_instBEqTheoremVal_beq(v_x_440_, v_x_441_);
lean_dec_ref(v_x_441_);
lean_dec_ref(v_x_440_);
v_r_443_ = lean_box(v_res_442_);
return v_r_443_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default___closed__0(void){
_start:
{
lean_object* v___x_446_; uint8_t v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_446_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_447_ = 0;
v___x_448_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_449_ = l_Lean_instInhabitedConstantVal_default;
v___x_450_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v___x_448_);
lean_ctor_set(v___x_450_, 2, v___x_446_);
lean_ctor_set_uint8(v___x_450_, sizeof(void*)*3, v___x_447_);
return v___x_450_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default(void){
_start:
{
lean_object* v___x_451_; 
v___x_451_ = lean_obj_once(&l_Lean_instInhabitedOpaqueVal_default___closed__0, &l_Lean_instInhabitedOpaqueVal_default___closed__0_once, _init_l_Lean_instInhabitedOpaqueVal_default___closed__0);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal(void){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Lean_instInhabitedOpaqueVal_default;
return v___x_452_;
}
}
uint8_t l_Lean_instBEqOpaqueVal_beq(lean_object* v_x_453_, lean_object* v_x_454_){
_start:
{
lean_object* v_toConstantVal_455_; lean_object* v_value_456_; uint8_t v_isUnsafe_457_; lean_object* v_all_458_; lean_object* v_toConstantVal_459_; lean_object* v_value_460_; uint8_t v_isUnsafe_461_; lean_object* v_all_462_; uint8_t v___y_464_; uint8_t v___x_466_; 
v_toConstantVal_455_ = lean_ctor_get(v_x_453_, 0);
v_value_456_ = lean_ctor_get(v_x_453_, 1);
v_isUnsafe_457_ = lean_ctor_get_uint8(v_x_453_, sizeof(void*)*3);
v_all_458_ = lean_ctor_get(v_x_453_, 2);
v_toConstantVal_459_ = lean_ctor_get(v_x_454_, 0);
v_value_460_ = lean_ctor_get(v_x_454_, 1);
v_isUnsafe_461_ = lean_ctor_get_uint8(v_x_454_, sizeof(void*)*3);
v_all_462_ = lean_ctor_get(v_x_454_, 2);
v___x_466_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_455_, v_toConstantVal_459_);
if (v___x_466_ == 0)
{
return v___x_466_;
}
else
{
uint8_t v___x_467_; 
v___x_467_ = lean_expr_eqv(v_value_456_, v_value_460_);
if (v___x_467_ == 0)
{
return v___x_467_;
}
else
{
if (v_isUnsafe_461_ == 0)
{
if (v_isUnsafe_457_ == 0)
{
v___y_464_ = v___x_467_;
goto v___jp_463_;
}
else
{
return v_isUnsafe_461_;
}
}
else
{
v___y_464_ = v_isUnsafe_457_;
goto v___jp_463_;
}
}
}
v___jp_463_:
{
if (v___y_464_ == 0)
{
return v___y_464_;
}
else
{
uint8_t v___x_465_; 
v___x_465_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_458_, v_all_462_);
return v___x_465_;
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqOpaqueVal_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_453_ = stack[0].m_obj;
lean_object* v_x_454_ = stack[1].m_obj;
uint8_t v_res_468_;
v_res_468_ = l_Lean_instBEqOpaqueVal_beq(v_x_453_, v_x_454_);
stack->m_num = v_res_468_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqOpaqueVal_beq___boxed(lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
uint8_t v_res_471_; lean_object* v_r_472_; 
v_res_471_ = l_Lean_instBEqOpaqueVal_beq(v_x_469_, v_x_470_);
lean_dec_ref(v_x_470_);
lean_dec_ref(v_x_469_);
v_r_472_ = lean_box(v_res_471_);
return v_r_472_;
}
}
uint8_t lean_opaque_val_is_unsafe(lean_object* v_v_475_){
_start:
{
uint8_t v_isUnsafe_476_; 
v_isUnsafe_476_ = lean_ctor_get_uint8(v_v_475_, sizeof(void*)*3);
lean_dec_ref(v_v_475_);
return v_isUnsafe_476_;
}
}
LEAN_EXPORT void lean_opaque_val_is_unsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_475_ = stack[0].m_obj;
uint8_t v_res_477_;
v_res_477_ = lean_opaque_val_is_unsafe(v_v_475_);
stack->m_num = v_res_477_;
}
LEAN_EXPORT lean_object* l_Lean_OpaqueVal_isUnsafeEx___boxed(lean_object* v_v_478_){
_start:
{
uint8_t v_res_479_; lean_object* v_r_480_; 
v_res_479_ = lean_opaque_val_is_unsafe(v_v_478_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__0(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_box(0);
v___x_482_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_483_ = l_Lean_Expr_const___override(v___x_482_, v___x_481_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__1(void){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_484_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_485_ = lean_box(0);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default(void){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__1, &l_Lean_instInhabitedConstructor_default___closed__1_once, _init_l_Lean_instInhabitedConstructor_default___closed__1);
return v___x_487_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor(void){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Lean_instInhabitedConstructor_default;
return v___x_488_;
}
}
uint8_t l_Lean_instBEqConstructor_beq(lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
lean_object* v_name_491_; lean_object* v_type_492_; lean_object* v_name_493_; lean_object* v_type_494_; uint8_t v___x_495_; 
v_name_491_ = lean_ctor_get(v_x_489_, 0);
v_type_492_ = lean_ctor_get(v_x_489_, 1);
v_name_493_ = lean_ctor_get(v_x_490_, 0);
v_type_494_ = lean_ctor_get(v_x_490_, 1);
v___x_495_ = lean_name_eq(v_name_491_, v_name_493_);
if (v___x_495_ == 0)
{
return v___x_495_;
}
else
{
uint8_t v___x_496_; 
v___x_496_ = lean_expr_eqv(v_type_492_, v_type_494_);
return v___x_496_;
}
}
}
LEAN_EXPORT void l_Lean_instBEqConstructor_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_489_ = stack[0].m_obj;
lean_object* v_x_490_ = stack[1].m_obj;
uint8_t v_res_497_;
v_res_497_ = l_Lean_instBEqConstructor_beq(v_x_489_, v_x_490_);
stack->m_num = v_res_497_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructor_beq___boxed(lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
uint8_t v_res_500_; lean_object* v_r_501_; 
v_res_500_ = l_Lean_instBEqConstructor_beq(v_x_498_, v_x_499_);
lean_dec_ref(v_x_499_);
lean_dec_ref(v_x_498_);
v_r_501_ = lean_box(v_res_500_);
return v_r_501_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default___closed__0(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_504_ = lean_box(0);
v___x_505_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_506_ = lean_box(0);
v___x_507_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___x_505_);
lean_ctor_set(v___x_507_, 2, v___x_504_);
return v___x_507_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default(void){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = lean_obj_once(&l_Lean_instInhabitedInductiveType_default___closed__0, &l_Lean_instInhabitedInductiveType_default___closed__0_once, _init_l_Lean_instInhabitedInductiveType_default___closed__0);
return v___x_508_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType(void){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_instInhabitedInductiveType_default;
return v___x_509_;
}
}
uint8_t l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
if (lean_obj_tag(v_x_511_) == 0)
{
uint8_t v___x_512_; 
v___x_512_ = 1;
return v___x_512_;
}
else
{
uint8_t v___x_513_; 
v___x_513_ = 0;
return v___x_513_;
}
}
else
{
if (lean_obj_tag(v_x_511_) == 0)
{
uint8_t v___x_514_; 
v___x_514_ = 0;
return v___x_514_;
}
else
{
lean_object* v_head_515_; lean_object* v_tail_516_; lean_object* v_head_517_; lean_object* v_tail_518_; uint8_t v___x_519_; 
v_head_515_ = lean_ctor_get(v_x_510_, 0);
v_tail_516_ = lean_ctor_get(v_x_510_, 1);
v_head_517_ = lean_ctor_get(v_x_511_, 0);
v_tail_518_ = lean_ctor_get(v_x_511_, 1);
v___x_519_ = l_Lean_instBEqConstructor_beq(v_head_515_, v_head_517_);
if (v___x_519_ == 0)
{
return v___x_519_;
}
else
{
v_x_510_ = v_tail_516_;
v_x_511_ = v_tail_518_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_510_ = stack[0].m_obj;
lean_object* v_x_511_ = stack[1].m_obj;
uint8_t v_res_521_;
v_res_521_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_x_510_, v_x_511_);
stack->m_num = v_res_521_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0___boxed(lean_object* v_x_522_, lean_object* v_x_523_){
_start:
{
uint8_t v_res_524_; lean_object* v_r_525_; 
v_res_524_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_x_522_, v_x_523_);
lean_dec(v_x_523_);
lean_dec(v_x_522_);
v_r_525_ = lean_box(v_res_524_);
return v_r_525_;
}
}
uint8_t l_Lean_instBEqInductiveType_beq(lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
lean_object* v_name_528_; lean_object* v_type_529_; lean_object* v_ctors_530_; lean_object* v_name_531_; lean_object* v_type_532_; lean_object* v_ctors_533_; uint8_t v___x_534_; 
v_name_528_ = lean_ctor_get(v_x_526_, 0);
v_type_529_ = lean_ctor_get(v_x_526_, 1);
v_ctors_530_ = lean_ctor_get(v_x_526_, 2);
v_name_531_ = lean_ctor_get(v_x_527_, 0);
v_type_532_ = lean_ctor_get(v_x_527_, 1);
v_ctors_533_ = lean_ctor_get(v_x_527_, 2);
v___x_534_ = lean_name_eq(v_name_528_, v_name_531_);
if (v___x_534_ == 0)
{
return v___x_534_;
}
else
{
uint8_t v___x_535_; 
v___x_535_ = lean_expr_eqv(v_type_529_, v_type_532_);
if (v___x_535_ == 0)
{
return v___x_535_;
}
else
{
uint8_t v___x_536_; 
v___x_536_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_ctors_530_, v_ctors_533_);
return v___x_536_;
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqInductiveType_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_526_ = stack[0].m_obj;
lean_object* v_x_527_ = stack[1].m_obj;
uint8_t v_res_537_;
v_res_537_ = l_Lean_instBEqInductiveType_beq(v_x_526_, v_x_527_);
stack->m_num = v_res_537_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveType_beq___boxed(lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
uint8_t v_res_540_; lean_object* v_r_541_; 
v_res_540_ = l_Lean_instBEqInductiveType_beq(v_x_538_, v_x_539_);
lean_dec_ref(v_x_539_);
lean_dec_ref(v_x_538_);
v_r_541_ = lean_box(v_res_540_);
return v_r_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___impl(lean_object* v_x_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = lean_obj_tag_nat(v_x_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___impl___boxed(lean_object* v_x_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Declaration_ctorIdx___impl(v_x_546_);
lean_dec(v_x_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___redArg(lean_object* v_t_548_, lean_object* v_k_549_){
_start:
{
switch(lean_obj_tag(v_t_548_))
{
case 4:
{
return v_k_549_;
}
case 5:
{
lean_object* v_defns_550_; lean_object* v___x_551_; 
v_defns_550_ = lean_ctor_get(v_t_548_, 0);
lean_inc(v_defns_550_);
lean_dec_ref_known(v_t_548_, 1);
v___x_551_ = lean_apply_1(v_k_549_, v_defns_550_);
return v___x_551_;
}
case 6:
{
lean_object* v_lparams_552_; lean_object* v_nparams_553_; lean_object* v_types_554_; uint8_t v_isUnsafe_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_lparams_552_ = lean_ctor_get(v_t_548_, 0);
lean_inc(v_lparams_552_);
v_nparams_553_ = lean_ctor_get(v_t_548_, 1);
lean_inc(v_nparams_553_);
v_types_554_ = lean_ctor_get(v_t_548_, 2);
lean_inc(v_types_554_);
v_isUnsafe_555_ = lean_ctor_get_uint8(v_t_548_, sizeof(void*)*3);
lean_dec_ref_known(v_t_548_, 3);
v___x_556_ = lean_box(v_isUnsafe_555_);
v___x_557_ = lean_apply_4(v_k_549_, v_lparams_552_, v_nparams_553_, v_types_554_, v___x_556_);
return v___x_557_;
}
default: 
{
lean_object* v_val_558_; lean_object* v___x_559_; 
v_val_558_ = lean_ctor_get(v_t_548_, 0);
lean_inc_ref(v_val_558_);
lean_dec(v_t_548_);
v___x_559_ = lean_apply_1(v_k_549_, v_val_558_);
return v___x_559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim(lean_object* v_motive_560_, lean_object* v_ctorIdx_561_, lean_object* v_t_562_, lean_object* v_h_563_, lean_object* v_k_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_Declaration_ctorElim___redArg(v_t_562_, v_k_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___boxed(lean_object* v_motive_566_, lean_object* v_ctorIdx_567_, lean_object* v_t_568_, lean_object* v_h_569_, lean_object* v_k_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_Declaration_ctorElim(v_motive_566_, v_ctorIdx_567_, v_t_568_, v_h_569_, v_k_570_);
lean_dec(v_ctorIdx_567_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim___redArg(lean_object* v_t_572_, lean_object* v_axiomDecl_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = l_Lean_Declaration_ctorElim___redArg(v_t_572_, v_axiomDecl_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim(lean_object* v_motive_575_, lean_object* v_t_576_, lean_object* v_h_577_, lean_object* v_axiomDecl_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Declaration_ctorElim___redArg(v_t_576_, v_axiomDecl_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim___redArg(lean_object* v_t_580_, lean_object* v_defnDecl_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_Lean_Declaration_ctorElim___redArg(v_t_580_, v_defnDecl_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim(lean_object* v_motive_583_, lean_object* v_t_584_, lean_object* v_h_585_, lean_object* v_defnDecl_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Declaration_ctorElim___redArg(v_t_584_, v_defnDecl_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim___redArg(lean_object* v_t_588_, lean_object* v_thmDecl_589_){
_start:
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Declaration_ctorElim___redArg(v_t_588_, v_thmDecl_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim(lean_object* v_motive_591_, lean_object* v_t_592_, lean_object* v_h_593_, lean_object* v_thmDecl_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Declaration_ctorElim___redArg(v_t_592_, v_thmDecl_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim___redArg(lean_object* v_t_596_, lean_object* v_opaqueDecl_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Lean_Declaration_ctorElim___redArg(v_t_596_, v_opaqueDecl_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim(lean_object* v_motive_599_, lean_object* v_t_600_, lean_object* v_h_601_, lean_object* v_opaqueDecl_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_Declaration_ctorElim___redArg(v_t_600_, v_opaqueDecl_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim___redArg(lean_object* v_t_604_, lean_object* v_quotDecl_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_Declaration_ctorElim___redArg(v_t_604_, v_quotDecl_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim(lean_object* v_motive_607_, lean_object* v_t_608_, lean_object* v_h_609_, lean_object* v_quotDecl_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_Declaration_ctorElim___redArg(v_t_608_, v_quotDecl_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim___redArg(lean_object* v_t_612_, lean_object* v_mutualDefnDecl_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Declaration_ctorElim___redArg(v_t_612_, v_mutualDefnDecl_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim(lean_object* v_motive_615_, lean_object* v_t_616_, lean_object* v_h_617_, lean_object* v_mutualDefnDecl_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_Declaration_ctorElim___redArg(v_t_616_, v_mutualDefnDecl_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim___redArg(lean_object* v_t_620_, lean_object* v_inductDecl_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Lean_Declaration_ctorElim___redArg(v_t_620_, v_inductDecl_621_);
return v___x_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim(lean_object* v_motive_623_, lean_object* v_t_624_, lean_object* v_h_625_, lean_object* v_inductDecl_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_Declaration_ctorElim___redArg(v_t_624_, v_inductDecl_626_);
return v___x_627_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default___closed__0(void){
_start:
{
lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_628_ = l_Lean_instInhabitedAxiomVal_default;
v___x_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default(void){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_obj_once(&l_Lean_instInhabitedDeclaration_default___closed__0, &l_Lean_instInhabitedDeclaration_default___closed__0_once, _init_l_Lean_instInhabitedDeclaration_default___closed__0);
return v___x_630_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration(void){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_instInhabitedDeclaration_default;
return v___x_631_;
}
}
uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(lean_object* v_x_632_, lean_object* v_x_633_){
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
v___x_641_ = l_Lean_instBEqDefinitionVal_beq(v_head_637_, v_head_639_);
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
LEAN_EXPORT void l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_632_ = stack[0].m_obj;
lean_object* v_x_633_ = stack[1].m_obj;
uint8_t v_res_643_;
v_res_643_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_x_632_, v_x_633_);
stack->m_num = v_res_643_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0___boxed(lean_object* v_x_644_, lean_object* v_x_645_){
_start:
{
uint8_t v_res_646_; lean_object* v_r_647_; 
v_res_646_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_x_644_, v_x_645_);
lean_dec(v_x_645_);
lean_dec(v_x_644_);
v_r_647_ = lean_box(v_res_646_);
return v_r_647_;
}
}
uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
if (lean_obj_tag(v_x_648_) == 0)
{
if (lean_obj_tag(v_x_649_) == 0)
{
uint8_t v___x_650_; 
v___x_650_ = 1;
return v___x_650_;
}
else
{
uint8_t v___x_651_; 
v___x_651_ = 0;
return v___x_651_;
}
}
else
{
if (lean_obj_tag(v_x_649_) == 0)
{
uint8_t v___x_652_; 
v___x_652_ = 0;
return v___x_652_;
}
else
{
lean_object* v_head_653_; lean_object* v_tail_654_; lean_object* v_head_655_; lean_object* v_tail_656_; uint8_t v___x_657_; 
v_head_653_ = lean_ctor_get(v_x_648_, 0);
v_tail_654_ = lean_ctor_get(v_x_648_, 1);
v_head_655_ = lean_ctor_get(v_x_649_, 0);
v_tail_656_ = lean_ctor_get(v_x_649_, 1);
v___x_657_ = l_Lean_instBEqInductiveType_beq(v_head_653_, v_head_655_);
if (v___x_657_ == 0)
{
return v___x_657_;
}
else
{
v_x_648_ = v_tail_654_;
v_x_649_ = v_tail_656_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_648_ = stack[0].m_obj;
lean_object* v_x_649_ = stack[1].m_obj;
uint8_t v_res_659_;
v_res_659_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_x_648_, v_x_649_);
stack->m_num = v_res_659_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1___boxed(lean_object* v_x_660_, lean_object* v_x_661_){
_start:
{
uint8_t v_res_662_; lean_object* v_r_663_; 
v_res_662_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_x_660_, v_x_661_);
lean_dec(v_x_661_);
lean_dec(v_x_660_);
v_r_663_ = lean_box(v_res_662_);
return v_r_663_;
}
}
uint8_t l_Lean_instBEqDeclaration_beq(lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
switch(lean_obj_tag(v_x_664_))
{
case 0:
{
if (lean_obj_tag(v_x_665_) == 0)
{
lean_object* v_val_666_; lean_object* v_val_667_; uint8_t v___x_668_; 
v_val_666_ = lean_ctor_get(v_x_664_, 0);
v_val_667_ = lean_ctor_get(v_x_665_, 0);
v___x_668_ = l_Lean_instBEqAxiomVal_beq(v_val_666_, v_val_667_);
return v___x_668_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = 0;
return v___x_669_;
}
}
case 1:
{
if (lean_obj_tag(v_x_665_) == 1)
{
lean_object* v_val_670_; lean_object* v_val_671_; uint8_t v___x_672_; 
v_val_670_ = lean_ctor_get(v_x_664_, 0);
v_val_671_ = lean_ctor_get(v_x_665_, 0);
v___x_672_ = l_Lean_instBEqDefinitionVal_beq(v_val_670_, v_val_671_);
return v___x_672_;
}
else
{
uint8_t v___x_673_; 
v___x_673_ = 0;
return v___x_673_;
}
}
case 2:
{
if (lean_obj_tag(v_x_665_) == 2)
{
lean_object* v_val_674_; lean_object* v_val_675_; uint8_t v___x_676_; 
v_val_674_ = lean_ctor_get(v_x_664_, 0);
v_val_675_ = lean_ctor_get(v_x_665_, 0);
v___x_676_ = l_Lean_instBEqTheoremVal_beq(v_val_674_, v_val_675_);
return v___x_676_;
}
else
{
uint8_t v___x_677_; 
v___x_677_ = 0;
return v___x_677_;
}
}
case 3:
{
if (lean_obj_tag(v_x_665_) == 3)
{
lean_object* v_val_678_; lean_object* v_val_679_; uint8_t v___x_680_; 
v_val_678_ = lean_ctor_get(v_x_664_, 0);
v_val_679_ = lean_ctor_get(v_x_665_, 0);
v___x_680_ = l_Lean_instBEqOpaqueVal_beq(v_val_678_, v_val_679_);
return v___x_680_;
}
else
{
uint8_t v___x_681_; 
v___x_681_ = 0;
return v___x_681_;
}
}
case 4:
{
if (lean_obj_tag(v_x_665_) == 4)
{
uint8_t v___x_682_; 
v___x_682_ = 1;
return v___x_682_;
}
else
{
uint8_t v___x_683_; 
v___x_683_ = 0;
return v___x_683_;
}
}
case 5:
{
if (lean_obj_tag(v_x_665_) == 5)
{
lean_object* v_defns_684_; lean_object* v_defns_685_; uint8_t v___x_686_; 
v_defns_684_ = lean_ctor_get(v_x_664_, 0);
v_defns_685_ = lean_ctor_get(v_x_665_, 0);
v___x_686_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_defns_684_, v_defns_685_);
return v___x_686_;
}
else
{
uint8_t v___x_687_; 
v___x_687_ = 0;
return v___x_687_;
}
}
default: 
{
if (lean_obj_tag(v_x_665_) == 6)
{
lean_object* v_lparams_688_; lean_object* v_nparams_689_; lean_object* v_types_690_; uint8_t v_isUnsafe_691_; lean_object* v_lparams_692_; lean_object* v_nparams_693_; lean_object* v_types_694_; uint8_t v_isUnsafe_695_; uint8_t v___x_696_; 
v_lparams_688_ = lean_ctor_get(v_x_664_, 0);
v_nparams_689_ = lean_ctor_get(v_x_664_, 1);
v_types_690_ = lean_ctor_get(v_x_664_, 2);
v_isUnsafe_691_ = lean_ctor_get_uint8(v_x_664_, sizeof(void*)*3);
v_lparams_692_ = lean_ctor_get(v_x_665_, 0);
v_nparams_693_ = lean_ctor_get(v_x_665_, 1);
v_types_694_ = lean_ctor_get(v_x_665_, 2);
v_isUnsafe_695_ = lean_ctor_get_uint8(v_x_665_, sizeof(void*)*3);
v___x_696_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_lparams_688_, v_lparams_692_);
if (v___x_696_ == 0)
{
return v___x_696_;
}
else
{
uint8_t v___x_697_; 
v___x_697_ = lean_nat_dec_eq(v_nparams_689_, v_nparams_693_);
if (v___x_697_ == 0)
{
return v___x_697_;
}
else
{
uint8_t v___x_698_; 
v___x_698_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_types_690_, v_types_694_);
if (v___x_698_ == 0)
{
return v___x_698_;
}
else
{
if (v_isUnsafe_695_ == 0)
{
if (v_isUnsafe_691_ == 0)
{
return v___x_698_;
}
else
{
return v_isUnsafe_695_;
}
}
else
{
return v_isUnsafe_691_;
}
}
}
}
}
else
{
uint8_t v___x_699_; 
v___x_699_ = 0;
return v___x_699_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqDeclaration_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_664_ = stack[0].m_obj;
lean_object* v_x_665_ = stack[1].m_obj;
uint8_t v_res_700_;
v_res_700_ = l_Lean_instBEqDeclaration_beq(v_x_664_, v_x_665_);
stack->m_num = v_res_700_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqDeclaration_beq___boxed(lean_object* v_x_701_, lean_object* v_x_702_){
_start:
{
uint8_t v_res_703_; lean_object* v_r_704_; 
v_res_703_ = l_Lean_instBEqDeclaration_beq(v_x_701_, v_x_702_);
lean_dec(v_x_702_);
lean_dec(v_x_701_);
v_r_704_ = lean_box(v_res_703_);
return v_r_704_;
}
}
lean_object* lean_mk_inductive_decl(lean_object* v_lparams_707_, lean_object* v_nparams_708_, lean_object* v_types_709_, uint8_t v_isUnsafe_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_711_, 0, v_lparams_707_);
lean_ctor_set(v___x_711_, 1, v_nparams_708_);
lean_ctor_set(v___x_711_, 2, v_types_709_);
lean_ctor_set_uint8(v___x_711_, sizeof(void*)*3, v_isUnsafe_710_);
return v___x_711_;
}
}
LEAN_EXPORT void lean_mk_inductive_decl_0interp(lean_interpreter_value* stack)
{
lean_object* v_lparams_707_ = stack[0].m_obj;
lean_object* v_nparams_708_ = stack[1].m_obj;
lean_object* v_types_709_ = stack[2].m_obj;
uint8_t v_isUnsafe_710_ = stack[3].m_num;
lean_object* v_res_712_;
v_res_712_ = lean_mk_inductive_decl(v_lparams_707_, v_nparams_708_, v_types_709_, v_isUnsafe_710_);
stack->m_obj
 = v_res_712_;
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveDeclEs___boxed(lean_object* v_lparams_713_, lean_object* v_nparams_714_, lean_object* v_types_715_, lean_object* v_isUnsafe_716_){
_start:
{
uint8_t v_isUnsafe_boxed_717_; lean_object* v_res_718_; 
v_isUnsafe_boxed_717_ = lean_unbox(v_isUnsafe_716_);
v_res_718_ = lean_mk_inductive_decl(v_lparams_713_, v_nparams_714_, v_types_715_, v_isUnsafe_boxed_717_);
return v_res_718_;
}
}
uint8_t lean_is_unsafe_inductive_decl(lean_object* v_x_719_){
_start:
{
if (lean_obj_tag(v_x_719_) == 6)
{
uint8_t v_isUnsafe_720_; 
v_isUnsafe_720_ = lean_ctor_get_uint8(v_x_719_, sizeof(void*)*3);
lean_dec_ref_known(v_x_719_, 3);
return v_isUnsafe_720_;
}
else
{
uint8_t v___x_721_; 
lean_dec(v_x_719_);
v___x_721_ = 0;
return v___x_721_;
}
}
}
LEAN_EXPORT void lean_is_unsafe_inductive_decl_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_719_ = stack[0].m_obj;
uint8_t v_res_722_;
v_res_722_ = lean_is_unsafe_inductive_decl(v_x_719_);
stack->m_num = v_res_722_;
}
LEAN_EXPORT lean_object* l_Lean_Declaration_isUnsafeInductiveDeclEx___boxed(lean_object* v_x_723_){
_start:
{
uint8_t v_res_724_; lean_object* v_r_725_; 
v_res_724_ = lean_is_unsafe_inductive_decl(v_x_723_);
v_r_725_ = lean_box(v_res_724_);
return v_r_725_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(lean_object* v_msg_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = l_Lean_instInhabitedDefinitionVal_default;
v___x_728_ = lean_panic_fn_borrowed(v___x_727_, v_msg_726_);
return v___x_728_;
}
}
static lean_object* _init_l_Lean_Declaration_definitionVal_x21___closed__3(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_732_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__2));
v___x_733_ = lean_unsigned_to_nat(9u);
v___x_734_ = lean_unsigned_to_nat(184u);
v___x_735_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__1));
v___x_736_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_737_ = l_mkPanicMessageWithDecl(v___x_736_, v___x_735_, v___x_734_, v___x_733_, v___x_732_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21(lean_object* v_x_738_){
_start:
{
if (lean_obj_tag(v_x_738_) == 1)
{
lean_object* v_val_739_; 
v_val_739_ = lean_ctor_get(v_x_738_, 0);
lean_inc_ref(v_val_739_);
return v_val_739_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_obj_once(&l_Lean_Declaration_definitionVal_x21___closed__3, &l_Lean_Declaration_definitionVal_x21___closed__3_once, _init_l_Lean_Declaration_definitionVal_x21___closed__3);
v___x_741_ = l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(v___x_740_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21___boxed(lean_object* v_x_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Lean_Declaration_definitionVal_x21(v_x_742_);
lean_dec(v_x_742_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
if (lean_obj_tag(v_a_744_) == 0)
{
lean_object* v___x_746_; 
v___x_746_ = l_List_reverse___redArg(v_a_745_);
return v___x_746_;
}
else
{
lean_object* v_head_747_; lean_object* v_toConstantVal_748_; lean_object* v_tail_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_758_; 
v_head_747_ = lean_ctor_get(v_a_744_, 0);
v_toConstantVal_748_ = lean_ctor_get(v_head_747_, 0);
lean_inc_ref(v_toConstantVal_748_);
v_tail_749_ = lean_ctor_get(v_a_744_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_a_744_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v_a_744_, 0);
lean_dec(v_unused_759_);
v___x_751_ = v_a_744_;
v_isShared_752_ = v_isSharedCheck_758_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_tail_749_);
lean_dec(v_a_744_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_758_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_name_753_; lean_object* v___x_755_; 
v_name_753_ = lean_ctor_get(v_toConstantVal_748_, 0);
lean_inc(v_name_753_);
lean_dec_ref(v_toConstantVal_748_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v_a_745_);
lean_ctor_set(v___x_751_, 0, v_name_753_);
v___x_755_ = v___x_751_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_name_753_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v_a_745_);
v___x_755_ = v_reuseFailAlloc_757_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
v_a_744_ = v_tail_749_;
v_a_745_ = v___x_755_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(lean_object* v_a_760_, lean_object* v_a_761_){
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
lean_object* v_head_763_; lean_object* v_tail_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_773_; 
v_head_763_ = lean_ctor_get(v_a_760_, 0);
v_tail_764_ = lean_ctor_get(v_a_760_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_a_760_);
if (v_isSharedCheck_773_ == 0)
{
v___x_766_ = v_a_760_;
v_isShared_767_ = v_isSharedCheck_773_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_tail_764_);
lean_inc(v_head_763_);
lean_dec(v_a_760_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_773_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v_name_768_; lean_object* v___x_770_; 
v_name_768_ = lean_ctor_get(v_head_763_, 0);
lean_inc(v_name_768_);
lean_dec(v_head_763_);
if (v_isShared_767_ == 0)
{
lean_ctor_set(v___x_766_, 1, v_a_761_);
lean_ctor_set(v___x_766_, 0, v_name_768_);
v___x_770_ = v___x_766_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_name_768_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v_a_761_);
v___x_770_ = v_reuseFailAlloc_772_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
v_a_760_ = v_tail_764_;
v_a_761_ = v___x_770_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getTopLevelNames(lean_object* v_x_780_){
_start:
{
switch(lean_obj_tag(v_x_780_))
{
case 4:
{
lean_object* v___x_781_; 
v___x_781_ = ((lean_object*)(l_Lean_Declaration_getTopLevelNames___closed__2));
return v___x_781_;
}
case 5:
{
lean_object* v_defns_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v_defns_782_ = lean_ctor_get(v_x_780_, 0);
lean_inc(v_defns_782_);
lean_dec_ref_known(v_x_780_, 1);
v___x_783_ = lean_box(0);
v___x_784_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_782_, v___x_783_);
return v___x_784_;
}
case 6:
{
lean_object* v_types_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_types_785_ = lean_ctor_get(v_x_780_, 2);
lean_inc(v_types_785_);
lean_dec_ref_known(v_x_780_, 3);
v___x_786_ = lean_box(0);
v___x_787_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(v_types_785_, v___x_786_);
return v___x_787_;
}
default: 
{
lean_object* v_val_788_; lean_object* v_toConstantVal_789_; lean_object* v_name_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_val_788_ = lean_ctor_get(v_x_780_, 0);
lean_inc_ref(v_val_788_);
lean_dec(v_x_780_);
v_toConstantVal_789_ = lean_ctor_get(v_val_788_, 0);
lean_inc_ref(v_toConstantVal_789_);
lean_dec_ref(v_val_788_);
v_name_790_ = lean_ctor_get(v_toConstantVal_789_, 0);
lean_inc(v_name_790_);
lean_dec_ref(v_toConstantVal_789_);
v___x_791_ = lean_box(0);
v___x_792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_792_, 0, v_name_790_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
return v___x_792_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
if (lean_obj_tag(v_a_793_) == 0)
{
lean_object* v___x_795_; 
v___x_795_ = l_List_reverse___redArg(v_a_794_);
return v___x_795_;
}
else
{
lean_object* v_head_796_; lean_object* v_tail_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_806_; 
v_head_796_ = lean_ctor_get(v_a_793_, 0);
v_tail_797_ = lean_ctor_get(v_a_793_, 1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_a_793_);
if (v_isSharedCheck_806_ == 0)
{
v___x_799_ = v_a_793_;
v_isShared_800_ = v_isSharedCheck_806_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_tail_797_);
lean_inc(v_head_796_);
lean_dec(v_a_793_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_806_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v_name_801_; lean_object* v___x_803_; 
v_name_801_ = lean_ctor_get(v_head_796_, 0);
lean_inc(v_name_801_);
lean_dec(v_head_796_);
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v_a_794_);
lean_ctor_set(v___x_799_, 0, v_name_801_);
v___x_803_ = v___x_799_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_name_801_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_a_794_);
v___x_803_ = v_reuseFailAlloc_805_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
v_a_793_ = v_tail_797_;
v_a_794_ = v___x_803_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(lean_object* v_a_810_, lean_object* v_a_811_){
_start:
{
if (lean_obj_tag(v_a_810_) == 0)
{
lean_object* v___x_812_; 
v___x_812_ = lean_array_to_list(v_a_811_);
return v___x_812_;
}
else
{
lean_object* v_head_813_; lean_object* v_tail_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_830_; 
v_head_813_ = lean_ctor_get(v_a_810_, 0);
v_tail_814_ = lean_ctor_get(v_a_810_, 1);
v_isSharedCheck_830_ = !lean_is_exclusive(v_a_810_);
if (v_isSharedCheck_830_ == 0)
{
v___x_816_ = v_a_810_;
v_isShared_817_ = v_isSharedCheck_830_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_tail_814_);
lean_inc(v_head_813_);
lean_dec(v_a_810_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_830_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v_name_818_; lean_object* v_ctors_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_825_; 
v_name_818_ = lean_ctor_get(v_head_813_, 0);
lean_inc(v_name_818_);
v_ctors_819_ = lean_ctor_get(v_head_813_, 2);
lean_inc(v_ctors_819_);
lean_dec(v_head_813_);
v___x_820_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1));
v___x_821_ = l_Lean_Name_appendCore(v_name_818_, v___x_820_);
v___x_822_ = lean_box(0);
v___x_823_ = l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(v_ctors_819_, v___x_822_);
if (v_isShared_817_ == 0)
{
lean_ctor_set(v___x_816_, 1, v___x_823_);
lean_ctor_set(v___x_816_, 0, v___x_821_);
v___x_825_ = v___x_816_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_821_);
lean_ctor_set(v_reuseFailAlloc_829_, 1, v___x_823_);
v___x_825_ = v_reuseFailAlloc_829_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_826_, 0, v_name_818_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_811_, v___x_826_);
v_a_810_ = v_tail_814_;
v_a_811_ = v___x_827_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getNames(lean_object* v_x_857_){
_start:
{
switch(lean_obj_tag(v_x_857_))
{
case 4:
{
lean_object* v___x_858_; 
v___x_858_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__9));
return v___x_858_;
}
case 5:
{
lean_object* v_defns_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v_defns_859_ = lean_ctor_get(v_x_857_, 0);
lean_inc(v_defns_859_);
lean_dec_ref_known(v_x_857_, 1);
v___x_860_ = lean_box(0);
v___x_861_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_859_, v___x_860_);
return v___x_861_;
}
case 6:
{
lean_object* v_types_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v_types_862_ = lean_ctor_get(v_x_857_, 2);
lean_inc(v_types_862_);
lean_dec_ref_known(v_x_857_, 3);
v___x_863_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__10));
v___x_864_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(v_types_862_, v___x_863_);
return v___x_864_;
}
default: 
{
lean_object* v_val_865_; lean_object* v_toConstantVal_866_; lean_object* v_name_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_val_865_ = lean_ctor_get(v_x_857_, 0);
lean_inc_ref(v_val_865_);
lean_dec(v_x_857_);
v_toConstantVal_866_ = lean_ctor_get(v_val_865_, 0);
lean_inc_ref(v_toConstantVal_866_);
lean_dec_ref(v_val_865_);
v_name_867_ = lean_ctor_get(v_toConstantVal_866_, 0);
lean_inc(v_name_867_);
lean_dec_ref(v_toConstantVal_866_);
v___x_868_ = lean_box(0);
v___x_869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_869_, 0, v_name_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
return v___x_869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__0(lean_object* v_f_870_, lean_object* v_value_871_, lean_object* v_a_872_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = lean_apply_2(v_f_870_, v_a_872_, v_value_871_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__3(lean_object* v_f_874_, lean_object* v_value_875_, lean_object* v_a_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = lean_apply_2(v_f_874_, v_a_876_, v_value_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__1(lean_object* v_f_878_, lean_object* v_toBind_879_, lean_object* v_a_880_, lean_object* v_v_881_){
_start:
{
lean_object* v_toConstantVal_882_; lean_object* v_value_883_; lean_object* v_type_884_; lean_object* v___f_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_toConstantVal_882_ = lean_ctor_get(v_v_881_, 0);
lean_inc_ref(v_toConstantVal_882_);
v_value_883_ = lean_ctor_get(v_v_881_, 1);
lean_inc_ref(v_value_883_);
lean_dec_ref(v_v_881_);
v_type_884_ = lean_ctor_get(v_toConstantVal_882_, 2);
lean_inc_ref(v_type_884_);
lean_dec_ref(v_toConstantVal_882_);
lean_inc(v_f_878_);
v___f_885_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__3), 3, 2);
lean_closure_set(v___f_885_, 0, v_f_878_);
lean_closure_set(v___f_885_, 1, v_value_883_);
v___x_886_ = lean_apply_2(v_f_878_, v_a_880_, v_type_884_);
v___x_887_ = lean_apply_4(v_toBind_879_, lean_box(0), lean_box(0), v___x_886_, v___f_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__2(lean_object* v_f_888_, lean_object* v_a_889_, lean_object* v_ctor_890_){
_start:
{
lean_object* v_type_891_; lean_object* v___x_892_; 
v_type_891_ = lean_ctor_get(v_ctor_890_, 1);
lean_inc_ref(v_type_891_);
lean_dec_ref(v_ctor_890_);
v___x_892_ = lean_apply_2(v_f_888_, v_a_889_, v_type_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__4(lean_object* v_inst_893_, lean_object* v___f_894_, lean_object* v_ctors_895_, lean_object* v_a_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_List_foldlM___redArg(v_inst_893_, v___f_894_, v_a_896_, v_ctors_895_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__5(lean_object* v_inst_898_, lean_object* v___f_899_, lean_object* v_f_900_, lean_object* v_toBind_901_, lean_object* v_a_902_, lean_object* v_inductType_903_){
_start:
{
lean_object* v_type_904_; lean_object* v_ctors_905_; lean_object* v___f_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_type_904_ = lean_ctor_get(v_inductType_903_, 1);
lean_inc_ref(v_type_904_);
v_ctors_905_ = lean_ctor_get(v_inductType_903_, 2);
lean_inc(v_ctors_905_);
lean_dec_ref(v_inductType_903_);
v___f_906_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__4), 4, 3);
lean_closure_set(v___f_906_, 0, v_inst_898_);
lean_closure_set(v___f_906_, 1, v___f_899_);
lean_closure_set(v___f_906_, 2, v_ctors_905_);
v___x_907_ = lean_apply_2(v_f_900_, v_a_902_, v_type_904_);
v___x_908_ = lean_apply_4(v_toBind_901_, lean_box(0), lean_box(0), v___x_907_, v___f_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object* v_inst_909_, lean_object* v_d_910_, lean_object* v_f_911_, lean_object* v_a_912_){
_start:
{
switch(lean_obj_tag(v_d_910_))
{
case 0:
{
lean_object* v_val_913_; lean_object* v_toConstantVal_914_; lean_object* v_type_915_; lean_object* v___x_916_; 
lean_dec_ref(v_inst_909_);
v_val_913_ = lean_ctor_get(v_d_910_, 0);
lean_inc_ref(v_val_913_);
lean_dec_ref_known(v_d_910_, 1);
v_toConstantVal_914_ = lean_ctor_get(v_val_913_, 0);
lean_inc_ref(v_toConstantVal_914_);
lean_dec_ref(v_val_913_);
v_type_915_ = lean_ctor_get(v_toConstantVal_914_, 2);
lean_inc_ref(v_type_915_);
lean_dec_ref(v_toConstantVal_914_);
v___x_916_ = lean_apply_2(v_f_911_, v_a_912_, v_type_915_);
return v___x_916_;
}
case 4:
{
lean_object* v_toApplicative_917_; lean_object* v_toPure_918_; lean_object* v___x_919_; 
v_toApplicative_917_ = lean_ctor_get(v_inst_909_, 0);
lean_inc_ref(v_toApplicative_917_);
lean_dec(v_f_911_);
lean_dec_ref(v_inst_909_);
v_toPure_918_ = lean_ctor_get(v_toApplicative_917_, 1);
lean_inc(v_toPure_918_);
lean_dec_ref(v_toApplicative_917_);
v___x_919_ = lean_apply_2(v_toPure_918_, lean_box(0), v_a_912_);
return v___x_919_;
}
case 5:
{
lean_object* v_toBind_920_; lean_object* v_defns_921_; lean_object* v___f_922_; lean_object* v___x_923_; 
v_toBind_920_ = lean_ctor_get(v_inst_909_, 1);
v_defns_921_ = lean_ctor_get(v_d_910_, 0);
lean_inc(v_defns_921_);
lean_dec_ref_known(v_d_910_, 1);
lean_inc(v_toBind_920_);
v___f_922_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_922_, 0, v_f_911_);
lean_closure_set(v___f_922_, 1, v_toBind_920_);
v___x_923_ = l_List_foldlM___redArg(v_inst_909_, v___f_922_, v_a_912_, v_defns_921_);
return v___x_923_;
}
case 6:
{
lean_object* v_toBind_924_; lean_object* v_types_925_; lean_object* v___f_926_; lean_object* v___f_927_; lean_object* v___x_928_; 
v_toBind_924_ = lean_ctor_get(v_inst_909_, 1);
v_types_925_ = lean_ctor_get(v_d_910_, 2);
lean_inc(v_types_925_);
lean_dec_ref_known(v_d_910_, 3);
lean_inc(v_f_911_);
v___f_926_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__2), 3, 1);
lean_closure_set(v___f_926_, 0, v_f_911_);
lean_inc(v_toBind_924_);
lean_inc_ref(v_inst_909_);
v___f_927_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__5), 6, 4);
lean_closure_set(v___f_927_, 0, v_inst_909_);
lean_closure_set(v___f_927_, 1, v___f_926_);
lean_closure_set(v___f_927_, 2, v_f_911_);
lean_closure_set(v___f_927_, 3, v_toBind_924_);
v___x_928_ = l_List_foldlM___redArg(v_inst_909_, v___f_927_, v_a_912_, v_types_925_);
return v___x_928_;
}
default: 
{
lean_object* v_val_929_; lean_object* v_toConstantVal_930_; lean_object* v_toBind_931_; lean_object* v_value_932_; lean_object* v_type_933_; lean_object* v___f_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_val_929_ = lean_ctor_get(v_d_910_, 0);
lean_inc_ref(v_val_929_);
lean_dec(v_d_910_);
v_toConstantVal_930_ = lean_ctor_get(v_val_929_, 0);
lean_inc_ref(v_toConstantVal_930_);
v_toBind_931_ = lean_ctor_get(v_inst_909_, 1);
lean_inc(v_toBind_931_);
lean_dec_ref(v_inst_909_);
v_value_932_ = lean_ctor_get(v_val_929_, 1);
lean_inc_ref(v_value_932_);
lean_dec_ref(v_val_929_);
v_type_933_ = lean_ctor_get(v_toConstantVal_930_, 2);
lean_inc_ref(v_type_933_);
lean_dec_ref(v_toConstantVal_930_);
lean_inc(v_f_911_);
v___f_934_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_934_, 0, v_f_911_);
lean_closure_set(v___f_934_, 1, v_value_932_);
v___x_935_ = lean_apply_2(v_f_911_, v_a_912_, v_type_933_);
v___x_936_ = lean_apply_4(v_toBind_931_, lean_box(0), lean_box(0), v___x_935_, v___f_934_);
return v___x_936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM(lean_object* v_00_u03b1_937_, lean_object* v_m_938_, lean_object* v_inst_939_, lean_object* v_d_940_, lean_object* v_f_941_, lean_object* v_a_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Lean_Declaration_foldExprM___redArg(v_inst_939_, v_d_940_, v_f_941_, v_a_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg___lam__0(lean_object* v_f_944_, lean_object* v_x_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = lean_apply_1(v_f_944_, v_a_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg(lean_object* v_inst_948_, lean_object* v_d_949_, lean_object* v_f_950_){
_start:
{
lean_object* v___f_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v___f_951_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_951_, 0, v_f_950_);
v___x_952_ = lean_box(0);
v___x_953_ = l_Lean_Declaration_foldExprM___redArg(v_inst_948_, v_d_949_, v___f_951_, v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM(lean_object* v_m_954_, lean_object* v_inst_955_, lean_object* v_d_956_, lean_object* v_f_957_){
_start:
{
lean_object* v___f_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___f_958_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_958_, 0, v_f_957_);
v___x_959_ = lean_box(0);
v___x_960_ = l_Lean_Declaration_foldExprM___redArg(v_inst_955_, v_d_956_, v___f_958_, v___x_959_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default___closed__0(void){
_start:
{
uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_961_ = 0;
v___x_962_ = lean_box(0);
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = l_Lean_instInhabitedConstantVal_default;
v___x_965_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v___x_963_);
lean_ctor_set(v___x_965_, 2, v___x_963_);
lean_ctor_set(v___x_965_, 3, v___x_962_);
lean_ctor_set(v___x_965_, 4, v___x_962_);
lean_ctor_set(v___x_965_, 5, v___x_963_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*6, v___x_961_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*6 + 1, v___x_961_);
lean_ctor_set_uint8(v___x_965_, sizeof(void*)*6 + 2, v___x_961_);
return v___x_965_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default(void){
_start:
{
lean_object* v___x_966_; 
v___x_966_ = lean_obj_once(&l_Lean_instInhabitedInductiveVal_default___closed__0, &l_Lean_instInhabitedInductiveVal_default___closed__0_once, _init_l_Lean_instInhabitedInductiveVal_default___closed__0);
return v___x_966_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal(void){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_instInhabitedInductiveVal_default;
return v___x_967_;
}
}
uint8_t l_Lean_instBEqInductiveVal_beq(lean_object* v_x_968_, lean_object* v_x_969_){
_start:
{
lean_object* v_toConstantVal_970_; lean_object* v_numParams_971_; lean_object* v_numIndices_972_; lean_object* v_all_973_; lean_object* v_ctors_974_; lean_object* v_numNested_975_; uint8_t v_isRec_976_; uint8_t v_isUnsafe_977_; uint8_t v_isReflexive_978_; lean_object* v_toConstantVal_979_; lean_object* v_numParams_980_; lean_object* v_numIndices_981_; lean_object* v_all_982_; lean_object* v_ctors_983_; lean_object* v_numNested_984_; uint8_t v_isRec_985_; uint8_t v_isUnsafe_986_; uint8_t v_isReflexive_987_; uint8_t v___y_989_; uint8_t v___y_991_; uint8_t v___x_992_; 
v_toConstantVal_970_ = lean_ctor_get(v_x_968_, 0);
v_numParams_971_ = lean_ctor_get(v_x_968_, 1);
v_numIndices_972_ = lean_ctor_get(v_x_968_, 2);
v_all_973_ = lean_ctor_get(v_x_968_, 3);
v_ctors_974_ = lean_ctor_get(v_x_968_, 4);
v_numNested_975_ = lean_ctor_get(v_x_968_, 5);
v_isRec_976_ = lean_ctor_get_uint8(v_x_968_, sizeof(void*)*6);
v_isUnsafe_977_ = lean_ctor_get_uint8(v_x_968_, sizeof(void*)*6 + 1);
v_isReflexive_978_ = lean_ctor_get_uint8(v_x_968_, sizeof(void*)*6 + 2);
v_toConstantVal_979_ = lean_ctor_get(v_x_969_, 0);
v_numParams_980_ = lean_ctor_get(v_x_969_, 1);
v_numIndices_981_ = lean_ctor_get(v_x_969_, 2);
v_all_982_ = lean_ctor_get(v_x_969_, 3);
v_ctors_983_ = lean_ctor_get(v_x_969_, 4);
v_numNested_984_ = lean_ctor_get(v_x_969_, 5);
v_isRec_985_ = lean_ctor_get_uint8(v_x_969_, sizeof(void*)*6);
v_isUnsafe_986_ = lean_ctor_get_uint8(v_x_969_, sizeof(void*)*6 + 1);
v_isReflexive_987_ = lean_ctor_get_uint8(v_x_969_, sizeof(void*)*6 + 2);
v___x_992_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_970_, v_toConstantVal_979_);
if (v___x_992_ == 0)
{
return v___x_992_;
}
else
{
uint8_t v___x_993_; 
v___x_993_ = lean_nat_dec_eq(v_numParams_971_, v_numParams_980_);
if (v___x_993_ == 0)
{
return v___x_993_;
}
else
{
uint8_t v___x_994_; 
v___x_994_ = lean_nat_dec_eq(v_numIndices_972_, v_numIndices_981_);
if (v___x_994_ == 0)
{
return v___x_994_;
}
else
{
uint8_t v___x_995_; 
v___x_995_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_973_, v_all_982_);
if (v___x_995_ == 0)
{
return v___x_995_;
}
else
{
uint8_t v___x_996_; 
v___x_996_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_ctors_974_, v_ctors_983_);
if (v___x_996_ == 0)
{
return v___x_996_;
}
else
{
uint8_t v___x_997_; 
v___x_997_ = lean_nat_dec_eq(v_numNested_975_, v_numNested_984_);
if (v___x_997_ == 0)
{
return v___x_997_;
}
else
{
if (v_isRec_985_ == 0)
{
if (v_isRec_976_ == 0)
{
v___y_991_ = v___x_997_;
goto v___jp_990_;
}
else
{
return v_isRec_985_;
}
}
else
{
v___y_991_ = v_isRec_976_;
goto v___jp_990_;
}
}
}
}
}
}
}
v___jp_988_:
{
if (v_isReflexive_987_ == 0)
{
if (v_isReflexive_978_ == 0)
{
return v___y_989_;
}
else
{
return v_isReflexive_987_;
}
}
else
{
return v_isReflexive_978_;
}
}
v___jp_990_:
{
if (v___y_991_ == 0)
{
return v___y_991_;
}
else
{
if (v_isUnsafe_986_ == 0)
{
if (v_isUnsafe_977_ == 0)
{
v___y_989_ = v___y_991_;
goto v___jp_988_;
}
else
{
return v_isUnsafe_986_;
}
}
else
{
if (v_isUnsafe_977_ == 0)
{
return v_isUnsafe_977_;
}
else
{
v___y_989_ = v_isUnsafe_977_;
goto v___jp_988_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqInductiveVal_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_968_ = stack[0].m_obj;
lean_object* v_x_969_ = stack[1].m_obj;
uint8_t v_res_998_;
v_res_998_ = l_Lean_instBEqInductiveVal_beq(v_x_968_, v_x_969_);
stack->m_num = v_res_998_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveVal_beq___boxed(lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
uint8_t v_res_1001_; lean_object* v_r_1002_; 
v_res_1001_ = l_Lean_instBEqInductiveVal_beq(v_x_999_, v_x_1000_);
lean_dec_ref(v_x_1000_);
lean_dec_ref(v_x_999_);
v_r_1002_ = lean_box(v_res_1001_);
return v_r_1002_;
}
}
lean_object* lean_mk_inductive_val(lean_object* v_name_1005_, lean_object* v_levelParams_1006_, lean_object* v_type_1007_, lean_object* v_numParams_1008_, lean_object* v_numIndices_1009_, lean_object* v_all_1010_, lean_object* v_ctors_1011_, lean_object* v_numNested_1012_, uint8_t v_isRec_1013_, uint8_t v_isUnsafe_1014_, uint8_t v_isReflexive_1015_){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1016_, 0, v_name_1005_);
lean_ctor_set(v___x_1016_, 1, v_levelParams_1006_);
lean_ctor_set(v___x_1016_, 2, v_type_1007_);
v___x_1017_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v_numParams_1008_);
lean_ctor_set(v___x_1017_, 2, v_numIndices_1009_);
lean_ctor_set(v___x_1017_, 3, v_all_1010_);
lean_ctor_set(v___x_1017_, 4, v_ctors_1011_);
lean_ctor_set(v___x_1017_, 5, v_numNested_1012_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*6, v_isRec_1013_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*6 + 1, v_isUnsafe_1014_);
lean_ctor_set_uint8(v___x_1017_, sizeof(void*)*6 + 2, v_isReflexive_1015_);
return v___x_1017_;
}
}
LEAN_EXPORT void lean_mk_inductive_val_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1005_ = stack[0].m_obj;
lean_object* v_levelParams_1006_ = stack[1].m_obj;
lean_object* v_type_1007_ = stack[2].m_obj;
lean_object* v_numParams_1008_ = stack[3].m_obj;
lean_object* v_numIndices_1009_ = stack[4].m_obj;
lean_object* v_all_1010_ = stack[5].m_obj;
lean_object* v_ctors_1011_ = stack[6].m_obj;
lean_object* v_numNested_1012_ = stack[7].m_obj;
uint8_t v_isRec_1013_ = stack[8].m_num;
uint8_t v_isUnsafe_1014_ = stack[9].m_num;
uint8_t v_isReflexive_1015_ = stack[10].m_num;
lean_object* v_res_1018_;
v_res_1018_ = lean_mk_inductive_val(v_name_1005_, v_levelParams_1006_, v_type_1007_, v_numParams_1008_, v_numIndices_1009_, v_all_1010_, v_ctors_1011_, v_numNested_1012_, v_isRec_1013_, v_isUnsafe_1014_, v_isReflexive_1015_);
stack->m_obj
 = v_res_1018_;
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveValEx___boxed(lean_object* v_name_1019_, lean_object* v_levelParams_1020_, lean_object* v_type_1021_, lean_object* v_numParams_1022_, lean_object* v_numIndices_1023_, lean_object* v_all_1024_, lean_object* v_ctors_1025_, lean_object* v_numNested_1026_, lean_object* v_isRec_1027_, lean_object* v_isUnsafe_1028_, lean_object* v_isReflexive_1029_){
_start:
{
uint8_t v_isRec_boxed_1030_; uint8_t v_isUnsafe_boxed_1031_; uint8_t v_isReflexive_boxed_1032_; lean_object* v_res_1033_; 
v_isRec_boxed_1030_ = lean_unbox(v_isRec_1027_);
v_isUnsafe_boxed_1031_ = lean_unbox(v_isUnsafe_1028_);
v_isReflexive_boxed_1032_ = lean_unbox(v_isReflexive_1029_);
v_res_1033_ = lean_mk_inductive_val(v_name_1019_, v_levelParams_1020_, v_type_1021_, v_numParams_1022_, v_numIndices_1023_, v_all_1024_, v_ctors_1025_, v_numNested_1026_, v_isRec_boxed_1030_, v_isUnsafe_boxed_1031_, v_isReflexive_boxed_1032_);
return v_res_1033_;
}
}
uint8_t lean_inductive_val_is_rec(lean_object* v_v_1034_){
_start:
{
uint8_t v_isRec_1035_; 
v_isRec_1035_ = lean_ctor_get_uint8(v_v_1034_, sizeof(void*)*6);
lean_dec_ref(v_v_1034_);
return v_isRec_1035_;
}
}
LEAN_EXPORT void lean_inductive_val_is_rec_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1034_ = stack[0].m_obj;
uint8_t v_res_1036_;
v_res_1036_ = lean_inductive_val_is_rec(v_v_1034_);
stack->m_num = v_res_1036_;
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isRecEx___boxed(lean_object* v_v_1037_){
_start:
{
uint8_t v_res_1038_; lean_object* v_r_1039_; 
v_res_1038_ = lean_inductive_val_is_rec(v_v_1037_);
v_r_1039_ = lean_box(v_res_1038_);
return v_r_1039_;
}
}
uint8_t lean_inductive_val_is_unsafe(lean_object* v_v_1040_){
_start:
{
uint8_t v_isUnsafe_1041_; 
v_isUnsafe_1041_ = lean_ctor_get_uint8(v_v_1040_, sizeof(void*)*6 + 1);
lean_dec_ref(v_v_1040_);
return v_isUnsafe_1041_;
}
}
LEAN_EXPORT void lean_inductive_val_is_unsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1040_ = stack[0].m_obj;
uint8_t v_res_1042_;
v_res_1042_ = lean_inductive_val_is_unsafe(v_v_1040_);
stack->m_num = v_res_1042_;
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isUnsafeEx___boxed(lean_object* v_v_1043_){
_start:
{
uint8_t v_res_1044_; lean_object* v_r_1045_; 
v_res_1044_ = lean_inductive_val_is_unsafe(v_v_1043_);
v_r_1045_ = lean_box(v_res_1044_);
return v_r_1045_;
}
}
uint8_t lean_inductive_val_is_reflexive(lean_object* v_v_1046_){
_start:
{
uint8_t v_isReflexive_1047_; 
v_isReflexive_1047_ = lean_ctor_get_uint8(v_v_1046_, sizeof(void*)*6 + 2);
lean_dec_ref(v_v_1046_);
return v_isReflexive_1047_;
}
}
LEAN_EXPORT void lean_inductive_val_is_reflexive_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1046_ = stack[0].m_obj;
uint8_t v_res_1048_;
v_res_1048_ = lean_inductive_val_is_reflexive(v_v_1046_);
stack->m_num = v_res_1048_;
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isReflexiveEx___boxed(lean_object* v_v_1049_){
_start:
{
uint8_t v_res_1050_; lean_object* v_r_1051_; 
v_res_1050_ = lean_inductive_val_is_reflexive(v_v_1049_);
v_r_1051_ = lean_box(v_res_1050_);
return v_r_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors(lean_object* v_v_1052_){
_start:
{
lean_object* v_ctors_1053_; lean_object* v___x_1054_; 
v_ctors_1053_ = lean_ctor_get(v_v_1052_, 4);
v___x_1054_ = l_List_lengthTR___redArg(v_ctors_1053_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors___boxed(lean_object* v_v_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_InductiveVal_numCtors(v_v_1055_);
lean_dec_ref(v_v_1055_);
return v_res_1056_;
}
}
uint8_t l_Lean_InductiveVal_isNested(lean_object* v_v_1057_){
_start:
{
lean_object* v_numNested_1058_; lean_object* v___x_1059_; uint8_t v___x_1060_; 
v_numNested_1058_ = lean_ctor_get(v_v_1057_, 5);
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_nat_dec_lt(v___x_1059_, v_numNested_1058_);
return v___x_1060_;
}
}
LEAN_EXPORT void l_Lean_InductiveVal_isNested_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1057_ = stack[0].m_obj;
uint8_t v_res_1061_;
v_res_1061_ = l_Lean_InductiveVal_isNested(v_v_1057_);
stack->m_num = v_res_1061_;
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isNested___boxed(lean_object* v_v_1062_){
_start:
{
uint8_t v_res_1063_; lean_object* v_r_1064_; 
v_res_1063_ = l_Lean_InductiveVal_isNested(v_v_1062_);
lean_dec_ref(v_v_1062_);
v_r_1064_ = lean_box(v_res_1063_);
return v_r_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object* v_v_1065_){
_start:
{
lean_object* v_all_1066_; lean_object* v_numNested_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_all_1066_ = lean_ctor_get(v_v_1065_, 3);
v_numNested_1067_ = lean_ctor_get(v_v_1065_, 5);
v___x_1068_ = l_List_lengthTR___redArg(v_all_1066_);
v___x_1069_ = lean_nat_add(v___x_1068_, v_numNested_1067_);
lean_dec(v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers___boxed(lean_object* v_v_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_InductiveVal_numTypeFormers(v_v_1070_);
lean_dec_ref(v_v_1070_);
return v_res_1071_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1072_ = 0;
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = lean_box(0);
v___x_1075_ = l_Lean_instInhabitedConstantVal_default;
v___x_1076_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v___x_1074_);
lean_ctor_set(v___x_1076_, 2, v___x_1073_);
lean_ctor_set(v___x_1076_, 3, v___x_1073_);
lean_ctor_set(v___x_1076_, 4, v___x_1073_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*5, v___x_1072_);
return v___x_1076_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default(void){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_obj_once(&l_Lean_instInhabitedConstructorVal_default___closed__0, &l_Lean_instInhabitedConstructorVal_default___closed__0_once, _init_l_Lean_instInhabitedConstructorVal_default___closed__0);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal(void){
_start:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_Lean_instInhabitedConstructorVal_default;
return v___x_1078_;
}
}
uint8_t l_Lean_instBEqConstructorVal_beq(lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v_toConstantVal_1081_; lean_object* v_induct_1082_; lean_object* v_cidx_1083_; lean_object* v_numParams_1084_; lean_object* v_numFields_1085_; uint8_t v_isUnsafe_1086_; lean_object* v_toConstantVal_1087_; lean_object* v_induct_1088_; lean_object* v_cidx_1089_; lean_object* v_numParams_1090_; lean_object* v_numFields_1091_; uint8_t v_isUnsafe_1092_; uint8_t v___x_1093_; 
v_toConstantVal_1081_ = lean_ctor_get(v_x_1079_, 0);
v_induct_1082_ = lean_ctor_get(v_x_1079_, 1);
v_cidx_1083_ = lean_ctor_get(v_x_1079_, 2);
v_numParams_1084_ = lean_ctor_get(v_x_1079_, 3);
v_numFields_1085_ = lean_ctor_get(v_x_1079_, 4);
v_isUnsafe_1086_ = lean_ctor_get_uint8(v_x_1079_, sizeof(void*)*5);
v_toConstantVal_1087_ = lean_ctor_get(v_x_1080_, 0);
v_induct_1088_ = lean_ctor_get(v_x_1080_, 1);
v_cidx_1089_ = lean_ctor_get(v_x_1080_, 2);
v_numParams_1090_ = lean_ctor_get(v_x_1080_, 3);
v_numFields_1091_ = lean_ctor_get(v_x_1080_, 4);
v_isUnsafe_1092_ = lean_ctor_get_uint8(v_x_1080_, sizeof(void*)*5);
v___x_1093_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1081_, v_toConstantVal_1087_);
if (v___x_1093_ == 0)
{
return v___x_1093_;
}
else
{
uint8_t v___x_1094_; 
v___x_1094_ = lean_name_eq(v_induct_1082_, v_induct_1088_);
if (v___x_1094_ == 0)
{
return v___x_1094_;
}
else
{
uint8_t v___x_1095_; 
v___x_1095_ = lean_nat_dec_eq(v_cidx_1083_, v_cidx_1089_);
if (v___x_1095_ == 0)
{
return v___x_1095_;
}
else
{
uint8_t v___x_1096_; 
v___x_1096_ = lean_nat_dec_eq(v_numParams_1084_, v_numParams_1090_);
if (v___x_1096_ == 0)
{
return v___x_1096_;
}
else
{
uint8_t v___x_1097_; 
v___x_1097_ = lean_nat_dec_eq(v_numFields_1085_, v_numFields_1091_);
if (v___x_1097_ == 0)
{
return v___x_1097_;
}
else
{
if (v_isUnsafe_1092_ == 0)
{
if (v_isUnsafe_1086_ == 0)
{
return v___x_1097_;
}
else
{
return v_isUnsafe_1092_;
}
}
else
{
return v_isUnsafe_1086_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqConstructorVal_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1079_ = stack[0].m_obj;
lean_object* v_x_1080_ = stack[1].m_obj;
uint8_t v_res_1098_;
v_res_1098_ = l_Lean_instBEqConstructorVal_beq(v_x_1079_, v_x_1080_);
stack->m_num = v_res_1098_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructorVal_beq___boxed(lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
uint8_t v_res_1101_; lean_object* v_r_1102_; 
v_res_1101_ = l_Lean_instBEqConstructorVal_beq(v_x_1099_, v_x_1100_);
lean_dec_ref(v_x_1100_);
lean_dec_ref(v_x_1099_);
v_r_1102_ = lean_box(v_res_1101_);
return v_r_1102_;
}
}
lean_object* lean_mk_constructor_val(lean_object* v_name_1105_, lean_object* v_levelParams_1106_, lean_object* v_type_1107_, lean_object* v_induct_1108_, lean_object* v_cidx_1109_, lean_object* v_numParams_1110_, lean_object* v_numFields_1111_, uint8_t v_isUnsafe_1112_){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1113_, 0, v_name_1105_);
lean_ctor_set(v___x_1113_, 1, v_levelParams_1106_);
lean_ctor_set(v___x_1113_, 2, v_type_1107_);
v___x_1114_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_induct_1108_);
lean_ctor_set(v___x_1114_, 2, v_cidx_1109_);
lean_ctor_set(v___x_1114_, 3, v_numParams_1110_);
lean_ctor_set(v___x_1114_, 4, v_numFields_1111_);
lean_ctor_set_uint8(v___x_1114_, sizeof(void*)*5, v_isUnsafe_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT void lean_mk_constructor_val_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1105_ = stack[0].m_obj;
lean_object* v_levelParams_1106_ = stack[1].m_obj;
lean_object* v_type_1107_ = stack[2].m_obj;
lean_object* v_induct_1108_ = stack[3].m_obj;
lean_object* v_cidx_1109_ = stack[4].m_obj;
lean_object* v_numParams_1110_ = stack[5].m_obj;
lean_object* v_numFields_1111_ = stack[6].m_obj;
uint8_t v_isUnsafe_1112_ = stack[7].m_num;
lean_object* v_res_1115_;
v_res_1115_ = lean_mk_constructor_val(v_name_1105_, v_levelParams_1106_, v_type_1107_, v_induct_1108_, v_cidx_1109_, v_numParams_1110_, v_numFields_1111_, v_isUnsafe_1112_);
stack->m_obj
 = v_res_1115_;
}
LEAN_EXPORT lean_object* l_Lean_mkConstructorValEx___boxed(lean_object* v_name_1116_, lean_object* v_levelParams_1117_, lean_object* v_type_1118_, lean_object* v_induct_1119_, lean_object* v_cidx_1120_, lean_object* v_numParams_1121_, lean_object* v_numFields_1122_, lean_object* v_isUnsafe_1123_){
_start:
{
uint8_t v_isUnsafe_boxed_1124_; lean_object* v_res_1125_; 
v_isUnsafe_boxed_1124_ = lean_unbox(v_isUnsafe_1123_);
v_res_1125_ = lean_mk_constructor_val(v_name_1116_, v_levelParams_1117_, v_type_1118_, v_induct_1119_, v_cidx_1120_, v_numParams_1121_, v_numFields_1122_, v_isUnsafe_boxed_1124_);
return v_res_1125_;
}
}
uint8_t lean_constructor_val_is_unsafe(lean_object* v_v_1126_){
_start:
{
uint8_t v_isUnsafe_1127_; 
v_isUnsafe_1127_ = lean_ctor_get_uint8(v_v_1126_, sizeof(void*)*5);
lean_dec_ref(v_v_1126_);
return v_isUnsafe_1127_;
}
}
LEAN_EXPORT void lean_constructor_val_is_unsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1126_ = stack[0].m_obj;
uint8_t v_res_1128_;
v_res_1128_ = lean_constructor_val_is_unsafe(v_v_1126_);
stack->m_num = v_res_1128_;
}
LEAN_EXPORT lean_object* l_Lean_ConstructorVal_isUnsafeEx___boxed(lean_object* v_v_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = lean_constructor_val_is_unsafe(v_v_1129_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default___closed__0(void){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1132_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_1133_ = lean_unsigned_to_nat(0u);
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
lean_ctor_set(v___x_1135_, 1, v___x_1133_);
lean_ctor_set(v___x_1135_, 2, v___x_1132_);
return v___x_1135_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default(void){
_start:
{
lean_object* v___x_1136_; 
v___x_1136_ = lean_obj_once(&l_Lean_instInhabitedRecursorRule_default___closed__0, &l_Lean_instInhabitedRecursorRule_default___closed__0_once, _init_l_Lean_instInhabitedRecursorRule_default___closed__0);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule(void){
_start:
{
lean_object* v___x_1137_; 
v___x_1137_ = l_Lean_instInhabitedRecursorRule_default;
return v___x_1137_;
}
}
uint8_t l_Lean_instBEqRecursorRule_beq(lean_object* v_x_1138_, lean_object* v_x_1139_){
_start:
{
lean_object* v_ctor_1140_; lean_object* v_nfields_1141_; lean_object* v_rhs_1142_; lean_object* v_ctor_1143_; lean_object* v_nfields_1144_; lean_object* v_rhs_1145_; uint8_t v___x_1146_; 
v_ctor_1140_ = lean_ctor_get(v_x_1138_, 0);
v_nfields_1141_ = lean_ctor_get(v_x_1138_, 1);
v_rhs_1142_ = lean_ctor_get(v_x_1138_, 2);
v_ctor_1143_ = lean_ctor_get(v_x_1139_, 0);
v_nfields_1144_ = lean_ctor_get(v_x_1139_, 1);
v_rhs_1145_ = lean_ctor_get(v_x_1139_, 2);
v___x_1146_ = lean_name_eq(v_ctor_1140_, v_ctor_1143_);
if (v___x_1146_ == 0)
{
return v___x_1146_;
}
else
{
uint8_t v___x_1147_; 
v___x_1147_ = lean_nat_dec_eq(v_nfields_1141_, v_nfields_1144_);
if (v___x_1147_ == 0)
{
return v___x_1147_;
}
else
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_expr_eqv(v_rhs_1142_, v_rhs_1145_);
return v___x_1148_;
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqRecursorRule_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1138_ = stack[0].m_obj;
lean_object* v_x_1139_ = stack[1].m_obj;
uint8_t v_res_1149_;
v_res_1149_ = l_Lean_instBEqRecursorRule_beq(v_x_1138_, v_x_1139_);
stack->m_num = v_res_1149_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorRule_beq___boxed(lean_object* v_x_1150_, lean_object* v_x_1151_){
_start:
{
uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_res_1152_ = l_Lean_instBEqRecursorRule_beq(v_x_1150_, v_x_1151_);
lean_dec_ref(v_x_1151_);
lean_dec_ref(v_x_1150_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1156_ = 0;
v___x_1157_ = lean_unsigned_to_nat(0u);
v___x_1158_ = lean_box(0);
v___x_1159_ = l_Lean_instInhabitedConstantVal_default;
v___x_1160_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v___x_1158_);
lean_ctor_set(v___x_1160_, 2, v___x_1157_);
lean_ctor_set(v___x_1160_, 3, v___x_1157_);
lean_ctor_set(v___x_1160_, 4, v___x_1157_);
lean_ctor_set(v___x_1160_, 5, v___x_1157_);
lean_ctor_set(v___x_1160_, 6, v___x_1158_);
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*7, v___x_1156_);
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*7 + 1, v___x_1156_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default(void){
_start:
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_obj_once(&l_Lean_instInhabitedRecursorVal_default___closed__0, &l_Lean_instInhabitedRecursorVal_default___closed__0_once, _init_l_Lean_instInhabitedRecursorVal_default___closed__0);
return v___x_1161_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal(void){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_instInhabitedRecursorVal_default;
return v___x_1162_;
}
}
uint8_t l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(lean_object* v_x_1163_, lean_object* v_x_1164_){
_start:
{
if (lean_obj_tag(v_x_1163_) == 0)
{
if (lean_obj_tag(v_x_1164_) == 0)
{
uint8_t v___x_1165_; 
v___x_1165_ = 1;
return v___x_1165_;
}
else
{
uint8_t v___x_1166_; 
v___x_1166_ = 0;
return v___x_1166_;
}
}
else
{
if (lean_obj_tag(v_x_1164_) == 0)
{
uint8_t v___x_1167_; 
v___x_1167_ = 0;
return v___x_1167_;
}
else
{
lean_object* v_head_1168_; lean_object* v_tail_1169_; lean_object* v_head_1170_; lean_object* v_tail_1171_; uint8_t v___x_1172_; 
v_head_1168_ = lean_ctor_get(v_x_1163_, 0);
v_tail_1169_ = lean_ctor_get(v_x_1163_, 1);
v_head_1170_ = lean_ctor_get(v_x_1164_, 0);
v_tail_1171_ = lean_ctor_get(v_x_1164_, 1);
v___x_1172_ = l_Lean_instBEqRecursorRule_beq(v_head_1168_, v_head_1170_);
if (v___x_1172_ == 0)
{
return v___x_1172_;
}
else
{
v_x_1163_ = v_tail_1169_;
v_x_1164_ = v_tail_1171_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1163_ = stack[0].m_obj;
lean_object* v_x_1164_ = stack[1].m_obj;
uint8_t v_res_1174_;
v_res_1174_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_x_1163_, v_x_1164_);
stack->m_num = v_res_1174_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0___boxed(lean_object* v_x_1175_, lean_object* v_x_1176_){
_start:
{
uint8_t v_res_1177_; lean_object* v_r_1178_; 
v_res_1177_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_x_1175_, v_x_1176_);
lean_dec(v_x_1176_);
lean_dec(v_x_1175_);
v_r_1178_ = lean_box(v_res_1177_);
return v_r_1178_;
}
}
uint8_t l_Lean_instBEqRecursorVal_beq(lean_object* v_x_1179_, lean_object* v_x_1180_){
_start:
{
lean_object* v_toConstantVal_1181_; lean_object* v_all_1182_; lean_object* v_numParams_1183_; lean_object* v_numIndices_1184_; lean_object* v_numMotives_1185_; lean_object* v_numMinors_1186_; lean_object* v_rules_1187_; uint8_t v_k_1188_; uint8_t v_isUnsafe_1189_; lean_object* v_toConstantVal_1190_; lean_object* v_all_1191_; lean_object* v_numParams_1192_; lean_object* v_numIndices_1193_; lean_object* v_numMotives_1194_; lean_object* v_numMinors_1195_; lean_object* v_rules_1196_; uint8_t v_k_1197_; uint8_t v_isUnsafe_1198_; uint8_t v___y_1200_; uint8_t v___x_1201_; 
v_toConstantVal_1181_ = lean_ctor_get(v_x_1179_, 0);
v_all_1182_ = lean_ctor_get(v_x_1179_, 1);
v_numParams_1183_ = lean_ctor_get(v_x_1179_, 2);
v_numIndices_1184_ = lean_ctor_get(v_x_1179_, 3);
v_numMotives_1185_ = lean_ctor_get(v_x_1179_, 4);
v_numMinors_1186_ = lean_ctor_get(v_x_1179_, 5);
v_rules_1187_ = lean_ctor_get(v_x_1179_, 6);
v_k_1188_ = lean_ctor_get_uint8(v_x_1179_, sizeof(void*)*7);
v_isUnsafe_1189_ = lean_ctor_get_uint8(v_x_1179_, sizeof(void*)*7 + 1);
v_toConstantVal_1190_ = lean_ctor_get(v_x_1180_, 0);
v_all_1191_ = lean_ctor_get(v_x_1180_, 1);
v_numParams_1192_ = lean_ctor_get(v_x_1180_, 2);
v_numIndices_1193_ = lean_ctor_get(v_x_1180_, 3);
v_numMotives_1194_ = lean_ctor_get(v_x_1180_, 4);
v_numMinors_1195_ = lean_ctor_get(v_x_1180_, 5);
v_rules_1196_ = lean_ctor_get(v_x_1180_, 6);
v_k_1197_ = lean_ctor_get_uint8(v_x_1180_, sizeof(void*)*7);
v_isUnsafe_1198_ = lean_ctor_get_uint8(v_x_1180_, sizeof(void*)*7 + 1);
v___x_1201_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1181_, v_toConstantVal_1190_);
if (v___x_1201_ == 0)
{
return v___x_1201_;
}
else
{
uint8_t v___x_1202_; 
v___x_1202_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_1182_, v_all_1191_);
if (v___x_1202_ == 0)
{
return v___x_1202_;
}
else
{
uint8_t v___x_1203_; 
v___x_1203_ = lean_nat_dec_eq(v_numParams_1183_, v_numParams_1192_);
if (v___x_1203_ == 0)
{
return v___x_1203_;
}
else
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_nat_dec_eq(v_numIndices_1184_, v_numIndices_1193_);
if (v___x_1204_ == 0)
{
return v___x_1204_;
}
else
{
uint8_t v___x_1205_; 
v___x_1205_ = lean_nat_dec_eq(v_numMotives_1185_, v_numMotives_1194_);
if (v___x_1205_ == 0)
{
return v___x_1205_;
}
else
{
uint8_t v___x_1206_; 
v___x_1206_ = lean_nat_dec_eq(v_numMinors_1186_, v_numMinors_1195_);
if (v___x_1206_ == 0)
{
return v___x_1206_;
}
else
{
uint8_t v___x_1207_; 
v___x_1207_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_rules_1187_, v_rules_1196_);
if (v___x_1207_ == 0)
{
return v___x_1207_;
}
else
{
if (v_k_1197_ == 0)
{
if (v_k_1188_ == 0)
{
v___y_1200_ = v___x_1207_;
goto v___jp_1199_;
}
else
{
return v_k_1197_;
}
}
else
{
v___y_1200_ = v_k_1188_;
goto v___jp_1199_;
}
}
}
}
}
}
}
}
v___jp_1199_:
{
if (v___y_1200_ == 0)
{
return v___y_1200_;
}
else
{
if (v_isUnsafe_1198_ == 0)
{
if (v_isUnsafe_1189_ == 0)
{
return v___y_1200_;
}
else
{
return v_isUnsafe_1198_;
}
}
else
{
return v_isUnsafe_1189_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqRecursorVal_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1179_ = stack[0].m_obj;
lean_object* v_x_1180_ = stack[1].m_obj;
uint8_t v_res_1208_;
v_res_1208_ = l_Lean_instBEqRecursorVal_beq(v_x_1179_, v_x_1180_);
stack->m_num = v_res_1208_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorVal_beq___boxed(lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
uint8_t v_res_1211_; lean_object* v_r_1212_; 
v_res_1211_ = l_Lean_instBEqRecursorVal_beq(v_x_1209_, v_x_1210_);
lean_dec_ref(v_x_1210_);
lean_dec_ref(v_x_1209_);
v_r_1212_ = lean_box(v_res_1211_);
return v_r_1212_;
}
}
lean_object* lean_mk_recursor_val(lean_object* v_name_1215_, lean_object* v_levelParams_1216_, lean_object* v_type_1217_, lean_object* v_all_1218_, lean_object* v_numParams_1219_, lean_object* v_numIndices_1220_, lean_object* v_numMotives_1221_, lean_object* v_numMinors_1222_, lean_object* v_rules_1223_, uint8_t v_k_1224_, uint8_t v_isUnsafe_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; 
v___x_1226_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1226_, 0, v_name_1215_);
lean_ctor_set(v___x_1226_, 1, v_levelParams_1216_);
lean_ctor_set(v___x_1226_, 2, v_type_1217_);
v___x_1227_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1227_, 0, v___x_1226_);
lean_ctor_set(v___x_1227_, 1, v_all_1218_);
lean_ctor_set(v___x_1227_, 2, v_numParams_1219_);
lean_ctor_set(v___x_1227_, 3, v_numIndices_1220_);
lean_ctor_set(v___x_1227_, 4, v_numMotives_1221_);
lean_ctor_set(v___x_1227_, 5, v_numMinors_1222_);
lean_ctor_set(v___x_1227_, 6, v_rules_1223_);
lean_ctor_set_uint8(v___x_1227_, sizeof(void*)*7, v_k_1224_);
lean_ctor_set_uint8(v___x_1227_, sizeof(void*)*7 + 1, v_isUnsafe_1225_);
return v___x_1227_;
}
}
LEAN_EXPORT void lean_mk_recursor_val_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1215_ = stack[0].m_obj;
lean_object* v_levelParams_1216_ = stack[1].m_obj;
lean_object* v_type_1217_ = stack[2].m_obj;
lean_object* v_all_1218_ = stack[3].m_obj;
lean_object* v_numParams_1219_ = stack[4].m_obj;
lean_object* v_numIndices_1220_ = stack[5].m_obj;
lean_object* v_numMotives_1221_ = stack[6].m_obj;
lean_object* v_numMinors_1222_ = stack[7].m_obj;
lean_object* v_rules_1223_ = stack[8].m_obj;
uint8_t v_k_1224_ = stack[9].m_num;
uint8_t v_isUnsafe_1225_ = stack[10].m_num;
lean_object* v_res_1228_;
v_res_1228_ = lean_mk_recursor_val(v_name_1215_, v_levelParams_1216_, v_type_1217_, v_all_1218_, v_numParams_1219_, v_numIndices_1220_, v_numMotives_1221_, v_numMinors_1222_, v_rules_1223_, v_k_1224_, v_isUnsafe_1225_);
stack->m_obj
 = v_res_1228_;
}
LEAN_EXPORT lean_object* l_Lean_mkRecursorValEx___boxed(lean_object* v_name_1229_, lean_object* v_levelParams_1230_, lean_object* v_type_1231_, lean_object* v_all_1232_, lean_object* v_numParams_1233_, lean_object* v_numIndices_1234_, lean_object* v_numMotives_1235_, lean_object* v_numMinors_1236_, lean_object* v_rules_1237_, lean_object* v_k_1238_, lean_object* v_isUnsafe_1239_){
_start:
{
uint8_t v_k_boxed_1240_; uint8_t v_isUnsafe_boxed_1241_; lean_object* v_res_1242_; 
v_k_boxed_1240_ = lean_unbox(v_k_1238_);
v_isUnsafe_boxed_1241_ = lean_unbox(v_isUnsafe_1239_);
v_res_1242_ = lean_mk_recursor_val(v_name_1229_, v_levelParams_1230_, v_type_1231_, v_all_1232_, v_numParams_1233_, v_numIndices_1234_, v_numMotives_1235_, v_numMinors_1236_, v_rules_1237_, v_k_boxed_1240_, v_isUnsafe_boxed_1241_);
return v_res_1242_;
}
}
uint8_t lean_recursor_k(lean_object* v_v_1243_){
_start:
{
uint8_t v_k_1244_; 
v_k_1244_ = lean_ctor_get_uint8(v_v_1243_, sizeof(void*)*7);
lean_dec_ref(v_v_1243_);
return v_k_1244_;
}
}
LEAN_EXPORT void lean_recursor_k_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1243_ = stack[0].m_obj;
uint8_t v_res_1245_;
v_res_1245_ = lean_recursor_k(v_v_1243_);
stack->m_num = v_res_1245_;
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_kEx___boxed(lean_object* v_v_1246_){
_start:
{
uint8_t v_res_1247_; lean_object* v_r_1248_; 
v_res_1247_ = lean_recursor_k(v_v_1246_);
v_r_1248_ = lean_box(v_res_1247_);
return v_r_1248_;
}
}
uint8_t lean_recursor_is_unsafe(lean_object* v_v_1249_){
_start:
{
uint8_t v_isUnsafe_1250_; 
v_isUnsafe_1250_ = lean_ctor_get_uint8(v_v_1249_, sizeof(void*)*7 + 1);
lean_dec_ref(v_v_1249_);
return v_isUnsafe_1250_;
}
}
LEAN_EXPORT void lean_recursor_is_unsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_1249_ = stack[0].m_obj;
uint8_t v_res_1251_;
v_res_1251_ = lean_recursor_is_unsafe(v_v_1249_);
stack->m_num = v_res_1251_;
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_isUnsafeEx___boxed(lean_object* v_v_1252_){
_start:
{
uint8_t v_res_1253_; lean_object* v_r_1254_; 
v_res_1253_ = lean_recursor_is_unsafe(v_v_1252_);
v_r_1254_ = lean_box(v_res_1253_);
return v_r_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object* v_v_1255_){
_start:
{
lean_object* v_numParams_1256_; lean_object* v_numIndices_1257_; lean_object* v_numMotives_1258_; lean_object* v_numMinors_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; 
v_numParams_1256_ = lean_ctor_get(v_v_1255_, 2);
v_numIndices_1257_ = lean_ctor_get(v_v_1255_, 3);
v_numMotives_1258_ = lean_ctor_get(v_v_1255_, 4);
v_numMinors_1259_ = lean_ctor_get(v_v_1255_, 5);
v___x_1260_ = lean_nat_add(v_numParams_1256_, v_numMotives_1258_);
v___x_1261_ = lean_nat_add(v___x_1260_, v_numMinors_1259_);
lean_dec(v___x_1260_);
v___x_1262_ = lean_nat_add(v___x_1261_, v_numIndices_1257_);
lean_dec(v___x_1261_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx___boxed(lean_object* v_v_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_RecursorVal_getMajorIdx(v_v_1263_);
lean_dec_ref(v_v_1263_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx(lean_object* v_v_1265_){
_start:
{
lean_object* v_numParams_1266_; lean_object* v_numMotives_1267_; lean_object* v_numMinors_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_numParams_1266_ = lean_ctor_get(v_v_1265_, 2);
v_numMotives_1267_ = lean_ctor_get(v_v_1265_, 4);
v_numMinors_1268_ = lean_ctor_get(v_v_1265_, 5);
v___x_1269_ = lean_nat_add(v_numParams_1266_, v_numMotives_1267_);
v___x_1270_ = lean_nat_add(v___x_1269_, v_numMinors_1268_);
lean_dec(v___x_1269_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx___boxed(lean_object* v_v_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_RecursorVal_getFirstIndexIdx(v_v_1271_);
lean_dec_ref(v_v_1271_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx(lean_object* v_v_1273_){
_start:
{
lean_object* v_numParams_1274_; lean_object* v_numMotives_1275_; lean_object* v___x_1276_; 
v_numParams_1274_ = lean_ctor_get(v_v_1273_, 2);
v_numMotives_1275_ = lean_ctor_get(v_v_1273_, 4);
v___x_1276_ = lean_nat_add(v_numParams_1274_, v_numMotives_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx___boxed(lean_object* v_v_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_RecursorVal_getFirstMinorIdx(v_v_1277_);
lean_dec_ref(v_v_1277_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(lean_object* v_x_1279_, lean_object* v_x_1280_){
_start:
{
lean_object* v_zero_1281_; uint8_t v_isZero_1282_; 
v_zero_1281_ = lean_unsigned_to_nat(0u);
v_isZero_1282_ = lean_nat_dec_eq(v_x_1279_, v_zero_1281_);
if (v_isZero_1282_ == 1)
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_dec(v_x_1279_);
v___x_1283_ = l_Lean_Expr_bindingDomain_x21(v_x_1280_);
lean_dec_ref(v_x_1280_);
v___x_1284_ = l_Lean_Expr_getAppFn(v___x_1283_);
lean_dec_ref(v___x_1283_);
v___x_1285_ = l_Lean_Expr_constName_x21(v___x_1284_);
lean_dec_ref(v___x_1284_);
return v___x_1285_;
}
else
{
lean_object* v_one_1286_; lean_object* v_n_1287_; lean_object* v___x_1288_; 
v_one_1286_ = lean_unsigned_to_nat(1u);
v_n_1287_ = lean_nat_sub(v_x_1279_, v_one_1286_);
lean_dec(v_x_1279_);
v___x_1288_ = l_Lean_Expr_bindingBody_x21(v_x_1280_);
lean_dec_ref(v_x_1280_);
v_x_1279_ = v_n_1287_;
v_x_1280_ = v___x_1288_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorInduct(lean_object* v_v_1290_){
_start:
{
lean_object* v_toConstantVal_1291_; lean_object* v_type_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v_toConstantVal_1291_ = lean_ctor_get(v_v_1290_, 0);
v_type_1292_ = lean_ctor_get(v_toConstantVal_1291_, 2);
lean_inc_ref(v_type_1292_);
v___x_1293_ = l_Lean_RecursorVal_getMajorIdx(v_v_1290_);
lean_dec_ref(v_v_1290_);
v___x_1294_ = l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(v___x_1293_, v_type_1292_);
return v___x_1294_;
}
}
lean_object* l_Lean_QuotKind_ctorIdx___impl(uint8_t v_x_1295_){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = lean_box(v_x_1295_);
v___x_1297_ = lean_obj_tag_nat(v___x_1296_);
lean_dec(v___x_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT void l_Lean_QuotKind_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1295_ = stack[0].m_num;
lean_object* v_res_1298_;
v_res_1298_ = l_Lean_QuotKind_ctorIdx___impl(v_x_1295_);
stack->m_obj
 = v_res_1298_;
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___impl___boxed(lean_object* v_x_1299_){
_start:
{
uint8_t v_x_4__boxed_1300_; lean_object* v_res_1301_; 
v_x_4__boxed_1300_ = lean_unbox(v_x_1299_);
v_res_1301_ = l_Lean_QuotKind_ctorIdx___impl(v_x_4__boxed_1300_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg(lean_object* v_k_1302_){
_start:
{
lean_inc(v_k_1302_);
return v_k_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg___boxed(lean_object* v_k_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Lean_QuotKind_ctorElim___redArg(v_k_1303_);
lean_dec(v_k_1303_);
return v_res_1304_;
}
}
lean_object* l_Lean_QuotKind_ctorElim(lean_object* v_motive_1305_, lean_object* v_ctorIdx_1306_, uint8_t v_t_1307_, lean_object* v_h_1308_, lean_object* v_k_1309_){
_start:
{
lean_inc(v_k_1309_);
return v_k_1309_;
}
}
LEAN_EXPORT void l_Lean_QuotKind_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_1306_ = stack[1].m_obj;
uint8_t v_t_1307_ = stack[2].m_num;
lean_object* v_k_1309_ = stack[4].m_obj;
lean_object* v_res_1310_;
v_res_1310_ = l_Lean_QuotKind_ctorElim(lean_box(0), v_ctorIdx_1306_, v_t_1307_, lean_box(0), v_k_1309_);
stack->m_obj
 = v_res_1310_;
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___boxed(lean_object* v_motive_1311_, lean_object* v_ctorIdx_1312_, lean_object* v_t_1313_, lean_object* v_h_1314_, lean_object* v_k_1315_){
_start:
{
uint8_t v_t_boxed_1316_; lean_object* v_res_1317_; 
v_t_boxed_1316_ = lean_unbox(v_t_1313_);
v_res_1317_ = l_Lean_QuotKind_ctorElim(v_motive_1311_, v_ctorIdx_1312_, v_t_boxed_1316_, v_h_1314_, v_k_1315_);
lean_dec(v_k_1315_);
lean_dec(v_ctorIdx_1312_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg(lean_object* v_type_1318_){
_start:
{
lean_inc(v_type_1318_);
return v_type_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg___boxed(lean_object* v_type_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_QuotKind_type_elim___redArg(v_type_1319_);
lean_dec(v_type_1319_);
return v_res_1320_;
}
}
lean_object* l_Lean_QuotKind_type_elim(lean_object* v_motive_1321_, uint8_t v_t_1322_, lean_object* v_h_1323_, lean_object* v_type_1324_){
_start:
{
lean_inc(v_type_1324_);
return v_type_1324_;
}
}
LEAN_EXPORT void l_Lean_QuotKind_type_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1322_ = stack[1].m_num;
lean_object* v_type_1324_ = stack[3].m_obj;
lean_object* v_res_1325_;
v_res_1325_ = l_Lean_QuotKind_type_elim(lean_box(0), v_t_1322_, lean_box(0), v_type_1324_);
stack->m_obj
 = v_res_1325_;
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
lean_object* l_Lean_QuotKind_ctor_elim(lean_object* v_motive_1335_, uint8_t v_t_1336_, lean_object* v_h_1337_, lean_object* v_ctor_1338_){
_start:
{
lean_inc(v_ctor_1338_);
return v_ctor_1338_;
}
}
LEAN_EXPORT void l_Lean_QuotKind_ctor_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1336_ = stack[1].m_num;
lean_object* v_ctor_1338_ = stack[3].m_obj;
lean_object* v_res_1339_;
v_res_1339_ = l_Lean_QuotKind_ctor_elim(lean_box(0), v_t_1336_, lean_box(0), v_ctor_1338_);
stack->m_obj
 = v_res_1339_;
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___boxed(lean_object* v_motive_1340_, lean_object* v_t_1341_, lean_object* v_h_1342_, lean_object* v_ctor_1343_){
_start:
{
uint8_t v_t_boxed_1344_; lean_object* v_res_1345_; 
v_t_boxed_1344_ = lean_unbox(v_t_1341_);
v_res_1345_ = l_Lean_QuotKind_ctor_elim(v_motive_1340_, v_t_boxed_1344_, v_h_1342_, v_ctor_1343_);
lean_dec(v_ctor_1343_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg(lean_object* v_lift_1346_){
_start:
{
lean_inc(v_lift_1346_);
return v_lift_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg___boxed(lean_object* v_lift_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Lean_QuotKind_lift_elim___redArg(v_lift_1347_);
lean_dec(v_lift_1347_);
return v_res_1348_;
}
}
lean_object* l_Lean_QuotKind_lift_elim(lean_object* v_motive_1349_, uint8_t v_t_1350_, lean_object* v_h_1351_, lean_object* v_lift_1352_){
_start:
{
lean_inc(v_lift_1352_);
return v_lift_1352_;
}
}
LEAN_EXPORT void l_Lean_QuotKind_lift_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1350_ = stack[1].m_num;
lean_object* v_lift_1352_ = stack[3].m_obj;
lean_object* v_res_1353_;
v_res_1353_ = l_Lean_QuotKind_lift_elim(lean_box(0), v_t_1350_, lean_box(0), v_lift_1352_);
stack->m_obj
 = v_res_1353_;
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___boxed(lean_object* v_motive_1354_, lean_object* v_t_1355_, lean_object* v_h_1356_, lean_object* v_lift_1357_){
_start:
{
uint8_t v_t_boxed_1358_; lean_object* v_res_1359_; 
v_t_boxed_1358_ = lean_unbox(v_t_1355_);
v_res_1359_ = l_Lean_QuotKind_lift_elim(v_motive_1354_, v_t_boxed_1358_, v_h_1356_, v_lift_1357_);
lean_dec(v_lift_1357_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg(lean_object* v_ind_1360_){
_start:
{
lean_inc(v_ind_1360_);
return v_ind_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg___boxed(lean_object* v_ind_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lean_QuotKind_ind_elim___redArg(v_ind_1361_);
lean_dec(v_ind_1361_);
return v_res_1362_;
}
}
lean_object* l_Lean_QuotKind_ind_elim(lean_object* v_motive_1363_, uint8_t v_t_1364_, lean_object* v_h_1365_, lean_object* v_ind_1366_){
_start:
{
lean_inc(v_ind_1366_);
return v_ind_1366_;
}
}
LEAN_EXPORT void l_Lean_QuotKind_ind_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_1364_ = stack[1].m_num;
lean_object* v_ind_1366_ = stack[3].m_obj;
lean_object* v_res_1367_;
v_res_1367_ = l_Lean_QuotKind_ind_elim(lean_box(0), v_t_1364_, lean_box(0), v_ind_1366_);
stack->m_obj
 = v_res_1367_;
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___boxed(lean_object* v_motive_1368_, lean_object* v_t_1369_, lean_object* v_h_1370_, lean_object* v_ind_1371_){
_start:
{
uint8_t v_t_boxed_1372_; lean_object* v_res_1373_; 
v_t_boxed_1372_ = lean_unbox(v_t_1369_);
v_res_1373_ = l_Lean_QuotKind_ind_elim(v_motive_1368_, v_t_boxed_1372_, v_h_1370_, v_ind_1371_);
lean_dec(v_ind_1371_);
return v_res_1373_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind_default(void){
_start:
{
uint8_t v___x_1374_; 
v___x_1374_ = 0;
return v___x_1374_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind(void){
_start:
{
uint8_t v___x_1375_; 
v___x_1375_ = 0;
return v___x_1375_;
}
}
uint8_t l_Lean_instBEqQuotKind_beq(uint8_t v_x_1376_, uint8_t v_y_1377_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1378_ = lean_box(v_x_1376_);
v___x_1379_ = lean_obj_tag_nat(v___x_1378_);
lean_dec(v___x_1378_);
v___x_1380_ = lean_box(v_y_1377_);
v___x_1381_ = lean_obj_tag_nat(v___x_1380_);
lean_dec(v___x_1380_);
v___x_1382_ = lean_nat_dec_eq(v___x_1379_, v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT void l_Lean_instBEqQuotKind_beq_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1376_ = stack[0].m_num;
uint8_t v_y_1377_ = stack[1].m_num;
uint8_t v_res_1383_;
v_res_1383_ = l_Lean_instBEqQuotKind_beq(v_x_1376_, v_y_1377_);
stack->m_num = v_res_1383_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqQuotKind_beq___boxed(lean_object* v_x_1384_, lean_object* v_y_1385_){
_start:
{
uint8_t v_x_24__boxed_1386_; uint8_t v_y_25__boxed_1387_; uint8_t v_res_1388_; lean_object* v_r_1389_; 
v_x_24__boxed_1386_ = lean_unbox(v_x_1384_);
v_y_25__boxed_1387_ = lean_unbox(v_y_1385_);
v_res_1388_ = l_Lean_instBEqQuotKind_beq(v_x_24__boxed_1386_, v_y_25__boxed_1387_);
v_r_1389_ = lean_box(v_res_1388_);
return v_r_1389_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default___closed__0(void){
_start:
{
uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = 0;
v___x_1393_ = l_Lean_instInhabitedConstantVal_default;
v___x_1394_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*1, v___x_1392_);
return v___x_1394_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default(void){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_obj_once(&l_Lean_instInhabitedQuotVal_default___closed__0, &l_Lean_instInhabitedQuotVal_default___closed__0_once, _init_l_Lean_instInhabitedQuotVal_default___closed__0);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal(void){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_instInhabitedQuotVal_default;
return v___x_1396_;
}
}
uint8_t l_Lean_instBEqQuotVal_beq(lean_object* v_x_1397_, lean_object* v_x_1398_){
_start:
{
lean_object* v_toConstantVal_1399_; uint8_t v_kind_1400_; lean_object* v_toConstantVal_1401_; uint8_t v_kind_1402_; uint8_t v___x_1403_; 
v_toConstantVal_1399_ = lean_ctor_get(v_x_1397_, 0);
v_kind_1400_ = lean_ctor_get_uint8(v_x_1397_, sizeof(void*)*1);
v_toConstantVal_1401_ = lean_ctor_get(v_x_1398_, 0);
v_kind_1402_ = lean_ctor_get_uint8(v_x_1398_, sizeof(void*)*1);
v___x_1403_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1399_, v_toConstantVal_1401_);
if (v___x_1403_ == 0)
{
return v___x_1403_;
}
else
{
uint8_t v___x_1404_; 
v___x_1404_ = l_Lean_instBEqQuotKind_beq(v_kind_1400_, v_kind_1402_);
return v___x_1404_;
}
}
}
LEAN_EXPORT void l_Lean_instBEqQuotVal_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1397_ = stack[0].m_obj;
lean_object* v_x_1398_ = stack[1].m_obj;
uint8_t v_res_1405_;
v_res_1405_ = l_Lean_instBEqQuotVal_beq(v_x_1397_, v_x_1398_);
stack->m_num = v_res_1405_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqQuotVal_beq___boxed(lean_object* v_x_1406_, lean_object* v_x_1407_){
_start:
{
uint8_t v_res_1408_; lean_object* v_r_1409_; 
v_res_1408_ = l_Lean_instBEqQuotVal_beq(v_x_1406_, v_x_1407_);
lean_dec_ref(v_x_1407_);
lean_dec_ref(v_x_1406_);
v_r_1409_ = lean_box(v_res_1408_);
return v_r_1409_;
}
}
lean_object* lean_mk_quot_val(lean_object* v_name_1412_, lean_object* v_levelParams_1413_, lean_object* v_type_1414_, uint8_t v_kind_1415_){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1416_, 0, v_name_1412_);
lean_ctor_set(v___x_1416_, 1, v_levelParams_1413_);
lean_ctor_set(v___x_1416_, 2, v_type_1414_);
v___x_1417_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1417_, 0, v___x_1416_);
lean_ctor_set_uint8(v___x_1417_, sizeof(void*)*1, v_kind_1415_);
return v___x_1417_;
}
}
LEAN_EXPORT void lean_mk_quot_val_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1412_ = stack[0].m_obj;
lean_object* v_levelParams_1413_ = stack[1].m_obj;
lean_object* v_type_1414_ = stack[2].m_obj;
uint8_t v_kind_1415_ = stack[3].m_num;
lean_object* v_res_1418_;
v_res_1418_ = lean_mk_quot_val(v_name_1412_, v_levelParams_1413_, v_type_1414_, v_kind_1415_);
stack->m_obj
 = v_res_1418_;
}
LEAN_EXPORT lean_object* l_Lean_mkQuotValEx___boxed(lean_object* v_name_1419_, lean_object* v_levelParams_1420_, lean_object* v_type_1421_, lean_object* v_kind_1422_){
_start:
{
uint8_t v_kind_boxed_1423_; lean_object* v_res_1424_; 
v_kind_boxed_1423_ = lean_unbox(v_kind_1422_);
v_res_1424_ = lean_mk_quot_val(v_name_1419_, v_levelParams_1420_, v_type_1421_, v_kind_boxed_1423_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___impl(lean_object* v_x_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_obj_tag_nat(v_x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___impl___boxed(lean_object* v_x_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Lean_ConstantInfo_ctorIdx___impl(v_x_1427_);
lean_dec_ref(v_x_1427_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___redArg(lean_object* v_t_1429_, lean_object* v_k_1430_){
_start:
{
lean_object* v_val_1431_; lean_object* v___x_1432_; 
v_val_1431_ = lean_ctor_get(v_t_1429_, 0);
lean_inc_ref(v_val_1431_);
lean_dec_ref(v_t_1429_);
v___x_1432_ = lean_apply_1(v_k_1430_, v_val_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim(lean_object* v_motive_1433_, lean_object* v_ctorIdx_1434_, lean_object* v_t_1435_, lean_object* v_h_1436_, lean_object* v_k_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1435_, v_k_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___boxed(lean_object* v_motive_1439_, lean_object* v_ctorIdx_1440_, lean_object* v_t_1441_, lean_object* v_h_1442_, lean_object* v_k_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_ConstantInfo_ctorElim(v_motive_1439_, v_ctorIdx_1440_, v_t_1441_, v_h_1442_, v_k_1443_);
lean_dec(v_ctorIdx_1440_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim___redArg(lean_object* v_t_1445_, lean_object* v_axiomInfo_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1445_, v_axiomInfo_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim(lean_object* v_motive_1448_, lean_object* v_t_1449_, lean_object* v_h_1450_, lean_object* v_axiomInfo_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1449_, v_axiomInfo_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim___redArg(lean_object* v_t_1453_, lean_object* v_defnInfo_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1453_, v_defnInfo_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim(lean_object* v_motive_1456_, lean_object* v_t_1457_, lean_object* v_h_1458_, lean_object* v_defnInfo_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1457_, v_defnInfo_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim___redArg(lean_object* v_t_1461_, lean_object* v_thmInfo_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1461_, v_thmInfo_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim(lean_object* v_motive_1464_, lean_object* v_t_1465_, lean_object* v_h_1466_, lean_object* v_thmInfo_1467_){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1465_, v_thmInfo_1467_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim___redArg(lean_object* v_t_1469_, lean_object* v_opaqueInfo_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1469_, v_opaqueInfo_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim(lean_object* v_motive_1472_, lean_object* v_t_1473_, lean_object* v_h_1474_, lean_object* v_opaqueInfo_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1473_, v_opaqueInfo_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim___redArg(lean_object* v_t_1477_, lean_object* v_quotInfo_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1477_, v_quotInfo_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim(lean_object* v_motive_1480_, lean_object* v_t_1481_, lean_object* v_h_1482_, lean_object* v_quotInfo_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1481_, v_quotInfo_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim___redArg(lean_object* v_t_1485_, lean_object* v_inductInfo_1486_){
_start:
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1485_, v_inductInfo_1486_);
return v___x_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim(lean_object* v_motive_1488_, lean_object* v_t_1489_, lean_object* v_h_1490_, lean_object* v_inductInfo_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1489_, v_inductInfo_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim___redArg(lean_object* v_t_1493_, lean_object* v_ctorInfo_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1493_, v_ctorInfo_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim(lean_object* v_motive_1496_, lean_object* v_t_1497_, lean_object* v_h_1498_, lean_object* v_ctorInfo_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1497_, v_ctorInfo_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim___redArg(lean_object* v_t_1501_, lean_object* v_recInfo_1502_){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1501_, v_recInfo_1502_);
return v___x_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim(lean_object* v_motive_1504_, lean_object* v_t_1505_, lean_object* v_h_1506_, lean_object* v_recInfo_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1505_, v_recInfo_1507_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default___closed__0(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = l_Lean_instInhabitedAxiomVal_default;
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default(void){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_obj_once(&l_Lean_instInhabitedConstantInfo_default___closed__0, &l_Lean_instInhabitedConstantInfo_default___closed__0_once, _init_l_Lean_instInhabitedConstantInfo_default___closed__0);
return v___x_1511_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo(void){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_instInhabitedConstantInfo_default;
return v___x_1512_;
}
}
uint8_t l_Lean_instBEqConstantInfo_beq(lean_object* v_x_1513_, lean_object* v_x_1514_){
_start:
{
switch(lean_obj_tag(v_x_1513_))
{
case 0:
{
if (lean_obj_tag(v_x_1514_) == 0)
{
lean_object* v_val_1515_; lean_object* v_val_1516_; uint8_t v___x_1517_; 
v_val_1515_ = lean_ctor_get(v_x_1513_, 0);
v_val_1516_ = lean_ctor_get(v_x_1514_, 0);
v___x_1517_ = l_Lean_instBEqAxiomVal_beq(v_val_1515_, v_val_1516_);
return v___x_1517_;
}
else
{
uint8_t v___x_1518_; 
v___x_1518_ = 0;
return v___x_1518_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1514_) == 1)
{
lean_object* v_val_1519_; lean_object* v_val_1520_; uint8_t v___x_1521_; 
v_val_1519_ = lean_ctor_get(v_x_1513_, 0);
v_val_1520_ = lean_ctor_get(v_x_1514_, 0);
v___x_1521_ = l_Lean_instBEqDefinitionVal_beq(v_val_1519_, v_val_1520_);
return v___x_1521_;
}
else
{
uint8_t v___x_1522_; 
v___x_1522_ = 0;
return v___x_1522_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1514_) == 2)
{
lean_object* v_val_1523_; lean_object* v_val_1524_; uint8_t v___x_1525_; 
v_val_1523_ = lean_ctor_get(v_x_1513_, 0);
v_val_1524_ = lean_ctor_get(v_x_1514_, 0);
v___x_1525_ = l_Lean_instBEqTheoremVal_beq(v_val_1523_, v_val_1524_);
return v___x_1525_;
}
else
{
uint8_t v___x_1526_; 
v___x_1526_ = 0;
return v___x_1526_;
}
}
case 3:
{
if (lean_obj_tag(v_x_1514_) == 3)
{
lean_object* v_val_1527_; lean_object* v_val_1528_; uint8_t v___x_1529_; 
v_val_1527_ = lean_ctor_get(v_x_1513_, 0);
v_val_1528_ = lean_ctor_get(v_x_1514_, 0);
v___x_1529_ = l_Lean_instBEqOpaqueVal_beq(v_val_1527_, v_val_1528_);
return v___x_1529_;
}
else
{
uint8_t v___x_1530_; 
v___x_1530_ = 0;
return v___x_1530_;
}
}
case 4:
{
if (lean_obj_tag(v_x_1514_) == 4)
{
lean_object* v_val_1531_; lean_object* v_val_1532_; uint8_t v___x_1533_; 
v_val_1531_ = lean_ctor_get(v_x_1513_, 0);
v_val_1532_ = lean_ctor_get(v_x_1514_, 0);
v___x_1533_ = l_Lean_instBEqQuotVal_beq(v_val_1531_, v_val_1532_);
return v___x_1533_;
}
else
{
uint8_t v___x_1534_; 
v___x_1534_ = 0;
return v___x_1534_;
}
}
case 5:
{
if (lean_obj_tag(v_x_1514_) == 5)
{
lean_object* v_val_1535_; lean_object* v_val_1536_; uint8_t v___x_1537_; 
v_val_1535_ = lean_ctor_get(v_x_1513_, 0);
v_val_1536_ = lean_ctor_get(v_x_1514_, 0);
v___x_1537_ = l_Lean_instBEqInductiveVal_beq(v_val_1535_, v_val_1536_);
return v___x_1537_;
}
else
{
uint8_t v___x_1538_; 
v___x_1538_ = 0;
return v___x_1538_;
}
}
case 6:
{
if (lean_obj_tag(v_x_1514_) == 6)
{
lean_object* v_val_1539_; lean_object* v_val_1540_; uint8_t v___x_1541_; 
v_val_1539_ = lean_ctor_get(v_x_1513_, 0);
v_val_1540_ = lean_ctor_get(v_x_1514_, 0);
v___x_1541_ = l_Lean_instBEqConstructorVal_beq(v_val_1539_, v_val_1540_);
return v___x_1541_;
}
else
{
uint8_t v___x_1542_; 
v___x_1542_ = 0;
return v___x_1542_;
}
}
default: 
{
if (lean_obj_tag(v_x_1514_) == 7)
{
lean_object* v_val_1543_; lean_object* v_val_1544_; uint8_t v___x_1545_; 
v_val_1543_ = lean_ctor_get(v_x_1513_, 0);
v_val_1544_ = lean_ctor_get(v_x_1514_, 0);
v___x_1545_ = l_Lean_instBEqRecursorVal_beq(v_val_1543_, v_val_1544_);
return v___x_1545_;
}
else
{
uint8_t v___x_1546_; 
v___x_1546_ = 0;
return v___x_1546_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instBEqConstantInfo_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1513_ = stack[0].m_obj;
lean_object* v_x_1514_ = stack[1].m_obj;
uint8_t v_res_1547_;
v_res_1547_ = l_Lean_instBEqConstantInfo_beq(v_x_1513_, v_x_1514_);
stack->m_num = v_res_1547_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstantInfo_beq___boxed(lean_object* v_x_1548_, lean_object* v_x_1549_){
_start:
{
uint8_t v_res_1550_; lean_object* v_r_1551_; 
v_res_1550_ = l_Lean_instBEqConstantInfo_beq(v_x_1548_, v_x_1549_);
lean_dec_ref(v_x_1549_);
lean_dec_ref(v_x_1548_);
v_r_1551_ = lean_box(v_res_1550_);
return v_r_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object* v_x_1554_){
_start:
{
lean_object* v_val_1555_; lean_object* v_toConstantVal_1556_; 
v_val_1555_ = lean_ctor_get(v_x_1554_, 0);
v_toConstantVal_1556_ = lean_ctor_get(v_val_1555_, 0);
lean_inc_ref(v_toConstantVal_1556_);
return v_toConstantVal_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object* v_x_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Lean_ConstantInfo_toConstantVal(v_x_1557_);
lean_dec_ref(v_x_1557_);
return v_res_1558_;
}
}
uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object* v_x_1559_){
_start:
{
switch(lean_obj_tag(v_x_1559_))
{
case 0:
{
lean_object* v_val_1560_; uint8_t v_isUnsafe_1561_; 
v_val_1560_ = lean_ctor_get(v_x_1559_, 0);
v_isUnsafe_1561_ = lean_ctor_get_uint8(v_val_1560_, sizeof(void*)*1);
return v_isUnsafe_1561_;
}
case 1:
{
lean_object* v_val_1562_; uint8_t v_safety_1563_; uint8_t v___x_1564_; uint8_t v___x_1565_; 
v_val_1562_ = lean_ctor_get(v_x_1559_, 0);
v_safety_1563_ = lean_ctor_get_uint8(v_val_1562_, sizeof(void*)*4);
v___x_1564_ = 0;
v___x_1565_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1563_, v___x_1564_);
return v___x_1565_;
}
case 3:
{
lean_object* v_val_1566_; uint8_t v_isUnsafe_1567_; 
v_val_1566_ = lean_ctor_get(v_x_1559_, 0);
v_isUnsafe_1567_ = lean_ctor_get_uint8(v_val_1566_, sizeof(void*)*3);
return v_isUnsafe_1567_;
}
case 5:
{
lean_object* v_val_1568_; uint8_t v_isUnsafe_1569_; 
v_val_1568_ = lean_ctor_get(v_x_1559_, 0);
v_isUnsafe_1569_ = lean_ctor_get_uint8(v_val_1568_, sizeof(void*)*6 + 1);
return v_isUnsafe_1569_;
}
case 6:
{
lean_object* v_val_1570_; uint8_t v_isUnsafe_1571_; 
v_val_1570_ = lean_ctor_get(v_x_1559_, 0);
v_isUnsafe_1571_ = lean_ctor_get_uint8(v_val_1570_, sizeof(void*)*5);
return v_isUnsafe_1571_;
}
case 7:
{
lean_object* v_val_1572_; uint8_t v_isUnsafe_1573_; 
v_val_1572_ = lean_ctor_get(v_x_1559_, 0);
v_isUnsafe_1573_ = lean_ctor_get_uint8(v_val_1572_, sizeof(void*)*7 + 1);
return v_isUnsafe_1573_;
}
default: 
{
uint8_t v___x_1574_; 
v___x_1574_ = 0;
return v___x_1574_;
}
}
}
}
LEAN_EXPORT void l_Lean_ConstantInfo_isUnsafe_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1559_ = stack[0].m_obj;
uint8_t v_res_1575_;
v_res_1575_ = l_Lean_ConstantInfo_isUnsafe(v_x_1559_);
stack->m_num = v_res_1575_;
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isUnsafe___boxed(lean_object* v_x_1576_){
_start:
{
uint8_t v_res_1577_; lean_object* v_r_1578_; 
v_res_1577_ = l_Lean_ConstantInfo_isUnsafe(v_x_1576_);
lean_dec_ref(v_x_1576_);
v_r_1578_ = lean_box(v_res_1577_);
return v_r_1578_;
}
}
uint8_t l_Lean_ConstantInfo_isPartial(lean_object* v_x_1579_){
_start:
{
if (lean_obj_tag(v_x_1579_) == 1)
{
lean_object* v_val_1580_; uint8_t v_safety_1581_; uint8_t v___x_1582_; uint8_t v___x_1583_; 
v_val_1580_ = lean_ctor_get(v_x_1579_, 0);
v_safety_1581_ = lean_ctor_get_uint8(v_val_1580_, sizeof(void*)*4);
v___x_1582_ = 2;
v___x_1583_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1581_, v___x_1582_);
return v___x_1583_;
}
else
{
uint8_t v___x_1584_; 
v___x_1584_ = 0;
return v___x_1584_;
}
}
}
LEAN_EXPORT void l_Lean_ConstantInfo_isPartial_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1579_ = stack[0].m_obj;
uint8_t v_res_1585_;
v_res_1585_ = l_Lean_ConstantInfo_isPartial(v_x_1579_);
stack->m_num = v_res_1585_;
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isPartial___boxed(lean_object* v_x_1586_){
_start:
{
uint8_t v_res_1587_; lean_object* v_r_1588_; 
v_res_1587_ = l_Lean_ConstantInfo_isPartial(v_x_1586_);
lean_dec_ref(v_x_1586_);
v_r_1588_ = lean_box(v_res_1587_);
return v_r_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name(lean_object* v_d_1589_){
_start:
{
lean_object* v___x_1590_; lean_object* v_name_1591_; 
v___x_1590_ = l_Lean_ConstantInfo_toConstantVal(v_d_1589_);
v_name_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_name_1591_);
lean_dec_ref(v___x_1590_);
return v_name_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name___boxed(lean_object* v_d_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_ConstantInfo_name(v_d_1592_);
lean_dec_ref(v_d_1592_);
return v_res_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams(lean_object* v_d_1594_){
_start:
{
lean_object* v___x_1595_; lean_object* v_levelParams_1596_; 
v___x_1595_ = l_Lean_ConstantInfo_toConstantVal(v_d_1594_);
v_levelParams_1596_ = lean_ctor_get(v___x_1595_, 1);
lean_inc(v_levelParams_1596_);
lean_dec_ref(v___x_1595_);
return v_levelParams_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams___boxed(lean_object* v_d_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Lean_ConstantInfo_levelParams(v_d_1597_);
lean_dec_ref(v_d_1597_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object* v_d_1599_){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1600_ = l_Lean_ConstantInfo_levelParams(v_d_1599_);
v___x_1601_ = l_List_lengthTR___redArg(v___x_1600_);
lean_dec(v___x_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams___boxed(lean_object* v_d_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Lean_ConstantInfo_numLevelParams(v_d_1602_);
lean_dec_ref(v_d_1602_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type(lean_object* v_d_1604_){
_start:
{
lean_object* v___x_1605_; lean_object* v_type_1606_; 
v___x_1605_ = l_Lean_ConstantInfo_toConstantVal(v_d_1604_);
v_type_1606_ = lean_ctor_get(v___x_1605_, 2);
lean_inc_ref(v_type_1606_);
lean_dec_ref(v___x_1605_);
return v_type_1606_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type___boxed(lean_object* v_d_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_ConstantInfo_type(v_d_1607_);
lean_dec_ref(v_d_1607_);
return v_res_1608_;
}
}
lean_object* l_Lean_ConstantInfo_value_x3f(lean_object* v_info_1609_, uint8_t v_allowOpaque_1610_){
_start:
{
switch(lean_obj_tag(v_info_1609_))
{
case 1:
{
lean_object* v_val_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1619_; 
v_val_1611_ = lean_ctor_get(v_info_1609_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_info_1609_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1613_ = v_info_1609_;
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_val_1611_);
lean_dec(v_info_1609_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1619_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_value_1615_; lean_object* v___x_1617_; 
v_value_1615_ = lean_ctor_get(v_val_1611_, 1);
lean_inc_ref(v_value_1615_);
lean_dec_ref(v_val_1611_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v_value_1615_);
v___x_1617_ = v___x_1613_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_value_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
case 2:
{
lean_object* v_val_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1629_; 
v_val_1620_ = lean_ctor_get(v_info_1609_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v_info_1609_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1622_ = v_info_1609_;
v_isShared_1623_ = v_isSharedCheck_1629_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_val_1620_);
lean_dec(v_info_1609_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1629_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
if (v_allowOpaque_1610_ == 0)
{
lean_object* v___x_1624_; 
lean_del_object(v___x_1622_);
lean_dec_ref(v_val_1620_);
v___x_1624_ = lean_box(0);
return v___x_1624_;
}
else
{
lean_object* v_value_1625_; lean_object* v___x_1627_; 
v_value_1625_ = lean_ctor_get(v_val_1620_, 1);
lean_inc_ref(v_value_1625_);
lean_dec_ref(v_val_1620_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 1);
lean_ctor_set(v___x_1622_, 0, v_value_1625_);
v___x_1627_ = v___x_1622_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_value_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
case 3:
{
lean_object* v_val_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1639_; 
v_val_1630_ = lean_ctor_get(v_info_1609_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_info_1609_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1632_ = v_info_1609_;
v_isShared_1633_ = v_isSharedCheck_1639_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_val_1630_);
lean_dec(v_info_1609_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1639_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
if (v_allowOpaque_1610_ == 0)
{
lean_object* v___x_1634_; 
lean_del_object(v___x_1632_);
lean_dec_ref(v_val_1630_);
v___x_1634_ = lean_box(0);
return v___x_1634_;
}
else
{
lean_object* v_value_1635_; lean_object* v___x_1637_; 
v_value_1635_ = lean_ctor_get(v_val_1630_, 1);
lean_inc_ref(v_value_1635_);
lean_dec_ref(v_val_1630_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set_tag(v___x_1632_, 1);
lean_ctor_set(v___x_1632_, 0, v_value_1635_);
v___x_1637_ = v___x_1632_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v_value_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
}
default: 
{
lean_object* v___x_1640_; 
lean_dec_ref(v_info_1609_);
v___x_1640_ = lean_box(0);
return v___x_1640_;
}
}
}
}
LEAN_EXPORT void l_Lean_ConstantInfo_value_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_1609_ = stack[0].m_obj;
uint8_t v_allowOpaque_1610_ = stack[1].m_num;
lean_object* v_res_1641_;
v_res_1641_ = l_Lean_ConstantInfo_value_x3f(v_info_1609_, v_allowOpaque_1610_);
stack->m_obj
 = v_res_1641_;
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
uint8_t l_Lean_ConstantInfo_hasValue(lean_object* v_info_1646_, uint8_t v_allowOpaque_1647_){
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
LEAN_EXPORT void l_Lean_ConstantInfo_hasValue_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_1646_ = stack[0].m_obj;
uint8_t v_allowOpaque_1647_ = stack[1].m_num;
uint8_t v_res_1650_;
v_res_1650_ = l_Lean_ConstantInfo_hasValue(v_info_1646_, v_allowOpaque_1647_);
stack->m_num = v_res_1650_;
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object* v_info_1651_, lean_object* v_allowOpaque_1652_){
_start:
{
uint8_t v_allowOpaque_boxed_1653_; uint8_t v_res_1654_; lean_object* v_r_1655_; 
v_allowOpaque_boxed_1653_ = lean_unbox(v_allowOpaque_1652_);
v_res_1654_ = l_Lean_ConstantInfo_hasValue(v_info_1651_, v_allowOpaque_boxed_1653_);
lean_dec_ref(v_info_1651_);
v_r_1655_ = lean_box(v_res_1654_);
return v_r_1655_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(lean_object* v_msg_1656_){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = l_Lean_instInhabitedExpr;
v___x_1658_ = lean_panic_fn_borrowed(v___x_1657_, v_msg_1656_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__2(void){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v___x_1661_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1662_ = lean_unsigned_to_nat(62u);
v___x_1663_ = lean_unsigned_to_nat(485u);
v___x_1664_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1665_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1666_ = l_mkPanicMessageWithDecl(v___x_1665_, v___x_1664_, v___x_1663_, v___x_1662_, v___x_1661_);
return v___x_1666_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__3(void){
_start:
{
lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1667_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1668_ = lean_unsigned_to_nat(62u);
v___x_1669_ = lean_unsigned_to_nat(486u);
v___x_1670_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1671_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1672_ = l_mkPanicMessageWithDecl(v___x_1671_, v___x_1670_, v___x_1669_, v___x_1668_, v___x_1667_);
return v___x_1672_;
}
}
lean_object* l_Lean_ConstantInfo_value_x21(lean_object* v_info_1675_, uint8_t v_allowOpaque_1676_){
_start:
{
switch(lean_obj_tag(v_info_1675_))
{
case 1:
{
lean_object* v_val_1677_; lean_object* v_value_1678_; 
v_val_1677_ = lean_ctor_get(v_info_1675_, 0);
v_value_1678_ = lean_ctor_get(v_val_1677_, 1);
lean_inc_ref(v_value_1678_);
return v_value_1678_;
}
case 2:
{
if (v_allowOpaque_1676_ == 0)
{
lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1679_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__2, &l_Lean_ConstantInfo_value_x21___closed__2_once, _init_l_Lean_ConstantInfo_value_x21___closed__2);
v___x_1680_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1679_);
return v___x_1680_;
}
else
{
lean_object* v_val_1681_; lean_object* v_value_1682_; 
v_val_1681_ = lean_ctor_get(v_info_1675_, 0);
v_value_1682_ = lean_ctor_get(v_val_1681_, 1);
lean_inc_ref(v_value_1682_);
return v_value_1682_;
}
}
case 3:
{
if (v_allowOpaque_1676_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__3, &l_Lean_ConstantInfo_value_x21___closed__3_once, _init_l_Lean_ConstantInfo_value_x21___closed__3);
v___x_1684_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1683_);
return v___x_1684_;
}
else
{
lean_object* v_val_1685_; lean_object* v_value_1686_; 
v_val_1685_ = lean_ctor_get(v_info_1675_, 0);
v_value_1686_ = lean_ctor_get(v_val_1685_, 1);
lean_inc_ref(v_value_1686_);
return v_value_1686_;
}
}
default: 
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v___x_1687_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1688_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1689_ = lean_unsigned_to_nat(487u);
v___x_1690_ = lean_unsigned_to_nat(31u);
v___x_1691_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__4));
v___x_1692_ = l_Lean_ConstantInfo_name(v_info_1675_);
v___x_1693_ = 1;
v___x_1694_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1692_, v___x_1693_);
v___x_1695_ = lean_string_append(v___x_1691_, v___x_1694_);
lean_dec_ref(v___x_1694_);
v___x_1696_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__5));
v___x_1697_ = lean_string_append(v___x_1695_, v___x_1696_);
v___x_1698_ = l_mkPanicMessageWithDecl(v___x_1687_, v___x_1688_, v___x_1689_, v___x_1690_, v___x_1697_);
lean_dec_ref(v___x_1697_);
v___x_1699_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1698_);
return v___x_1699_;
}
}
}
}
LEAN_EXPORT void l_Lean_ConstantInfo_value_x21_0interp(lean_interpreter_value* stack)
{
lean_object* v_info_1675_ = stack[0].m_obj;
uint8_t v_allowOpaque_1676_ = stack[1].m_num;
lean_object* v_res_1700_;
v_res_1700_ = l_Lean_ConstantInfo_value_x21(v_info_1675_, v_allowOpaque_1676_);
stack->m_obj
 = v_res_1700_;
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21___boxed(lean_object* v_info_1701_, lean_object* v_allowOpaque_1702_){
_start:
{
uint8_t v_allowOpaque_boxed_1703_; lean_object* v_res_1704_; 
v_allowOpaque_boxed_1703_ = lean_unbox(v_allowOpaque_1702_);
v_res_1704_ = l_Lean_ConstantInfo_value_x21(v_info_1701_, v_allowOpaque_boxed_1703_);
lean_dec_ref(v_info_1701_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints(lean_object* v_x_1705_){
_start:
{
if (lean_obj_tag(v_x_1705_) == 1)
{
lean_object* v_val_1706_; lean_object* v_hints_1707_; 
v_val_1706_ = lean_ctor_get(v_x_1705_, 0);
v_hints_1707_ = lean_ctor_get(v_val_1706_, 2);
lean_inc(v_hints_1707_);
return v_hints_1707_;
}
else
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_box(0);
return v___x_1708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object* v_x_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_ConstantInfo_hints(v_x_1709_);
lean_dec_ref(v_x_1709_);
return v_res_1710_;
}
}
uint8_t l_Lean_ConstantInfo_isCtor(lean_object* v_x_1711_){
_start:
{
if (lean_obj_tag(v_x_1711_) == 6)
{
uint8_t v___x_1712_; 
v___x_1712_ = 1;
return v___x_1712_;
}
else
{
uint8_t v___x_1713_; 
v___x_1713_ = 0;
return v___x_1713_;
}
}
}
LEAN_EXPORT void l_Lean_ConstantInfo_isCtor_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1711_ = stack[0].m_obj;
uint8_t v_res_1714_;
v_res_1714_ = l_Lean_ConstantInfo_isCtor(v_x_1711_);
stack->m_num = v_res_1714_;
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isCtor___boxed(lean_object* v_x_1715_){
_start:
{
uint8_t v_res_1716_; lean_object* v_r_1717_; 
v_res_1716_ = l_Lean_ConstantInfo_isCtor(v_x_1715_);
lean_dec_ref(v_x_1715_);
v_r_1717_ = lean_box(v_res_1716_);
return v_r_1717_;
}
}
uint8_t l_Lean_ConstantInfo_isAxiom(lean_object* v_x_1718_){
_start:
{
if (lean_obj_tag(v_x_1718_) == 0)
{
uint8_t v___x_1719_; 
v___x_1719_ = 1;
return v___x_1719_;
}
else
{
uint8_t v___x_1720_; 
v___x_1720_ = 0;
return v___x_1720_;
}
}
}
LEAN_EXPORT void l_Lean_ConstantInfo_isAxiom_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1718_ = stack[0].m_obj;
uint8_t v_res_1721_;
v_res_1721_ = l_Lean_ConstantInfo_isAxiom(v_x_1718_);
stack->m_num = v_res_1721_;
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isAxiom___boxed(lean_object* v_x_1722_){
_start:
{
uint8_t v_res_1723_; lean_object* v_r_1724_; 
v_res_1723_ = l_Lean_ConstantInfo_isAxiom(v_x_1722_);
lean_dec_ref(v_x_1722_);
v_r_1724_ = lean_box(v_res_1723_);
return v_r_1724_;
}
}
uint8_t l_Lean_ConstantInfo_isInductive(lean_object* v_x_1725_){
_start:
{
if (lean_obj_tag(v_x_1725_) == 5)
{
uint8_t v___x_1726_; 
v___x_1726_ = 1;
return v___x_1726_;
}
else
{
uint8_t v___x_1727_; 
v___x_1727_ = 0;
return v___x_1727_;
}
}
}
LEAN_EXPORT void l_Lean_ConstantInfo_isInductive_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1725_ = stack[0].m_obj;
uint8_t v_res_1728_;
v_res_1728_ = l_Lean_ConstantInfo_isInductive(v_x_1725_);
stack->m_num = v_res_1728_;
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isInductive___boxed(lean_object* v_x_1729_){
_start:
{
uint8_t v_res_1730_; lean_object* v_r_1731_; 
v_res_1730_ = l_Lean_ConstantInfo_isInductive(v_x_1729_);
lean_dec_ref(v_x_1729_);
v_r_1731_ = lean_box(v_res_1730_);
return v_r_1731_;
}
}
uint8_t l_Lean_ConstantInfo_isDefinition(lean_object* v_x_1732_){
_start:
{
if (lean_obj_tag(v_x_1732_) == 1)
{
uint8_t v___x_1733_; 
v___x_1733_ = 1;
return v___x_1733_;
}
else
{
uint8_t v___x_1734_; 
v___x_1734_ = 0;
return v___x_1734_;
}
}
}
LEAN_EXPORT void l_Lean_ConstantInfo_isDefinition_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1732_ = stack[0].m_obj;
uint8_t v_res_1735_;
v_res_1735_ = l_Lean_ConstantInfo_isDefinition(v_x_1732_);
stack->m_num = v_res_1735_;
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isDefinition___boxed(lean_object* v_x_1736_){
_start:
{
uint8_t v_res_1737_; lean_object* v_r_1738_; 
v_res_1737_ = l_Lean_ConstantInfo_isDefinition(v_x_1736_);
lean_dec_ref(v_x_1736_);
v_r_1738_ = lean_box(v_res_1737_);
return v_r_1738_;
}
}
uint8_t l_Lean_ConstantInfo_isTheorem(lean_object* v_x_1739_){
_start:
{
if (lean_obj_tag(v_x_1739_) == 2)
{
uint8_t v___x_1740_; 
v___x_1740_ = 1;
return v___x_1740_;
}
else
{
uint8_t v___x_1741_; 
v___x_1741_ = 0;
return v___x_1741_;
}
}
}
LEAN_EXPORT void l_Lean_ConstantInfo_isTheorem_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1739_ = stack[0].m_obj;
uint8_t v_res_1742_;
v_res_1742_ = l_Lean_ConstantInfo_isTheorem(v_x_1739_);
stack->m_num = v_res_1742_;
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isTheorem___boxed(lean_object* v_x_1743_){
_start:
{
uint8_t v_res_1744_; lean_object* v_r_1745_; 
v_res_1744_ = l_Lean_ConstantInfo_isTheorem(v_x_1743_);
lean_dec_ref(v_x_1743_);
v_r_1745_ = lean_box(v_res_1744_);
return v_r_1745_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(lean_object* v_msg_1746_){
_start:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1747_ = l_Lean_instInhabitedInductiveVal_default;
v___x_1748_ = lean_panic_fn_borrowed(v___x_1747_, v_msg_1746_);
return v___x_1748_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1751_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__1));
v___x_1752_ = lean_unsigned_to_nat(9u);
v___x_1753_ = lean_unsigned_to_nat(515u);
v___x_1754_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__0));
v___x_1755_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1756_ = l_mkPanicMessageWithDecl(v___x_1755_, v___x_1754_, v___x_1753_, v___x_1752_, v___x_1751_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object* v_x_1757_){
_start:
{
if (lean_obj_tag(v_x_1757_) == 5)
{
lean_object* v_val_1758_; 
v_val_1758_ = lean_ctor_get(v_x_1757_, 0);
lean_inc_ref(v_val_1758_);
return v_val_1758_;
}
else
{
lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1759_ = lean_obj_once(&l_Lean_ConstantInfo_inductiveVal_x21___closed__2, &l_Lean_ConstantInfo_inductiveVal_x21___closed__2_once, _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2);
v___x_1760_ = l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(v___x_1759_);
return v___x_1760_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21___boxed(lean_object* v_x_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_ConstantInfo_inductiveVal_x21(v_x_1761_);
lean_dec_ref(v_x_1761_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all(lean_object* v_x_1763_){
_start:
{
switch(lean_obj_tag(v_x_1763_))
{
case 5:
{
lean_object* v_val_1764_; lean_object* v_all_1765_; 
v_val_1764_ = lean_ctor_get(v_x_1763_, 0);
v_all_1765_ = lean_ctor_get(v_val_1764_, 3);
lean_inc(v_all_1765_);
return v_all_1765_;
}
case 1:
{
lean_object* v_val_1766_; lean_object* v_all_1767_; 
v_val_1766_ = lean_ctor_get(v_x_1763_, 0);
v_all_1767_ = lean_ctor_get(v_val_1766_, 3);
lean_inc(v_all_1767_);
return v_all_1767_;
}
case 2:
{
lean_object* v_val_1768_; lean_object* v_all_1769_; 
v_val_1768_ = lean_ctor_get(v_x_1763_, 0);
v_all_1769_ = lean_ctor_get(v_val_1768_, 2);
lean_inc(v_all_1769_);
return v_all_1769_;
}
case 3:
{
lean_object* v_val_1770_; lean_object* v_all_1771_; 
v_val_1770_ = lean_ctor_get(v_x_1763_, 0);
v_all_1771_ = lean_ctor_get(v_val_1770_, 2);
lean_inc(v_all_1771_);
return v_all_1771_;
}
default: 
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = l_Lean_ConstantInfo_name(v_x_1763_);
v___x_1773_ = lean_box(0);
v___x_1774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1774_, 0, v___x_1772_);
lean_ctor_set(v___x_1774_, 1, v___x_1773_);
return v___x_1774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all___boxed(lean_object* v_x_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_ConstantInfo_all(v_x_1775_);
lean_dec_ref(v_x_1775_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecName(lean_object* v_declName_1777_){
_start:
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0));
v___x_1779_ = l_Lean_Name_str___override(v_declName_1777_, v___x_1778_);
return v___x_1779_;
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
