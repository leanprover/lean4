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
LEAN_EXPORT uint8_t lean_axiom_val_is_unsafe(lean_object* v_v_206_){
_start:
{
uint8_t v_isUnsafe_207_; 
v_isUnsafe_207_ = lean_ctor_get_uint8(v_v_206_, sizeof(void*)*1);
lean_dec_ref(v_v_206_);
return v_isUnsafe_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_AxiomVal_isUnsafeEx___boxed(lean_object* v_v_208_){
_start:
{
uint8_t v_res_209_; lean_object* v_r_210_; 
v_res_209_ = lean_axiom_val_is_unsafe(v_v_208_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorIdx___impl(uint8_t v_x_211_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_box(v_x_211_);
v___x_213_ = lean_obj_tag_nat(v___x_212_);
lean_dec(v___x_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorIdx___impl___boxed(lean_object* v_x_214_){
_start:
{
uint8_t v_x_4__boxed_215_; lean_object* v_res_216_; 
v_x_4__boxed_215_ = lean_unbox(v_x_214_);
v_res_216_ = l_Lean_DefinitionSafety_ctorIdx___impl(v_x_4__boxed_215_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg(lean_object* v_k_217_){
_start:
{
lean_inc(v_k_217_);
return v_k_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___redArg___boxed(lean_object* v_k_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_DefinitionSafety_ctorElim___redArg(v_k_218_);
lean_dec(v_k_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim(lean_object* v_motive_220_, lean_object* v_ctorIdx_221_, uint8_t v_t_222_, lean_object* v_h_223_, lean_object* v_k_224_){
_start:
{
lean_inc(v_k_224_);
return v_k_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_ctorElim___boxed(lean_object* v_motive_225_, lean_object* v_ctorIdx_226_, lean_object* v_t_227_, lean_object* v_h_228_, lean_object* v_k_229_){
_start:
{
uint8_t v_t_boxed_230_; lean_object* v_res_231_; 
v_t_boxed_230_ = lean_unbox(v_t_227_);
v_res_231_ = l_Lean_DefinitionSafety_ctorElim(v_motive_225_, v_ctorIdx_226_, v_t_boxed_230_, v_h_228_, v_k_229_);
lean_dec(v_k_229_);
lean_dec(v_ctorIdx_226_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___redArg(lean_object* v_unsafe_232_){
_start:
{
lean_inc(v_unsafe_232_);
return v_unsafe_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___redArg___boxed(lean_object* v_unsafe_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_DefinitionSafety_unsafe_elim___redArg(v_unsafe_233_);
lean_dec(v_unsafe_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim(lean_object* v_motive_235_, uint8_t v_t_236_, lean_object* v_h_237_, lean_object* v_unsafe_238_){
_start:
{
lean_inc(v_unsafe_238_);
return v_unsafe_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_unsafe_elim___boxed(lean_object* v_motive_239_, lean_object* v_t_240_, lean_object* v_h_241_, lean_object* v_unsafe_242_){
_start:
{
uint8_t v_t_boxed_243_; lean_object* v_res_244_; 
v_t_boxed_243_ = lean_unbox(v_t_240_);
v_res_244_ = l_Lean_DefinitionSafety_unsafe_elim(v_motive_239_, v_t_boxed_243_, v_h_241_, v_unsafe_242_);
lean_dec(v_unsafe_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg(lean_object* v_safe_245_){
_start:
{
lean_inc(v_safe_245_);
return v_safe_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___redArg___boxed(lean_object* v_safe_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_DefinitionSafety_safe_elim___redArg(v_safe_246_);
lean_dec(v_safe_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim(lean_object* v_motive_248_, uint8_t v_t_249_, lean_object* v_h_250_, lean_object* v_safe_251_){
_start:
{
lean_inc(v_safe_251_);
return v_safe_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_safe_elim___boxed(lean_object* v_motive_252_, lean_object* v_t_253_, lean_object* v_h_254_, lean_object* v_safe_255_){
_start:
{
uint8_t v_t_boxed_256_; lean_object* v_res_257_; 
v_t_boxed_256_ = lean_unbox(v_t_253_);
v_res_257_ = l_Lean_DefinitionSafety_safe_elim(v_motive_252_, v_t_boxed_256_, v_h_254_, v_safe_255_);
lean_dec(v_safe_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg(lean_object* v_partial_258_){
_start:
{
lean_inc(v_partial_258_);
return v_partial_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___redArg___boxed(lean_object* v_partial_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_DefinitionSafety_partial_elim___redArg(v_partial_259_);
lean_dec(v_partial_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim(lean_object* v_motive_261_, uint8_t v_t_262_, lean_object* v_h_263_, lean_object* v_partial_264_){
_start:
{
lean_inc(v_partial_264_);
return v_partial_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionSafety_partial_elim___boxed(lean_object* v_motive_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_partial_268_){
_start:
{
uint8_t v_t_boxed_269_; lean_object* v_res_270_; 
v_t_boxed_269_ = lean_unbox(v_t_266_);
v_res_270_ = l_Lean_DefinitionSafety_partial_elim(v_motive_265_, v_t_boxed_269_, v_h_267_, v_partial_268_);
lean_dec(v_partial_268_);
return v_res_270_;
}
}
static uint8_t _init_l_Lean_instInhabitedDefinitionSafety_default(void){
_start:
{
uint8_t v___x_271_; 
v___x_271_ = 0;
return v___x_271_;
}
}
static uint8_t _init_l_Lean_instInhabitedDefinitionSafety(void){
_start:
{
uint8_t v___x_272_; 
v___x_272_ = 0;
return v___x_272_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t v_x_273_, uint8_t v_y_274_){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_275_ = lean_box(v_x_273_);
v___x_276_ = lean_obj_tag_nat(v___x_275_);
lean_dec(v___x_275_);
v___x_277_ = lean_box(v_y_274_);
v___x_278_ = lean_obj_tag_nat(v___x_277_);
lean_dec(v___x_277_);
v___x_279_ = lean_nat_dec_eq(v___x_276_, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionSafety_beq___boxed(lean_object* v_x_280_, lean_object* v_y_281_){
_start:
{
uint8_t v_x_24__boxed_282_; uint8_t v_y_25__boxed_283_; uint8_t v_res_284_; lean_object* v_r_285_; 
v_x_24__boxed_282_ = lean_unbox(v_x_280_);
v_y_25__boxed_283_ = lean_unbox(v_y_281_);
v_res_284_ = l_Lean_instBEqDefinitionSafety_beq(v_x_24__boxed_282_, v_y_25__boxed_283_);
v_r_285_ = lean_box(v_res_284_);
return v_r_285_;
}
}
static lean_object* _init_l_Lean_instReprDefinitionSafety_repr___closed__6(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(2u);
v___x_298_ = lean_nat_to_int(v___x_297_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_instReprDefinitionSafety_repr___closed__7(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lean_nat_to_int(v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDefinitionSafety_repr(uint8_t v_x_301_, lean_object* v_prec_302_){
_start:
{
lean_object* v___y_304_; lean_object* v___y_311_; lean_object* v___y_318_; 
switch(v_x_301_)
{
case 0:
{
lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(1024u);
v___x_325_ = lean_nat_dec_le(v___x_324_, v_prec_302_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; 
v___x_326_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_304_ = v___x_326_;
goto v___jp_303_;
}
else
{
lean_object* v___x_327_; 
v___x_327_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_304_ = v___x_327_;
goto v___jp_303_;
}
}
case 1:
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = lean_unsigned_to_nat(1024u);
v___x_329_ = lean_nat_dec_le(v___x_328_, v_prec_302_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
v___x_330_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_311_ = v___x_330_;
goto v___jp_310_;
}
else
{
lean_object* v___x_331_; 
v___x_331_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_311_ = v___x_331_;
goto v___jp_310_;
}
}
default: 
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_unsigned_to_nat(1024u);
v___x_333_ = lean_nat_dec_le(v___x_332_, v_prec_302_);
if (v___x_333_ == 0)
{
lean_object* v___x_334_; 
v___x_334_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__6, &l_Lean_instReprDefinitionSafety_repr___closed__6_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__6);
v___y_318_ = v___x_334_;
goto v___jp_317_;
}
else
{
lean_object* v___x_335_; 
v___x_335_ = lean_obj_once(&l_Lean_instReprDefinitionSafety_repr___closed__7, &l_Lean_instReprDefinitionSafety_repr___closed__7_once, _init_l_Lean_instReprDefinitionSafety_repr___closed__7);
v___y_318_ = v___x_335_;
goto v___jp_317_;
}
}
}
v___jp_303_:
{
lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_305_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__1));
lean_inc(v___y_304_);
v___x_306_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_306_, 0, v___y_304_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
v___x_307_ = 0;
v___x_308_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_308_, 0, v___x_306_);
lean_ctor_set_uint8(v___x_308_, sizeof(void*)*1, v___x_307_);
v___x_309_ = l_Repr_addAppParen(v___x_308_, v_prec_302_);
return v___x_309_;
}
v___jp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_312_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__3));
lean_inc(v___y_311_);
v___x_313_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_313_, 0, v___y_311_);
lean_ctor_set(v___x_313_, 1, v___x_312_);
v___x_314_ = 0;
v___x_315_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_315_, 0, v___x_313_);
lean_ctor_set_uint8(v___x_315_, sizeof(void*)*1, v___x_314_);
v___x_316_ = l_Repr_addAppParen(v___x_315_, v_prec_302_);
return v___x_316_;
}
v___jp_317_:
{
lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_319_ = ((lean_object*)(l_Lean_instReprDefinitionSafety_repr___closed__5));
lean_inc(v___y_318_);
v___x_320_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_320_, 0, v___y_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = 0;
v___x_322_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_322_, 0, v___x_320_);
lean_ctor_set_uint8(v___x_322_, sizeof(void*)*1, v___x_321_);
v___x_323_ = l_Repr_addAppParen(v___x_322_, v_prec_302_);
return v___x_323_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprDefinitionSafety_repr___boxed(lean_object* v_x_336_, lean_object* v_prec_337_){
_start:
{
uint8_t v_x_171__boxed_338_; lean_object* v_res_339_; 
v_x_171__boxed_338_ = lean_unbox(v_x_336_);
v_res_339_ = l_Lean_instReprDefinitionSafety_repr(v_x_171__boxed_338_, v_prec_337_);
lean_dec(v_prec_337_);
return v_res_339_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default___closed__0(void){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = lean_box(0);
v___x_343_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_344_ = l_Lean_Expr_const___override(v___x_343_, v___x_342_);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default___closed__2(void){
_start:
{
lean_object* v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_348_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_349_ = 0;
v___x_350_ = lean_box(0);
v___x_351_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_352_ = l_Lean_instInhabitedConstantVal_default;
v___x_353_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_353_, 0, v___x_352_);
lean_ctor_set(v___x_353_, 1, v___x_351_);
lean_ctor_set(v___x_353_, 2, v___x_350_);
lean_ctor_set(v___x_353_, 3, v___x_348_);
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*4, v___x_349_);
return v___x_353_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal_default(void){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__2, &l_Lean_instInhabitedDefinitionVal_default___closed__2_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__2);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_instInhabitedDefinitionVal(void){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_instInhabitedDefinitionVal_default;
return v___x_355_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDefinitionVal_beq(lean_object* v_x_356_, lean_object* v_x_357_){
_start:
{
lean_object* v_toConstantVal_358_; lean_object* v_value_359_; lean_object* v_hints_360_; uint8_t v_safety_361_; lean_object* v_all_362_; lean_object* v_toConstantVal_363_; lean_object* v_value_364_; lean_object* v_hints_365_; uint8_t v_safety_366_; lean_object* v_all_367_; uint8_t v___x_368_; 
v_toConstantVal_358_ = lean_ctor_get(v_x_356_, 0);
v_value_359_ = lean_ctor_get(v_x_356_, 1);
v_hints_360_ = lean_ctor_get(v_x_356_, 2);
v_safety_361_ = lean_ctor_get_uint8(v_x_356_, sizeof(void*)*4);
v_all_362_ = lean_ctor_get(v_x_356_, 3);
v_toConstantVal_363_ = lean_ctor_get(v_x_357_, 0);
v_value_364_ = lean_ctor_get(v_x_357_, 1);
v_hints_365_ = lean_ctor_get(v_x_357_, 2);
v_safety_366_ = lean_ctor_get_uint8(v_x_357_, sizeof(void*)*4);
v_all_367_ = lean_ctor_get(v_x_357_, 3);
v___x_368_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_358_, v_toConstantVal_363_);
if (v___x_368_ == 0)
{
return v___x_368_;
}
else
{
uint8_t v___x_369_; 
v___x_369_ = lean_expr_eqv(v_value_359_, v_value_364_);
if (v___x_369_ == 0)
{
return v___x_369_;
}
else
{
uint8_t v___x_370_; 
v___x_370_ = l_Lean_instBEqReducibilityHints_beq(v_hints_360_, v_hints_365_);
if (v___x_370_ == 0)
{
return v___x_370_;
}
else
{
uint8_t v___x_371_; 
v___x_371_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_361_, v_safety_366_);
if (v___x_371_ == 0)
{
return v___x_371_;
}
else
{
uint8_t v___x_372_; 
v___x_372_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_362_, v_all_367_);
return v___x_372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDefinitionVal_beq___boxed(lean_object* v_x_373_, lean_object* v_x_374_){
_start:
{
uint8_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l_Lean_instBEqDefinitionVal_beq(v_x_373_, v_x_374_);
lean_dec_ref(v_x_374_);
lean_dec_ref(v_x_373_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT lean_object* lean_mk_definition_val(lean_object* v_name_379_, lean_object* v_levelParams_380_, lean_object* v_type_381_, lean_object* v_value_382_, lean_object* v_hints_383_, uint8_t v_safety_384_, lean_object* v_all_385_){
_start:
{
lean_object* v___x_386_; lean_object* v___x_387_; 
v___x_386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_386_, 0, v_name_379_);
lean_ctor_set(v___x_386_, 1, v_levelParams_380_);
lean_ctor_set(v___x_386_, 2, v_type_381_);
v___x_387_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v_value_382_);
lean_ctor_set(v___x_387_, 2, v_hints_383_);
lean_ctor_set(v___x_387_, 3, v_all_385_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*4, v_safety_384_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValEx___boxed(lean_object* v_name_388_, lean_object* v_levelParams_389_, lean_object* v_type_390_, lean_object* v_value_391_, lean_object* v_hints_392_, lean_object* v_safety_393_, lean_object* v_all_394_){
_start:
{
uint8_t v_safety_boxed_395_; lean_object* v_res_396_; 
v_safety_boxed_395_ = lean_unbox(v_safety_393_);
v_res_396_ = lean_mk_definition_val(v_name_388_, v_levelParams_389_, v_type_390_, v_value_391_, v_hints_392_, v_safety_boxed_395_, v_all_394_);
return v_res_396_;
}
}
LEAN_EXPORT uint8_t lean_definition_val_get_safety(lean_object* v_v_397_){
_start:
{
uint8_t v_safety_398_; 
v_safety_398_ = lean_ctor_get_uint8(v_v_397_, sizeof(void*)*4);
lean_dec_ref(v_v_397_);
return v_safety_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_DefinitionVal_getSafetyEx___boxed(lean_object* v_v_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = lean_definition_val_get_safety(v_v_399_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default___closed__0(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_402_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_403_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_404_ = l_Lean_instInhabitedConstantVal_default;
v___x_405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v___x_403_);
lean_ctor_set(v___x_405_, 2, v___x_402_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal_default(void){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = lean_obj_once(&l_Lean_instInhabitedTheoremVal_default___closed__0, &l_Lean_instInhabitedTheoremVal_default___closed__0_once, _init_l_Lean_instInhabitedTheoremVal_default___closed__0);
return v___x_406_;
}
}
static lean_object* _init_l_Lean_instInhabitedTheoremVal(void){
_start:
{
lean_object* v___x_407_; 
v___x_407_ = l_Lean_instInhabitedTheoremVal_default;
return v___x_407_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqTheoremVal_beq(lean_object* v_x_408_, lean_object* v_x_409_){
_start:
{
lean_object* v_toConstantVal_410_; lean_object* v_value_411_; lean_object* v_all_412_; lean_object* v_toConstantVal_413_; lean_object* v_value_414_; lean_object* v_all_415_; uint8_t v___x_416_; 
v_toConstantVal_410_ = lean_ctor_get(v_x_408_, 0);
v_value_411_ = lean_ctor_get(v_x_408_, 1);
v_all_412_ = lean_ctor_get(v_x_408_, 2);
v_toConstantVal_413_ = lean_ctor_get(v_x_409_, 0);
v_value_414_ = lean_ctor_get(v_x_409_, 1);
v_all_415_ = lean_ctor_get(v_x_409_, 2);
v___x_416_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_410_, v_toConstantVal_413_);
if (v___x_416_ == 0)
{
return v___x_416_;
}
else
{
uint8_t v___x_417_; 
v___x_417_ = lean_expr_eqv(v_value_411_, v_value_414_);
if (v___x_417_ == 0)
{
return v___x_417_;
}
else
{
uint8_t v___x_418_; 
v___x_418_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_412_, v_all_415_);
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqTheoremVal_beq___boxed(lean_object* v_x_419_, lean_object* v_x_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_Lean_instBEqTheoremVal_beq(v_x_419_, v_x_420_);
lean_dec_ref(v_x_420_);
lean_dec_ref(v_x_419_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default___closed__0(void){
_start:
{
lean_object* v___x_425_; uint8_t v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_425_ = ((lean_object*)(l_Lean_instInhabitedDefinitionVal_default___closed__1));
v___x_426_ = 0;
v___x_427_ = lean_obj_once(&l_Lean_instInhabitedDefinitionVal_default___closed__0, &l_Lean_instInhabitedDefinitionVal_default___closed__0_once, _init_l_Lean_instInhabitedDefinitionVal_default___closed__0);
v___x_428_ = l_Lean_instInhabitedConstantVal_default;
v___x_429_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
lean_ctor_set(v___x_429_, 2, v___x_425_);
lean_ctor_set_uint8(v___x_429_, sizeof(void*)*3, v___x_426_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal_default(void){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_obj_once(&l_Lean_instInhabitedOpaqueVal_default___closed__0, &l_Lean_instInhabitedOpaqueVal_default___closed__0_once, _init_l_Lean_instInhabitedOpaqueVal_default___closed__0);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_instInhabitedOpaqueVal(void){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_instInhabitedOpaqueVal_default;
return v___x_431_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqOpaqueVal_beq(lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
lean_object* v_toConstantVal_434_; lean_object* v_value_435_; uint8_t v_isUnsafe_436_; lean_object* v_all_437_; lean_object* v_toConstantVal_438_; lean_object* v_value_439_; uint8_t v_isUnsafe_440_; lean_object* v_all_441_; uint8_t v___x_442_; 
v_toConstantVal_434_ = lean_ctor_get(v_x_432_, 0);
v_value_435_ = lean_ctor_get(v_x_432_, 1);
v_isUnsafe_436_ = lean_ctor_get_uint8(v_x_432_, sizeof(void*)*3);
v_all_437_ = lean_ctor_get(v_x_432_, 2);
v_toConstantVal_438_ = lean_ctor_get(v_x_433_, 0);
v_value_439_ = lean_ctor_get(v_x_433_, 1);
v_isUnsafe_440_ = lean_ctor_get_uint8(v_x_433_, sizeof(void*)*3);
v_all_441_ = lean_ctor_get(v_x_433_, 2);
v___x_442_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_434_, v_toConstantVal_438_);
if (v___x_442_ == 0)
{
return v___x_442_;
}
else
{
uint8_t v___x_443_; 
v___x_443_ = lean_expr_eqv(v_value_435_, v_value_439_);
if (v___x_443_ == 0)
{
return v___x_443_;
}
else
{
if (v_isUnsafe_440_ == 0)
{
if (v_isUnsafe_436_ == 0)
{
uint8_t v___x_444_; 
v___x_444_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_437_, v_all_441_);
return v___x_444_;
}
else
{
return v_isUnsafe_440_;
}
}
else
{
if (v_isUnsafe_436_ == 0)
{
return v_isUnsafe_436_;
}
else
{
uint8_t v___x_445_; 
v___x_445_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_437_, v_all_441_);
return v___x_445_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqOpaqueVal_beq___boxed(lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
uint8_t v_res_448_; lean_object* v_r_449_; 
v_res_448_ = l_Lean_instBEqOpaqueVal_beq(v_x_446_, v_x_447_);
lean_dec_ref(v_x_447_);
lean_dec_ref(v_x_446_);
v_r_449_ = lean_box(v_res_448_);
return v_r_449_;
}
}
LEAN_EXPORT uint8_t lean_opaque_val_is_unsafe(lean_object* v_v_452_){
_start:
{
uint8_t v_isUnsafe_453_; 
v_isUnsafe_453_ = lean_ctor_get_uint8(v_v_452_, sizeof(void*)*3);
lean_dec_ref(v_v_452_);
return v_isUnsafe_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpaqueVal_isUnsafeEx___boxed(lean_object* v_v_454_){
_start:
{
uint8_t v_res_455_; lean_object* v_r_456_; 
v_res_455_ = lean_opaque_val_is_unsafe(v_v_454_);
v_r_456_ = lean_box(v_res_455_);
return v_r_456_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__0(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_box(0);
v___x_458_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_459_ = l_Lean_Expr_const___override(v___x_458_, v___x_457_);
return v___x_459_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__1(void){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_460_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_461_ = lean_box(0);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
return v___x_462_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default(void){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__1, &l_Lean_instInhabitedConstructor_default___closed__1_once, _init_l_Lean_instInhabitedConstructor_default___closed__1);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_instInhabitedConstructor_default;
return v___x_464_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructor_beq(lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
lean_object* v_name_467_; lean_object* v_type_468_; lean_object* v_name_469_; lean_object* v_type_470_; uint8_t v___x_471_; 
v_name_467_ = lean_ctor_get(v_x_465_, 0);
v_type_468_ = lean_ctor_get(v_x_465_, 1);
v_name_469_ = lean_ctor_get(v_x_466_, 0);
v_type_470_ = lean_ctor_get(v_x_466_, 1);
v___x_471_ = lean_name_eq(v_name_467_, v_name_469_);
if (v___x_471_ == 0)
{
return v___x_471_;
}
else
{
uint8_t v___x_472_; 
v___x_472_ = lean_expr_eqv(v_type_468_, v_type_470_);
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructor_beq___boxed(lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
uint8_t v_res_475_; lean_object* v_r_476_; 
v_res_475_ = l_Lean_instBEqConstructor_beq(v_x_473_, v_x_474_);
lean_dec_ref(v_x_474_);
lean_dec_ref(v_x_473_);
v_r_476_ = lean_box(v_res_475_);
return v_r_476_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default___closed__0(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_479_ = lean_box(0);
v___x_480_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_481_ = lean_box(0);
v___x_482_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v___x_480_);
lean_ctor_set(v___x_482_, 2, v___x_479_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default(void){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = lean_obj_once(&l_Lean_instInhabitedInductiveType_default___closed__0, &l_Lean_instInhabitedInductiveType_default___closed__0_once, _init_l_Lean_instInhabitedInductiveType_default___closed__0);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType(void){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Lean_instInhabitedInductiveType_default;
return v___x_484_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(lean_object* v_x_485_, lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_485_) == 0)
{
if (lean_obj_tag(v_x_486_) == 0)
{
uint8_t v___x_487_; 
v___x_487_ = 1;
return v___x_487_;
}
else
{
uint8_t v___x_488_; 
v___x_488_ = 0;
return v___x_488_;
}
}
else
{
if (lean_obj_tag(v_x_486_) == 0)
{
uint8_t v___x_489_; 
v___x_489_ = 0;
return v___x_489_;
}
else
{
lean_object* v_head_490_; lean_object* v_tail_491_; lean_object* v_head_492_; lean_object* v_tail_493_; uint8_t v___x_494_; 
v_head_490_ = lean_ctor_get(v_x_485_, 0);
v_tail_491_ = lean_ctor_get(v_x_485_, 1);
v_head_492_ = lean_ctor_get(v_x_486_, 0);
v_tail_493_ = lean_ctor_get(v_x_486_, 1);
v___x_494_ = l_Lean_instBEqConstructor_beq(v_head_490_, v_head_492_);
if (v___x_494_ == 0)
{
return v___x_494_;
}
else
{
v_x_485_ = v_tail_491_;
v_x_486_ = v_tail_493_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0___boxed(lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
uint8_t v_res_498_; lean_object* v_r_499_; 
v_res_498_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_x_496_, v_x_497_);
lean_dec(v_x_497_);
lean_dec(v_x_496_);
v_r_499_ = lean_box(v_res_498_);
return v_r_499_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveType_beq(lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
lean_object* v_name_502_; lean_object* v_type_503_; lean_object* v_ctors_504_; lean_object* v_name_505_; lean_object* v_type_506_; lean_object* v_ctors_507_; uint8_t v___x_508_; 
v_name_502_ = lean_ctor_get(v_x_500_, 0);
v_type_503_ = lean_ctor_get(v_x_500_, 1);
v_ctors_504_ = lean_ctor_get(v_x_500_, 2);
v_name_505_ = lean_ctor_get(v_x_501_, 0);
v_type_506_ = lean_ctor_get(v_x_501_, 1);
v_ctors_507_ = lean_ctor_get(v_x_501_, 2);
v___x_508_ = lean_name_eq(v_name_502_, v_name_505_);
if (v___x_508_ == 0)
{
return v___x_508_;
}
else
{
uint8_t v___x_509_; 
v___x_509_ = lean_expr_eqv(v_type_503_, v_type_506_);
if (v___x_509_ == 0)
{
return v___x_509_;
}
else
{
uint8_t v___x_510_; 
v___x_510_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_ctors_504_, v_ctors_507_);
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveType_beq___boxed(lean_object* v_x_511_, lean_object* v_x_512_){
_start:
{
uint8_t v_res_513_; lean_object* v_r_514_; 
v_res_513_ = l_Lean_instBEqInductiveType_beq(v_x_511_, v_x_512_);
lean_dec_ref(v_x_512_);
lean_dec_ref(v_x_511_);
v_r_514_ = lean_box(v_res_513_);
return v_r_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___impl(lean_object* v_x_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = lean_obj_tag_nat(v_x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___impl___boxed(lean_object* v_x_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Declaration_ctorIdx___impl(v_x_519_);
lean_dec(v_x_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___redArg(lean_object* v_t_521_, lean_object* v_k_522_){
_start:
{
switch(lean_obj_tag(v_t_521_))
{
case 4:
{
return v_k_522_;
}
case 5:
{
lean_object* v_defns_523_; lean_object* v___x_524_; 
v_defns_523_ = lean_ctor_get(v_t_521_, 0);
lean_inc(v_defns_523_);
lean_dec_ref_known(v_t_521_, 1);
v___x_524_ = lean_apply_1(v_k_522_, v_defns_523_);
return v___x_524_;
}
case 6:
{
lean_object* v_lparams_525_; lean_object* v_nparams_526_; lean_object* v_types_527_; uint8_t v_isUnsafe_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_lparams_525_ = lean_ctor_get(v_t_521_, 0);
lean_inc(v_lparams_525_);
v_nparams_526_ = lean_ctor_get(v_t_521_, 1);
lean_inc(v_nparams_526_);
v_types_527_ = lean_ctor_get(v_t_521_, 2);
lean_inc(v_types_527_);
v_isUnsafe_528_ = lean_ctor_get_uint8(v_t_521_, sizeof(void*)*3);
lean_dec_ref_known(v_t_521_, 3);
v___x_529_ = lean_box(v_isUnsafe_528_);
v___x_530_ = lean_apply_4(v_k_522_, v_lparams_525_, v_nparams_526_, v_types_527_, v___x_529_);
return v___x_530_;
}
default: 
{
lean_object* v_val_531_; lean_object* v___x_532_; 
v_val_531_ = lean_ctor_get(v_t_521_, 0);
lean_inc_ref(v_val_531_);
lean_dec(v_t_521_);
v___x_532_ = lean_apply_1(v_k_522_, v_val_531_);
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim(lean_object* v_motive_533_, lean_object* v_ctorIdx_534_, lean_object* v_t_535_, lean_object* v_h_536_, lean_object* v_k_537_){
_start:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Declaration_ctorElim___redArg(v_t_535_, v_k_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___boxed(lean_object* v_motive_539_, lean_object* v_ctorIdx_540_, lean_object* v_t_541_, lean_object* v_h_542_, lean_object* v_k_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Declaration_ctorElim(v_motive_539_, v_ctorIdx_540_, v_t_541_, v_h_542_, v_k_543_);
lean_dec(v_ctorIdx_540_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim___redArg(lean_object* v_t_545_, lean_object* v_axiomDecl_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l_Lean_Declaration_ctorElim___redArg(v_t_545_, v_axiomDecl_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim(lean_object* v_motive_548_, lean_object* v_t_549_, lean_object* v_h_550_, lean_object* v_axiomDecl_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l_Lean_Declaration_ctorElim___redArg(v_t_549_, v_axiomDecl_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim___redArg(lean_object* v_t_553_, lean_object* v_defnDecl_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Lean_Declaration_ctorElim___redArg(v_t_553_, v_defnDecl_554_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim(lean_object* v_motive_556_, lean_object* v_t_557_, lean_object* v_h_558_, lean_object* v_defnDecl_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_Declaration_ctorElim___redArg(v_t_557_, v_defnDecl_559_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim___redArg(lean_object* v_t_561_, lean_object* v_thmDecl_562_){
_start:
{
lean_object* v___x_563_; 
v___x_563_ = l_Lean_Declaration_ctorElim___redArg(v_t_561_, v_thmDecl_562_);
return v___x_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim(lean_object* v_motive_564_, lean_object* v_t_565_, lean_object* v_h_566_, lean_object* v_thmDecl_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Declaration_ctorElim___redArg(v_t_565_, v_thmDecl_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim___redArg(lean_object* v_t_569_, lean_object* v_opaqueDecl_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Lean_Declaration_ctorElim___redArg(v_t_569_, v_opaqueDecl_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim(lean_object* v_motive_572_, lean_object* v_t_573_, lean_object* v_h_574_, lean_object* v_opaqueDecl_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_Declaration_ctorElim___redArg(v_t_573_, v_opaqueDecl_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim___redArg(lean_object* v_t_577_, lean_object* v_quotDecl_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_Declaration_ctorElim___redArg(v_t_577_, v_quotDecl_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim(lean_object* v_motive_580_, lean_object* v_t_581_, lean_object* v_h_582_, lean_object* v_quotDecl_583_){
_start:
{
lean_object* v___x_584_; 
v___x_584_ = l_Lean_Declaration_ctorElim___redArg(v_t_581_, v_quotDecl_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim___redArg(lean_object* v_t_585_, lean_object* v_mutualDefnDecl_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_Declaration_ctorElim___redArg(v_t_585_, v_mutualDefnDecl_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim(lean_object* v_motive_588_, lean_object* v_t_589_, lean_object* v_h_590_, lean_object* v_mutualDefnDecl_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_Declaration_ctorElim___redArg(v_t_589_, v_mutualDefnDecl_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim___redArg(lean_object* v_t_593_, lean_object* v_inductDecl_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Declaration_ctorElim___redArg(v_t_593_, v_inductDecl_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim(lean_object* v_motive_596_, lean_object* v_t_597_, lean_object* v_h_598_, lean_object* v_inductDecl_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_Declaration_ctorElim___redArg(v_t_597_, v_inductDecl_599_);
return v___x_600_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default___closed__0(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = l_Lean_instInhabitedAxiomVal_default;
v___x_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
return v___x_602_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default(void){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_obj_once(&l_Lean_instInhabitedDeclaration_default___closed__0, &l_Lean_instInhabitedDeclaration_default___closed__0_once, _init_l_Lean_instInhabitedDeclaration_default___closed__0);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration(void){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_instInhabitedDeclaration_default;
return v___x_604_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
if (lean_obj_tag(v_x_606_) == 0)
{
uint8_t v___x_607_; 
v___x_607_ = 1;
return v___x_607_;
}
else
{
uint8_t v___x_608_; 
v___x_608_ = 0;
return v___x_608_;
}
}
else
{
if (lean_obj_tag(v_x_606_) == 0)
{
uint8_t v___x_609_; 
v___x_609_ = 0;
return v___x_609_;
}
else
{
lean_object* v_head_610_; lean_object* v_tail_611_; lean_object* v_head_612_; lean_object* v_tail_613_; uint8_t v___x_614_; 
v_head_610_ = lean_ctor_get(v_x_605_, 0);
v_tail_611_ = lean_ctor_get(v_x_605_, 1);
v_head_612_ = lean_ctor_get(v_x_606_, 0);
v_tail_613_ = lean_ctor_get(v_x_606_, 1);
v___x_614_ = l_Lean_instBEqDefinitionVal_beq(v_head_610_, v_head_612_);
if (v___x_614_ == 0)
{
return v___x_614_;
}
else
{
v_x_605_ = v_tail_611_;
v_x_606_ = v_tail_613_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0___boxed(lean_object* v_x_616_, lean_object* v_x_617_){
_start:
{
uint8_t v_res_618_; lean_object* v_r_619_; 
v_res_618_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_x_616_, v_x_617_);
lean_dec(v_x_617_);
lean_dec(v_x_616_);
v_r_619_ = lean_box(v_res_618_);
return v_r_619_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
if (lean_obj_tag(v_x_620_) == 0)
{
if (lean_obj_tag(v_x_621_) == 0)
{
uint8_t v___x_622_; 
v___x_622_ = 1;
return v___x_622_;
}
else
{
uint8_t v___x_623_; 
v___x_623_ = 0;
return v___x_623_;
}
}
else
{
if (lean_obj_tag(v_x_621_) == 0)
{
uint8_t v___x_624_; 
v___x_624_ = 0;
return v___x_624_;
}
else
{
lean_object* v_head_625_; lean_object* v_tail_626_; lean_object* v_head_627_; lean_object* v_tail_628_; uint8_t v___x_629_; 
v_head_625_ = lean_ctor_get(v_x_620_, 0);
v_tail_626_ = lean_ctor_get(v_x_620_, 1);
v_head_627_ = lean_ctor_get(v_x_621_, 0);
v_tail_628_ = lean_ctor_get(v_x_621_, 1);
v___x_629_ = l_Lean_instBEqInductiveType_beq(v_head_625_, v_head_627_);
if (v___x_629_ == 0)
{
return v___x_629_;
}
else
{
v_x_620_ = v_tail_626_;
v_x_621_ = v_tail_628_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1___boxed(lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
uint8_t v_res_633_; lean_object* v_r_634_; 
v_res_633_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_x_631_, v_x_632_);
lean_dec(v_x_632_);
lean_dec(v_x_631_);
v_r_634_ = lean_box(v_res_633_);
return v_r_634_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDeclaration_beq(lean_object* v_x_635_, lean_object* v_x_636_){
_start:
{
switch(lean_obj_tag(v_x_635_))
{
case 0:
{
if (lean_obj_tag(v_x_636_) == 0)
{
lean_object* v_val_637_; lean_object* v_val_638_; uint8_t v___x_639_; 
v_val_637_ = lean_ctor_get(v_x_635_, 0);
v_val_638_ = lean_ctor_get(v_x_636_, 0);
v___x_639_ = l_Lean_instBEqAxiomVal_beq(v_val_637_, v_val_638_);
return v___x_639_;
}
else
{
uint8_t v___x_640_; 
v___x_640_ = 0;
return v___x_640_;
}
}
case 1:
{
if (lean_obj_tag(v_x_636_) == 1)
{
lean_object* v_val_641_; lean_object* v_val_642_; uint8_t v___x_643_; 
v_val_641_ = lean_ctor_get(v_x_635_, 0);
v_val_642_ = lean_ctor_get(v_x_636_, 0);
v___x_643_ = l_Lean_instBEqDefinitionVal_beq(v_val_641_, v_val_642_);
return v___x_643_;
}
else
{
uint8_t v___x_644_; 
v___x_644_ = 0;
return v___x_644_;
}
}
case 2:
{
if (lean_obj_tag(v_x_636_) == 2)
{
lean_object* v_val_645_; lean_object* v_val_646_; uint8_t v___x_647_; 
v_val_645_ = lean_ctor_get(v_x_635_, 0);
v_val_646_ = lean_ctor_get(v_x_636_, 0);
v___x_647_ = l_Lean_instBEqTheoremVal_beq(v_val_645_, v_val_646_);
return v___x_647_;
}
else
{
uint8_t v___x_648_; 
v___x_648_ = 0;
return v___x_648_;
}
}
case 3:
{
if (lean_obj_tag(v_x_636_) == 3)
{
lean_object* v_val_649_; lean_object* v_val_650_; uint8_t v___x_651_; 
v_val_649_ = lean_ctor_get(v_x_635_, 0);
v_val_650_ = lean_ctor_get(v_x_636_, 0);
v___x_651_ = l_Lean_instBEqOpaqueVal_beq(v_val_649_, v_val_650_);
return v___x_651_;
}
else
{
uint8_t v___x_652_; 
v___x_652_ = 0;
return v___x_652_;
}
}
case 4:
{
if (lean_obj_tag(v_x_636_) == 4)
{
uint8_t v___x_653_; 
v___x_653_ = 1;
return v___x_653_;
}
else
{
uint8_t v___x_654_; 
v___x_654_ = 0;
return v___x_654_;
}
}
case 5:
{
if (lean_obj_tag(v_x_636_) == 5)
{
lean_object* v_defns_655_; lean_object* v_defns_656_; uint8_t v___x_657_; 
v_defns_655_ = lean_ctor_get(v_x_635_, 0);
v_defns_656_ = lean_ctor_get(v_x_636_, 0);
v___x_657_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_defns_655_, v_defns_656_);
return v___x_657_;
}
else
{
uint8_t v___x_658_; 
v___x_658_ = 0;
return v___x_658_;
}
}
default: 
{
if (lean_obj_tag(v_x_636_) == 6)
{
lean_object* v_lparams_659_; lean_object* v_nparams_660_; lean_object* v_types_661_; uint8_t v_isUnsafe_662_; lean_object* v_lparams_663_; lean_object* v_nparams_664_; lean_object* v_types_665_; uint8_t v_isUnsafe_666_; uint8_t v___x_667_; 
v_lparams_659_ = lean_ctor_get(v_x_635_, 0);
v_nparams_660_ = lean_ctor_get(v_x_635_, 1);
v_types_661_ = lean_ctor_get(v_x_635_, 2);
v_isUnsafe_662_ = lean_ctor_get_uint8(v_x_635_, sizeof(void*)*3);
v_lparams_663_ = lean_ctor_get(v_x_636_, 0);
v_nparams_664_ = lean_ctor_get(v_x_636_, 1);
v_types_665_ = lean_ctor_get(v_x_636_, 2);
v_isUnsafe_666_ = lean_ctor_get_uint8(v_x_636_, sizeof(void*)*3);
v___x_667_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_lparams_659_, v_lparams_663_);
if (v___x_667_ == 0)
{
return v___x_667_;
}
else
{
uint8_t v___x_668_; 
v___x_668_ = lean_nat_dec_eq(v_nparams_660_, v_nparams_664_);
if (v___x_668_ == 0)
{
return v___x_668_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_types_661_, v_types_665_);
if (v___x_669_ == 0)
{
return v___x_669_;
}
else
{
if (v_isUnsafe_666_ == 0)
{
if (v_isUnsafe_662_ == 0)
{
return v___x_669_;
}
else
{
return v_isUnsafe_666_;
}
}
else
{
return v_isUnsafe_662_;
}
}
}
}
}
else
{
uint8_t v___x_670_; 
v___x_670_ = 0;
return v___x_670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDeclaration_beq___boxed(lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_Lean_instBEqDeclaration_beq(v_x_671_, v_x_672_);
lean_dec(v_x_672_);
lean_dec(v_x_671_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_decl(lean_object* v_lparams_677_, lean_object* v_nparams_678_, lean_object* v_types_679_, uint8_t v_isUnsafe_680_){
_start:
{
lean_object* v___x_681_; 
v___x_681_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_681_, 0, v_lparams_677_);
lean_ctor_set(v___x_681_, 1, v_nparams_678_);
lean_ctor_set(v___x_681_, 2, v_types_679_);
lean_ctor_set_uint8(v___x_681_, sizeof(void*)*3, v_isUnsafe_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveDeclEs___boxed(lean_object* v_lparams_682_, lean_object* v_nparams_683_, lean_object* v_types_684_, lean_object* v_isUnsafe_685_){
_start:
{
uint8_t v_isUnsafe_boxed_686_; lean_object* v_res_687_; 
v_isUnsafe_boxed_686_ = lean_unbox(v_isUnsafe_685_);
v_res_687_ = lean_mk_inductive_decl(v_lparams_682_, v_nparams_683_, v_types_684_, v_isUnsafe_boxed_686_);
return v_res_687_;
}
}
LEAN_EXPORT uint8_t lean_is_unsafe_inductive_decl(lean_object* v_x_688_){
_start:
{
if (lean_obj_tag(v_x_688_) == 6)
{
uint8_t v_isUnsafe_689_; 
v_isUnsafe_689_ = lean_ctor_get_uint8(v_x_688_, sizeof(void*)*3);
lean_dec_ref_known(v_x_688_, 3);
return v_isUnsafe_689_;
}
else
{
uint8_t v___x_690_; 
lean_dec(v_x_688_);
v___x_690_ = 0;
return v___x_690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_isUnsafeInductiveDeclEx___boxed(lean_object* v_x_691_){
_start:
{
uint8_t v_res_692_; lean_object* v_r_693_; 
v_res_692_ = lean_is_unsafe_inductive_decl(v_x_691_);
v_r_693_ = lean_box(v_res_692_);
return v_r_693_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(lean_object* v_msg_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = l_Lean_instInhabitedDefinitionVal_default;
v___x_696_ = lean_panic_fn_borrowed(v___x_695_, v_msg_694_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_Declaration_definitionVal_x21___closed__3(void){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_700_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__2));
v___x_701_ = lean_unsigned_to_nat(9u);
v___x_702_ = lean_unsigned_to_nat(184u);
v___x_703_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__1));
v___x_704_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_705_ = l_mkPanicMessageWithDecl(v___x_704_, v___x_703_, v___x_702_, v___x_701_, v___x_700_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21(lean_object* v_x_706_){
_start:
{
if (lean_obj_tag(v_x_706_) == 1)
{
lean_object* v_val_707_; 
v_val_707_ = lean_ctor_get(v_x_706_, 0);
lean_inc_ref(v_val_707_);
return v_val_707_;
}
else
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = lean_obj_once(&l_Lean_Declaration_definitionVal_x21___closed__3, &l_Lean_Declaration_definitionVal_x21___closed__3_once, _init_l_Lean_Declaration_definitionVal_x21___closed__3);
v___x_709_ = l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(v___x_708_);
return v___x_709_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21___boxed(lean_object* v_x_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Declaration_definitionVal_x21(v_x_710_);
lean_dec(v_x_710_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(lean_object* v_a_712_, lean_object* v_a_713_){
_start:
{
if (lean_obj_tag(v_a_712_) == 0)
{
lean_object* v___x_714_; 
v___x_714_ = l_List_reverse___redArg(v_a_713_);
return v___x_714_;
}
else
{
lean_object* v_head_715_; lean_object* v_toConstantVal_716_; lean_object* v_tail_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_726_; 
v_head_715_ = lean_ctor_get(v_a_712_, 0);
v_toConstantVal_716_ = lean_ctor_get(v_head_715_, 0);
lean_inc_ref(v_toConstantVal_716_);
v_tail_717_ = lean_ctor_get(v_a_712_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_a_712_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v_a_712_, 0);
lean_dec(v_unused_727_);
v___x_719_ = v_a_712_;
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_tail_717_);
lean_dec(v_a_712_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_726_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_name_721_; lean_object* v___x_723_; 
v_name_721_ = lean_ctor_get(v_toConstantVal_716_, 0);
lean_inc(v_name_721_);
lean_dec_ref(v_toConstantVal_716_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 1, v_a_713_);
lean_ctor_set(v___x_719_, 0, v_name_721_);
v___x_723_ = v___x_719_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_name_721_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_a_713_);
v___x_723_ = v_reuseFailAlloc_725_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
v_a_712_ = v_tail_717_;
v_a_713_ = v___x_723_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(lean_object* v_a_728_, lean_object* v_a_729_){
_start:
{
if (lean_obj_tag(v_a_728_) == 0)
{
lean_object* v___x_730_; 
v___x_730_ = l_List_reverse___redArg(v_a_729_);
return v___x_730_;
}
else
{
lean_object* v_head_731_; lean_object* v_tail_732_; lean_object* v___x_734_; uint8_t v_isShared_735_; uint8_t v_isSharedCheck_741_; 
v_head_731_ = lean_ctor_get(v_a_728_, 0);
v_tail_732_ = lean_ctor_get(v_a_728_, 1);
v_isSharedCheck_741_ = !lean_is_exclusive(v_a_728_);
if (v_isSharedCheck_741_ == 0)
{
v___x_734_ = v_a_728_;
v_isShared_735_ = v_isSharedCheck_741_;
goto v_resetjp_733_;
}
else
{
lean_inc(v_tail_732_);
lean_inc(v_head_731_);
lean_dec(v_a_728_);
v___x_734_ = lean_box(0);
v_isShared_735_ = v_isSharedCheck_741_;
goto v_resetjp_733_;
}
v_resetjp_733_:
{
lean_object* v_name_736_; lean_object* v___x_738_; 
v_name_736_ = lean_ctor_get(v_head_731_, 0);
lean_inc(v_name_736_);
lean_dec(v_head_731_);
if (v_isShared_735_ == 0)
{
lean_ctor_set(v___x_734_, 1, v_a_729_);
lean_ctor_set(v___x_734_, 0, v_name_736_);
v___x_738_ = v___x_734_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_name_736_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_a_729_);
v___x_738_ = v_reuseFailAlloc_740_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
v_a_728_ = v_tail_732_;
v_a_729_ = v___x_738_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getTopLevelNames(lean_object* v_x_748_){
_start:
{
switch(lean_obj_tag(v_x_748_))
{
case 4:
{
lean_object* v___x_749_; 
v___x_749_ = ((lean_object*)(l_Lean_Declaration_getTopLevelNames___closed__2));
return v___x_749_;
}
case 5:
{
lean_object* v_defns_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v_defns_750_ = lean_ctor_get(v_x_748_, 0);
lean_inc(v_defns_750_);
lean_dec_ref_known(v_x_748_, 1);
v___x_751_ = lean_box(0);
v___x_752_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_750_, v___x_751_);
return v___x_752_;
}
case 6:
{
lean_object* v_types_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_types_753_ = lean_ctor_get(v_x_748_, 2);
lean_inc(v_types_753_);
lean_dec_ref_known(v_x_748_, 3);
v___x_754_ = lean_box(0);
v___x_755_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(v_types_753_, v___x_754_);
return v___x_755_;
}
default: 
{
lean_object* v_val_756_; lean_object* v_toConstantVal_757_; lean_object* v_name_758_; lean_object* v___x_759_; lean_object* v___x_760_; 
v_val_756_ = lean_ctor_get(v_x_748_, 0);
lean_inc_ref(v_val_756_);
lean_dec(v_x_748_);
v_toConstantVal_757_ = lean_ctor_get(v_val_756_, 0);
lean_inc_ref(v_toConstantVal_757_);
lean_dec_ref(v_val_756_);
v_name_758_ = lean_ctor_get(v_toConstantVal_757_, 0);
lean_inc(v_name_758_);
lean_dec_ref(v_toConstantVal_757_);
v___x_759_ = lean_box(0);
v___x_760_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_760_, 0, v_name_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
if (lean_obj_tag(v_a_761_) == 0)
{
lean_object* v___x_763_; 
v___x_763_ = l_List_reverse___redArg(v_a_762_);
return v___x_763_;
}
else
{
lean_object* v_head_764_; lean_object* v_tail_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_774_; 
v_head_764_ = lean_ctor_get(v_a_761_, 0);
v_tail_765_ = lean_ctor_get(v_a_761_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v_a_761_);
if (v_isSharedCheck_774_ == 0)
{
v___x_767_ = v_a_761_;
v_isShared_768_ = v_isSharedCheck_774_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_tail_765_);
lean_inc(v_head_764_);
lean_dec(v_a_761_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_774_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v_name_769_; lean_object* v___x_771_; 
v_name_769_ = lean_ctor_get(v_head_764_, 0);
lean_inc(v_name_769_);
lean_dec(v_head_764_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 1, v_a_762_);
lean_ctor_set(v___x_767_, 0, v_name_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_name_769_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_a_762_);
v___x_771_ = v_reuseFailAlloc_773_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
v_a_761_ = v_tail_765_;
v_a_762_ = v___x_771_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
if (lean_obj_tag(v_a_778_) == 0)
{
lean_object* v___x_780_; 
v___x_780_ = lean_array_to_list(v_a_779_);
return v___x_780_;
}
else
{
lean_object* v_head_781_; lean_object* v_tail_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_798_; 
v_head_781_ = lean_ctor_get(v_a_778_, 0);
v_tail_782_ = lean_ctor_get(v_a_778_, 1);
v_isSharedCheck_798_ = !lean_is_exclusive(v_a_778_);
if (v_isSharedCheck_798_ == 0)
{
v___x_784_ = v_a_778_;
v_isShared_785_ = v_isSharedCheck_798_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_tail_782_);
lean_inc(v_head_781_);
lean_dec(v_a_778_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_798_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_name_786_; lean_object* v_ctors_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v_name_786_ = lean_ctor_get(v_head_781_, 0);
lean_inc(v_name_786_);
v_ctors_787_ = lean_ctor_get(v_head_781_, 2);
lean_inc(v_ctors_787_);
lean_dec(v_head_781_);
v___x_788_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1));
v___x_789_ = l_Lean_Name_appendCore(v_name_786_, v___x_788_);
v___x_790_ = lean_box(0);
v___x_791_ = l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(v_ctors_787_, v___x_790_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v___x_791_);
lean_ctor_set(v___x_784_, 0, v___x_789_);
v___x_793_ = v___x_784_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v___x_791_);
v___x_793_ = v_reuseFailAlloc_797_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_794_, 0, v_name_786_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_779_, v___x_794_);
v_a_778_ = v_tail_782_;
v_a_779_ = v___x_795_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getNames(lean_object* v_x_825_){
_start:
{
switch(lean_obj_tag(v_x_825_))
{
case 4:
{
lean_object* v___x_826_; 
v___x_826_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__9));
return v___x_826_;
}
case 5:
{
lean_object* v_defns_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_defns_827_ = lean_ctor_get(v_x_825_, 0);
lean_inc(v_defns_827_);
lean_dec_ref_known(v_x_825_, 1);
v___x_828_ = lean_box(0);
v___x_829_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_827_, v___x_828_);
return v___x_829_;
}
case 6:
{
lean_object* v_types_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_types_830_ = lean_ctor_get(v_x_825_, 2);
lean_inc(v_types_830_);
lean_dec_ref_known(v_x_825_, 3);
v___x_831_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__10));
v___x_832_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(v_types_830_, v___x_831_);
return v___x_832_;
}
default: 
{
lean_object* v_val_833_; lean_object* v_toConstantVal_834_; lean_object* v_name_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_val_833_ = lean_ctor_get(v_x_825_, 0);
lean_inc_ref(v_val_833_);
lean_dec(v_x_825_);
v_toConstantVal_834_ = lean_ctor_get(v_val_833_, 0);
lean_inc_ref(v_toConstantVal_834_);
lean_dec_ref(v_val_833_);
v_name_835_ = lean_ctor_get(v_toConstantVal_834_, 0);
lean_inc(v_name_835_);
lean_dec_ref(v_toConstantVal_834_);
v___x_836_ = lean_box(0);
v___x_837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_837_, 0, v_name_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
return v___x_837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__0(lean_object* v_f_838_, lean_object* v_value_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_apply_2(v_f_838_, v_a_840_, v_value_839_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__3(lean_object* v_f_842_, lean_object* v_value_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = lean_apply_2(v_f_842_, v_a_844_, v_value_843_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__1(lean_object* v_f_846_, lean_object* v_toBind_847_, lean_object* v_a_848_, lean_object* v_v_849_){
_start:
{
lean_object* v_toConstantVal_850_; lean_object* v_value_851_; lean_object* v_type_852_; lean_object* v___f_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_toConstantVal_850_ = lean_ctor_get(v_v_849_, 0);
lean_inc_ref(v_toConstantVal_850_);
v_value_851_ = lean_ctor_get(v_v_849_, 1);
lean_inc_ref(v_value_851_);
lean_dec_ref(v_v_849_);
v_type_852_ = lean_ctor_get(v_toConstantVal_850_, 2);
lean_inc_ref(v_type_852_);
lean_dec_ref(v_toConstantVal_850_);
lean_inc(v_f_846_);
v___f_853_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__3), 3, 2);
lean_closure_set(v___f_853_, 0, v_f_846_);
lean_closure_set(v___f_853_, 1, v_value_851_);
v___x_854_ = lean_apply_2(v_f_846_, v_a_848_, v_type_852_);
v___x_855_ = lean_apply_4(v_toBind_847_, lean_box(0), lean_box(0), v___x_854_, v___f_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__2(lean_object* v_f_856_, lean_object* v_a_857_, lean_object* v_ctor_858_){
_start:
{
lean_object* v_type_859_; lean_object* v___x_860_; 
v_type_859_ = lean_ctor_get(v_ctor_858_, 1);
lean_inc_ref(v_type_859_);
lean_dec_ref(v_ctor_858_);
v___x_860_ = lean_apply_2(v_f_856_, v_a_857_, v_type_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__4(lean_object* v_inst_861_, lean_object* v___f_862_, lean_object* v_ctors_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_List_foldlM___redArg(v_inst_861_, v___f_862_, v_a_864_, v_ctors_863_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__5(lean_object* v_inst_866_, lean_object* v___f_867_, lean_object* v_f_868_, lean_object* v_toBind_869_, lean_object* v_a_870_, lean_object* v_inductType_871_){
_start:
{
lean_object* v_type_872_; lean_object* v_ctors_873_; lean_object* v___f_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_type_872_ = lean_ctor_get(v_inductType_871_, 1);
lean_inc_ref(v_type_872_);
v_ctors_873_ = lean_ctor_get(v_inductType_871_, 2);
lean_inc(v_ctors_873_);
lean_dec_ref(v_inductType_871_);
v___f_874_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__4), 4, 3);
lean_closure_set(v___f_874_, 0, v_inst_866_);
lean_closure_set(v___f_874_, 1, v___f_867_);
lean_closure_set(v___f_874_, 2, v_ctors_873_);
v___x_875_ = lean_apply_2(v_f_868_, v_a_870_, v_type_872_);
v___x_876_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_875_, v___f_874_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object* v_inst_877_, lean_object* v_d_878_, lean_object* v_f_879_, lean_object* v_a_880_){
_start:
{
switch(lean_obj_tag(v_d_878_))
{
case 0:
{
lean_object* v_val_881_; lean_object* v_toConstantVal_882_; lean_object* v_type_883_; lean_object* v___x_884_; 
lean_dec_ref(v_inst_877_);
v_val_881_ = lean_ctor_get(v_d_878_, 0);
lean_inc_ref(v_val_881_);
lean_dec_ref_known(v_d_878_, 1);
v_toConstantVal_882_ = lean_ctor_get(v_val_881_, 0);
lean_inc_ref(v_toConstantVal_882_);
lean_dec_ref(v_val_881_);
v_type_883_ = lean_ctor_get(v_toConstantVal_882_, 2);
lean_inc_ref(v_type_883_);
lean_dec_ref(v_toConstantVal_882_);
v___x_884_ = lean_apply_2(v_f_879_, v_a_880_, v_type_883_);
return v___x_884_;
}
case 4:
{
lean_object* v_toApplicative_885_; lean_object* v_toPure_886_; lean_object* v___x_887_; 
v_toApplicative_885_ = lean_ctor_get(v_inst_877_, 0);
lean_inc_ref(v_toApplicative_885_);
lean_dec(v_f_879_);
lean_dec_ref(v_inst_877_);
v_toPure_886_ = lean_ctor_get(v_toApplicative_885_, 1);
lean_inc(v_toPure_886_);
lean_dec_ref(v_toApplicative_885_);
v___x_887_ = lean_apply_2(v_toPure_886_, lean_box(0), v_a_880_);
return v___x_887_;
}
case 5:
{
lean_object* v_toBind_888_; lean_object* v_defns_889_; lean_object* v___f_890_; lean_object* v___x_891_; 
v_toBind_888_ = lean_ctor_get(v_inst_877_, 1);
v_defns_889_ = lean_ctor_get(v_d_878_, 0);
lean_inc(v_defns_889_);
lean_dec_ref_known(v_d_878_, 1);
lean_inc(v_toBind_888_);
v___f_890_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_890_, 0, v_f_879_);
lean_closure_set(v___f_890_, 1, v_toBind_888_);
v___x_891_ = l_List_foldlM___redArg(v_inst_877_, v___f_890_, v_a_880_, v_defns_889_);
return v___x_891_;
}
case 6:
{
lean_object* v_toBind_892_; lean_object* v_types_893_; lean_object* v___f_894_; lean_object* v___f_895_; lean_object* v___x_896_; 
v_toBind_892_ = lean_ctor_get(v_inst_877_, 1);
v_types_893_ = lean_ctor_get(v_d_878_, 2);
lean_inc(v_types_893_);
lean_dec_ref_known(v_d_878_, 3);
lean_inc(v_f_879_);
v___f_894_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__2), 3, 1);
lean_closure_set(v___f_894_, 0, v_f_879_);
lean_inc(v_toBind_892_);
lean_inc_ref(v_inst_877_);
v___f_895_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__5), 6, 4);
lean_closure_set(v___f_895_, 0, v_inst_877_);
lean_closure_set(v___f_895_, 1, v___f_894_);
lean_closure_set(v___f_895_, 2, v_f_879_);
lean_closure_set(v___f_895_, 3, v_toBind_892_);
v___x_896_ = l_List_foldlM___redArg(v_inst_877_, v___f_895_, v_a_880_, v_types_893_);
return v___x_896_;
}
default: 
{
lean_object* v_val_897_; lean_object* v_toConstantVal_898_; lean_object* v_toBind_899_; lean_object* v_value_900_; lean_object* v_type_901_; lean_object* v___f_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_val_897_ = lean_ctor_get(v_d_878_, 0);
lean_inc_ref(v_val_897_);
lean_dec(v_d_878_);
v_toConstantVal_898_ = lean_ctor_get(v_val_897_, 0);
lean_inc_ref(v_toConstantVal_898_);
v_toBind_899_ = lean_ctor_get(v_inst_877_, 1);
lean_inc(v_toBind_899_);
lean_dec_ref(v_inst_877_);
v_value_900_ = lean_ctor_get(v_val_897_, 1);
lean_inc_ref(v_value_900_);
lean_dec_ref(v_val_897_);
v_type_901_ = lean_ctor_get(v_toConstantVal_898_, 2);
lean_inc_ref(v_type_901_);
lean_dec_ref(v_toConstantVal_898_);
lean_inc(v_f_879_);
v___f_902_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_902_, 0, v_f_879_);
lean_closure_set(v___f_902_, 1, v_value_900_);
v___x_903_ = lean_apply_2(v_f_879_, v_a_880_, v_type_901_);
v___x_904_ = lean_apply_4(v_toBind_899_, lean_box(0), lean_box(0), v___x_903_, v___f_902_);
return v___x_904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM(lean_object* v_00_u03b1_905_, lean_object* v_m_906_, lean_object* v_inst_907_, lean_object* v_d_908_, lean_object* v_f_909_, lean_object* v_a_910_){
_start:
{
lean_object* v___x_911_; 
v___x_911_ = l_Lean_Declaration_foldExprM___redArg(v_inst_907_, v_d_908_, v_f_909_, v_a_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg___lam__0(lean_object* v_f_912_, lean_object* v_x_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = lean_apply_1(v_f_912_, v_a_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg(lean_object* v_inst_916_, lean_object* v_d_917_, lean_object* v_f_918_){
_start:
{
lean_object* v___f_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___f_919_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_919_, 0, v_f_918_);
v___x_920_ = lean_box(0);
v___x_921_ = l_Lean_Declaration_foldExprM___redArg(v_inst_916_, v_d_917_, v___f_919_, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM(lean_object* v_m_922_, lean_object* v_inst_923_, lean_object* v_d_924_, lean_object* v_f_925_){
_start:
{
lean_object* v___f_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___f_926_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_926_, 0, v_f_925_);
v___x_927_ = lean_box(0);
v___x_928_ = l_Lean_Declaration_foldExprM___redArg(v_inst_923_, v_d_924_, v___f_926_, v___x_927_);
return v___x_928_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default___closed__0(void){
_start:
{
uint8_t v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_929_ = 0;
v___x_930_ = lean_box(0);
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_932_ = l_Lean_instInhabitedConstantVal_default;
v___x_933_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_933_, 0, v___x_932_);
lean_ctor_set(v___x_933_, 1, v___x_931_);
lean_ctor_set(v___x_933_, 2, v___x_931_);
lean_ctor_set(v___x_933_, 3, v___x_930_);
lean_ctor_set(v___x_933_, 4, v___x_930_);
lean_ctor_set(v___x_933_, 5, v___x_931_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*6, v___x_929_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*6 + 1, v___x_929_);
lean_ctor_set_uint8(v___x_933_, sizeof(void*)*6 + 2, v___x_929_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default(void){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = lean_obj_once(&l_Lean_instInhabitedInductiveVal_default___closed__0, &l_Lean_instInhabitedInductiveVal_default___closed__0_once, _init_l_Lean_instInhabitedInductiveVal_default___closed__0);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal(void){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_instInhabitedInductiveVal_default;
return v___x_935_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveVal_beq(lean_object* v_x_936_, lean_object* v_x_937_){
_start:
{
lean_object* v_toConstantVal_938_; lean_object* v_numParams_939_; lean_object* v_numIndices_940_; lean_object* v_all_941_; lean_object* v_ctors_942_; lean_object* v_numNested_943_; uint8_t v_isRec_944_; uint8_t v_isUnsafe_945_; uint8_t v_isReflexive_946_; lean_object* v_toConstantVal_947_; lean_object* v_numParams_948_; lean_object* v_numIndices_949_; lean_object* v_all_950_; lean_object* v_ctors_951_; lean_object* v_numNested_952_; uint8_t v_isRec_953_; uint8_t v_isUnsafe_954_; uint8_t v_isReflexive_955_; uint8_t v___y_957_; uint8_t v___y_959_; uint8_t v___x_960_; 
v_toConstantVal_938_ = lean_ctor_get(v_x_936_, 0);
v_numParams_939_ = lean_ctor_get(v_x_936_, 1);
v_numIndices_940_ = lean_ctor_get(v_x_936_, 2);
v_all_941_ = lean_ctor_get(v_x_936_, 3);
v_ctors_942_ = lean_ctor_get(v_x_936_, 4);
v_numNested_943_ = lean_ctor_get(v_x_936_, 5);
v_isRec_944_ = lean_ctor_get_uint8(v_x_936_, sizeof(void*)*6);
v_isUnsafe_945_ = lean_ctor_get_uint8(v_x_936_, sizeof(void*)*6 + 1);
v_isReflexive_946_ = lean_ctor_get_uint8(v_x_936_, sizeof(void*)*6 + 2);
v_toConstantVal_947_ = lean_ctor_get(v_x_937_, 0);
v_numParams_948_ = lean_ctor_get(v_x_937_, 1);
v_numIndices_949_ = lean_ctor_get(v_x_937_, 2);
v_all_950_ = lean_ctor_get(v_x_937_, 3);
v_ctors_951_ = lean_ctor_get(v_x_937_, 4);
v_numNested_952_ = lean_ctor_get(v_x_937_, 5);
v_isRec_953_ = lean_ctor_get_uint8(v_x_937_, sizeof(void*)*6);
v_isUnsafe_954_ = lean_ctor_get_uint8(v_x_937_, sizeof(void*)*6 + 1);
v_isReflexive_955_ = lean_ctor_get_uint8(v_x_937_, sizeof(void*)*6 + 2);
v___x_960_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_938_, v_toConstantVal_947_);
if (v___x_960_ == 0)
{
return v___x_960_;
}
else
{
uint8_t v___x_961_; 
v___x_961_ = lean_nat_dec_eq(v_numParams_939_, v_numParams_948_);
if (v___x_961_ == 0)
{
return v___x_961_;
}
else
{
uint8_t v___x_962_; 
v___x_962_ = lean_nat_dec_eq(v_numIndices_940_, v_numIndices_949_);
if (v___x_962_ == 0)
{
return v___x_962_;
}
else
{
uint8_t v___x_963_; 
v___x_963_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_941_, v_all_950_);
if (v___x_963_ == 0)
{
return v___x_963_;
}
else
{
uint8_t v___x_964_; 
v___x_964_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_ctors_942_, v_ctors_951_);
if (v___x_964_ == 0)
{
return v___x_964_;
}
else
{
uint8_t v___x_965_; 
v___x_965_ = lean_nat_dec_eq(v_numNested_943_, v_numNested_952_);
if (v___x_965_ == 0)
{
return v___x_965_;
}
else
{
if (v_isRec_953_ == 0)
{
if (v_isRec_944_ == 0)
{
v___y_959_ = v___x_965_;
goto v___jp_958_;
}
else
{
return v_isRec_953_;
}
}
else
{
if (v_isRec_944_ == 0)
{
return v_isRec_944_;
}
else
{
v___y_959_ = v_isRec_944_;
goto v___jp_958_;
}
}
}
}
}
}
}
}
v___jp_956_:
{
if (v_isReflexive_955_ == 0)
{
if (v_isReflexive_946_ == 0)
{
return v___y_957_;
}
else
{
return v_isReflexive_955_;
}
}
else
{
return v_isReflexive_946_;
}
}
v___jp_958_:
{
if (v_isUnsafe_954_ == 0)
{
if (v_isUnsafe_945_ == 0)
{
v___y_957_ = v___y_959_;
goto v___jp_956_;
}
else
{
return v_isUnsafe_954_;
}
}
else
{
if (v_isUnsafe_945_ == 0)
{
return v_isUnsafe_945_;
}
else
{
v___y_957_ = v_isUnsafe_945_;
goto v___jp_956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveVal_beq___boxed(lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
uint8_t v_res_968_; lean_object* v_r_969_; 
v_res_968_ = l_Lean_instBEqInductiveVal_beq(v_x_966_, v_x_967_);
lean_dec_ref(v_x_967_);
lean_dec_ref(v_x_966_);
v_r_969_ = lean_box(v_res_968_);
return v_r_969_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_val(lean_object* v_name_972_, lean_object* v_levelParams_973_, lean_object* v_type_974_, lean_object* v_numParams_975_, lean_object* v_numIndices_976_, lean_object* v_all_977_, lean_object* v_ctors_978_, lean_object* v_numNested_979_, uint8_t v_isRec_980_, uint8_t v_isUnsafe_981_, uint8_t v_isReflexive_982_){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_983_, 0, v_name_972_);
lean_ctor_set(v___x_983_, 1, v_levelParams_973_);
lean_ctor_set(v___x_983_, 2, v_type_974_);
v___x_984_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v_numParams_975_);
lean_ctor_set(v___x_984_, 2, v_numIndices_976_);
lean_ctor_set(v___x_984_, 3, v_all_977_);
lean_ctor_set(v___x_984_, 4, v_ctors_978_);
lean_ctor_set(v___x_984_, 5, v_numNested_979_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*6, v_isRec_980_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*6 + 1, v_isUnsafe_981_);
lean_ctor_set_uint8(v___x_984_, sizeof(void*)*6 + 2, v_isReflexive_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveValEx___boxed(lean_object* v_name_985_, lean_object* v_levelParams_986_, lean_object* v_type_987_, lean_object* v_numParams_988_, lean_object* v_numIndices_989_, lean_object* v_all_990_, lean_object* v_ctors_991_, lean_object* v_numNested_992_, lean_object* v_isRec_993_, lean_object* v_isUnsafe_994_, lean_object* v_isReflexive_995_){
_start:
{
uint8_t v_isRec_boxed_996_; uint8_t v_isUnsafe_boxed_997_; uint8_t v_isReflexive_boxed_998_; lean_object* v_res_999_; 
v_isRec_boxed_996_ = lean_unbox(v_isRec_993_);
v_isUnsafe_boxed_997_ = lean_unbox(v_isUnsafe_994_);
v_isReflexive_boxed_998_ = lean_unbox(v_isReflexive_995_);
v_res_999_ = lean_mk_inductive_val(v_name_985_, v_levelParams_986_, v_type_987_, v_numParams_988_, v_numIndices_989_, v_all_990_, v_ctors_991_, v_numNested_992_, v_isRec_boxed_996_, v_isUnsafe_boxed_997_, v_isReflexive_boxed_998_);
return v_res_999_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_rec(lean_object* v_v_1000_){
_start:
{
uint8_t v_isRec_1001_; 
v_isRec_1001_ = lean_ctor_get_uint8(v_v_1000_, sizeof(void*)*6);
lean_dec_ref(v_v_1000_);
return v_isRec_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isRecEx___boxed(lean_object* v_v_1002_){
_start:
{
uint8_t v_res_1003_; lean_object* v_r_1004_; 
v_res_1003_ = lean_inductive_val_is_rec(v_v_1002_);
v_r_1004_ = lean_box(v_res_1003_);
return v_r_1004_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_unsafe(lean_object* v_v_1005_){
_start:
{
uint8_t v_isUnsafe_1006_; 
v_isUnsafe_1006_ = lean_ctor_get_uint8(v_v_1005_, sizeof(void*)*6 + 1);
lean_dec_ref(v_v_1005_);
return v_isUnsafe_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isUnsafeEx___boxed(lean_object* v_v_1007_){
_start:
{
uint8_t v_res_1008_; lean_object* v_r_1009_; 
v_res_1008_ = lean_inductive_val_is_unsafe(v_v_1007_);
v_r_1009_ = lean_box(v_res_1008_);
return v_r_1009_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_reflexive(lean_object* v_v_1010_){
_start:
{
uint8_t v_isReflexive_1011_; 
v_isReflexive_1011_ = lean_ctor_get_uint8(v_v_1010_, sizeof(void*)*6 + 2);
lean_dec_ref(v_v_1010_);
return v_isReflexive_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isReflexiveEx___boxed(lean_object* v_v_1012_){
_start:
{
uint8_t v_res_1013_; lean_object* v_r_1014_; 
v_res_1013_ = lean_inductive_val_is_reflexive(v_v_1012_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors(lean_object* v_v_1015_){
_start:
{
lean_object* v_ctors_1016_; lean_object* v___x_1017_; 
v_ctors_1016_ = lean_ctor_get(v_v_1015_, 4);
v___x_1017_ = l_List_lengthTR___redArg(v_ctors_1016_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors___boxed(lean_object* v_v_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Lean_InductiveVal_numCtors(v_v_1018_);
lean_dec_ref(v_v_1018_);
return v_res_1019_;
}
}
LEAN_EXPORT uint8_t l_Lean_InductiveVal_isNested(lean_object* v_v_1020_){
_start:
{
lean_object* v_numNested_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v_numNested_1021_ = lean_ctor_get(v_v_1020_, 5);
v___x_1022_ = lean_unsigned_to_nat(0u);
v___x_1023_ = lean_nat_dec_lt(v___x_1022_, v_numNested_1021_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isNested___boxed(lean_object* v_v_1024_){
_start:
{
uint8_t v_res_1025_; lean_object* v_r_1026_; 
v_res_1025_ = l_Lean_InductiveVal_isNested(v_v_1024_);
lean_dec_ref(v_v_1024_);
v_r_1026_ = lean_box(v_res_1025_);
return v_r_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object* v_v_1027_){
_start:
{
lean_object* v_all_1028_; lean_object* v_numNested_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_all_1028_ = lean_ctor_get(v_v_1027_, 3);
v_numNested_1029_ = lean_ctor_get(v_v_1027_, 5);
v___x_1030_ = l_List_lengthTR___redArg(v_all_1028_);
v___x_1031_ = lean_nat_add(v___x_1030_, v_numNested_1029_);
lean_dec(v___x_1030_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers___boxed(lean_object* v_v_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_InductiveVal_numTypeFormers(v_v_1032_);
lean_dec_ref(v_v_1032_);
return v_res_1033_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1034_ = 0;
v___x_1035_ = lean_unsigned_to_nat(0u);
v___x_1036_ = lean_box(0);
v___x_1037_ = l_Lean_instInhabitedConstantVal_default;
v___x_1038_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v___x_1036_);
lean_ctor_set(v___x_1038_, 2, v___x_1035_);
lean_ctor_set(v___x_1038_, 3, v___x_1035_);
lean_ctor_set(v___x_1038_, 4, v___x_1035_);
lean_ctor_set_uint8(v___x_1038_, sizeof(void*)*5, v___x_1034_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default(void){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_obj_once(&l_Lean_instInhabitedConstructorVal_default___closed__0, &l_Lean_instInhabitedConstructorVal_default___closed__0_once, _init_l_Lean_instInhabitedConstructorVal_default___closed__0);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal(void){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_instInhabitedConstructorVal_default;
return v___x_1040_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructorVal_beq(lean_object* v_x_1041_, lean_object* v_x_1042_){
_start:
{
lean_object* v_toConstantVal_1043_; lean_object* v_induct_1044_; lean_object* v_cidx_1045_; lean_object* v_numParams_1046_; lean_object* v_numFields_1047_; uint8_t v_isUnsafe_1048_; lean_object* v_toConstantVal_1049_; lean_object* v_induct_1050_; lean_object* v_cidx_1051_; lean_object* v_numParams_1052_; lean_object* v_numFields_1053_; uint8_t v_isUnsafe_1054_; uint8_t v___x_1055_; 
v_toConstantVal_1043_ = lean_ctor_get(v_x_1041_, 0);
v_induct_1044_ = lean_ctor_get(v_x_1041_, 1);
v_cidx_1045_ = lean_ctor_get(v_x_1041_, 2);
v_numParams_1046_ = lean_ctor_get(v_x_1041_, 3);
v_numFields_1047_ = lean_ctor_get(v_x_1041_, 4);
v_isUnsafe_1048_ = lean_ctor_get_uint8(v_x_1041_, sizeof(void*)*5);
v_toConstantVal_1049_ = lean_ctor_get(v_x_1042_, 0);
v_induct_1050_ = lean_ctor_get(v_x_1042_, 1);
v_cidx_1051_ = lean_ctor_get(v_x_1042_, 2);
v_numParams_1052_ = lean_ctor_get(v_x_1042_, 3);
v_numFields_1053_ = lean_ctor_get(v_x_1042_, 4);
v_isUnsafe_1054_ = lean_ctor_get_uint8(v_x_1042_, sizeof(void*)*5);
v___x_1055_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1043_, v_toConstantVal_1049_);
if (v___x_1055_ == 0)
{
return v___x_1055_;
}
else
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_name_eq(v_induct_1044_, v_induct_1050_);
if (v___x_1056_ == 0)
{
return v___x_1056_;
}
else
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_nat_dec_eq(v_cidx_1045_, v_cidx_1051_);
if (v___x_1057_ == 0)
{
return v___x_1057_;
}
else
{
uint8_t v___x_1058_; 
v___x_1058_ = lean_nat_dec_eq(v_numParams_1046_, v_numParams_1052_);
if (v___x_1058_ == 0)
{
return v___x_1058_;
}
else
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_nat_dec_eq(v_numFields_1047_, v_numFields_1053_);
if (v___x_1059_ == 0)
{
return v___x_1059_;
}
else
{
if (v_isUnsafe_1054_ == 0)
{
if (v_isUnsafe_1048_ == 0)
{
return v___x_1059_;
}
else
{
return v_isUnsafe_1054_;
}
}
else
{
return v_isUnsafe_1048_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructorVal_beq___boxed(lean_object* v_x_1060_, lean_object* v_x_1061_){
_start:
{
uint8_t v_res_1062_; lean_object* v_r_1063_; 
v_res_1062_ = l_Lean_instBEqConstructorVal_beq(v_x_1060_, v_x_1061_);
lean_dec_ref(v_x_1061_);
lean_dec_ref(v_x_1060_);
v_r_1063_ = lean_box(v_res_1062_);
return v_r_1063_;
}
}
LEAN_EXPORT lean_object* lean_mk_constructor_val(lean_object* v_name_1066_, lean_object* v_levelParams_1067_, lean_object* v_type_1068_, lean_object* v_induct_1069_, lean_object* v_cidx_1070_, lean_object* v_numParams_1071_, lean_object* v_numFields_1072_, uint8_t v_isUnsafe_1073_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1074_, 0, v_name_1066_);
lean_ctor_set(v___x_1074_, 1, v_levelParams_1067_);
lean_ctor_set(v___x_1074_, 2, v_type_1068_);
v___x_1075_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
lean_ctor_set(v___x_1075_, 1, v_induct_1069_);
lean_ctor_set(v___x_1075_, 2, v_cidx_1070_);
lean_ctor_set(v___x_1075_, 3, v_numParams_1071_);
lean_ctor_set(v___x_1075_, 4, v_numFields_1072_);
lean_ctor_set_uint8(v___x_1075_, sizeof(void*)*5, v_isUnsafe_1073_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstructorValEx___boxed(lean_object* v_name_1076_, lean_object* v_levelParams_1077_, lean_object* v_type_1078_, lean_object* v_induct_1079_, lean_object* v_cidx_1080_, lean_object* v_numParams_1081_, lean_object* v_numFields_1082_, lean_object* v_isUnsafe_1083_){
_start:
{
uint8_t v_isUnsafe_boxed_1084_; lean_object* v_res_1085_; 
v_isUnsafe_boxed_1084_ = lean_unbox(v_isUnsafe_1083_);
v_res_1085_ = lean_mk_constructor_val(v_name_1076_, v_levelParams_1077_, v_type_1078_, v_induct_1079_, v_cidx_1080_, v_numParams_1081_, v_numFields_1082_, v_isUnsafe_boxed_1084_);
return v_res_1085_;
}
}
LEAN_EXPORT uint8_t lean_constructor_val_is_unsafe(lean_object* v_v_1086_){
_start:
{
uint8_t v_isUnsafe_1087_; 
v_isUnsafe_1087_ = lean_ctor_get_uint8(v_v_1086_, sizeof(void*)*5);
lean_dec_ref(v_v_1086_);
return v_isUnsafe_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstructorVal_isUnsafeEx___boxed(lean_object* v_v_1088_){
_start:
{
uint8_t v_res_1089_; lean_object* v_r_1090_; 
v_res_1089_ = lean_constructor_val_is_unsafe(v_v_1088_);
v_r_1090_ = lean_box(v_res_1089_);
return v_r_1090_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default___closed__0(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1091_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v___x_1092_);
lean_ctor_set(v___x_1094_, 2, v___x_1091_);
return v___x_1094_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default(void){
_start:
{
lean_object* v___x_1095_; 
v___x_1095_ = lean_obj_once(&l_Lean_instInhabitedRecursorRule_default___closed__0, &l_Lean_instInhabitedRecursorRule_default___closed__0_once, _init_l_Lean_instInhabitedRecursorRule_default___closed__0);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule(void){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = l_Lean_instInhabitedRecursorRule_default;
return v___x_1096_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorRule_beq(lean_object* v_x_1097_, lean_object* v_x_1098_){
_start:
{
lean_object* v_ctor_1099_; lean_object* v_nfields_1100_; lean_object* v_rhs_1101_; lean_object* v_ctor_1102_; lean_object* v_nfields_1103_; lean_object* v_rhs_1104_; uint8_t v___x_1105_; 
v_ctor_1099_ = lean_ctor_get(v_x_1097_, 0);
v_nfields_1100_ = lean_ctor_get(v_x_1097_, 1);
v_rhs_1101_ = lean_ctor_get(v_x_1097_, 2);
v_ctor_1102_ = lean_ctor_get(v_x_1098_, 0);
v_nfields_1103_ = lean_ctor_get(v_x_1098_, 1);
v_rhs_1104_ = lean_ctor_get(v_x_1098_, 2);
v___x_1105_ = lean_name_eq(v_ctor_1099_, v_ctor_1102_);
if (v___x_1105_ == 0)
{
return v___x_1105_;
}
else
{
uint8_t v___x_1106_; 
v___x_1106_ = lean_nat_dec_eq(v_nfields_1100_, v_nfields_1103_);
if (v___x_1106_ == 0)
{
return v___x_1106_;
}
else
{
uint8_t v___x_1107_; 
v___x_1107_ = lean_expr_eqv(v_rhs_1101_, v_rhs_1104_);
return v___x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorRule_beq___boxed(lean_object* v_x_1108_, lean_object* v_x_1109_){
_start:
{
uint8_t v_res_1110_; lean_object* v_r_1111_; 
v_res_1110_ = l_Lean_instBEqRecursorRule_beq(v_x_1108_, v_x_1109_);
lean_dec_ref(v_x_1109_);
lean_dec_ref(v_x_1108_);
v_r_1111_ = lean_box(v_res_1110_);
return v_r_1111_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1114_ = 0;
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_box(0);
v___x_1117_ = l_Lean_instInhabitedConstantVal_default;
v___x_1118_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v___x_1116_);
lean_ctor_set(v___x_1118_, 2, v___x_1115_);
lean_ctor_set(v___x_1118_, 3, v___x_1115_);
lean_ctor_set(v___x_1118_, 4, v___x_1115_);
lean_ctor_set(v___x_1118_, 5, v___x_1115_);
lean_ctor_set(v___x_1118_, 6, v___x_1116_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*7, v___x_1114_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*7 + 1, v___x_1114_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default(void){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_obj_once(&l_Lean_instInhabitedRecursorVal_default___closed__0, &l_Lean_instInhabitedRecursorVal_default___closed__0_once, _init_l_Lean_instInhabitedRecursorVal_default___closed__0);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal(void){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = l_Lean_instInhabitedRecursorVal_default;
return v___x_1120_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(lean_object* v_x_1121_, lean_object* v_x_1122_){
_start:
{
if (lean_obj_tag(v_x_1121_) == 0)
{
if (lean_obj_tag(v_x_1122_) == 0)
{
uint8_t v___x_1123_; 
v___x_1123_ = 1;
return v___x_1123_;
}
else
{
uint8_t v___x_1124_; 
v___x_1124_ = 0;
return v___x_1124_;
}
}
else
{
if (lean_obj_tag(v_x_1122_) == 0)
{
uint8_t v___x_1125_; 
v___x_1125_ = 0;
return v___x_1125_;
}
else
{
lean_object* v_head_1126_; lean_object* v_tail_1127_; lean_object* v_head_1128_; lean_object* v_tail_1129_; uint8_t v___x_1130_; 
v_head_1126_ = lean_ctor_get(v_x_1121_, 0);
v_tail_1127_ = lean_ctor_get(v_x_1121_, 1);
v_head_1128_ = lean_ctor_get(v_x_1122_, 0);
v_tail_1129_ = lean_ctor_get(v_x_1122_, 1);
v___x_1130_ = l_Lean_instBEqRecursorRule_beq(v_head_1126_, v_head_1128_);
if (v___x_1130_ == 0)
{
return v___x_1130_;
}
else
{
v_x_1121_ = v_tail_1127_;
v_x_1122_ = v_tail_1129_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0___boxed(lean_object* v_x_1132_, lean_object* v_x_1133_){
_start:
{
uint8_t v_res_1134_; lean_object* v_r_1135_; 
v_res_1134_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_x_1132_, v_x_1133_);
lean_dec(v_x_1133_);
lean_dec(v_x_1132_);
v_r_1135_ = lean_box(v_res_1134_);
return v_r_1135_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorVal_beq(lean_object* v_x_1136_, lean_object* v_x_1137_){
_start:
{
lean_object* v_toConstantVal_1138_; lean_object* v_all_1139_; lean_object* v_numParams_1140_; lean_object* v_numIndices_1141_; lean_object* v_numMotives_1142_; lean_object* v_numMinors_1143_; lean_object* v_rules_1144_; uint8_t v_k_1145_; uint8_t v_isUnsafe_1146_; lean_object* v_toConstantVal_1147_; lean_object* v_all_1148_; lean_object* v_numParams_1149_; lean_object* v_numIndices_1150_; lean_object* v_numMotives_1151_; lean_object* v_numMinors_1152_; lean_object* v_rules_1153_; uint8_t v_k_1154_; uint8_t v_isUnsafe_1155_; uint8_t v___y_1157_; uint8_t v___x_1158_; 
v_toConstantVal_1138_ = lean_ctor_get(v_x_1136_, 0);
v_all_1139_ = lean_ctor_get(v_x_1136_, 1);
v_numParams_1140_ = lean_ctor_get(v_x_1136_, 2);
v_numIndices_1141_ = lean_ctor_get(v_x_1136_, 3);
v_numMotives_1142_ = lean_ctor_get(v_x_1136_, 4);
v_numMinors_1143_ = lean_ctor_get(v_x_1136_, 5);
v_rules_1144_ = lean_ctor_get(v_x_1136_, 6);
v_k_1145_ = lean_ctor_get_uint8(v_x_1136_, sizeof(void*)*7);
v_isUnsafe_1146_ = lean_ctor_get_uint8(v_x_1136_, sizeof(void*)*7 + 1);
v_toConstantVal_1147_ = lean_ctor_get(v_x_1137_, 0);
v_all_1148_ = lean_ctor_get(v_x_1137_, 1);
v_numParams_1149_ = lean_ctor_get(v_x_1137_, 2);
v_numIndices_1150_ = lean_ctor_get(v_x_1137_, 3);
v_numMotives_1151_ = lean_ctor_get(v_x_1137_, 4);
v_numMinors_1152_ = lean_ctor_get(v_x_1137_, 5);
v_rules_1153_ = lean_ctor_get(v_x_1137_, 6);
v_k_1154_ = lean_ctor_get_uint8(v_x_1137_, sizeof(void*)*7);
v_isUnsafe_1155_ = lean_ctor_get_uint8(v_x_1137_, sizeof(void*)*7 + 1);
v___x_1158_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1138_, v_toConstantVal_1147_);
if (v___x_1158_ == 0)
{
return v___x_1158_;
}
else
{
uint8_t v___x_1159_; 
v___x_1159_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_1139_, v_all_1148_);
if (v___x_1159_ == 0)
{
return v___x_1159_;
}
else
{
uint8_t v___x_1160_; 
v___x_1160_ = lean_nat_dec_eq(v_numParams_1140_, v_numParams_1149_);
if (v___x_1160_ == 0)
{
return v___x_1160_;
}
else
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_nat_dec_eq(v_numIndices_1141_, v_numIndices_1150_);
if (v___x_1161_ == 0)
{
return v___x_1161_;
}
else
{
uint8_t v___x_1162_; 
v___x_1162_ = lean_nat_dec_eq(v_numMotives_1142_, v_numMotives_1151_);
if (v___x_1162_ == 0)
{
return v___x_1162_;
}
else
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_nat_dec_eq(v_numMinors_1143_, v_numMinors_1152_);
if (v___x_1163_ == 0)
{
return v___x_1163_;
}
else
{
uint8_t v___x_1164_; 
v___x_1164_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_rules_1144_, v_rules_1153_);
if (v___x_1164_ == 0)
{
return v___x_1164_;
}
else
{
if (v_k_1154_ == 0)
{
if (v_k_1145_ == 0)
{
v___y_1157_ = v___x_1164_;
goto v___jp_1156_;
}
else
{
return v_k_1154_;
}
}
else
{
if (v_k_1145_ == 0)
{
return v_k_1145_;
}
else
{
v___y_1157_ = v_k_1145_;
goto v___jp_1156_;
}
}
}
}
}
}
}
}
}
v___jp_1156_:
{
if (v_isUnsafe_1155_ == 0)
{
if (v_isUnsafe_1146_ == 0)
{
return v___y_1157_;
}
else
{
return v_isUnsafe_1155_;
}
}
else
{
return v_isUnsafe_1146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorVal_beq___boxed(lean_object* v_x_1165_, lean_object* v_x_1166_){
_start:
{
uint8_t v_res_1167_; lean_object* v_r_1168_; 
v_res_1167_ = l_Lean_instBEqRecursorVal_beq(v_x_1165_, v_x_1166_);
lean_dec_ref(v_x_1166_);
lean_dec_ref(v_x_1165_);
v_r_1168_ = lean_box(v_res_1167_);
return v_r_1168_;
}
}
LEAN_EXPORT lean_object* lean_mk_recursor_val(lean_object* v_name_1171_, lean_object* v_levelParams_1172_, lean_object* v_type_1173_, lean_object* v_all_1174_, lean_object* v_numParams_1175_, lean_object* v_numIndices_1176_, lean_object* v_numMotives_1177_, lean_object* v_numMinors_1178_, lean_object* v_rules_1179_, uint8_t v_k_1180_, uint8_t v_isUnsafe_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1182_, 0, v_name_1171_);
lean_ctor_set(v___x_1182_, 1, v_levelParams_1172_);
lean_ctor_set(v___x_1182_, 2, v_type_1173_);
v___x_1183_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1183_, 0, v___x_1182_);
lean_ctor_set(v___x_1183_, 1, v_all_1174_);
lean_ctor_set(v___x_1183_, 2, v_numParams_1175_);
lean_ctor_set(v___x_1183_, 3, v_numIndices_1176_);
lean_ctor_set(v___x_1183_, 4, v_numMotives_1177_);
lean_ctor_set(v___x_1183_, 5, v_numMinors_1178_);
lean_ctor_set(v___x_1183_, 6, v_rules_1179_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*7, v_k_1180_);
lean_ctor_set_uint8(v___x_1183_, sizeof(void*)*7 + 1, v_isUnsafe_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecursorValEx___boxed(lean_object* v_name_1184_, lean_object* v_levelParams_1185_, lean_object* v_type_1186_, lean_object* v_all_1187_, lean_object* v_numParams_1188_, lean_object* v_numIndices_1189_, lean_object* v_numMotives_1190_, lean_object* v_numMinors_1191_, lean_object* v_rules_1192_, lean_object* v_k_1193_, lean_object* v_isUnsafe_1194_){
_start:
{
uint8_t v_k_boxed_1195_; uint8_t v_isUnsafe_boxed_1196_; lean_object* v_res_1197_; 
v_k_boxed_1195_ = lean_unbox(v_k_1193_);
v_isUnsafe_boxed_1196_ = lean_unbox(v_isUnsafe_1194_);
v_res_1197_ = lean_mk_recursor_val(v_name_1184_, v_levelParams_1185_, v_type_1186_, v_all_1187_, v_numParams_1188_, v_numIndices_1189_, v_numMotives_1190_, v_numMinors_1191_, v_rules_1192_, v_k_boxed_1195_, v_isUnsafe_boxed_1196_);
return v_res_1197_;
}
}
LEAN_EXPORT uint8_t lean_recursor_k(lean_object* v_v_1198_){
_start:
{
uint8_t v_k_1199_; 
v_k_1199_ = lean_ctor_get_uint8(v_v_1198_, sizeof(void*)*7);
lean_dec_ref(v_v_1198_);
return v_k_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_kEx___boxed(lean_object* v_v_1200_){
_start:
{
uint8_t v_res_1201_; lean_object* v_r_1202_; 
v_res_1201_ = lean_recursor_k(v_v_1200_);
v_r_1202_ = lean_box(v_res_1201_);
return v_r_1202_;
}
}
LEAN_EXPORT uint8_t lean_recursor_is_unsafe(lean_object* v_v_1203_){
_start:
{
uint8_t v_isUnsafe_1204_; 
v_isUnsafe_1204_ = lean_ctor_get_uint8(v_v_1203_, sizeof(void*)*7 + 1);
lean_dec_ref(v_v_1203_);
return v_isUnsafe_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_isUnsafeEx___boxed(lean_object* v_v_1205_){
_start:
{
uint8_t v_res_1206_; lean_object* v_r_1207_; 
v_res_1206_ = lean_recursor_is_unsafe(v_v_1205_);
v_r_1207_ = lean_box(v_res_1206_);
return v_r_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object* v_v_1208_){
_start:
{
lean_object* v_numParams_1209_; lean_object* v_numIndices_1210_; lean_object* v_numMotives_1211_; lean_object* v_numMinors_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v_numParams_1209_ = lean_ctor_get(v_v_1208_, 2);
v_numIndices_1210_ = lean_ctor_get(v_v_1208_, 3);
v_numMotives_1211_ = lean_ctor_get(v_v_1208_, 4);
v_numMinors_1212_ = lean_ctor_get(v_v_1208_, 5);
v___x_1213_ = lean_nat_add(v_numParams_1209_, v_numMotives_1211_);
v___x_1214_ = lean_nat_add(v___x_1213_, v_numMinors_1212_);
lean_dec(v___x_1213_);
v___x_1215_ = lean_nat_add(v___x_1214_, v_numIndices_1210_);
lean_dec(v___x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx___boxed(lean_object* v_v_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Lean_RecursorVal_getMajorIdx(v_v_1216_);
lean_dec_ref(v_v_1216_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx(lean_object* v_v_1218_){
_start:
{
lean_object* v_numParams_1219_; lean_object* v_numMotives_1220_; lean_object* v_numMinors_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; 
v_numParams_1219_ = lean_ctor_get(v_v_1218_, 2);
v_numMotives_1220_ = lean_ctor_get(v_v_1218_, 4);
v_numMinors_1221_ = lean_ctor_get(v_v_1218_, 5);
v___x_1222_ = lean_nat_add(v_numParams_1219_, v_numMotives_1220_);
v___x_1223_ = lean_nat_add(v___x_1222_, v_numMinors_1221_);
lean_dec(v___x_1222_);
return v___x_1223_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx___boxed(lean_object* v_v_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_RecursorVal_getFirstIndexIdx(v_v_1224_);
lean_dec_ref(v_v_1224_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx(lean_object* v_v_1226_){
_start:
{
lean_object* v_numParams_1227_; lean_object* v_numMotives_1228_; lean_object* v___x_1229_; 
v_numParams_1227_ = lean_ctor_get(v_v_1226_, 2);
v_numMotives_1228_ = lean_ctor_get(v_v_1226_, 4);
v___x_1229_ = lean_nat_add(v_numParams_1227_, v_numMotives_1228_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx___boxed(lean_object* v_v_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_RecursorVal_getFirstMinorIdx(v_v_1230_);
lean_dec_ref(v_v_1230_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(lean_object* v_x_1232_, lean_object* v_x_1233_){
_start:
{
lean_object* v_zero_1234_; uint8_t v_isZero_1235_; 
v_zero_1234_ = lean_unsigned_to_nat(0u);
v_isZero_1235_ = lean_nat_dec_eq(v_x_1232_, v_zero_1234_);
if (v_isZero_1235_ == 1)
{
lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; 
lean_dec(v_x_1232_);
v___x_1236_ = l_Lean_Expr_bindingDomain_x21(v_x_1233_);
lean_dec_ref(v_x_1233_);
v___x_1237_ = l_Lean_Expr_getAppFn(v___x_1236_);
lean_dec_ref(v___x_1236_);
v___x_1238_ = l_Lean_Expr_constName_x21(v___x_1237_);
lean_dec_ref(v___x_1237_);
return v___x_1238_;
}
else
{
lean_object* v_one_1239_; lean_object* v_n_1240_; lean_object* v___x_1241_; 
v_one_1239_ = lean_unsigned_to_nat(1u);
v_n_1240_ = lean_nat_sub(v_x_1232_, v_one_1239_);
lean_dec(v_x_1232_);
v___x_1241_ = l_Lean_Expr_bindingBody_x21(v_x_1233_);
lean_dec_ref(v_x_1233_);
v_x_1232_ = v_n_1240_;
v_x_1233_ = v___x_1241_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorInduct(lean_object* v_v_1243_){
_start:
{
lean_object* v_toConstantVal_1244_; lean_object* v_type_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v_toConstantVal_1244_ = lean_ctor_get(v_v_1243_, 0);
v_type_1245_ = lean_ctor_get(v_toConstantVal_1244_, 2);
lean_inc_ref(v_type_1245_);
v___x_1246_ = l_Lean_RecursorVal_getMajorIdx(v_v_1243_);
lean_dec_ref(v_v_1243_);
v___x_1247_ = l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(v___x_1246_, v_type_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___impl(uint8_t v_x_1248_){
_start:
{
lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1249_ = lean_box(v_x_1248_);
v___x_1250_ = lean_obj_tag_nat(v___x_1249_);
lean_dec(v___x_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___impl___boxed(lean_object* v_x_1251_){
_start:
{
uint8_t v_x_4__boxed_1252_; lean_object* v_res_1253_; 
v_x_4__boxed_1252_ = lean_unbox(v_x_1251_);
v_res_1253_ = l_Lean_QuotKind_ctorIdx___impl(v_x_4__boxed_1252_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg(lean_object* v_k_1254_){
_start:
{
lean_inc(v_k_1254_);
return v_k_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg___boxed(lean_object* v_k_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_QuotKind_ctorElim___redArg(v_k_1255_);
lean_dec(v_k_1255_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim(lean_object* v_motive_1257_, lean_object* v_ctorIdx_1258_, uint8_t v_t_1259_, lean_object* v_h_1260_, lean_object* v_k_1261_){
_start:
{
lean_inc(v_k_1261_);
return v_k_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___boxed(lean_object* v_motive_1262_, lean_object* v_ctorIdx_1263_, lean_object* v_t_1264_, lean_object* v_h_1265_, lean_object* v_k_1266_){
_start:
{
uint8_t v_t_boxed_1267_; lean_object* v_res_1268_; 
v_t_boxed_1267_ = lean_unbox(v_t_1264_);
v_res_1268_ = l_Lean_QuotKind_ctorElim(v_motive_1262_, v_ctorIdx_1263_, v_t_boxed_1267_, v_h_1265_, v_k_1266_);
lean_dec(v_k_1266_);
lean_dec(v_ctorIdx_1263_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg(lean_object* v_type_1269_){
_start:
{
lean_inc(v_type_1269_);
return v_type_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg___boxed(lean_object* v_type_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_QuotKind_type_elim___redArg(v_type_1270_);
lean_dec(v_type_1270_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim(lean_object* v_motive_1272_, uint8_t v_t_1273_, lean_object* v_h_1274_, lean_object* v_type_1275_){
_start:
{
lean_inc(v_type_1275_);
return v_type_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___boxed(lean_object* v_motive_1276_, lean_object* v_t_1277_, lean_object* v_h_1278_, lean_object* v_type_1279_){
_start:
{
uint8_t v_t_boxed_1280_; lean_object* v_res_1281_; 
v_t_boxed_1280_ = lean_unbox(v_t_1277_);
v_res_1281_ = l_Lean_QuotKind_type_elim(v_motive_1276_, v_t_boxed_1280_, v_h_1278_, v_type_1279_);
lean_dec(v_type_1279_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg(lean_object* v_ctor_1282_){
_start:
{
lean_inc(v_ctor_1282_);
return v_ctor_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg___boxed(lean_object* v_ctor_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Lean_QuotKind_ctor_elim___redArg(v_ctor_1283_);
lean_dec(v_ctor_1283_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim(lean_object* v_motive_1285_, uint8_t v_t_1286_, lean_object* v_h_1287_, lean_object* v_ctor_1288_){
_start:
{
lean_inc(v_ctor_1288_);
return v_ctor_1288_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___boxed(lean_object* v_motive_1289_, lean_object* v_t_1290_, lean_object* v_h_1291_, lean_object* v_ctor_1292_){
_start:
{
uint8_t v_t_boxed_1293_; lean_object* v_res_1294_; 
v_t_boxed_1293_ = lean_unbox(v_t_1290_);
v_res_1294_ = l_Lean_QuotKind_ctor_elim(v_motive_1289_, v_t_boxed_1293_, v_h_1291_, v_ctor_1292_);
lean_dec(v_ctor_1292_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg(lean_object* v_lift_1295_){
_start:
{
lean_inc(v_lift_1295_);
return v_lift_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg___boxed(lean_object* v_lift_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_QuotKind_lift_elim___redArg(v_lift_1296_);
lean_dec(v_lift_1296_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim(lean_object* v_motive_1298_, uint8_t v_t_1299_, lean_object* v_h_1300_, lean_object* v_lift_1301_){
_start:
{
lean_inc(v_lift_1301_);
return v_lift_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___boxed(lean_object* v_motive_1302_, lean_object* v_t_1303_, lean_object* v_h_1304_, lean_object* v_lift_1305_){
_start:
{
uint8_t v_t_boxed_1306_; lean_object* v_res_1307_; 
v_t_boxed_1306_ = lean_unbox(v_t_1303_);
v_res_1307_ = l_Lean_QuotKind_lift_elim(v_motive_1302_, v_t_boxed_1306_, v_h_1304_, v_lift_1305_);
lean_dec(v_lift_1305_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg(lean_object* v_ind_1308_){
_start:
{
lean_inc(v_ind_1308_);
return v_ind_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg___boxed(lean_object* v_ind_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_Lean_QuotKind_ind_elim___redArg(v_ind_1309_);
lean_dec(v_ind_1309_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim(lean_object* v_motive_1311_, uint8_t v_t_1312_, lean_object* v_h_1313_, lean_object* v_ind_1314_){
_start:
{
lean_inc(v_ind_1314_);
return v_ind_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___boxed(lean_object* v_motive_1315_, lean_object* v_t_1316_, lean_object* v_h_1317_, lean_object* v_ind_1318_){
_start:
{
uint8_t v_t_boxed_1319_; lean_object* v_res_1320_; 
v_t_boxed_1319_ = lean_unbox(v_t_1316_);
v_res_1320_ = l_Lean_QuotKind_ind_elim(v_motive_1315_, v_t_boxed_1319_, v_h_1317_, v_ind_1318_);
lean_dec(v_ind_1318_);
return v_res_1320_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind_default(void){
_start:
{
uint8_t v___x_1321_; 
v___x_1321_ = 0;
return v___x_1321_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind(void){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = 0;
return v___x_1322_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqQuotKind_beq(uint8_t v_x_1323_, uint8_t v_y_1324_){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1325_ = lean_box(v_x_1323_);
v___x_1326_ = lean_obj_tag_nat(v___x_1325_);
lean_dec(v___x_1325_);
v___x_1327_ = lean_box(v_y_1324_);
v___x_1328_ = lean_obj_tag_nat(v___x_1327_);
lean_dec(v___x_1327_);
v___x_1329_ = lean_nat_dec_eq(v___x_1326_, v___x_1328_);
return v___x_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqQuotKind_beq___boxed(lean_object* v_x_1330_, lean_object* v_y_1331_){
_start:
{
uint8_t v_x_24__boxed_1332_; uint8_t v_y_25__boxed_1333_; uint8_t v_res_1334_; lean_object* v_r_1335_; 
v_x_24__boxed_1332_ = lean_unbox(v_x_1330_);
v_y_25__boxed_1333_ = lean_unbox(v_y_1331_);
v_res_1334_ = l_Lean_instBEqQuotKind_beq(v_x_24__boxed_1332_, v_y_25__boxed_1333_);
v_r_1335_ = lean_box(v_res_1334_);
return v_r_1335_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default___closed__0(void){
_start:
{
uint8_t v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1338_ = 0;
v___x_1339_ = l_Lean_instInhabitedConstantVal_default;
v___x_1340_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1340_, 0, v___x_1339_);
lean_ctor_set_uint8(v___x_1340_, sizeof(void*)*1, v___x_1338_);
return v___x_1340_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default(void){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = lean_obj_once(&l_Lean_instInhabitedQuotVal_default___closed__0, &l_Lean_instInhabitedQuotVal_default___closed__0_once, _init_l_Lean_instInhabitedQuotVal_default___closed__0);
return v___x_1341_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal(void){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_instInhabitedQuotVal_default;
return v___x_1342_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqQuotVal_beq(lean_object* v_x_1343_, lean_object* v_x_1344_){
_start:
{
lean_object* v_toConstantVal_1345_; uint8_t v_kind_1346_; lean_object* v_toConstantVal_1347_; uint8_t v_kind_1348_; uint8_t v___x_1349_; 
v_toConstantVal_1345_ = lean_ctor_get(v_x_1343_, 0);
v_kind_1346_ = lean_ctor_get_uint8(v_x_1343_, sizeof(void*)*1);
v_toConstantVal_1347_ = lean_ctor_get(v_x_1344_, 0);
v_kind_1348_ = lean_ctor_get_uint8(v_x_1344_, sizeof(void*)*1);
v___x_1349_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1345_, v_toConstantVal_1347_);
if (v___x_1349_ == 0)
{
return v___x_1349_;
}
else
{
uint8_t v___x_1350_; 
v___x_1350_ = l_Lean_instBEqQuotKind_beq(v_kind_1346_, v_kind_1348_);
return v___x_1350_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqQuotVal_beq___boxed(lean_object* v_x_1351_, lean_object* v_x_1352_){
_start:
{
uint8_t v_res_1353_; lean_object* v_r_1354_; 
v_res_1353_ = l_Lean_instBEqQuotVal_beq(v_x_1351_, v_x_1352_);
lean_dec_ref(v_x_1352_);
lean_dec_ref(v_x_1351_);
v_r_1354_ = lean_box(v_res_1353_);
return v_r_1354_;
}
}
LEAN_EXPORT lean_object* lean_mk_quot_val(lean_object* v_name_1357_, lean_object* v_levelParams_1358_, lean_object* v_type_1359_, uint8_t v_kind_1360_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1361_, 0, v_name_1357_);
lean_ctor_set(v___x_1361_, 1, v_levelParams_1358_);
lean_ctor_set(v___x_1361_, 2, v_type_1359_);
v___x_1362_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set_uint8(v___x_1362_, sizeof(void*)*1, v_kind_1360_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkQuotValEx___boxed(lean_object* v_name_1363_, lean_object* v_levelParams_1364_, lean_object* v_type_1365_, lean_object* v_kind_1366_){
_start:
{
uint8_t v_kind_boxed_1367_; lean_object* v_res_1368_; 
v_kind_boxed_1367_ = lean_unbox(v_kind_1366_);
v_res_1368_ = lean_mk_quot_val(v_name_1363_, v_levelParams_1364_, v_type_1365_, v_kind_boxed_1367_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___impl(lean_object* v_x_1369_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_obj_tag_nat(v_x_1369_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___impl___boxed(lean_object* v_x_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Lean_ConstantInfo_ctorIdx___impl(v_x_1371_);
lean_dec_ref(v_x_1371_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___redArg(lean_object* v_t_1373_, lean_object* v_k_1374_){
_start:
{
lean_object* v_val_1375_; lean_object* v___x_1376_; 
v_val_1375_ = lean_ctor_get(v_t_1373_, 0);
lean_inc_ref(v_val_1375_);
lean_dec_ref(v_t_1373_);
v___x_1376_ = lean_apply_1(v_k_1374_, v_val_1375_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim(lean_object* v_motive_1377_, lean_object* v_ctorIdx_1378_, lean_object* v_t_1379_, lean_object* v_h_1380_, lean_object* v_k_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1379_, v_k_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorElim___boxed(lean_object* v_motive_1383_, lean_object* v_ctorIdx_1384_, lean_object* v_t_1385_, lean_object* v_h_1386_, lean_object* v_k_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_ConstantInfo_ctorElim(v_motive_1383_, v_ctorIdx_1384_, v_t_1385_, v_h_1386_, v_k_1387_);
lean_dec(v_ctorIdx_1384_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim___redArg(lean_object* v_t_1389_, lean_object* v_axiomInfo_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1389_, v_axiomInfo_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_axiomInfo_elim(lean_object* v_motive_1392_, lean_object* v_t_1393_, lean_object* v_h_1394_, lean_object* v_axiomInfo_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1393_, v_axiomInfo_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim___redArg(lean_object* v_t_1397_, lean_object* v_defnInfo_1398_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1397_, v_defnInfo_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_defnInfo_elim(lean_object* v_motive_1400_, lean_object* v_t_1401_, lean_object* v_h_1402_, lean_object* v_defnInfo_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1401_, v_defnInfo_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim___redArg(lean_object* v_t_1405_, lean_object* v_thmInfo_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1405_, v_thmInfo_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_thmInfo_elim(lean_object* v_motive_1408_, lean_object* v_t_1409_, lean_object* v_h_1410_, lean_object* v_thmInfo_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1409_, v_thmInfo_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim___redArg(lean_object* v_t_1413_, lean_object* v_opaqueInfo_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1413_, v_opaqueInfo_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_opaqueInfo_elim(lean_object* v_motive_1416_, lean_object* v_t_1417_, lean_object* v_h_1418_, lean_object* v_opaqueInfo_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1417_, v_opaqueInfo_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim___redArg(lean_object* v_t_1421_, lean_object* v_quotInfo_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1421_, v_quotInfo_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_quotInfo_elim(lean_object* v_motive_1424_, lean_object* v_t_1425_, lean_object* v_h_1426_, lean_object* v_quotInfo_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1425_, v_quotInfo_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim___redArg(lean_object* v_t_1429_, lean_object* v_inductInfo_1430_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1429_, v_inductInfo_1430_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductInfo_elim(lean_object* v_motive_1432_, lean_object* v_t_1433_, lean_object* v_h_1434_, lean_object* v_inductInfo_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1433_, v_inductInfo_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim___redArg(lean_object* v_t_1437_, lean_object* v_ctorInfo_1438_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1437_, v_ctorInfo_1438_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorInfo_elim(lean_object* v_motive_1440_, lean_object* v_t_1441_, lean_object* v_h_1442_, lean_object* v_ctorInfo_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1441_, v_ctorInfo_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim___redArg(lean_object* v_t_1445_, lean_object* v_recInfo_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1445_, v_recInfo_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_recInfo_elim(lean_object* v_motive_1448_, lean_object* v_t_1449_, lean_object* v_h_1450_, lean_object* v_recInfo_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_ConstantInfo_ctorElim___redArg(v_t_1449_, v_recInfo_1451_);
return v___x_1452_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default___closed__0(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = l_Lean_instInhabitedAxiomVal_default;
v___x_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
return v___x_1454_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo_default(void){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_obj_once(&l_Lean_instInhabitedConstantInfo_default___closed__0, &l_Lean_instInhabitedConstantInfo_default___closed__0_once, _init_l_Lean_instInhabitedConstantInfo_default___closed__0);
return v___x_1455_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstantInfo(void){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_instInhabitedConstantInfo_default;
return v___x_1456_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstantInfo_beq(lean_object* v_x_1457_, lean_object* v_x_1458_){
_start:
{
switch(lean_obj_tag(v_x_1457_))
{
case 0:
{
if (lean_obj_tag(v_x_1458_) == 0)
{
lean_object* v_val_1459_; lean_object* v_val_1460_; uint8_t v___x_1461_; 
v_val_1459_ = lean_ctor_get(v_x_1457_, 0);
v_val_1460_ = lean_ctor_get(v_x_1458_, 0);
v___x_1461_ = l_Lean_instBEqAxiomVal_beq(v_val_1459_, v_val_1460_);
return v___x_1461_;
}
else
{
uint8_t v___x_1462_; 
v___x_1462_ = 0;
return v___x_1462_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1458_) == 1)
{
lean_object* v_val_1463_; lean_object* v_val_1464_; uint8_t v___x_1465_; 
v_val_1463_ = lean_ctor_get(v_x_1457_, 0);
v_val_1464_ = lean_ctor_get(v_x_1458_, 0);
v___x_1465_ = l_Lean_instBEqDefinitionVal_beq(v_val_1463_, v_val_1464_);
return v___x_1465_;
}
else
{
uint8_t v___x_1466_; 
v___x_1466_ = 0;
return v___x_1466_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1458_) == 2)
{
lean_object* v_val_1467_; lean_object* v_val_1468_; uint8_t v___x_1469_; 
v_val_1467_ = lean_ctor_get(v_x_1457_, 0);
v_val_1468_ = lean_ctor_get(v_x_1458_, 0);
v___x_1469_ = l_Lean_instBEqTheoremVal_beq(v_val_1467_, v_val_1468_);
return v___x_1469_;
}
else
{
uint8_t v___x_1470_; 
v___x_1470_ = 0;
return v___x_1470_;
}
}
case 3:
{
if (lean_obj_tag(v_x_1458_) == 3)
{
lean_object* v_val_1471_; lean_object* v_val_1472_; uint8_t v___x_1473_; 
v_val_1471_ = lean_ctor_get(v_x_1457_, 0);
v_val_1472_ = lean_ctor_get(v_x_1458_, 0);
v___x_1473_ = l_Lean_instBEqOpaqueVal_beq(v_val_1471_, v_val_1472_);
return v___x_1473_;
}
else
{
uint8_t v___x_1474_; 
v___x_1474_ = 0;
return v___x_1474_;
}
}
case 4:
{
if (lean_obj_tag(v_x_1458_) == 4)
{
lean_object* v_val_1475_; lean_object* v_val_1476_; uint8_t v___x_1477_; 
v_val_1475_ = lean_ctor_get(v_x_1457_, 0);
v_val_1476_ = lean_ctor_get(v_x_1458_, 0);
v___x_1477_ = l_Lean_instBEqQuotVal_beq(v_val_1475_, v_val_1476_);
return v___x_1477_;
}
else
{
uint8_t v___x_1478_; 
v___x_1478_ = 0;
return v___x_1478_;
}
}
case 5:
{
if (lean_obj_tag(v_x_1458_) == 5)
{
lean_object* v_val_1479_; lean_object* v_val_1480_; uint8_t v___x_1481_; 
v_val_1479_ = lean_ctor_get(v_x_1457_, 0);
v_val_1480_ = lean_ctor_get(v_x_1458_, 0);
v___x_1481_ = l_Lean_instBEqInductiveVal_beq(v_val_1479_, v_val_1480_);
return v___x_1481_;
}
else
{
uint8_t v___x_1482_; 
v___x_1482_ = 0;
return v___x_1482_;
}
}
case 6:
{
if (lean_obj_tag(v_x_1458_) == 6)
{
lean_object* v_val_1483_; lean_object* v_val_1484_; uint8_t v___x_1485_; 
v_val_1483_ = lean_ctor_get(v_x_1457_, 0);
v_val_1484_ = lean_ctor_get(v_x_1458_, 0);
v___x_1485_ = l_Lean_instBEqConstructorVal_beq(v_val_1483_, v_val_1484_);
return v___x_1485_;
}
else
{
uint8_t v___x_1486_; 
v___x_1486_ = 0;
return v___x_1486_;
}
}
default: 
{
if (lean_obj_tag(v_x_1458_) == 7)
{
lean_object* v_val_1487_; lean_object* v_val_1488_; uint8_t v___x_1489_; 
v_val_1487_ = lean_ctor_get(v_x_1457_, 0);
v_val_1488_ = lean_ctor_get(v_x_1458_, 0);
v___x_1489_ = l_Lean_instBEqRecursorVal_beq(v_val_1487_, v_val_1488_);
return v___x_1489_;
}
else
{
uint8_t v___x_1490_; 
v___x_1490_ = 0;
return v___x_1490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstantInfo_beq___boxed(lean_object* v_x_1491_, lean_object* v_x_1492_){
_start:
{
uint8_t v_res_1493_; lean_object* v_r_1494_; 
v_res_1493_ = l_Lean_instBEqConstantInfo_beq(v_x_1491_, v_x_1492_);
lean_dec_ref(v_x_1492_);
lean_dec_ref(v_x_1491_);
v_r_1494_ = lean_box(v_res_1493_);
return v_r_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object* v_x_1497_){
_start:
{
lean_object* v_val_1498_; lean_object* v_toConstantVal_1499_; 
v_val_1498_ = lean_ctor_get(v_x_1497_, 0);
v_toConstantVal_1499_ = lean_ctor_get(v_val_1498_, 0);
lean_inc_ref(v_toConstantVal_1499_);
return v_toConstantVal_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object* v_x_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_ConstantInfo_toConstantVal(v_x_1500_);
lean_dec_ref(v_x_1500_);
return v_res_1501_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object* v_x_1502_){
_start:
{
switch(lean_obj_tag(v_x_1502_))
{
case 0:
{
lean_object* v_val_1503_; uint8_t v_isUnsafe_1504_; 
v_val_1503_ = lean_ctor_get(v_x_1502_, 0);
v_isUnsafe_1504_ = lean_ctor_get_uint8(v_val_1503_, sizeof(void*)*1);
return v_isUnsafe_1504_;
}
case 1:
{
lean_object* v_val_1505_; uint8_t v_safety_1506_; uint8_t v___x_1507_; uint8_t v___x_1508_; 
v_val_1505_ = lean_ctor_get(v_x_1502_, 0);
v_safety_1506_ = lean_ctor_get_uint8(v_val_1505_, sizeof(void*)*4);
v___x_1507_ = 0;
v___x_1508_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1506_, v___x_1507_);
return v___x_1508_;
}
case 3:
{
lean_object* v_val_1509_; uint8_t v_isUnsafe_1510_; 
v_val_1509_ = lean_ctor_get(v_x_1502_, 0);
v_isUnsafe_1510_ = lean_ctor_get_uint8(v_val_1509_, sizeof(void*)*3);
return v_isUnsafe_1510_;
}
case 5:
{
lean_object* v_val_1511_; uint8_t v_isUnsafe_1512_; 
v_val_1511_ = lean_ctor_get(v_x_1502_, 0);
v_isUnsafe_1512_ = lean_ctor_get_uint8(v_val_1511_, sizeof(void*)*6 + 1);
return v_isUnsafe_1512_;
}
case 6:
{
lean_object* v_val_1513_; uint8_t v_isUnsafe_1514_; 
v_val_1513_ = lean_ctor_get(v_x_1502_, 0);
v_isUnsafe_1514_ = lean_ctor_get_uint8(v_val_1513_, sizeof(void*)*5);
return v_isUnsafe_1514_;
}
case 7:
{
lean_object* v_val_1515_; uint8_t v_isUnsafe_1516_; 
v_val_1515_ = lean_ctor_get(v_x_1502_, 0);
v_isUnsafe_1516_ = lean_ctor_get_uint8(v_val_1515_, sizeof(void*)*7 + 1);
return v_isUnsafe_1516_;
}
default: 
{
uint8_t v___x_1517_; 
v___x_1517_ = 0;
return v___x_1517_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isUnsafe___boxed(lean_object* v_x_1518_){
_start:
{
uint8_t v_res_1519_; lean_object* v_r_1520_; 
v_res_1519_ = l_Lean_ConstantInfo_isUnsafe(v_x_1518_);
lean_dec_ref(v_x_1518_);
v_r_1520_ = lean_box(v_res_1519_);
return v_r_1520_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isPartial(lean_object* v_x_1521_){
_start:
{
if (lean_obj_tag(v_x_1521_) == 1)
{
lean_object* v_val_1522_; uint8_t v_safety_1523_; uint8_t v___x_1524_; uint8_t v___x_1525_; 
v_val_1522_ = lean_ctor_get(v_x_1521_, 0);
v_safety_1523_ = lean_ctor_get_uint8(v_val_1522_, sizeof(void*)*4);
v___x_1524_ = 2;
v___x_1525_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1523_, v___x_1524_);
return v___x_1525_;
}
else
{
uint8_t v___x_1526_; 
v___x_1526_ = 0;
return v___x_1526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isPartial___boxed(lean_object* v_x_1527_){
_start:
{
uint8_t v_res_1528_; lean_object* v_r_1529_; 
v_res_1528_ = l_Lean_ConstantInfo_isPartial(v_x_1527_);
lean_dec_ref(v_x_1527_);
v_r_1529_ = lean_box(v_res_1528_);
return v_r_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name(lean_object* v_d_1530_){
_start:
{
lean_object* v___x_1531_; lean_object* v_name_1532_; 
v___x_1531_ = l_Lean_ConstantInfo_toConstantVal(v_d_1530_);
v_name_1532_ = lean_ctor_get(v___x_1531_, 0);
lean_inc(v_name_1532_);
lean_dec_ref(v___x_1531_);
return v_name_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name___boxed(lean_object* v_d_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_Lean_ConstantInfo_name(v_d_1533_);
lean_dec_ref(v_d_1533_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams(lean_object* v_d_1535_){
_start:
{
lean_object* v___x_1536_; lean_object* v_levelParams_1537_; 
v___x_1536_ = l_Lean_ConstantInfo_toConstantVal(v_d_1535_);
v_levelParams_1537_ = lean_ctor_get(v___x_1536_, 1);
lean_inc(v_levelParams_1537_);
lean_dec_ref(v___x_1536_);
return v_levelParams_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams___boxed(lean_object* v_d_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_Lean_ConstantInfo_levelParams(v_d_1538_);
lean_dec_ref(v_d_1538_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object* v_d_1540_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = l_Lean_ConstantInfo_levelParams(v_d_1540_);
v___x_1542_ = l_List_lengthTR___redArg(v___x_1541_);
lean_dec(v___x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams___boxed(lean_object* v_d_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_ConstantInfo_numLevelParams(v_d_1543_);
lean_dec_ref(v_d_1543_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type(lean_object* v_d_1545_){
_start:
{
lean_object* v___x_1546_; lean_object* v_type_1547_; 
v___x_1546_ = l_Lean_ConstantInfo_toConstantVal(v_d_1545_);
v_type_1547_ = lean_ctor_get(v___x_1546_, 2);
lean_inc_ref(v_type_1547_);
lean_dec_ref(v___x_1546_);
return v_type_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type___boxed(lean_object* v_d_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_ConstantInfo_type(v_d_1548_);
lean_dec_ref(v_d_1548_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f(lean_object* v_info_1550_, uint8_t v_allowOpaque_1551_){
_start:
{
switch(lean_obj_tag(v_info_1550_))
{
case 1:
{
lean_object* v_val_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1560_; 
v_val_1552_ = lean_ctor_get(v_info_1550_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_info_1550_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1554_ = v_info_1550_;
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_val_1552_);
lean_dec(v_info_1550_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v_value_1556_; lean_object* v___x_1558_; 
v_value_1556_ = lean_ctor_get(v_val_1552_, 1);
lean_inc_ref(v_value_1556_);
lean_dec_ref(v_val_1552_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 0, v_value_1556_);
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_value_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
case 2:
{
lean_object* v_val_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1570_; 
v_val_1561_ = lean_ctor_get(v_info_1550_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_info_1550_);
if (v_isSharedCheck_1570_ == 0)
{
v___x_1563_ = v_info_1550_;
v_isShared_1564_ = v_isSharedCheck_1570_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_val_1561_);
lean_dec(v_info_1550_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1570_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
if (v_allowOpaque_1551_ == 0)
{
lean_object* v___x_1565_; 
lean_del_object(v___x_1563_);
lean_dec_ref(v_val_1561_);
v___x_1565_ = lean_box(0);
return v___x_1565_;
}
else
{
lean_object* v_value_1566_; lean_object* v___x_1568_; 
v_value_1566_ = lean_ctor_get(v_val_1561_, 1);
lean_inc_ref(v_value_1566_);
lean_dec_ref(v_val_1561_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set_tag(v___x_1563_, 1);
lean_ctor_set(v___x_1563_, 0, v_value_1566_);
v___x_1568_ = v___x_1563_;
goto v_reusejp_1567_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v_value_1566_);
v___x_1568_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1567_;
}
v_reusejp_1567_:
{
return v___x_1568_;
}
}
}
}
case 3:
{
lean_object* v_val_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1580_; 
v_val_1571_ = lean_ctor_get(v_info_1550_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_info_1550_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1573_ = v_info_1550_;
v_isShared_1574_ = v_isSharedCheck_1580_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_val_1571_);
lean_dec(v_info_1550_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1580_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
if (v_allowOpaque_1551_ == 0)
{
lean_object* v___x_1575_; 
lean_del_object(v___x_1573_);
lean_dec_ref(v_val_1571_);
v___x_1575_ = lean_box(0);
return v___x_1575_;
}
else
{
lean_object* v_value_1576_; lean_object* v___x_1578_; 
v_value_1576_ = lean_ctor_get(v_val_1571_, 1);
lean_inc_ref(v_value_1576_);
lean_dec_ref(v_val_1571_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set_tag(v___x_1573_, 1);
lean_ctor_set(v___x_1573_, 0, v_value_1576_);
v___x_1578_ = v___x_1573_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_value_1576_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
default: 
{
lean_object* v___x_1581_; 
lean_dec_ref(v_info_1550_);
v___x_1581_ = lean_box(0);
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f___boxed(lean_object* v_info_1582_, lean_object* v_allowOpaque_1583_){
_start:
{
uint8_t v_allowOpaque_boxed_1584_; lean_object* v_res_1585_; 
v_allowOpaque_boxed_1584_ = lean_unbox(v_allowOpaque_1583_);
v_res_1585_ = l_Lean_ConstantInfo_value_x3f(v_info_1582_, v_allowOpaque_boxed_1584_);
return v_res_1585_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_hasValue(lean_object* v_info_1586_, uint8_t v_allowOpaque_1587_){
_start:
{
switch(lean_obj_tag(v_info_1586_))
{
case 1:
{
uint8_t v___x_1588_; 
v___x_1588_ = 1;
return v___x_1588_;
}
case 2:
{
return v_allowOpaque_1587_;
}
case 3:
{
return v_allowOpaque_1587_;
}
default: 
{
uint8_t v___x_1589_; 
v___x_1589_ = 0;
return v___x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object* v_info_1590_, lean_object* v_allowOpaque_1591_){
_start:
{
uint8_t v_allowOpaque_boxed_1592_; uint8_t v_res_1593_; lean_object* v_r_1594_; 
v_allowOpaque_boxed_1592_ = lean_unbox(v_allowOpaque_1591_);
v_res_1593_ = l_Lean_ConstantInfo_hasValue(v_info_1590_, v_allowOpaque_boxed_1592_);
lean_dec_ref(v_info_1590_);
v_r_1594_ = lean_box(v_res_1593_);
return v_r_1594_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(lean_object* v_msg_1595_){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = l_Lean_instInhabitedExpr;
v___x_1597_ = lean_panic_fn_borrowed(v___x_1596_, v_msg_1595_);
return v___x_1597_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__2(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1600_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1601_ = lean_unsigned_to_nat(62u);
v___x_1602_ = lean_unsigned_to_nat(485u);
v___x_1603_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1604_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1605_ = l_mkPanicMessageWithDecl(v___x_1604_, v___x_1603_, v___x_1602_, v___x_1601_, v___x_1600_);
return v___x_1605_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__3(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1606_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1607_ = lean_unsigned_to_nat(62u);
v___x_1608_ = lean_unsigned_to_nat(486u);
v___x_1609_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1610_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1611_ = l_mkPanicMessageWithDecl(v___x_1610_, v___x_1609_, v___x_1608_, v___x_1607_, v___x_1606_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21(lean_object* v_info_1614_, uint8_t v_allowOpaque_1615_){
_start:
{
switch(lean_obj_tag(v_info_1614_))
{
case 1:
{
lean_object* v_val_1616_; lean_object* v_value_1617_; 
v_val_1616_ = lean_ctor_get(v_info_1614_, 0);
v_value_1617_ = lean_ctor_get(v_val_1616_, 1);
lean_inc_ref(v_value_1617_);
return v_value_1617_;
}
case 2:
{
if (v_allowOpaque_1615_ == 0)
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__2, &l_Lean_ConstantInfo_value_x21___closed__2_once, _init_l_Lean_ConstantInfo_value_x21___closed__2);
v___x_1619_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1618_);
return v___x_1619_;
}
else
{
lean_object* v_val_1620_; lean_object* v_value_1621_; 
v_val_1620_ = lean_ctor_get(v_info_1614_, 0);
v_value_1621_ = lean_ctor_get(v_val_1620_, 1);
lean_inc_ref(v_value_1621_);
return v_value_1621_;
}
}
case 3:
{
if (v_allowOpaque_1615_ == 0)
{
lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1622_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__3, &l_Lean_ConstantInfo_value_x21___closed__3_once, _init_l_Lean_ConstantInfo_value_x21___closed__3);
v___x_1623_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1622_);
return v___x_1623_;
}
else
{
lean_object* v_val_1624_; lean_object* v_value_1625_; 
v_val_1624_ = lean_ctor_get(v_info_1614_, 0);
v_value_1625_ = lean_ctor_get(v_val_1624_, 1);
lean_inc_ref(v_value_1625_);
return v_value_1625_;
}
}
default: 
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; uint8_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v___x_1626_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1627_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1628_ = lean_unsigned_to_nat(487u);
v___x_1629_ = lean_unsigned_to_nat(31u);
v___x_1630_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__4));
v___x_1631_ = l_Lean_ConstantInfo_name(v_info_1614_);
v___x_1632_ = 1;
v___x_1633_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1631_, v___x_1632_);
v___x_1634_ = lean_string_append(v___x_1630_, v___x_1633_);
lean_dec_ref(v___x_1633_);
v___x_1635_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__5));
v___x_1636_ = lean_string_append(v___x_1634_, v___x_1635_);
v___x_1637_ = l_mkPanicMessageWithDecl(v___x_1626_, v___x_1627_, v___x_1628_, v___x_1629_, v___x_1636_);
lean_dec_ref(v___x_1636_);
v___x_1638_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1637_);
return v___x_1638_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21___boxed(lean_object* v_info_1639_, lean_object* v_allowOpaque_1640_){
_start:
{
uint8_t v_allowOpaque_boxed_1641_; lean_object* v_res_1642_; 
v_allowOpaque_boxed_1641_ = lean_unbox(v_allowOpaque_1640_);
v_res_1642_ = l_Lean_ConstantInfo_value_x21(v_info_1639_, v_allowOpaque_boxed_1641_);
lean_dec_ref(v_info_1639_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints(lean_object* v_x_1643_){
_start:
{
if (lean_obj_tag(v_x_1643_) == 1)
{
lean_object* v_val_1644_; lean_object* v_hints_1645_; 
v_val_1644_ = lean_ctor_get(v_x_1643_, 0);
v_hints_1645_ = lean_ctor_get(v_val_1644_, 2);
lean_inc(v_hints_1645_);
return v_hints_1645_;
}
else
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_box(0);
return v___x_1646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object* v_x_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lean_ConstantInfo_hints(v_x_1647_);
lean_dec_ref(v_x_1647_);
return v_res_1648_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isCtor(lean_object* v_x_1649_){
_start:
{
if (lean_obj_tag(v_x_1649_) == 6)
{
uint8_t v___x_1650_; 
v___x_1650_ = 1;
return v___x_1650_;
}
else
{
uint8_t v___x_1651_; 
v___x_1651_ = 0;
return v___x_1651_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isCtor___boxed(lean_object* v_x_1652_){
_start:
{
uint8_t v_res_1653_; lean_object* v_r_1654_; 
v_res_1653_ = l_Lean_ConstantInfo_isCtor(v_x_1652_);
lean_dec_ref(v_x_1652_);
v_r_1654_ = lean_box(v_res_1653_);
return v_r_1654_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isAxiom(lean_object* v_x_1655_){
_start:
{
if (lean_obj_tag(v_x_1655_) == 0)
{
uint8_t v___x_1656_; 
v___x_1656_ = 1;
return v___x_1656_;
}
else
{
uint8_t v___x_1657_; 
v___x_1657_ = 0;
return v___x_1657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isAxiom___boxed(lean_object* v_x_1658_){
_start:
{
uint8_t v_res_1659_; lean_object* v_r_1660_; 
v_res_1659_ = l_Lean_ConstantInfo_isAxiom(v_x_1658_);
lean_dec_ref(v_x_1658_);
v_r_1660_ = lean_box(v_res_1659_);
return v_r_1660_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isInductive(lean_object* v_x_1661_){
_start:
{
if (lean_obj_tag(v_x_1661_) == 5)
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
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isInductive___boxed(lean_object* v_x_1664_){
_start:
{
uint8_t v_res_1665_; lean_object* v_r_1666_; 
v_res_1665_ = l_Lean_ConstantInfo_isInductive(v_x_1664_);
lean_dec_ref(v_x_1664_);
v_r_1666_ = lean_box(v_res_1665_);
return v_r_1666_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isDefinition(lean_object* v_x_1667_){
_start:
{
if (lean_obj_tag(v_x_1667_) == 1)
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
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isDefinition___boxed(lean_object* v_x_1670_){
_start:
{
uint8_t v_res_1671_; lean_object* v_r_1672_; 
v_res_1671_ = l_Lean_ConstantInfo_isDefinition(v_x_1670_);
lean_dec_ref(v_x_1670_);
v_r_1672_ = lean_box(v_res_1671_);
return v_r_1672_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isTheorem(lean_object* v_x_1673_){
_start:
{
if (lean_obj_tag(v_x_1673_) == 2)
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
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isTheorem___boxed(lean_object* v_x_1676_){
_start:
{
uint8_t v_res_1677_; lean_object* v_r_1678_; 
v_res_1677_ = l_Lean_ConstantInfo_isTheorem(v_x_1676_);
lean_dec_ref(v_x_1676_);
v_r_1678_ = lean_box(v_res_1677_);
return v_r_1678_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(lean_object* v_msg_1679_){
_start:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = l_Lean_instInhabitedInductiveVal_default;
v___x_1681_ = lean_panic_fn_borrowed(v___x_1680_, v_msg_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1684_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__1));
v___x_1685_ = lean_unsigned_to_nat(9u);
v___x_1686_ = lean_unsigned_to_nat(515u);
v___x_1687_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__0));
v___x_1688_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1689_ = l_mkPanicMessageWithDecl(v___x_1688_, v___x_1687_, v___x_1686_, v___x_1685_, v___x_1684_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object* v_x_1690_){
_start:
{
if (lean_obj_tag(v_x_1690_) == 5)
{
lean_object* v_val_1691_; 
v_val_1691_ = lean_ctor_get(v_x_1690_, 0);
lean_inc_ref(v_val_1691_);
return v_val_1691_;
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_obj_once(&l_Lean_ConstantInfo_inductiveVal_x21___closed__2, &l_Lean_ConstantInfo_inductiveVal_x21___closed__2_once, _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2);
v___x_1693_ = l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(v___x_1692_);
return v___x_1693_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21___boxed(lean_object* v_x_1694_){
_start:
{
lean_object* v_res_1695_; 
v_res_1695_ = l_Lean_ConstantInfo_inductiveVal_x21(v_x_1694_);
lean_dec_ref(v_x_1694_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all(lean_object* v_x_1696_){
_start:
{
switch(lean_obj_tag(v_x_1696_))
{
case 5:
{
lean_object* v_val_1697_; lean_object* v_all_1698_; 
v_val_1697_ = lean_ctor_get(v_x_1696_, 0);
v_all_1698_ = lean_ctor_get(v_val_1697_, 3);
lean_inc(v_all_1698_);
return v_all_1698_;
}
case 1:
{
lean_object* v_val_1699_; lean_object* v_all_1700_; 
v_val_1699_ = lean_ctor_get(v_x_1696_, 0);
v_all_1700_ = lean_ctor_get(v_val_1699_, 3);
lean_inc(v_all_1700_);
return v_all_1700_;
}
case 2:
{
lean_object* v_val_1701_; lean_object* v_all_1702_; 
v_val_1701_ = lean_ctor_get(v_x_1696_, 0);
v_all_1702_ = lean_ctor_get(v_val_1701_, 2);
lean_inc(v_all_1702_);
return v_all_1702_;
}
case 3:
{
lean_object* v_val_1703_; lean_object* v_all_1704_; 
v_val_1703_ = lean_ctor_get(v_x_1696_, 0);
v_all_1704_ = lean_ctor_get(v_val_1703_, 2);
lean_inc(v_all_1704_);
return v_all_1704_;
}
default: 
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = l_Lean_ConstantInfo_name(v_x_1696_);
v___x_1706_ = lean_box(0);
v___x_1707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1705_);
lean_ctor_set(v___x_1707_, 1, v___x_1706_);
return v___x_1707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all___boxed(lean_object* v_x_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_ConstantInfo_all(v_x_1708_);
lean_dec_ref(v_x_1708_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecName(lean_object* v_declName_1710_){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0));
v___x_1712_ = l_Lean_Name_str___override(v_declName_1710_, v___x_1711_);
return v___x_1712_;
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
