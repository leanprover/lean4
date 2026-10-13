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
lean_object* v_toConstantVal_434_; lean_object* v_value_435_; uint8_t v_isUnsafe_436_; lean_object* v_all_437_; lean_object* v_toConstantVal_438_; lean_object* v_value_439_; uint8_t v_isUnsafe_440_; lean_object* v_all_441_; uint8_t v___y_443_; uint8_t v___x_445_; 
v_toConstantVal_434_ = lean_ctor_get(v_x_432_, 0);
v_value_435_ = lean_ctor_get(v_x_432_, 1);
v_isUnsafe_436_ = lean_ctor_get_uint8(v_x_432_, sizeof(void*)*3);
v_all_437_ = lean_ctor_get(v_x_432_, 2);
v_toConstantVal_438_ = lean_ctor_get(v_x_433_, 0);
v_value_439_ = lean_ctor_get(v_x_433_, 1);
v_isUnsafe_440_ = lean_ctor_get_uint8(v_x_433_, sizeof(void*)*3);
v_all_441_ = lean_ctor_get(v_x_433_, 2);
v___x_445_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_434_, v_toConstantVal_438_);
if (v___x_445_ == 0)
{
return v___x_445_;
}
else
{
uint8_t v___x_446_; 
v___x_446_ = lean_expr_eqv(v_value_435_, v_value_439_);
if (v___x_446_ == 0)
{
return v___x_446_;
}
else
{
if (v_isUnsafe_440_ == 0)
{
if (v_isUnsafe_436_ == 0)
{
v___y_443_ = v___x_446_;
goto v___jp_442_;
}
else
{
return v_isUnsafe_440_;
}
}
else
{
v___y_443_ = v_isUnsafe_436_;
goto v___jp_442_;
}
}
}
v___jp_442_:
{
if (v___y_443_ == 0)
{
return v___y_443_;
}
else
{
uint8_t v___x_444_; 
v___x_444_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_437_, v_all_441_);
return v___x_444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqOpaqueVal_beq___boxed(lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
uint8_t v_res_449_; lean_object* v_r_450_; 
v_res_449_ = l_Lean_instBEqOpaqueVal_beq(v_x_447_, v_x_448_);
lean_dec_ref(v_x_448_);
lean_dec_ref(v_x_447_);
v_r_450_ = lean_box(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT uint8_t lean_opaque_val_is_unsafe(lean_object* v_v_453_){
_start:
{
uint8_t v_isUnsafe_454_; 
v_isUnsafe_454_ = lean_ctor_get_uint8(v_v_453_, sizeof(void*)*3);
lean_dec_ref(v_v_453_);
return v_isUnsafe_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_OpaqueVal_isUnsafeEx___boxed(lean_object* v_v_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = lean_opaque_val_is_unsafe(v_v_455_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__0(void){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_458_ = lean_box(0);
v___x_459_ = ((lean_object*)(l_Lean_instInhabitedConstantVal_default___closed__1));
v___x_460_ = l_Lean_Expr_const___override(v___x_459_, v___x_458_);
return v___x_460_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default___closed__1(void){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_461_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_462_ = lean_box(0);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
return v___x_463_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor_default(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__1, &l_Lean_instInhabitedConstructor_default___closed__1_once, _init_l_Lean_instInhabitedConstructor_default___closed__1);
return v___x_464_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructor(void){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_instInhabitedConstructor_default;
return v___x_465_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructor_beq(lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
lean_object* v_name_468_; lean_object* v_type_469_; lean_object* v_name_470_; lean_object* v_type_471_; uint8_t v___x_472_; 
v_name_468_ = lean_ctor_get(v_x_466_, 0);
v_type_469_ = lean_ctor_get(v_x_466_, 1);
v_name_470_ = lean_ctor_get(v_x_467_, 0);
v_type_471_ = lean_ctor_get(v_x_467_, 1);
v___x_472_ = lean_name_eq(v_name_468_, v_name_470_);
if (v___x_472_ == 0)
{
return v___x_472_;
}
else
{
uint8_t v___x_473_; 
v___x_473_ = lean_expr_eqv(v_type_469_, v_type_471_);
return v___x_473_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructor_beq___boxed(lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
uint8_t v_res_476_; lean_object* v_r_477_; 
v_res_476_ = l_Lean_instBEqConstructor_beq(v_x_474_, v_x_475_);
lean_dec_ref(v_x_475_);
lean_dec_ref(v_x_474_);
v_r_477_ = lean_box(v_res_476_);
return v_r_477_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default___closed__0(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_480_ = lean_box(0);
v___x_481_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_482_ = lean_box(0);
v___x_483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_481_);
lean_ctor_set(v___x_483_, 2, v___x_480_);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType_default(void){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_obj_once(&l_Lean_instInhabitedInductiveType_default___closed__0, &l_Lean_instInhabitedInductiveType_default___closed__0_once, _init_l_Lean_instInhabitedInductiveType_default___closed__0);
return v___x_484_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveType(void){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_instInhabitedInductiveType_default;
return v___x_485_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
if (lean_obj_tag(v_x_486_) == 0)
{
if (lean_obj_tag(v_x_487_) == 0)
{
uint8_t v___x_488_; 
v___x_488_ = 1;
return v___x_488_;
}
else
{
uint8_t v___x_489_; 
v___x_489_ = 0;
return v___x_489_;
}
}
else
{
if (lean_obj_tag(v_x_487_) == 0)
{
uint8_t v___x_490_; 
v___x_490_ = 0;
return v___x_490_;
}
else
{
lean_object* v_head_491_; lean_object* v_tail_492_; lean_object* v_head_493_; lean_object* v_tail_494_; uint8_t v___x_495_; 
v_head_491_ = lean_ctor_get(v_x_486_, 0);
v_tail_492_ = lean_ctor_get(v_x_486_, 1);
v_head_493_ = lean_ctor_get(v_x_487_, 0);
v_tail_494_ = lean_ctor_get(v_x_487_, 1);
v___x_495_ = l_Lean_instBEqConstructor_beq(v_head_491_, v_head_493_);
if (v___x_495_ == 0)
{
return v___x_495_;
}
else
{
v_x_486_ = v_tail_492_;
v_x_487_ = v_tail_494_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0___boxed(lean_object* v_x_497_, lean_object* v_x_498_){
_start:
{
uint8_t v_res_499_; lean_object* v_r_500_; 
v_res_499_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_x_497_, v_x_498_);
lean_dec(v_x_498_);
lean_dec(v_x_497_);
v_r_500_ = lean_box(v_res_499_);
return v_r_500_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveType_beq(lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
lean_object* v_name_503_; lean_object* v_type_504_; lean_object* v_ctors_505_; lean_object* v_name_506_; lean_object* v_type_507_; lean_object* v_ctors_508_; uint8_t v___x_509_; 
v_name_503_ = lean_ctor_get(v_x_501_, 0);
v_type_504_ = lean_ctor_get(v_x_501_, 1);
v_ctors_505_ = lean_ctor_get(v_x_501_, 2);
v_name_506_ = lean_ctor_get(v_x_502_, 0);
v_type_507_ = lean_ctor_get(v_x_502_, 1);
v_ctors_508_ = lean_ctor_get(v_x_502_, 2);
v___x_509_ = lean_name_eq(v_name_503_, v_name_506_);
if (v___x_509_ == 0)
{
return v___x_509_;
}
else
{
uint8_t v___x_510_; 
v___x_510_ = lean_expr_eqv(v_type_504_, v_type_507_);
if (v___x_510_ == 0)
{
return v___x_510_;
}
else
{
uint8_t v___x_511_; 
v___x_511_ = l_List_beq___at___00Lean_instBEqInductiveType_beq_spec__0(v_ctors_505_, v_ctors_508_);
return v___x_511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveType_beq___boxed(lean_object* v_x_512_, lean_object* v_x_513_){
_start:
{
uint8_t v_res_514_; lean_object* v_r_515_; 
v_res_514_ = l_Lean_instBEqInductiveType_beq(v_x_512_, v_x_513_);
lean_dec_ref(v_x_513_);
lean_dec_ref(v_x_512_);
v_r_515_ = lean_box(v_res_514_);
return v_r_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___impl(lean_object* v_x_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = lean_obj_tag_nat(v_x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorIdx___impl___boxed(lean_object* v_x_520_){
_start:
{
lean_object* v_res_521_; 
v_res_521_ = l_Lean_Declaration_ctorIdx___impl(v_x_520_);
lean_dec(v_x_520_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___redArg(lean_object* v_t_522_, lean_object* v_k_523_){
_start:
{
switch(lean_obj_tag(v_t_522_))
{
case 4:
{
return v_k_523_;
}
case 5:
{
lean_object* v_defns_524_; lean_object* v___x_525_; 
v_defns_524_ = lean_ctor_get(v_t_522_, 0);
lean_inc(v_defns_524_);
lean_dec_ref_known(v_t_522_, 1);
v___x_525_ = lean_apply_1(v_k_523_, v_defns_524_);
return v___x_525_;
}
case 6:
{
lean_object* v_lparams_526_; lean_object* v_nparams_527_; lean_object* v_types_528_; uint8_t v_isUnsafe_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v_lparams_526_ = lean_ctor_get(v_t_522_, 0);
lean_inc(v_lparams_526_);
v_nparams_527_ = lean_ctor_get(v_t_522_, 1);
lean_inc(v_nparams_527_);
v_types_528_ = lean_ctor_get(v_t_522_, 2);
lean_inc(v_types_528_);
v_isUnsafe_529_ = lean_ctor_get_uint8(v_t_522_, sizeof(void*)*3);
lean_dec_ref_known(v_t_522_, 3);
v___x_530_ = lean_box(v_isUnsafe_529_);
v___x_531_ = lean_apply_4(v_k_523_, v_lparams_526_, v_nparams_527_, v_types_528_, v___x_530_);
return v___x_531_;
}
default: 
{
lean_object* v_val_532_; lean_object* v___x_533_; 
v_val_532_ = lean_ctor_get(v_t_522_, 0);
lean_inc_ref(v_val_532_);
lean_dec(v_t_522_);
v___x_533_ = lean_apply_1(v_k_523_, v_val_532_);
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim(lean_object* v_motive_534_, lean_object* v_ctorIdx_535_, lean_object* v_t_536_, lean_object* v_h_537_, lean_object* v_k_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Declaration_ctorElim___redArg(v_t_536_, v_k_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_ctorElim___boxed(lean_object* v_motive_540_, lean_object* v_ctorIdx_541_, lean_object* v_t_542_, lean_object* v_h_543_, lean_object* v_k_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_Declaration_ctorElim(v_motive_540_, v_ctorIdx_541_, v_t_542_, v_h_543_, v_k_544_);
lean_dec(v_ctorIdx_541_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim___redArg(lean_object* v_t_546_, lean_object* v_axiomDecl_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Lean_Declaration_ctorElim___redArg(v_t_546_, v_axiomDecl_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_axiomDecl_elim(lean_object* v_motive_549_, lean_object* v_t_550_, lean_object* v_h_551_, lean_object* v_axiomDecl_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Declaration_ctorElim___redArg(v_t_550_, v_axiomDecl_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim___redArg(lean_object* v_t_554_, lean_object* v_defnDecl_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_Declaration_ctorElim___redArg(v_t_554_, v_defnDecl_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_defnDecl_elim(lean_object* v_motive_557_, lean_object* v_t_558_, lean_object* v_h_559_, lean_object* v_defnDecl_560_){
_start:
{
lean_object* v___x_561_; 
v___x_561_ = l_Lean_Declaration_ctorElim___redArg(v_t_558_, v_defnDecl_560_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim___redArg(lean_object* v_t_562_, lean_object* v_thmDecl_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = l_Lean_Declaration_ctorElim___redArg(v_t_562_, v_thmDecl_563_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_thmDecl_elim(lean_object* v_motive_565_, lean_object* v_t_566_, lean_object* v_h_567_, lean_object* v_thmDecl_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l_Lean_Declaration_ctorElim___redArg(v_t_566_, v_thmDecl_568_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim___redArg(lean_object* v_t_570_, lean_object* v_opaqueDecl_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = l_Lean_Declaration_ctorElim___redArg(v_t_570_, v_opaqueDecl_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_opaqueDecl_elim(lean_object* v_motive_573_, lean_object* v_t_574_, lean_object* v_h_575_, lean_object* v_opaqueDecl_576_){
_start:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_Declaration_ctorElim___redArg(v_t_574_, v_opaqueDecl_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim___redArg(lean_object* v_t_578_, lean_object* v_quotDecl_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Lean_Declaration_ctorElim___redArg(v_t_578_, v_quotDecl_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_quotDecl_elim(lean_object* v_motive_581_, lean_object* v_t_582_, lean_object* v_h_583_, lean_object* v_quotDecl_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_Declaration_ctorElim___redArg(v_t_582_, v_quotDecl_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim___redArg(lean_object* v_t_586_, lean_object* v_mutualDefnDecl_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Declaration_ctorElim___redArg(v_t_586_, v_mutualDefnDecl_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_mutualDefnDecl_elim(lean_object* v_motive_589_, lean_object* v_t_590_, lean_object* v_h_591_, lean_object* v_mutualDefnDecl_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Declaration_ctorElim___redArg(v_t_590_, v_mutualDefnDecl_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim___redArg(lean_object* v_t_594_, lean_object* v_inductDecl_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_Declaration_ctorElim___redArg(v_t_594_, v_inductDecl_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_inductDecl_elim(lean_object* v_motive_597_, lean_object* v_t_598_, lean_object* v_h_599_, lean_object* v_inductDecl_600_){
_start:
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Declaration_ctorElim___redArg(v_t_598_, v_inductDecl_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default___closed__0(void){
_start:
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = l_Lean_instInhabitedAxiomVal_default;
v___x_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
return v___x_603_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration_default(void){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = lean_obj_once(&l_Lean_instInhabitedDeclaration_default___closed__0, &l_Lean_instInhabitedDeclaration_default___closed__0_once, _init_l_Lean_instInhabitedDeclaration_default___closed__0);
return v___x_604_;
}
}
static lean_object* _init_l_Lean_instInhabitedDeclaration(void){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_instInhabitedDeclaration_default;
return v___x_605_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(lean_object* v_x_606_, lean_object* v_x_607_){
_start:
{
if (lean_obj_tag(v_x_606_) == 0)
{
if (lean_obj_tag(v_x_607_) == 0)
{
uint8_t v___x_608_; 
v___x_608_ = 1;
return v___x_608_;
}
else
{
uint8_t v___x_609_; 
v___x_609_ = 0;
return v___x_609_;
}
}
else
{
if (lean_obj_tag(v_x_607_) == 0)
{
uint8_t v___x_610_; 
v___x_610_ = 0;
return v___x_610_;
}
else
{
lean_object* v_head_611_; lean_object* v_tail_612_; lean_object* v_head_613_; lean_object* v_tail_614_; uint8_t v___x_615_; 
v_head_611_ = lean_ctor_get(v_x_606_, 0);
v_tail_612_ = lean_ctor_get(v_x_606_, 1);
v_head_613_ = lean_ctor_get(v_x_607_, 0);
v_tail_614_ = lean_ctor_get(v_x_607_, 1);
v___x_615_ = l_Lean_instBEqDefinitionVal_beq(v_head_611_, v_head_613_);
if (v___x_615_ == 0)
{
return v___x_615_;
}
else
{
v_x_606_ = v_tail_612_;
v_x_607_ = v_tail_614_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0___boxed(lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
uint8_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_x_617_, v_x_618_);
lean_dec(v_x_618_);
lean_dec(v_x_617_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
if (lean_obj_tag(v_x_621_) == 0)
{
if (lean_obj_tag(v_x_622_) == 0)
{
uint8_t v___x_623_; 
v___x_623_ = 1;
return v___x_623_;
}
else
{
uint8_t v___x_624_; 
v___x_624_ = 0;
return v___x_624_;
}
}
else
{
if (lean_obj_tag(v_x_622_) == 0)
{
uint8_t v___x_625_; 
v___x_625_ = 0;
return v___x_625_;
}
else
{
lean_object* v_head_626_; lean_object* v_tail_627_; lean_object* v_head_628_; lean_object* v_tail_629_; uint8_t v___x_630_; 
v_head_626_ = lean_ctor_get(v_x_621_, 0);
v_tail_627_ = lean_ctor_get(v_x_621_, 1);
v_head_628_ = lean_ctor_get(v_x_622_, 0);
v_tail_629_ = lean_ctor_get(v_x_622_, 1);
v___x_630_ = l_Lean_instBEqInductiveType_beq(v_head_626_, v_head_628_);
if (v___x_630_ == 0)
{
return v___x_630_;
}
else
{
v_x_621_ = v_tail_627_;
v_x_622_ = v_tail_629_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1___boxed(lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
uint8_t v_res_634_; lean_object* v_r_635_; 
v_res_634_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_x_632_, v_x_633_);
lean_dec(v_x_633_);
lean_dec(v_x_632_);
v_r_635_ = lean_box(v_res_634_);
return v_r_635_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqDeclaration_beq(lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
switch(lean_obj_tag(v_x_636_))
{
case 0:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v_val_638_; lean_object* v_val_639_; uint8_t v___x_640_; 
v_val_638_ = lean_ctor_get(v_x_636_, 0);
v_val_639_ = lean_ctor_get(v_x_637_, 0);
v___x_640_ = l_Lean_instBEqAxiomVal_beq(v_val_638_, v_val_639_);
return v___x_640_;
}
else
{
uint8_t v___x_641_; 
v___x_641_ = 0;
return v___x_641_;
}
}
case 1:
{
if (lean_obj_tag(v_x_637_) == 1)
{
lean_object* v_val_642_; lean_object* v_val_643_; uint8_t v___x_644_; 
v_val_642_ = lean_ctor_get(v_x_636_, 0);
v_val_643_ = lean_ctor_get(v_x_637_, 0);
v___x_644_ = l_Lean_instBEqDefinitionVal_beq(v_val_642_, v_val_643_);
return v___x_644_;
}
else
{
uint8_t v___x_645_; 
v___x_645_ = 0;
return v___x_645_;
}
}
case 2:
{
if (lean_obj_tag(v_x_637_) == 2)
{
lean_object* v_val_646_; lean_object* v_val_647_; uint8_t v___x_648_; 
v_val_646_ = lean_ctor_get(v_x_636_, 0);
v_val_647_ = lean_ctor_get(v_x_637_, 0);
v___x_648_ = l_Lean_instBEqTheoremVal_beq(v_val_646_, v_val_647_);
return v___x_648_;
}
else
{
uint8_t v___x_649_; 
v___x_649_ = 0;
return v___x_649_;
}
}
case 3:
{
if (lean_obj_tag(v_x_637_) == 3)
{
lean_object* v_val_650_; lean_object* v_val_651_; uint8_t v___x_652_; 
v_val_650_ = lean_ctor_get(v_x_636_, 0);
v_val_651_ = lean_ctor_get(v_x_637_, 0);
v___x_652_ = l_Lean_instBEqOpaqueVal_beq(v_val_650_, v_val_651_);
return v___x_652_;
}
else
{
uint8_t v___x_653_; 
v___x_653_ = 0;
return v___x_653_;
}
}
case 4:
{
if (lean_obj_tag(v_x_637_) == 4)
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
case 5:
{
if (lean_obj_tag(v_x_637_) == 5)
{
lean_object* v_defns_656_; lean_object* v_defns_657_; uint8_t v___x_658_; 
v_defns_656_ = lean_ctor_get(v_x_636_, 0);
v_defns_657_ = lean_ctor_get(v_x_637_, 0);
v___x_658_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__0(v_defns_656_, v_defns_657_);
return v___x_658_;
}
else
{
uint8_t v___x_659_; 
v___x_659_ = 0;
return v___x_659_;
}
}
default: 
{
if (lean_obj_tag(v_x_637_) == 6)
{
lean_object* v_lparams_660_; lean_object* v_nparams_661_; lean_object* v_types_662_; uint8_t v_isUnsafe_663_; lean_object* v_lparams_664_; lean_object* v_nparams_665_; lean_object* v_types_666_; uint8_t v_isUnsafe_667_; uint8_t v___x_668_; 
v_lparams_660_ = lean_ctor_get(v_x_636_, 0);
v_nparams_661_ = lean_ctor_get(v_x_636_, 1);
v_types_662_ = lean_ctor_get(v_x_636_, 2);
v_isUnsafe_663_ = lean_ctor_get_uint8(v_x_636_, sizeof(void*)*3);
v_lparams_664_ = lean_ctor_get(v_x_637_, 0);
v_nparams_665_ = lean_ctor_get(v_x_637_, 1);
v_types_666_ = lean_ctor_get(v_x_637_, 2);
v_isUnsafe_667_ = lean_ctor_get_uint8(v_x_637_, sizeof(void*)*3);
v___x_668_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_lparams_660_, v_lparams_664_);
if (v___x_668_ == 0)
{
return v___x_668_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_eq(v_nparams_661_, v_nparams_665_);
if (v___x_669_ == 0)
{
return v___x_669_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = l_List_beq___at___00Lean_instBEqDeclaration_beq_spec__1(v_types_662_, v_types_666_);
if (v___x_670_ == 0)
{
return v___x_670_;
}
else
{
if (v_isUnsafe_667_ == 0)
{
if (v_isUnsafe_663_ == 0)
{
return v___x_670_;
}
else
{
return v_isUnsafe_667_;
}
}
else
{
return v_isUnsafe_663_;
}
}
}
}
}
else
{
uint8_t v___x_671_; 
v___x_671_ = 0;
return v___x_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqDeclaration_beq___boxed(lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
uint8_t v_res_674_; lean_object* v_r_675_; 
v_res_674_ = l_Lean_instBEqDeclaration_beq(v_x_672_, v_x_673_);
lean_dec(v_x_673_);
lean_dec(v_x_672_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_decl(lean_object* v_lparams_678_, lean_object* v_nparams_679_, lean_object* v_types_680_, uint8_t v_isUnsafe_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(v___x_682_, 0, v_lparams_678_);
lean_ctor_set(v___x_682_, 1, v_nparams_679_);
lean_ctor_set(v___x_682_, 2, v_types_680_);
lean_ctor_set_uint8(v___x_682_, sizeof(void*)*3, v_isUnsafe_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveDeclEs___boxed(lean_object* v_lparams_683_, lean_object* v_nparams_684_, lean_object* v_types_685_, lean_object* v_isUnsafe_686_){
_start:
{
uint8_t v_isUnsafe_boxed_687_; lean_object* v_res_688_; 
v_isUnsafe_boxed_687_ = lean_unbox(v_isUnsafe_686_);
v_res_688_ = lean_mk_inductive_decl(v_lparams_683_, v_nparams_684_, v_types_685_, v_isUnsafe_boxed_687_);
return v_res_688_;
}
}
LEAN_EXPORT uint8_t lean_is_unsafe_inductive_decl(lean_object* v_x_689_){
_start:
{
if (lean_obj_tag(v_x_689_) == 6)
{
uint8_t v_isUnsafe_690_; 
v_isUnsafe_690_ = lean_ctor_get_uint8(v_x_689_, sizeof(void*)*3);
lean_dec_ref_known(v_x_689_, 3);
return v_isUnsafe_690_;
}
else
{
uint8_t v___x_691_; 
lean_dec(v_x_689_);
v___x_691_ = 0;
return v___x_691_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_isUnsafeInductiveDeclEx___boxed(lean_object* v_x_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = lean_is_unsafe_inductive_decl(v_x_692_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(lean_object* v_msg_695_){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = l_Lean_instInhabitedDefinitionVal_default;
v___x_697_ = lean_panic_fn_borrowed(v___x_696_, v_msg_695_);
return v___x_697_;
}
}
static lean_object* _init_l_Lean_Declaration_definitionVal_x21___closed__3(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_701_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__2));
v___x_702_ = lean_unsigned_to_nat(9u);
v___x_703_ = lean_unsigned_to_nat(184u);
v___x_704_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__1));
v___x_705_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_706_ = l_mkPanicMessageWithDecl(v___x_705_, v___x_704_, v___x_703_, v___x_702_, v___x_701_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21(lean_object* v_x_707_){
_start:
{
if (lean_obj_tag(v_x_707_) == 1)
{
lean_object* v_val_708_; 
v_val_708_ = lean_ctor_get(v_x_707_, 0);
lean_inc_ref(v_val_708_);
return v_val_708_;
}
else
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_obj_once(&l_Lean_Declaration_definitionVal_x21___closed__3, &l_Lean_Declaration_definitionVal_x21___closed__3_once, _init_l_Lean_Declaration_definitionVal_x21___closed__3);
v___x_710_ = l_panic___at___00Lean_Declaration_definitionVal_x21_spec__0(v___x_709_);
return v___x_710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_definitionVal_x21___boxed(lean_object* v_x_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Declaration_definitionVal_x21(v_x_711_);
lean_dec(v_x_711_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
if (lean_obj_tag(v_a_713_) == 0)
{
lean_object* v___x_715_; 
v___x_715_ = l_List_reverse___redArg(v_a_714_);
return v___x_715_;
}
else
{
lean_object* v_head_716_; lean_object* v_toConstantVal_717_; lean_object* v_tail_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_727_; 
v_head_716_ = lean_ctor_get(v_a_713_, 0);
v_toConstantVal_717_ = lean_ctor_get(v_head_716_, 0);
lean_inc_ref(v_toConstantVal_717_);
v_tail_718_ = lean_ctor_get(v_a_713_, 1);
v_isSharedCheck_727_ = !lean_is_exclusive(v_a_713_);
if (v_isSharedCheck_727_ == 0)
{
lean_object* v_unused_728_; 
v_unused_728_ = lean_ctor_get(v_a_713_, 0);
lean_dec(v_unused_728_);
v___x_720_ = v_a_713_;
v_isShared_721_ = v_isSharedCheck_727_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_tail_718_);
lean_dec(v_a_713_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_727_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v_name_722_; lean_object* v___x_724_; 
v_name_722_ = lean_ctor_get(v_toConstantVal_717_, 0);
lean_inc(v_name_722_);
lean_dec_ref(v_toConstantVal_717_);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 1, v_a_714_);
lean_ctor_set(v___x_720_, 0, v_name_722_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_name_722_);
lean_ctor_set(v_reuseFailAlloc_726_, 1, v_a_714_);
v___x_724_ = v_reuseFailAlloc_726_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
v_a_713_ = v_tail_718_;
v_a_714_ = v___x_724_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
if (lean_obj_tag(v_a_729_) == 0)
{
lean_object* v___x_731_; 
v___x_731_ = l_List_reverse___redArg(v_a_730_);
return v___x_731_;
}
else
{
lean_object* v_head_732_; lean_object* v_tail_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_742_; 
v_head_732_ = lean_ctor_get(v_a_729_, 0);
v_tail_733_ = lean_ctor_get(v_a_729_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_a_729_);
if (v_isSharedCheck_742_ == 0)
{
v___x_735_ = v_a_729_;
v_isShared_736_ = v_isSharedCheck_742_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_tail_733_);
lean_inc(v_head_732_);
lean_dec(v_a_729_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_742_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_name_737_; lean_object* v___x_739_; 
v_name_737_ = lean_ctor_get(v_head_732_, 0);
lean_inc(v_name_737_);
lean_dec(v_head_732_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 1, v_a_730_);
lean_ctor_set(v___x_735_, 0, v_name_737_);
v___x_739_ = v___x_735_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_name_737_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v_a_730_);
v___x_739_ = v_reuseFailAlloc_741_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
v_a_729_ = v_tail_733_;
v_a_730_ = v___x_739_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getTopLevelNames(lean_object* v_x_749_){
_start:
{
switch(lean_obj_tag(v_x_749_))
{
case 4:
{
lean_object* v___x_750_; 
v___x_750_ = ((lean_object*)(l_Lean_Declaration_getTopLevelNames___closed__2));
return v___x_750_;
}
case 5:
{
lean_object* v_defns_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_defns_751_ = lean_ctor_get(v_x_749_, 0);
lean_inc(v_defns_751_);
lean_dec_ref_known(v_x_749_, 1);
v___x_752_ = lean_box(0);
v___x_753_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_751_, v___x_752_);
return v___x_753_;
}
case 6:
{
lean_object* v_types_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_types_754_ = lean_ctor_get(v_x_749_, 2);
lean_inc(v_types_754_);
lean_dec_ref_known(v_x_749_, 3);
v___x_755_ = lean_box(0);
v___x_756_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__1(v_types_754_, v___x_755_);
return v___x_756_;
}
default: 
{
lean_object* v_val_757_; lean_object* v_toConstantVal_758_; lean_object* v_name_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_val_757_ = lean_ctor_get(v_x_749_, 0);
lean_inc_ref(v_val_757_);
lean_dec(v_x_749_);
v_toConstantVal_758_ = lean_ctor_get(v_val_757_, 0);
lean_inc_ref(v_toConstantVal_758_);
lean_dec_ref(v_val_757_);
v_name_759_ = lean_ctor_get(v_toConstantVal_758_, 0);
lean_inc(v_name_759_);
lean_dec_ref(v_toConstantVal_758_);
v___x_760_ = lean_box(0);
v___x_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_761_, 0, v_name_759_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
if (lean_obj_tag(v_a_762_) == 0)
{
lean_object* v___x_764_; 
v___x_764_ = l_List_reverse___redArg(v_a_763_);
return v___x_764_;
}
else
{
lean_object* v_head_765_; lean_object* v_tail_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_775_; 
v_head_765_ = lean_ctor_get(v_a_762_, 0);
v_tail_766_ = lean_ctor_get(v_a_762_, 1);
v_isSharedCheck_775_ = !lean_is_exclusive(v_a_762_);
if (v_isSharedCheck_775_ == 0)
{
v___x_768_ = v_a_762_;
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_tail_766_);
lean_inc(v_head_765_);
lean_dec(v_a_762_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_775_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_name_770_; lean_object* v___x_772_; 
v_name_770_ = lean_ctor_get(v_head_765_, 0);
lean_inc(v_name_770_);
lean_dec(v_head_765_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 1, v_a_763_);
lean_ctor_set(v___x_768_, 0, v_name_770_);
v___x_772_ = v___x_768_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_name_770_);
lean_ctor_set(v_reuseFailAlloc_774_, 1, v_a_763_);
v___x_772_ = v_reuseFailAlloc_774_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
v_a_762_ = v_tail_766_;
v_a_763_ = v___x_772_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(lean_object* v_a_779_, lean_object* v_a_780_){
_start:
{
if (lean_obj_tag(v_a_779_) == 0)
{
lean_object* v___x_781_; 
v___x_781_ = lean_array_to_list(v_a_780_);
return v___x_781_;
}
else
{
lean_object* v_head_782_; lean_object* v_tail_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_799_; 
v_head_782_ = lean_ctor_get(v_a_779_, 0);
v_tail_783_ = lean_ctor_get(v_a_779_, 1);
v_isSharedCheck_799_ = !lean_is_exclusive(v_a_779_);
if (v_isSharedCheck_799_ == 0)
{
v___x_785_ = v_a_779_;
v_isShared_786_ = v_isSharedCheck_799_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_tail_783_);
lean_inc(v_head_782_);
lean_dec(v_a_779_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_799_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v_name_787_; lean_object* v_ctors_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_794_; 
v_name_787_ = lean_ctor_get(v_head_782_, 0);
lean_inc(v_name_787_);
v_ctors_788_ = lean_ctor_get(v_head_782_, 2);
lean_inc(v_ctors_788_);
lean_dec(v_head_782_);
v___x_789_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__1));
v___x_790_ = l_Lean_Name_appendCore(v_name_787_, v___x_789_);
v___x_791_ = lean_box(0);
v___x_792_ = l_List_mapTR_loop___at___00Lean_Declaration_getNames_spec__0(v_ctors_788_, v___x_791_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v___x_792_);
lean_ctor_set(v___x_785_, 0, v___x_790_);
v___x_794_ = v___x_785_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_790_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_792_);
v___x_794_ = v_reuseFailAlloc_798_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_795_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_795_, 0, v_name_787_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
v___x_796_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_780_, v___x_795_);
v_a_779_ = v_tail_783_;
v_a_780_ = v___x_796_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_getNames(lean_object* v_x_826_){
_start:
{
switch(lean_obj_tag(v_x_826_))
{
case 4:
{
lean_object* v___x_827_; 
v___x_827_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__9));
return v___x_827_;
}
case 5:
{
lean_object* v_defns_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_defns_828_ = lean_ctor_get(v_x_826_, 0);
lean_inc(v_defns_828_);
lean_dec_ref_known(v_x_826_, 1);
v___x_829_ = lean_box(0);
v___x_830_ = l_List_mapTR_loop___at___00Lean_Declaration_getTopLevelNames_spec__0(v_defns_828_, v___x_829_);
return v___x_830_;
}
case 6:
{
lean_object* v_types_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v_types_831_ = lean_ctor_get(v_x_826_, 2);
lean_inc(v_types_831_);
lean_dec_ref_known(v_x_826_, 3);
v___x_832_ = ((lean_object*)(l_Lean_Declaration_getNames___closed__10));
v___x_833_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1(v_types_831_, v___x_832_);
return v___x_833_;
}
default: 
{
lean_object* v_val_834_; lean_object* v_toConstantVal_835_; lean_object* v_name_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_val_834_ = lean_ctor_get(v_x_826_, 0);
lean_inc_ref(v_val_834_);
lean_dec(v_x_826_);
v_toConstantVal_835_ = lean_ctor_get(v_val_834_, 0);
lean_inc_ref(v_toConstantVal_835_);
lean_dec_ref(v_val_834_);
v_name_836_ = lean_ctor_get(v_toConstantVal_835_, 0);
lean_inc(v_name_836_);
lean_dec_ref(v_toConstantVal_835_);
v___x_837_ = lean_box(0);
v___x_838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_838_, 0, v_name_836_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
return v___x_838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__0(lean_object* v_f_839_, lean_object* v_value_840_, lean_object* v_a_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = lean_apply_2(v_f_839_, v_a_841_, v_value_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__3(lean_object* v_f_843_, lean_object* v_value_844_, lean_object* v_a_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = lean_apply_2(v_f_843_, v_a_845_, v_value_844_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__1(lean_object* v_f_847_, lean_object* v_toBind_848_, lean_object* v_a_849_, lean_object* v_v_850_){
_start:
{
lean_object* v_toConstantVal_851_; lean_object* v_value_852_; lean_object* v_type_853_; lean_object* v___f_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
v_toConstantVal_851_ = lean_ctor_get(v_v_850_, 0);
lean_inc_ref(v_toConstantVal_851_);
v_value_852_ = lean_ctor_get(v_v_850_, 1);
lean_inc_ref(v_value_852_);
lean_dec_ref(v_v_850_);
v_type_853_ = lean_ctor_get(v_toConstantVal_851_, 2);
lean_inc_ref(v_type_853_);
lean_dec_ref(v_toConstantVal_851_);
lean_inc(v_f_847_);
v___f_854_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__3), 3, 2);
lean_closure_set(v___f_854_, 0, v_f_847_);
lean_closure_set(v___f_854_, 1, v_value_852_);
v___x_855_ = lean_apply_2(v_f_847_, v_a_849_, v_type_853_);
v___x_856_ = lean_apply_4(v_toBind_848_, lean_box(0), lean_box(0), v___x_855_, v___f_854_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__2(lean_object* v_f_857_, lean_object* v_a_858_, lean_object* v_ctor_859_){
_start:
{
lean_object* v_type_860_; lean_object* v___x_861_; 
v_type_860_ = lean_ctor_get(v_ctor_859_, 1);
lean_inc_ref(v_type_860_);
lean_dec_ref(v_ctor_859_);
v___x_861_ = lean_apply_2(v_f_857_, v_a_858_, v_type_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__4(lean_object* v_inst_862_, lean_object* v___f_863_, lean_object* v_ctors_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___x_866_; 
v___x_866_ = l_List_foldlM___redArg(v_inst_862_, v___f_863_, v_a_865_, v_ctors_864_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg___lam__5(lean_object* v_inst_867_, lean_object* v___f_868_, lean_object* v_f_869_, lean_object* v_toBind_870_, lean_object* v_a_871_, lean_object* v_inductType_872_){
_start:
{
lean_object* v_type_873_; lean_object* v_ctors_874_; lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_type_873_ = lean_ctor_get(v_inductType_872_, 1);
lean_inc_ref(v_type_873_);
v_ctors_874_ = lean_ctor_get(v_inductType_872_, 2);
lean_inc(v_ctors_874_);
lean_dec_ref(v_inductType_872_);
v___f_875_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__4), 4, 3);
lean_closure_set(v___f_875_, 0, v_inst_867_);
lean_closure_set(v___f_875_, 1, v___f_868_);
lean_closure_set(v___f_875_, 2, v_ctors_874_);
v___x_876_ = lean_apply_2(v_f_869_, v_a_871_, v_type_873_);
v___x_877_ = lean_apply_4(v_toBind_870_, lean_box(0), lean_box(0), v___x_876_, v___f_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object* v_inst_878_, lean_object* v_d_879_, lean_object* v_f_880_, lean_object* v_a_881_){
_start:
{
switch(lean_obj_tag(v_d_879_))
{
case 0:
{
lean_object* v_val_882_; lean_object* v_toConstantVal_883_; lean_object* v_type_884_; lean_object* v___x_885_; 
lean_dec_ref(v_inst_878_);
v_val_882_ = lean_ctor_get(v_d_879_, 0);
lean_inc_ref(v_val_882_);
lean_dec_ref_known(v_d_879_, 1);
v_toConstantVal_883_ = lean_ctor_get(v_val_882_, 0);
lean_inc_ref(v_toConstantVal_883_);
lean_dec_ref(v_val_882_);
v_type_884_ = lean_ctor_get(v_toConstantVal_883_, 2);
lean_inc_ref(v_type_884_);
lean_dec_ref(v_toConstantVal_883_);
v___x_885_ = lean_apply_2(v_f_880_, v_a_881_, v_type_884_);
return v___x_885_;
}
case 4:
{
lean_object* v_toApplicative_886_; lean_object* v_toPure_887_; lean_object* v___x_888_; 
v_toApplicative_886_ = lean_ctor_get(v_inst_878_, 0);
lean_inc_ref(v_toApplicative_886_);
lean_dec(v_f_880_);
lean_dec_ref(v_inst_878_);
v_toPure_887_ = lean_ctor_get(v_toApplicative_886_, 1);
lean_inc(v_toPure_887_);
lean_dec_ref(v_toApplicative_886_);
v___x_888_ = lean_apply_2(v_toPure_887_, lean_box(0), v_a_881_);
return v___x_888_;
}
case 5:
{
lean_object* v_toBind_889_; lean_object* v_defns_890_; lean_object* v___f_891_; lean_object* v___x_892_; 
v_toBind_889_ = lean_ctor_get(v_inst_878_, 1);
v_defns_890_ = lean_ctor_get(v_d_879_, 0);
lean_inc(v_defns_890_);
lean_dec_ref_known(v_d_879_, 1);
lean_inc(v_toBind_889_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_891_, 0, v_f_880_);
lean_closure_set(v___f_891_, 1, v_toBind_889_);
v___x_892_ = l_List_foldlM___redArg(v_inst_878_, v___f_891_, v_a_881_, v_defns_890_);
return v___x_892_;
}
case 6:
{
lean_object* v_toBind_893_; lean_object* v_types_894_; lean_object* v___f_895_; lean_object* v___f_896_; lean_object* v___x_897_; 
v_toBind_893_ = lean_ctor_get(v_inst_878_, 1);
v_types_894_ = lean_ctor_get(v_d_879_, 2);
lean_inc(v_types_894_);
lean_dec_ref_known(v_d_879_, 3);
lean_inc(v_f_880_);
v___f_895_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__2), 3, 1);
lean_closure_set(v___f_895_, 0, v_f_880_);
lean_inc(v_toBind_893_);
lean_inc_ref(v_inst_878_);
v___f_896_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__5), 6, 4);
lean_closure_set(v___f_896_, 0, v_inst_878_);
lean_closure_set(v___f_896_, 1, v___f_895_);
lean_closure_set(v___f_896_, 2, v_f_880_);
lean_closure_set(v___f_896_, 3, v_toBind_893_);
v___x_897_ = l_List_foldlM___redArg(v_inst_878_, v___f_896_, v_a_881_, v_types_894_);
return v___x_897_;
}
default: 
{
lean_object* v_val_898_; lean_object* v_toConstantVal_899_; lean_object* v_toBind_900_; lean_object* v_value_901_; lean_object* v_type_902_; lean_object* v___f_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v_val_898_ = lean_ctor_get(v_d_879_, 0);
lean_inc_ref(v_val_898_);
lean_dec(v_d_879_);
v_toConstantVal_899_ = lean_ctor_get(v_val_898_, 0);
lean_inc_ref(v_toConstantVal_899_);
v_toBind_900_ = lean_ctor_get(v_inst_878_, 1);
lean_inc(v_toBind_900_);
lean_dec_ref(v_inst_878_);
v_value_901_ = lean_ctor_get(v_val_898_, 1);
lean_inc_ref(v_value_901_);
lean_dec_ref(v_val_898_);
v_type_902_ = lean_ctor_get(v_toConstantVal_899_, 2);
lean_inc_ref(v_type_902_);
lean_dec_ref(v_toConstantVal_899_);
lean_inc(v_f_880_);
v___f_903_ = lean_alloc_closure((void*)(l_Lean_Declaration_foldExprM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_903_, 0, v_f_880_);
lean_closure_set(v___f_903_, 1, v_value_901_);
v___x_904_ = lean_apply_2(v_f_880_, v_a_881_, v_type_902_);
v___x_905_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_904_, v___f_903_);
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM(lean_object* v_00_u03b1_906_, lean_object* v_m_907_, lean_object* v_inst_908_, lean_object* v_d_909_, lean_object* v_f_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Lean_Declaration_foldExprM___redArg(v_inst_908_, v_d_909_, v_f_910_, v_a_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg___lam__0(lean_object* v_f_913_, lean_object* v_x_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___x_916_; 
v___x_916_ = lean_apply_1(v_f_913_, v_a_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM___redArg(lean_object* v_inst_917_, lean_object* v_d_918_, lean_object* v_f_919_){
_start:
{
lean_object* v___f_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___f_920_ = lean_alloc_closure((void*)(l_Lean_Declaration_forExprM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_920_, 0, v_f_919_);
v___x_921_ = lean_box(0);
v___x_922_ = l_Lean_Declaration_foldExprM___redArg(v_inst_917_, v_d_918_, v___f_920_, v___x_921_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forExprM(lean_object* v_m_923_, lean_object* v_inst_924_, lean_object* v_d_925_, lean_object* v_f_926_){
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
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default___closed__0(void){
_start:
{
uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_930_ = 0;
v___x_931_ = lean_box(0);
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = l_Lean_instInhabitedConstantVal_default;
v___x_934_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_934_, 0, v___x_933_);
lean_ctor_set(v___x_934_, 1, v___x_932_);
lean_ctor_set(v___x_934_, 2, v___x_932_);
lean_ctor_set(v___x_934_, 3, v___x_931_);
lean_ctor_set(v___x_934_, 4, v___x_931_);
lean_ctor_set(v___x_934_, 5, v___x_932_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*6, v___x_930_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*6 + 1, v___x_930_);
lean_ctor_set_uint8(v___x_934_, sizeof(void*)*6 + 2, v___x_930_);
return v___x_934_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal_default(void){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = lean_obj_once(&l_Lean_instInhabitedInductiveVal_default___closed__0, &l_Lean_instInhabitedInductiveVal_default___closed__0_once, _init_l_Lean_instInhabitedInductiveVal_default___closed__0);
return v___x_935_;
}
}
static lean_object* _init_l_Lean_instInhabitedInductiveVal(void){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l_Lean_instInhabitedInductiveVal_default;
return v___x_936_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqInductiveVal_beq(lean_object* v_x_937_, lean_object* v_x_938_){
_start:
{
lean_object* v_toConstantVal_939_; lean_object* v_numParams_940_; lean_object* v_numIndices_941_; lean_object* v_all_942_; lean_object* v_ctors_943_; lean_object* v_numNested_944_; uint8_t v_isRec_945_; uint8_t v_isUnsafe_946_; uint8_t v_isReflexive_947_; lean_object* v_toConstantVal_948_; lean_object* v_numParams_949_; lean_object* v_numIndices_950_; lean_object* v_all_951_; lean_object* v_ctors_952_; lean_object* v_numNested_953_; uint8_t v_isRec_954_; uint8_t v_isUnsafe_955_; uint8_t v_isReflexive_956_; uint8_t v___y_958_; uint8_t v___y_960_; uint8_t v___x_961_; 
v_toConstantVal_939_ = lean_ctor_get(v_x_937_, 0);
v_numParams_940_ = lean_ctor_get(v_x_937_, 1);
v_numIndices_941_ = lean_ctor_get(v_x_937_, 2);
v_all_942_ = lean_ctor_get(v_x_937_, 3);
v_ctors_943_ = lean_ctor_get(v_x_937_, 4);
v_numNested_944_ = lean_ctor_get(v_x_937_, 5);
v_isRec_945_ = lean_ctor_get_uint8(v_x_937_, sizeof(void*)*6);
v_isUnsafe_946_ = lean_ctor_get_uint8(v_x_937_, sizeof(void*)*6 + 1);
v_isReflexive_947_ = lean_ctor_get_uint8(v_x_937_, sizeof(void*)*6 + 2);
v_toConstantVal_948_ = lean_ctor_get(v_x_938_, 0);
v_numParams_949_ = lean_ctor_get(v_x_938_, 1);
v_numIndices_950_ = lean_ctor_get(v_x_938_, 2);
v_all_951_ = lean_ctor_get(v_x_938_, 3);
v_ctors_952_ = lean_ctor_get(v_x_938_, 4);
v_numNested_953_ = lean_ctor_get(v_x_938_, 5);
v_isRec_954_ = lean_ctor_get_uint8(v_x_938_, sizeof(void*)*6);
v_isUnsafe_955_ = lean_ctor_get_uint8(v_x_938_, sizeof(void*)*6 + 1);
v_isReflexive_956_ = lean_ctor_get_uint8(v_x_938_, sizeof(void*)*6 + 2);
v___x_961_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_939_, v_toConstantVal_948_);
if (v___x_961_ == 0)
{
return v___x_961_;
}
else
{
uint8_t v___x_962_; 
v___x_962_ = lean_nat_dec_eq(v_numParams_940_, v_numParams_949_);
if (v___x_962_ == 0)
{
return v___x_962_;
}
else
{
uint8_t v___x_963_; 
v___x_963_ = lean_nat_dec_eq(v_numIndices_941_, v_numIndices_950_);
if (v___x_963_ == 0)
{
return v___x_963_;
}
else
{
uint8_t v___x_964_; 
v___x_964_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_942_, v_all_951_);
if (v___x_964_ == 0)
{
return v___x_964_;
}
else
{
uint8_t v___x_965_; 
v___x_965_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_ctors_943_, v_ctors_952_);
if (v___x_965_ == 0)
{
return v___x_965_;
}
else
{
uint8_t v___x_966_; 
v___x_966_ = lean_nat_dec_eq(v_numNested_944_, v_numNested_953_);
if (v___x_966_ == 0)
{
return v___x_966_;
}
else
{
if (v_isRec_954_ == 0)
{
if (v_isRec_945_ == 0)
{
v___y_960_ = v___x_966_;
goto v___jp_959_;
}
else
{
return v_isRec_954_;
}
}
else
{
v___y_960_ = v_isRec_945_;
goto v___jp_959_;
}
}
}
}
}
}
}
v___jp_957_:
{
if (v_isReflexive_956_ == 0)
{
if (v_isReflexive_947_ == 0)
{
return v___y_958_;
}
else
{
return v_isReflexive_956_;
}
}
else
{
return v_isReflexive_947_;
}
}
v___jp_959_:
{
if (v___y_960_ == 0)
{
return v___y_960_;
}
else
{
if (v_isUnsafe_955_ == 0)
{
if (v_isUnsafe_946_ == 0)
{
v___y_958_ = v___y_960_;
goto v___jp_957_;
}
else
{
return v_isUnsafe_955_;
}
}
else
{
if (v_isUnsafe_946_ == 0)
{
return v_isUnsafe_946_;
}
else
{
v___y_958_ = v_isUnsafe_946_;
goto v___jp_957_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqInductiveVal_beq___boxed(lean_object* v_x_967_, lean_object* v_x_968_){
_start:
{
uint8_t v_res_969_; lean_object* v_r_970_; 
v_res_969_ = l_Lean_instBEqInductiveVal_beq(v_x_967_, v_x_968_);
lean_dec_ref(v_x_968_);
lean_dec_ref(v_x_967_);
v_r_970_ = lean_box(v_res_969_);
return v_r_970_;
}
}
LEAN_EXPORT lean_object* lean_mk_inductive_val(lean_object* v_name_973_, lean_object* v_levelParams_974_, lean_object* v_type_975_, lean_object* v_numParams_976_, lean_object* v_numIndices_977_, lean_object* v_all_978_, lean_object* v_ctors_979_, lean_object* v_numNested_980_, uint8_t v_isRec_981_, uint8_t v_isUnsafe_982_, uint8_t v_isReflexive_983_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_984_, 0, v_name_973_);
lean_ctor_set(v___x_984_, 1, v_levelParams_974_);
lean_ctor_set(v___x_984_, 2, v_type_975_);
v___x_985_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v_numParams_976_);
lean_ctor_set(v___x_985_, 2, v_numIndices_977_);
lean_ctor_set(v___x_985_, 3, v_all_978_);
lean_ctor_set(v___x_985_, 4, v_ctors_979_);
lean_ctor_set(v___x_985_, 5, v_numNested_980_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*6, v_isRec_981_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*6 + 1, v_isUnsafe_982_);
lean_ctor_set_uint8(v___x_985_, sizeof(void*)*6 + 2, v_isReflexive_983_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkInductiveValEx___boxed(lean_object* v_name_986_, lean_object* v_levelParams_987_, lean_object* v_type_988_, lean_object* v_numParams_989_, lean_object* v_numIndices_990_, lean_object* v_all_991_, lean_object* v_ctors_992_, lean_object* v_numNested_993_, lean_object* v_isRec_994_, lean_object* v_isUnsafe_995_, lean_object* v_isReflexive_996_){
_start:
{
uint8_t v_isRec_boxed_997_; uint8_t v_isUnsafe_boxed_998_; uint8_t v_isReflexive_boxed_999_; lean_object* v_res_1000_; 
v_isRec_boxed_997_ = lean_unbox(v_isRec_994_);
v_isUnsafe_boxed_998_ = lean_unbox(v_isUnsafe_995_);
v_isReflexive_boxed_999_ = lean_unbox(v_isReflexive_996_);
v_res_1000_ = lean_mk_inductive_val(v_name_986_, v_levelParams_987_, v_type_988_, v_numParams_989_, v_numIndices_990_, v_all_991_, v_ctors_992_, v_numNested_993_, v_isRec_boxed_997_, v_isUnsafe_boxed_998_, v_isReflexive_boxed_999_);
return v_res_1000_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_rec(lean_object* v_v_1001_){
_start:
{
uint8_t v_isRec_1002_; 
v_isRec_1002_ = lean_ctor_get_uint8(v_v_1001_, sizeof(void*)*6);
lean_dec_ref(v_v_1001_);
return v_isRec_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isRecEx___boxed(lean_object* v_v_1003_){
_start:
{
uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_res_1004_ = lean_inductive_val_is_rec(v_v_1003_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_unsafe(lean_object* v_v_1006_){
_start:
{
uint8_t v_isUnsafe_1007_; 
v_isUnsafe_1007_ = lean_ctor_get_uint8(v_v_1006_, sizeof(void*)*6 + 1);
lean_dec_ref(v_v_1006_);
return v_isUnsafe_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isUnsafeEx___boxed(lean_object* v_v_1008_){
_start:
{
uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_res_1009_ = lean_inductive_val_is_unsafe(v_v_1008_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT uint8_t lean_inductive_val_is_reflexive(lean_object* v_v_1011_){
_start:
{
uint8_t v_isReflexive_1012_; 
v_isReflexive_1012_ = lean_ctor_get_uint8(v_v_1011_, sizeof(void*)*6 + 2);
lean_dec_ref(v_v_1011_);
return v_isReflexive_1012_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isReflexiveEx___boxed(lean_object* v_v_1013_){
_start:
{
uint8_t v_res_1014_; lean_object* v_r_1015_; 
v_res_1014_ = lean_inductive_val_is_reflexive(v_v_1013_);
v_r_1015_ = lean_box(v_res_1014_);
return v_r_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors(lean_object* v_v_1016_){
_start:
{
lean_object* v_ctors_1017_; lean_object* v___x_1018_; 
v_ctors_1017_ = lean_ctor_get(v_v_1016_, 4);
v___x_1018_ = l_List_lengthTR___redArg(v_ctors_1017_);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numCtors___boxed(lean_object* v_v_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_InductiveVal_numCtors(v_v_1019_);
lean_dec_ref(v_v_1019_);
return v_res_1020_;
}
}
LEAN_EXPORT uint8_t l_Lean_InductiveVal_isNested(lean_object* v_v_1021_){
_start:
{
lean_object* v_numNested_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_numNested_1022_ = lean_ctor_get(v_v_1021_, 5);
v___x_1023_ = lean_unsigned_to_nat(0u);
v___x_1024_ = lean_nat_dec_lt(v___x_1023_, v_numNested_1022_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_isNested___boxed(lean_object* v_v_1025_){
_start:
{
uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_res_1026_ = l_Lean_InductiveVal_isNested(v_v_1025_);
lean_dec_ref(v_v_1025_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object* v_v_1028_){
_start:
{
lean_object* v_all_1029_; lean_object* v_numNested_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v_all_1029_ = lean_ctor_get(v_v_1028_, 3);
v_numNested_1030_ = lean_ctor_get(v_v_1028_, 5);
v___x_1031_ = l_List_lengthTR___redArg(v_all_1029_);
v___x_1032_ = lean_nat_add(v___x_1031_, v_numNested_1030_);
lean_dec(v___x_1031_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_InductiveVal_numTypeFormers___boxed(lean_object* v_v_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_InductiveVal_numTypeFormers(v_v_1033_);
lean_dec_ref(v_v_1033_);
return v_res_1034_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1035_ = 0;
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = lean_box(0);
v___x_1038_ = l_Lean_instInhabitedConstantVal_default;
v___x_1039_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___x_1037_);
lean_ctor_set(v___x_1039_, 2, v___x_1036_);
lean_ctor_set(v___x_1039_, 3, v___x_1036_);
lean_ctor_set(v___x_1039_, 4, v___x_1036_);
lean_ctor_set_uint8(v___x_1039_, sizeof(void*)*5, v___x_1035_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal_default(void){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = lean_obj_once(&l_Lean_instInhabitedConstructorVal_default___closed__0, &l_Lean_instInhabitedConstructorVal_default___closed__0_once, _init_l_Lean_instInhabitedConstructorVal_default___closed__0);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstructorVal(void){
_start:
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_instInhabitedConstructorVal_default;
return v___x_1041_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqConstructorVal_beq(lean_object* v_x_1042_, lean_object* v_x_1043_){
_start:
{
lean_object* v_toConstantVal_1044_; lean_object* v_induct_1045_; lean_object* v_cidx_1046_; lean_object* v_numParams_1047_; lean_object* v_numFields_1048_; uint8_t v_isUnsafe_1049_; lean_object* v_toConstantVal_1050_; lean_object* v_induct_1051_; lean_object* v_cidx_1052_; lean_object* v_numParams_1053_; lean_object* v_numFields_1054_; uint8_t v_isUnsafe_1055_; uint8_t v___x_1056_; 
v_toConstantVal_1044_ = lean_ctor_get(v_x_1042_, 0);
v_induct_1045_ = lean_ctor_get(v_x_1042_, 1);
v_cidx_1046_ = lean_ctor_get(v_x_1042_, 2);
v_numParams_1047_ = lean_ctor_get(v_x_1042_, 3);
v_numFields_1048_ = lean_ctor_get(v_x_1042_, 4);
v_isUnsafe_1049_ = lean_ctor_get_uint8(v_x_1042_, sizeof(void*)*5);
v_toConstantVal_1050_ = lean_ctor_get(v_x_1043_, 0);
v_induct_1051_ = lean_ctor_get(v_x_1043_, 1);
v_cidx_1052_ = lean_ctor_get(v_x_1043_, 2);
v_numParams_1053_ = lean_ctor_get(v_x_1043_, 3);
v_numFields_1054_ = lean_ctor_get(v_x_1043_, 4);
v_isUnsafe_1055_ = lean_ctor_get_uint8(v_x_1043_, sizeof(void*)*5);
v___x_1056_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1044_, v_toConstantVal_1050_);
if (v___x_1056_ == 0)
{
return v___x_1056_;
}
else
{
uint8_t v___x_1057_; 
v___x_1057_ = lean_name_eq(v_induct_1045_, v_induct_1051_);
if (v___x_1057_ == 0)
{
return v___x_1057_;
}
else
{
uint8_t v___x_1058_; 
v___x_1058_ = lean_nat_dec_eq(v_cidx_1046_, v_cidx_1052_);
if (v___x_1058_ == 0)
{
return v___x_1058_;
}
else
{
uint8_t v___x_1059_; 
v___x_1059_ = lean_nat_dec_eq(v_numParams_1047_, v_numParams_1053_);
if (v___x_1059_ == 0)
{
return v___x_1059_;
}
else
{
uint8_t v___x_1060_; 
v___x_1060_ = lean_nat_dec_eq(v_numFields_1048_, v_numFields_1054_);
if (v___x_1060_ == 0)
{
return v___x_1060_;
}
else
{
if (v_isUnsafe_1055_ == 0)
{
if (v_isUnsafe_1049_ == 0)
{
return v___x_1060_;
}
else
{
return v_isUnsafe_1055_;
}
}
else
{
return v_isUnsafe_1049_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstructorVal_beq___boxed(lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
uint8_t v_res_1063_; lean_object* v_r_1064_; 
v_res_1063_ = l_Lean_instBEqConstructorVal_beq(v_x_1061_, v_x_1062_);
lean_dec_ref(v_x_1062_);
lean_dec_ref(v_x_1061_);
v_r_1064_ = lean_box(v_res_1063_);
return v_r_1064_;
}
}
LEAN_EXPORT lean_object* lean_mk_constructor_val(lean_object* v_name_1067_, lean_object* v_levelParams_1068_, lean_object* v_type_1069_, lean_object* v_induct_1070_, lean_object* v_cidx_1071_, lean_object* v_numParams_1072_, lean_object* v_numFields_1073_, uint8_t v_isUnsafe_1074_){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1075_, 0, v_name_1067_);
lean_ctor_set(v___x_1075_, 1, v_levelParams_1068_);
lean_ctor_set(v___x_1075_, 2, v_type_1069_);
v___x_1076_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
lean_ctor_set(v___x_1076_, 1, v_induct_1070_);
lean_ctor_set(v___x_1076_, 2, v_cidx_1071_);
lean_ctor_set(v___x_1076_, 3, v_numParams_1072_);
lean_ctor_set(v___x_1076_, 4, v_numFields_1073_);
lean_ctor_set_uint8(v___x_1076_, sizeof(void*)*5, v_isUnsafe_1074_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstructorValEx___boxed(lean_object* v_name_1077_, lean_object* v_levelParams_1078_, lean_object* v_type_1079_, lean_object* v_induct_1080_, lean_object* v_cidx_1081_, lean_object* v_numParams_1082_, lean_object* v_numFields_1083_, lean_object* v_isUnsafe_1084_){
_start:
{
uint8_t v_isUnsafe_boxed_1085_; lean_object* v_res_1086_; 
v_isUnsafe_boxed_1085_ = lean_unbox(v_isUnsafe_1084_);
v_res_1086_ = lean_mk_constructor_val(v_name_1077_, v_levelParams_1078_, v_type_1079_, v_induct_1080_, v_cidx_1081_, v_numParams_1082_, v_numFields_1083_, v_isUnsafe_boxed_1085_);
return v_res_1086_;
}
}
LEAN_EXPORT uint8_t lean_constructor_val_is_unsafe(lean_object* v_v_1087_){
_start:
{
uint8_t v_isUnsafe_1088_; 
v_isUnsafe_1088_ = lean_ctor_get_uint8(v_v_1087_, sizeof(void*)*5);
lean_dec_ref(v_v_1087_);
return v_isUnsafe_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstructorVal_isUnsafeEx___boxed(lean_object* v_v_1089_){
_start:
{
uint8_t v_res_1090_; lean_object* v_r_1091_; 
v_res_1090_ = lean_constructor_val_is_unsafe(v_v_1089_);
v_r_1091_ = lean_box(v_res_1090_);
return v_r_1091_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default___closed__0(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1092_ = lean_obj_once(&l_Lean_instInhabitedConstructor_default___closed__0, &l_Lean_instInhabitedConstructor_default___closed__0_once, _init_l_Lean_instInhabitedConstructor_default___closed__0);
v___x_1093_ = lean_unsigned_to_nat(0u);
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v___x_1093_);
lean_ctor_set(v___x_1095_, 2, v___x_1092_);
return v___x_1095_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule_default(void){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_obj_once(&l_Lean_instInhabitedRecursorRule_default___closed__0, &l_Lean_instInhabitedRecursorRule_default___closed__0_once, _init_l_Lean_instInhabitedRecursorRule_default___closed__0);
return v___x_1096_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorRule(void){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_instInhabitedRecursorRule_default;
return v___x_1097_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorRule_beq(lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
lean_object* v_ctor_1100_; lean_object* v_nfields_1101_; lean_object* v_rhs_1102_; lean_object* v_ctor_1103_; lean_object* v_nfields_1104_; lean_object* v_rhs_1105_; uint8_t v___x_1106_; 
v_ctor_1100_ = lean_ctor_get(v_x_1098_, 0);
v_nfields_1101_ = lean_ctor_get(v_x_1098_, 1);
v_rhs_1102_ = lean_ctor_get(v_x_1098_, 2);
v_ctor_1103_ = lean_ctor_get(v_x_1099_, 0);
v_nfields_1104_ = lean_ctor_get(v_x_1099_, 1);
v_rhs_1105_ = lean_ctor_get(v_x_1099_, 2);
v___x_1106_ = lean_name_eq(v_ctor_1100_, v_ctor_1103_);
if (v___x_1106_ == 0)
{
return v___x_1106_;
}
else
{
uint8_t v___x_1107_; 
v___x_1107_ = lean_nat_dec_eq(v_nfields_1101_, v_nfields_1104_);
if (v___x_1107_ == 0)
{
return v___x_1107_;
}
else
{
uint8_t v___x_1108_; 
v___x_1108_ = lean_expr_eqv(v_rhs_1102_, v_rhs_1105_);
return v___x_1108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorRule_beq___boxed(lean_object* v_x_1109_, lean_object* v_x_1110_){
_start:
{
uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_res_1111_ = l_Lean_instBEqRecursorRule_beq(v_x_1109_, v_x_1110_);
lean_dec_ref(v_x_1110_);
lean_dec_ref(v_x_1109_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default___closed__0(void){
_start:
{
uint8_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1115_ = 0;
v___x_1116_ = lean_unsigned_to_nat(0u);
v___x_1117_ = lean_box(0);
v___x_1118_ = l_Lean_instInhabitedConstantVal_default;
v___x_1119_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v___x_1117_);
lean_ctor_set(v___x_1119_, 2, v___x_1116_);
lean_ctor_set(v___x_1119_, 3, v___x_1116_);
lean_ctor_set(v___x_1119_, 4, v___x_1116_);
lean_ctor_set(v___x_1119_, 5, v___x_1116_);
lean_ctor_set(v___x_1119_, 6, v___x_1117_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*7, v___x_1115_);
lean_ctor_set_uint8(v___x_1119_, sizeof(void*)*7 + 1, v___x_1115_);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal_default(void){
_start:
{
lean_object* v___x_1120_; 
v___x_1120_ = lean_obj_once(&l_Lean_instInhabitedRecursorVal_default___closed__0, &l_Lean_instInhabitedRecursorVal_default___closed__0_once, _init_l_Lean_instInhabitedRecursorVal_default___closed__0);
return v___x_1120_;
}
}
static lean_object* _init_l_Lean_instInhabitedRecursorVal(void){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Lean_instInhabitedRecursorVal_default;
return v___x_1121_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
if (lean_obj_tag(v_x_1122_) == 0)
{
if (lean_obj_tag(v_x_1123_) == 0)
{
uint8_t v___x_1124_; 
v___x_1124_ = 1;
return v___x_1124_;
}
else
{
uint8_t v___x_1125_; 
v___x_1125_ = 0;
return v___x_1125_;
}
}
else
{
if (lean_obj_tag(v_x_1123_) == 0)
{
uint8_t v___x_1126_; 
v___x_1126_ = 0;
return v___x_1126_;
}
else
{
lean_object* v_head_1127_; lean_object* v_tail_1128_; lean_object* v_head_1129_; lean_object* v_tail_1130_; uint8_t v___x_1131_; 
v_head_1127_ = lean_ctor_get(v_x_1122_, 0);
v_tail_1128_ = lean_ctor_get(v_x_1122_, 1);
v_head_1129_ = lean_ctor_get(v_x_1123_, 0);
v_tail_1130_ = lean_ctor_get(v_x_1123_, 1);
v___x_1131_ = l_Lean_instBEqRecursorRule_beq(v_head_1127_, v_head_1129_);
if (v___x_1131_ == 0)
{
return v___x_1131_;
}
else
{
v_x_1122_ = v_tail_1128_;
v_x_1123_ = v_tail_1130_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0___boxed(lean_object* v_x_1133_, lean_object* v_x_1134_){
_start:
{
uint8_t v_res_1135_; lean_object* v_r_1136_; 
v_res_1135_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_x_1133_, v_x_1134_);
lean_dec(v_x_1134_);
lean_dec(v_x_1133_);
v_r_1136_ = lean_box(v_res_1135_);
return v_r_1136_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqRecursorVal_beq(lean_object* v_x_1137_, lean_object* v_x_1138_){
_start:
{
lean_object* v_toConstantVal_1139_; lean_object* v_all_1140_; lean_object* v_numParams_1141_; lean_object* v_numIndices_1142_; lean_object* v_numMotives_1143_; lean_object* v_numMinors_1144_; lean_object* v_rules_1145_; uint8_t v_k_1146_; uint8_t v_isUnsafe_1147_; lean_object* v_toConstantVal_1148_; lean_object* v_all_1149_; lean_object* v_numParams_1150_; lean_object* v_numIndices_1151_; lean_object* v_numMotives_1152_; lean_object* v_numMinors_1153_; lean_object* v_rules_1154_; uint8_t v_k_1155_; uint8_t v_isUnsafe_1156_; uint8_t v___y_1158_; uint8_t v___x_1159_; 
v_toConstantVal_1139_ = lean_ctor_get(v_x_1137_, 0);
v_all_1140_ = lean_ctor_get(v_x_1137_, 1);
v_numParams_1141_ = lean_ctor_get(v_x_1137_, 2);
v_numIndices_1142_ = lean_ctor_get(v_x_1137_, 3);
v_numMotives_1143_ = lean_ctor_get(v_x_1137_, 4);
v_numMinors_1144_ = lean_ctor_get(v_x_1137_, 5);
v_rules_1145_ = lean_ctor_get(v_x_1137_, 6);
v_k_1146_ = lean_ctor_get_uint8(v_x_1137_, sizeof(void*)*7);
v_isUnsafe_1147_ = lean_ctor_get_uint8(v_x_1137_, sizeof(void*)*7 + 1);
v_toConstantVal_1148_ = lean_ctor_get(v_x_1138_, 0);
v_all_1149_ = lean_ctor_get(v_x_1138_, 1);
v_numParams_1150_ = lean_ctor_get(v_x_1138_, 2);
v_numIndices_1151_ = lean_ctor_get(v_x_1138_, 3);
v_numMotives_1152_ = lean_ctor_get(v_x_1138_, 4);
v_numMinors_1153_ = lean_ctor_get(v_x_1138_, 5);
v_rules_1154_ = lean_ctor_get(v_x_1138_, 6);
v_k_1155_ = lean_ctor_get_uint8(v_x_1138_, sizeof(void*)*7);
v_isUnsafe_1156_ = lean_ctor_get_uint8(v_x_1138_, sizeof(void*)*7 + 1);
v___x_1159_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1139_, v_toConstantVal_1148_);
if (v___x_1159_ == 0)
{
return v___x_1159_;
}
else
{
uint8_t v___x_1160_; 
v___x_1160_ = l_List_beq___at___00Lean_instBEqConstantVal_beq_spec__0(v_all_1140_, v_all_1149_);
if (v___x_1160_ == 0)
{
return v___x_1160_;
}
else
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_nat_dec_eq(v_numParams_1141_, v_numParams_1150_);
if (v___x_1161_ == 0)
{
return v___x_1161_;
}
else
{
uint8_t v___x_1162_; 
v___x_1162_ = lean_nat_dec_eq(v_numIndices_1142_, v_numIndices_1151_);
if (v___x_1162_ == 0)
{
return v___x_1162_;
}
else
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_nat_dec_eq(v_numMotives_1143_, v_numMotives_1152_);
if (v___x_1163_ == 0)
{
return v___x_1163_;
}
else
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_nat_dec_eq(v_numMinors_1144_, v_numMinors_1153_);
if (v___x_1164_ == 0)
{
return v___x_1164_;
}
else
{
uint8_t v___x_1165_; 
v___x_1165_ = l_List_beq___at___00Lean_instBEqRecursorVal_beq_spec__0(v_rules_1145_, v_rules_1154_);
if (v___x_1165_ == 0)
{
return v___x_1165_;
}
else
{
if (v_k_1155_ == 0)
{
if (v_k_1146_ == 0)
{
v___y_1158_ = v___x_1165_;
goto v___jp_1157_;
}
else
{
return v_k_1155_;
}
}
else
{
v___y_1158_ = v_k_1146_;
goto v___jp_1157_;
}
}
}
}
}
}
}
}
v___jp_1157_:
{
if (v___y_1158_ == 0)
{
return v___y_1158_;
}
else
{
if (v_isUnsafe_1156_ == 0)
{
if (v_isUnsafe_1147_ == 0)
{
return v___y_1158_;
}
else
{
return v_isUnsafe_1156_;
}
}
else
{
return v_isUnsafe_1147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqRecursorVal_beq___boxed(lean_object* v_x_1166_, lean_object* v_x_1167_){
_start:
{
uint8_t v_res_1168_; lean_object* v_r_1169_; 
v_res_1168_ = l_Lean_instBEqRecursorVal_beq(v_x_1166_, v_x_1167_);
lean_dec_ref(v_x_1167_);
lean_dec_ref(v_x_1166_);
v_r_1169_ = lean_box(v_res_1168_);
return v_r_1169_;
}
}
LEAN_EXPORT lean_object* lean_mk_recursor_val(lean_object* v_name_1172_, lean_object* v_levelParams_1173_, lean_object* v_type_1174_, lean_object* v_all_1175_, lean_object* v_numParams_1176_, lean_object* v_numIndices_1177_, lean_object* v_numMotives_1178_, lean_object* v_numMinors_1179_, lean_object* v_rules_1180_, uint8_t v_k_1181_, uint8_t v_isUnsafe_1182_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1183_, 0, v_name_1172_);
lean_ctor_set(v___x_1183_, 1, v_levelParams_1173_);
lean_ctor_set(v___x_1183_, 2, v_type_1174_);
v___x_1184_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v_all_1175_);
lean_ctor_set(v___x_1184_, 2, v_numParams_1176_);
lean_ctor_set(v___x_1184_, 3, v_numIndices_1177_);
lean_ctor_set(v___x_1184_, 4, v_numMotives_1178_);
lean_ctor_set(v___x_1184_, 5, v_numMinors_1179_);
lean_ctor_set(v___x_1184_, 6, v_rules_1180_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*7, v_k_1181_);
lean_ctor_set_uint8(v___x_1184_, sizeof(void*)*7 + 1, v_isUnsafe_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecursorValEx___boxed(lean_object* v_name_1185_, lean_object* v_levelParams_1186_, lean_object* v_type_1187_, lean_object* v_all_1188_, lean_object* v_numParams_1189_, lean_object* v_numIndices_1190_, lean_object* v_numMotives_1191_, lean_object* v_numMinors_1192_, lean_object* v_rules_1193_, lean_object* v_k_1194_, lean_object* v_isUnsafe_1195_){
_start:
{
uint8_t v_k_boxed_1196_; uint8_t v_isUnsafe_boxed_1197_; lean_object* v_res_1198_; 
v_k_boxed_1196_ = lean_unbox(v_k_1194_);
v_isUnsafe_boxed_1197_ = lean_unbox(v_isUnsafe_1195_);
v_res_1198_ = lean_mk_recursor_val(v_name_1185_, v_levelParams_1186_, v_type_1187_, v_all_1188_, v_numParams_1189_, v_numIndices_1190_, v_numMotives_1191_, v_numMinors_1192_, v_rules_1193_, v_k_boxed_1196_, v_isUnsafe_boxed_1197_);
return v_res_1198_;
}
}
LEAN_EXPORT uint8_t lean_recursor_k(lean_object* v_v_1199_){
_start:
{
uint8_t v_k_1200_; 
v_k_1200_ = lean_ctor_get_uint8(v_v_1199_, sizeof(void*)*7);
lean_dec_ref(v_v_1199_);
return v_k_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_kEx___boxed(lean_object* v_v_1201_){
_start:
{
uint8_t v_res_1202_; lean_object* v_r_1203_; 
v_res_1202_ = lean_recursor_k(v_v_1201_);
v_r_1203_ = lean_box(v_res_1202_);
return v_r_1203_;
}
}
LEAN_EXPORT uint8_t lean_recursor_is_unsafe(lean_object* v_v_1204_){
_start:
{
uint8_t v_isUnsafe_1205_; 
v_isUnsafe_1205_ = lean_ctor_get_uint8(v_v_1204_, sizeof(void*)*7 + 1);
lean_dec_ref(v_v_1204_);
return v_isUnsafe_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_isUnsafeEx___boxed(lean_object* v_v_1206_){
_start:
{
uint8_t v_res_1207_; lean_object* v_r_1208_; 
v_res_1207_ = lean_recursor_is_unsafe(v_v_1206_);
v_r_1208_ = lean_box(v_res_1207_);
return v_r_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object* v_v_1209_){
_start:
{
lean_object* v_numParams_1210_; lean_object* v_numIndices_1211_; lean_object* v_numMotives_1212_; lean_object* v_numMinors_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v_numParams_1210_ = lean_ctor_get(v_v_1209_, 2);
v_numIndices_1211_ = lean_ctor_get(v_v_1209_, 3);
v_numMotives_1212_ = lean_ctor_get(v_v_1209_, 4);
v_numMinors_1213_ = lean_ctor_get(v_v_1209_, 5);
v___x_1214_ = lean_nat_add(v_numParams_1210_, v_numMotives_1212_);
v___x_1215_ = lean_nat_add(v___x_1214_, v_numMinors_1213_);
lean_dec(v___x_1214_);
v___x_1216_ = lean_nat_add(v___x_1215_, v_numIndices_1211_);
lean_dec(v___x_1215_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorIdx___boxed(lean_object* v_v_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Lean_RecursorVal_getMajorIdx(v_v_1217_);
lean_dec_ref(v_v_1217_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx(lean_object* v_v_1219_){
_start:
{
lean_object* v_numParams_1220_; lean_object* v_numMotives_1221_; lean_object* v_numMinors_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v_numParams_1220_ = lean_ctor_get(v_v_1219_, 2);
v_numMotives_1221_ = lean_ctor_get(v_v_1219_, 4);
v_numMinors_1222_ = lean_ctor_get(v_v_1219_, 5);
v___x_1223_ = lean_nat_add(v_numParams_1220_, v_numMotives_1221_);
v___x_1224_ = lean_nat_add(v___x_1223_, v_numMinors_1222_);
lean_dec(v___x_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstIndexIdx___boxed(lean_object* v_v_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Lean_RecursorVal_getFirstIndexIdx(v_v_1225_);
lean_dec_ref(v_v_1225_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx(lean_object* v_v_1227_){
_start:
{
lean_object* v_numParams_1228_; lean_object* v_numMotives_1229_; lean_object* v___x_1230_; 
v_numParams_1228_ = lean_ctor_get(v_v_1227_, 2);
v_numMotives_1229_ = lean_ctor_get(v_v_1227_, 4);
v___x_1230_ = lean_nat_add(v_numParams_1228_, v_numMotives_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getFirstMinorIdx___boxed(lean_object* v_v_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Lean_RecursorVal_getFirstMinorIdx(v_v_1231_);
lean_dec_ref(v_v_1231_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(lean_object* v_x_1233_, lean_object* v_x_1234_){
_start:
{
lean_object* v_zero_1235_; uint8_t v_isZero_1236_; 
v_zero_1235_ = lean_unsigned_to_nat(0u);
v_isZero_1236_ = lean_nat_dec_eq(v_x_1233_, v_zero_1235_);
if (v_isZero_1236_ == 1)
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
lean_dec(v_x_1233_);
v___x_1237_ = l_Lean_Expr_bindingDomain_x21(v_x_1234_);
lean_dec_ref(v_x_1234_);
v___x_1238_ = l_Lean_Expr_getAppFn(v___x_1237_);
lean_dec_ref(v___x_1237_);
v___x_1239_ = l_Lean_Expr_constName_x21(v___x_1238_);
lean_dec_ref(v___x_1238_);
return v___x_1239_;
}
else
{
lean_object* v_one_1240_; lean_object* v_n_1241_; lean_object* v___x_1242_; 
v_one_1240_ = lean_unsigned_to_nat(1u);
v_n_1241_ = lean_nat_sub(v_x_1233_, v_one_1240_);
lean_dec(v_x_1233_);
v___x_1242_ = l_Lean_Expr_bindingBody_x21(v_x_1234_);
lean_dec_ref(v_x_1234_);
v_x_1233_ = v_n_1241_;
v_x_1234_ = v___x_1242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RecursorVal_getMajorInduct(lean_object* v_v_1244_){
_start:
{
lean_object* v_toConstantVal_1245_; lean_object* v_type_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v_toConstantVal_1245_ = lean_ctor_get(v_v_1244_, 0);
v_type_1246_ = lean_ctor_get(v_toConstantVal_1245_, 2);
lean_inc_ref(v_type_1246_);
v___x_1247_ = l_Lean_RecursorVal_getMajorIdx(v_v_1244_);
lean_dec_ref(v_v_1244_);
v___x_1248_ = l___private_Lean_Declaration_0__Lean_RecursorVal_getMajorInduct_go(v___x_1247_, v_type_1246_);
return v___x_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___impl(uint8_t v_x_1249_){
_start:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_box(v_x_1249_);
v___x_1251_ = lean_obj_tag_nat(v___x_1250_);
lean_dec(v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorIdx___impl___boxed(lean_object* v_x_1252_){
_start:
{
uint8_t v_x_4__boxed_1253_; lean_object* v_res_1254_; 
v_x_4__boxed_1253_ = lean_unbox(v_x_1252_);
v_res_1254_ = l_Lean_QuotKind_ctorIdx___impl(v_x_4__boxed_1253_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg(lean_object* v_k_1255_){
_start:
{
lean_inc(v_k_1255_);
return v_k_1255_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___redArg___boxed(lean_object* v_k_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_QuotKind_ctorElim___redArg(v_k_1256_);
lean_dec(v_k_1256_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim(lean_object* v_motive_1258_, lean_object* v_ctorIdx_1259_, uint8_t v_t_1260_, lean_object* v_h_1261_, lean_object* v_k_1262_){
_start:
{
lean_inc(v_k_1262_);
return v_k_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctorElim___boxed(lean_object* v_motive_1263_, lean_object* v_ctorIdx_1264_, lean_object* v_t_1265_, lean_object* v_h_1266_, lean_object* v_k_1267_){
_start:
{
uint8_t v_t_boxed_1268_; lean_object* v_res_1269_; 
v_t_boxed_1268_ = lean_unbox(v_t_1265_);
v_res_1269_ = l_Lean_QuotKind_ctorElim(v_motive_1263_, v_ctorIdx_1264_, v_t_boxed_1268_, v_h_1266_, v_k_1267_);
lean_dec(v_k_1267_);
lean_dec(v_ctorIdx_1264_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg(lean_object* v_type_1270_){
_start:
{
lean_inc(v_type_1270_);
return v_type_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___redArg___boxed(lean_object* v_type_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l_Lean_QuotKind_type_elim___redArg(v_type_1271_);
lean_dec(v_type_1271_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim(lean_object* v_motive_1273_, uint8_t v_t_1274_, lean_object* v_h_1275_, lean_object* v_type_1276_){
_start:
{
lean_inc(v_type_1276_);
return v_type_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_type_elim___boxed(lean_object* v_motive_1277_, lean_object* v_t_1278_, lean_object* v_h_1279_, lean_object* v_type_1280_){
_start:
{
uint8_t v_t_boxed_1281_; lean_object* v_res_1282_; 
v_t_boxed_1281_ = lean_unbox(v_t_1278_);
v_res_1282_ = l_Lean_QuotKind_type_elim(v_motive_1277_, v_t_boxed_1281_, v_h_1279_, v_type_1280_);
lean_dec(v_type_1280_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg(lean_object* v_ctor_1283_){
_start:
{
lean_inc(v_ctor_1283_);
return v_ctor_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___redArg___boxed(lean_object* v_ctor_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_QuotKind_ctor_elim___redArg(v_ctor_1284_);
lean_dec(v_ctor_1284_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim(lean_object* v_motive_1286_, uint8_t v_t_1287_, lean_object* v_h_1288_, lean_object* v_ctor_1289_){
_start:
{
lean_inc(v_ctor_1289_);
return v_ctor_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ctor_elim___boxed(lean_object* v_motive_1290_, lean_object* v_t_1291_, lean_object* v_h_1292_, lean_object* v_ctor_1293_){
_start:
{
uint8_t v_t_boxed_1294_; lean_object* v_res_1295_; 
v_t_boxed_1294_ = lean_unbox(v_t_1291_);
v_res_1295_ = l_Lean_QuotKind_ctor_elim(v_motive_1290_, v_t_boxed_1294_, v_h_1292_, v_ctor_1293_);
lean_dec(v_ctor_1293_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg(lean_object* v_lift_1296_){
_start:
{
lean_inc(v_lift_1296_);
return v_lift_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___redArg___boxed(lean_object* v_lift_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_QuotKind_lift_elim___redArg(v_lift_1297_);
lean_dec(v_lift_1297_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim(lean_object* v_motive_1299_, uint8_t v_t_1300_, lean_object* v_h_1301_, lean_object* v_lift_1302_){
_start:
{
lean_inc(v_lift_1302_);
return v_lift_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_lift_elim___boxed(lean_object* v_motive_1303_, lean_object* v_t_1304_, lean_object* v_h_1305_, lean_object* v_lift_1306_){
_start:
{
uint8_t v_t_boxed_1307_; lean_object* v_res_1308_; 
v_t_boxed_1307_ = lean_unbox(v_t_1304_);
v_res_1308_ = l_Lean_QuotKind_lift_elim(v_motive_1303_, v_t_boxed_1307_, v_h_1305_, v_lift_1306_);
lean_dec(v_lift_1306_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg(lean_object* v_ind_1309_){
_start:
{
lean_inc(v_ind_1309_);
return v_ind_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___redArg___boxed(lean_object* v_ind_1310_){
_start:
{
lean_object* v_res_1311_; 
v_res_1311_ = l_Lean_QuotKind_ind_elim___redArg(v_ind_1310_);
lean_dec(v_ind_1310_);
return v_res_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim(lean_object* v_motive_1312_, uint8_t v_t_1313_, lean_object* v_h_1314_, lean_object* v_ind_1315_){
_start:
{
lean_inc(v_ind_1315_);
return v_ind_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_QuotKind_ind_elim___boxed(lean_object* v_motive_1316_, lean_object* v_t_1317_, lean_object* v_h_1318_, lean_object* v_ind_1319_){
_start:
{
uint8_t v_t_boxed_1320_; lean_object* v_res_1321_; 
v_t_boxed_1320_ = lean_unbox(v_t_1317_);
v_res_1321_ = l_Lean_QuotKind_ind_elim(v_motive_1316_, v_t_boxed_1320_, v_h_1318_, v_ind_1319_);
lean_dec(v_ind_1319_);
return v_res_1321_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind_default(void){
_start:
{
uint8_t v___x_1322_; 
v___x_1322_ = 0;
return v___x_1322_;
}
}
static uint8_t _init_l_Lean_instInhabitedQuotKind(void){
_start:
{
uint8_t v___x_1323_; 
v___x_1323_ = 0;
return v___x_1323_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqQuotKind_beq(uint8_t v_x_1324_, uint8_t v_y_1325_){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1326_ = lean_box(v_x_1324_);
v___x_1327_ = lean_obj_tag_nat(v___x_1326_);
lean_dec(v___x_1326_);
v___x_1328_ = lean_box(v_y_1325_);
v___x_1329_ = lean_obj_tag_nat(v___x_1328_);
lean_dec(v___x_1328_);
v___x_1330_ = lean_nat_dec_eq(v___x_1327_, v___x_1329_);
return v___x_1330_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqQuotKind_beq___boxed(lean_object* v_x_1331_, lean_object* v_y_1332_){
_start:
{
uint8_t v_x_24__boxed_1333_; uint8_t v_y_25__boxed_1334_; uint8_t v_res_1335_; lean_object* v_r_1336_; 
v_x_24__boxed_1333_ = lean_unbox(v_x_1331_);
v_y_25__boxed_1334_ = lean_unbox(v_y_1332_);
v_res_1335_ = l_Lean_instBEqQuotKind_beq(v_x_24__boxed_1333_, v_y_25__boxed_1334_);
v_r_1336_ = lean_box(v_res_1335_);
return v_r_1336_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default___closed__0(void){
_start:
{
uint8_t v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; 
v___x_1339_ = 0;
v___x_1340_ = l_Lean_instInhabitedConstantVal_default;
v___x_1341_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set_uint8(v___x_1341_, sizeof(void*)*1, v___x_1339_);
return v___x_1341_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal_default(void){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = lean_obj_once(&l_Lean_instInhabitedQuotVal_default___closed__0, &l_Lean_instInhabitedQuotVal_default___closed__0_once, _init_l_Lean_instInhabitedQuotVal_default___closed__0);
return v___x_1342_;
}
}
static lean_object* _init_l_Lean_instInhabitedQuotVal(void){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = l_Lean_instInhabitedQuotVal_default;
return v___x_1343_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqQuotVal_beq(lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
lean_object* v_toConstantVal_1346_; uint8_t v_kind_1347_; lean_object* v_toConstantVal_1348_; uint8_t v_kind_1349_; uint8_t v___x_1350_; 
v_toConstantVal_1346_ = lean_ctor_get(v_x_1344_, 0);
v_kind_1347_ = lean_ctor_get_uint8(v_x_1344_, sizeof(void*)*1);
v_toConstantVal_1348_ = lean_ctor_get(v_x_1345_, 0);
v_kind_1349_ = lean_ctor_get_uint8(v_x_1345_, sizeof(void*)*1);
v___x_1350_ = l_Lean_instBEqConstantVal_beq(v_toConstantVal_1346_, v_toConstantVal_1348_);
if (v___x_1350_ == 0)
{
return v___x_1350_;
}
else
{
uint8_t v___x_1351_; 
v___x_1351_ = l_Lean_instBEqQuotKind_beq(v_kind_1347_, v_kind_1349_);
return v___x_1351_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqQuotVal_beq___boxed(lean_object* v_x_1352_, lean_object* v_x_1353_){
_start:
{
uint8_t v_res_1354_; lean_object* v_r_1355_; 
v_res_1354_ = l_Lean_instBEqQuotVal_beq(v_x_1352_, v_x_1353_);
lean_dec_ref(v_x_1353_);
lean_dec_ref(v_x_1352_);
v_r_1355_ = lean_box(v_res_1354_);
return v_r_1355_;
}
}
LEAN_EXPORT lean_object* lean_mk_quot_val(lean_object* v_name_1358_, lean_object* v_levelParams_1359_, lean_object* v_type_1360_, uint8_t v_kind_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1362_, 0, v_name_1358_);
lean_ctor_set(v___x_1362_, 1, v_levelParams_1359_);
lean_ctor_set(v___x_1362_, 2, v_type_1360_);
v___x_1363_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*1, v_kind_1361_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkQuotValEx___boxed(lean_object* v_name_1364_, lean_object* v_levelParams_1365_, lean_object* v_type_1366_, lean_object* v_kind_1367_){
_start:
{
uint8_t v_kind_boxed_1368_; lean_object* v_res_1369_; 
v_kind_boxed_1368_ = lean_unbox(v_kind_1367_);
v_res_1369_ = lean_mk_quot_val(v_name_1364_, v_levelParams_1365_, v_type_1366_, v_kind_boxed_1368_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___impl(lean_object* v_x_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = lean_obj_tag_nat(v_x_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_ctorIdx___impl___boxed(lean_object* v_x_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_ConstantInfo_ctorIdx___impl(v_x_1372_);
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
LEAN_EXPORT uint8_t l_Lean_instBEqConstantInfo_beq(lean_object* v_x_1458_, lean_object* v_x_1459_){
_start:
{
switch(lean_obj_tag(v_x_1458_))
{
case 0:
{
if (lean_obj_tag(v_x_1459_) == 0)
{
lean_object* v_val_1460_; lean_object* v_val_1461_; uint8_t v___x_1462_; 
v_val_1460_ = lean_ctor_get(v_x_1458_, 0);
v_val_1461_ = lean_ctor_get(v_x_1459_, 0);
v___x_1462_ = l_Lean_instBEqAxiomVal_beq(v_val_1460_, v_val_1461_);
return v___x_1462_;
}
else
{
uint8_t v___x_1463_; 
v___x_1463_ = 0;
return v___x_1463_;
}
}
case 1:
{
if (lean_obj_tag(v_x_1459_) == 1)
{
lean_object* v_val_1464_; lean_object* v_val_1465_; uint8_t v___x_1466_; 
v_val_1464_ = lean_ctor_get(v_x_1458_, 0);
v_val_1465_ = lean_ctor_get(v_x_1459_, 0);
v___x_1466_ = l_Lean_instBEqDefinitionVal_beq(v_val_1464_, v_val_1465_);
return v___x_1466_;
}
else
{
uint8_t v___x_1467_; 
v___x_1467_ = 0;
return v___x_1467_;
}
}
case 2:
{
if (lean_obj_tag(v_x_1459_) == 2)
{
lean_object* v_val_1468_; lean_object* v_val_1469_; uint8_t v___x_1470_; 
v_val_1468_ = lean_ctor_get(v_x_1458_, 0);
v_val_1469_ = lean_ctor_get(v_x_1459_, 0);
v___x_1470_ = l_Lean_instBEqTheoremVal_beq(v_val_1468_, v_val_1469_);
return v___x_1470_;
}
else
{
uint8_t v___x_1471_; 
v___x_1471_ = 0;
return v___x_1471_;
}
}
case 3:
{
if (lean_obj_tag(v_x_1459_) == 3)
{
lean_object* v_val_1472_; lean_object* v_val_1473_; uint8_t v___x_1474_; 
v_val_1472_ = lean_ctor_get(v_x_1458_, 0);
v_val_1473_ = lean_ctor_get(v_x_1459_, 0);
v___x_1474_ = l_Lean_instBEqOpaqueVal_beq(v_val_1472_, v_val_1473_);
return v___x_1474_;
}
else
{
uint8_t v___x_1475_; 
v___x_1475_ = 0;
return v___x_1475_;
}
}
case 4:
{
if (lean_obj_tag(v_x_1459_) == 4)
{
lean_object* v_val_1476_; lean_object* v_val_1477_; uint8_t v___x_1478_; 
v_val_1476_ = lean_ctor_get(v_x_1458_, 0);
v_val_1477_ = lean_ctor_get(v_x_1459_, 0);
v___x_1478_ = l_Lean_instBEqQuotVal_beq(v_val_1476_, v_val_1477_);
return v___x_1478_;
}
else
{
uint8_t v___x_1479_; 
v___x_1479_ = 0;
return v___x_1479_;
}
}
case 5:
{
if (lean_obj_tag(v_x_1459_) == 5)
{
lean_object* v_val_1480_; lean_object* v_val_1481_; uint8_t v___x_1482_; 
v_val_1480_ = lean_ctor_get(v_x_1458_, 0);
v_val_1481_ = lean_ctor_get(v_x_1459_, 0);
v___x_1482_ = l_Lean_instBEqInductiveVal_beq(v_val_1480_, v_val_1481_);
return v___x_1482_;
}
else
{
uint8_t v___x_1483_; 
v___x_1483_ = 0;
return v___x_1483_;
}
}
case 6:
{
if (lean_obj_tag(v_x_1459_) == 6)
{
lean_object* v_val_1484_; lean_object* v_val_1485_; uint8_t v___x_1486_; 
v_val_1484_ = lean_ctor_get(v_x_1458_, 0);
v_val_1485_ = lean_ctor_get(v_x_1459_, 0);
v___x_1486_ = l_Lean_instBEqConstructorVal_beq(v_val_1484_, v_val_1485_);
return v___x_1486_;
}
else
{
uint8_t v___x_1487_; 
v___x_1487_ = 0;
return v___x_1487_;
}
}
default: 
{
if (lean_obj_tag(v_x_1459_) == 7)
{
lean_object* v_val_1488_; lean_object* v_val_1489_; uint8_t v___x_1490_; 
v_val_1488_ = lean_ctor_get(v_x_1458_, 0);
v_val_1489_ = lean_ctor_get(v_x_1459_, 0);
v___x_1490_ = l_Lean_instBEqRecursorVal_beq(v_val_1488_, v_val_1489_);
return v___x_1490_;
}
else
{
uint8_t v___x_1491_; 
v___x_1491_ = 0;
return v___x_1491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqConstantInfo_beq___boxed(lean_object* v_x_1492_, lean_object* v_x_1493_){
_start:
{
uint8_t v_res_1494_; lean_object* v_r_1495_; 
v_res_1494_ = l_Lean_instBEqConstantInfo_beq(v_x_1492_, v_x_1493_);
lean_dec_ref(v_x_1493_);
lean_dec_ref(v_x_1492_);
v_r_1495_ = lean_box(v_res_1494_);
return v_r_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal(lean_object* v_x_1498_){
_start:
{
lean_object* v_val_1499_; lean_object* v_toConstantVal_1500_; 
v_val_1499_ = lean_ctor_get(v_x_1498_, 0);
v_toConstantVal_1500_ = lean_ctor_get(v_val_1499_, 0);
lean_inc_ref(v_toConstantVal_1500_);
return v_toConstantVal_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_toConstantVal___boxed(lean_object* v_x_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_ConstantInfo_toConstantVal(v_x_1501_);
lean_dec_ref(v_x_1501_);
return v_res_1502_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isUnsafe(lean_object* v_x_1503_){
_start:
{
switch(lean_obj_tag(v_x_1503_))
{
case 0:
{
lean_object* v_val_1504_; uint8_t v_isUnsafe_1505_; 
v_val_1504_ = lean_ctor_get(v_x_1503_, 0);
v_isUnsafe_1505_ = lean_ctor_get_uint8(v_val_1504_, sizeof(void*)*1);
return v_isUnsafe_1505_;
}
case 1:
{
lean_object* v_val_1506_; uint8_t v_safety_1507_; uint8_t v___x_1508_; uint8_t v___x_1509_; 
v_val_1506_ = lean_ctor_get(v_x_1503_, 0);
v_safety_1507_ = lean_ctor_get_uint8(v_val_1506_, sizeof(void*)*4);
v___x_1508_ = 0;
v___x_1509_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1507_, v___x_1508_);
return v___x_1509_;
}
case 3:
{
lean_object* v_val_1510_; uint8_t v_isUnsafe_1511_; 
v_val_1510_ = lean_ctor_get(v_x_1503_, 0);
v_isUnsafe_1511_ = lean_ctor_get_uint8(v_val_1510_, sizeof(void*)*3);
return v_isUnsafe_1511_;
}
case 5:
{
lean_object* v_val_1512_; uint8_t v_isUnsafe_1513_; 
v_val_1512_ = lean_ctor_get(v_x_1503_, 0);
v_isUnsafe_1513_ = lean_ctor_get_uint8(v_val_1512_, sizeof(void*)*6 + 1);
return v_isUnsafe_1513_;
}
case 6:
{
lean_object* v_val_1514_; uint8_t v_isUnsafe_1515_; 
v_val_1514_ = lean_ctor_get(v_x_1503_, 0);
v_isUnsafe_1515_ = lean_ctor_get_uint8(v_val_1514_, sizeof(void*)*5);
return v_isUnsafe_1515_;
}
case 7:
{
lean_object* v_val_1516_; uint8_t v_isUnsafe_1517_; 
v_val_1516_ = lean_ctor_get(v_x_1503_, 0);
v_isUnsafe_1517_ = lean_ctor_get_uint8(v_val_1516_, sizeof(void*)*7 + 1);
return v_isUnsafe_1517_;
}
default: 
{
uint8_t v___x_1518_; 
v___x_1518_ = 0;
return v___x_1518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isUnsafe___boxed(lean_object* v_x_1519_){
_start:
{
uint8_t v_res_1520_; lean_object* v_r_1521_; 
v_res_1520_ = l_Lean_ConstantInfo_isUnsafe(v_x_1519_);
lean_dec_ref(v_x_1519_);
v_r_1521_ = lean_box(v_res_1520_);
return v_r_1521_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isPartial(lean_object* v_x_1522_){
_start:
{
if (lean_obj_tag(v_x_1522_) == 1)
{
lean_object* v_val_1523_; uint8_t v_safety_1524_; uint8_t v___x_1525_; uint8_t v___x_1526_; 
v_val_1523_ = lean_ctor_get(v_x_1522_, 0);
v_safety_1524_ = lean_ctor_get_uint8(v_val_1523_, sizeof(void*)*4);
v___x_1525_ = 2;
v___x_1526_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_1524_, v___x_1525_);
return v___x_1526_;
}
else
{
uint8_t v___x_1527_; 
v___x_1527_ = 0;
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isPartial___boxed(lean_object* v_x_1528_){
_start:
{
uint8_t v_res_1529_; lean_object* v_r_1530_; 
v_res_1529_ = l_Lean_ConstantInfo_isPartial(v_x_1528_);
lean_dec_ref(v_x_1528_);
v_r_1530_ = lean_box(v_res_1529_);
return v_r_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name(lean_object* v_d_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v_name_1533_; 
v___x_1532_ = l_Lean_ConstantInfo_toConstantVal(v_d_1531_);
v_name_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_name_1533_);
lean_dec_ref(v___x_1532_);
return v_name_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_name___boxed(lean_object* v_d_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_ConstantInfo_name(v_d_1534_);
lean_dec_ref(v_d_1534_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams(lean_object* v_d_1536_){
_start:
{
lean_object* v___x_1537_; lean_object* v_levelParams_1538_; 
v___x_1537_ = l_Lean_ConstantInfo_toConstantVal(v_d_1536_);
v_levelParams_1538_ = lean_ctor_get(v___x_1537_, 1);
lean_inc(v_levelParams_1538_);
lean_dec_ref(v___x_1537_);
return v_levelParams_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_levelParams___boxed(lean_object* v_d_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_Lean_ConstantInfo_levelParams(v_d_1539_);
lean_dec_ref(v_d_1539_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object* v_d_1541_){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = l_Lean_ConstantInfo_levelParams(v_d_1541_);
v___x_1543_ = l_List_lengthTR___redArg(v___x_1542_);
lean_dec(v___x_1542_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_numLevelParams___boxed(lean_object* v_d_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_Lean_ConstantInfo_numLevelParams(v_d_1544_);
lean_dec_ref(v_d_1544_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type(lean_object* v_d_1546_){
_start:
{
lean_object* v___x_1547_; lean_object* v_type_1548_; 
v___x_1547_ = l_Lean_ConstantInfo_toConstantVal(v_d_1546_);
v_type_1548_ = lean_ctor_get(v___x_1547_, 2);
lean_inc_ref(v_type_1548_);
lean_dec_ref(v___x_1547_);
return v_type_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_type___boxed(lean_object* v_d_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Lean_ConstantInfo_type(v_d_1549_);
lean_dec_ref(v_d_1549_);
return v_res_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f(lean_object* v_info_1551_, uint8_t v_allowOpaque_1552_){
_start:
{
switch(lean_obj_tag(v_info_1551_))
{
case 1:
{
lean_object* v_val_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1561_; 
v_val_1553_ = lean_ctor_get(v_info_1551_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v_info_1551_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1555_ = v_info_1551_;
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_val_1553_);
lean_dec(v_info_1551_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1561_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v_value_1557_; lean_object* v___x_1559_; 
v_value_1557_ = lean_ctor_get(v_val_1553_, 1);
lean_inc_ref(v_value_1557_);
lean_dec_ref(v_val_1553_);
if (v_isShared_1556_ == 0)
{
lean_ctor_set(v___x_1555_, 0, v_value_1557_);
v___x_1559_ = v___x_1555_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_value_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
case 2:
{
lean_object* v_val_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1571_; 
v_val_1562_ = lean_ctor_get(v_info_1551_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_info_1551_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1564_ = v_info_1551_;
v_isShared_1565_ = v_isSharedCheck_1571_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_val_1562_);
lean_dec(v_info_1551_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1571_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
if (v_allowOpaque_1552_ == 0)
{
lean_object* v___x_1566_; 
lean_del_object(v___x_1564_);
lean_dec_ref(v_val_1562_);
v___x_1566_ = lean_box(0);
return v___x_1566_;
}
else
{
lean_object* v_value_1567_; lean_object* v___x_1569_; 
v_value_1567_ = lean_ctor_get(v_val_1562_, 1);
lean_inc_ref(v_value_1567_);
lean_dec_ref(v_val_1562_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set_tag(v___x_1564_, 1);
lean_ctor_set(v___x_1564_, 0, v_value_1567_);
v___x_1569_ = v___x_1564_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_value_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
case 3:
{
lean_object* v_val_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1581_; 
v_val_1572_ = lean_ctor_get(v_info_1551_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_info_1551_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1574_ = v_info_1551_;
v_isShared_1575_ = v_isSharedCheck_1581_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_val_1572_);
lean_dec(v_info_1551_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1581_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
if (v_allowOpaque_1552_ == 0)
{
lean_object* v___x_1576_; 
lean_del_object(v___x_1574_);
lean_dec_ref(v_val_1572_);
v___x_1576_ = lean_box(0);
return v___x_1576_;
}
else
{
lean_object* v_value_1577_; lean_object* v___x_1579_; 
v_value_1577_ = lean_ctor_get(v_val_1572_, 1);
lean_inc_ref(v_value_1577_);
lean_dec_ref(v_val_1572_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set_tag(v___x_1574_, 1);
lean_ctor_set(v___x_1574_, 0, v_value_1577_);
v___x_1579_ = v___x_1574_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_value_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
default: 
{
lean_object* v___x_1582_; 
lean_dec_ref(v_info_1551_);
v___x_1582_ = lean_box(0);
return v___x_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x3f___boxed(lean_object* v_info_1583_, lean_object* v_allowOpaque_1584_){
_start:
{
uint8_t v_allowOpaque_boxed_1585_; lean_object* v_res_1586_; 
v_allowOpaque_boxed_1585_ = lean_unbox(v_allowOpaque_1584_);
v_res_1586_ = l_Lean_ConstantInfo_value_x3f(v_info_1583_, v_allowOpaque_boxed_1585_);
return v_res_1586_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_hasValue(lean_object* v_info_1587_, uint8_t v_allowOpaque_1588_){
_start:
{
switch(lean_obj_tag(v_info_1587_))
{
case 1:
{
uint8_t v___x_1589_; 
v___x_1589_ = 1;
return v___x_1589_;
}
case 2:
{
return v_allowOpaque_1588_;
}
case 3:
{
return v_allowOpaque_1588_;
}
default: 
{
uint8_t v___x_1590_; 
v___x_1590_ = 0;
return v___x_1590_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hasValue___boxed(lean_object* v_info_1591_, lean_object* v_allowOpaque_1592_){
_start:
{
uint8_t v_allowOpaque_boxed_1593_; uint8_t v_res_1594_; lean_object* v_r_1595_; 
v_allowOpaque_boxed_1593_ = lean_unbox(v_allowOpaque_1592_);
v_res_1594_ = l_Lean_ConstantInfo_hasValue(v_info_1591_, v_allowOpaque_boxed_1593_);
lean_dec_ref(v_info_1591_);
v_r_1595_ = lean_box(v_res_1594_);
return v_r_1595_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(lean_object* v_msg_1596_){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1597_ = l_Lean_instInhabitedExpr;
v___x_1598_ = lean_panic_fn_borrowed(v___x_1597_, v_msg_1596_);
return v___x_1598_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__2(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1601_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1602_ = lean_unsigned_to_nat(62u);
v___x_1603_ = lean_unsigned_to_nat(485u);
v___x_1604_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1605_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1606_ = l_mkPanicMessageWithDecl(v___x_1605_, v___x_1604_, v___x_1603_, v___x_1602_, v___x_1601_);
return v___x_1606_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_value_x21___closed__3(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1607_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__1));
v___x_1608_ = lean_unsigned_to_nat(62u);
v___x_1609_ = lean_unsigned_to_nat(486u);
v___x_1610_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1611_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1612_ = l_mkPanicMessageWithDecl(v___x_1611_, v___x_1610_, v___x_1609_, v___x_1608_, v___x_1607_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21(lean_object* v_info_1615_, uint8_t v_allowOpaque_1616_){
_start:
{
switch(lean_obj_tag(v_info_1615_))
{
case 1:
{
lean_object* v_val_1617_; lean_object* v_value_1618_; 
v_val_1617_ = lean_ctor_get(v_info_1615_, 0);
v_value_1618_ = lean_ctor_get(v_val_1617_, 1);
lean_inc_ref(v_value_1618_);
return v_value_1618_;
}
case 2:
{
if (v_allowOpaque_1616_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__2, &l_Lean_ConstantInfo_value_x21___closed__2_once, _init_l_Lean_ConstantInfo_value_x21___closed__2);
v___x_1620_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1619_);
return v___x_1620_;
}
else
{
lean_object* v_val_1621_; lean_object* v_value_1622_; 
v_val_1621_ = lean_ctor_get(v_info_1615_, 0);
v_value_1622_ = lean_ctor_get(v_val_1621_, 1);
lean_inc_ref(v_value_1622_);
return v_value_1622_;
}
}
case 3:
{
if (v_allowOpaque_1616_ == 0)
{
lean_object* v___x_1623_; lean_object* v___x_1624_; 
v___x_1623_ = lean_obj_once(&l_Lean_ConstantInfo_value_x21___closed__3, &l_Lean_ConstantInfo_value_x21___closed__3_once, _init_l_Lean_ConstantInfo_value_x21___closed__3);
v___x_1624_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1623_);
return v___x_1624_;
}
else
{
lean_object* v_val_1625_; lean_object* v_value_1626_; 
v_val_1625_ = lean_ctor_get(v_info_1615_, 0);
v_value_1626_ = lean_ctor_get(v_val_1625_, 1);
lean_inc_ref(v_value_1626_);
return v_value_1626_;
}
}
default: 
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1627_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1628_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__0));
v___x_1629_ = lean_unsigned_to_nat(487u);
v___x_1630_ = lean_unsigned_to_nat(31u);
v___x_1631_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__4));
v___x_1632_ = l_Lean_ConstantInfo_name(v_info_1615_);
v___x_1633_ = 1;
v___x_1634_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1632_, v___x_1633_);
v___x_1635_ = lean_string_append(v___x_1631_, v___x_1634_);
lean_dec_ref(v___x_1634_);
v___x_1636_ = ((lean_object*)(l_Lean_ConstantInfo_value_x21___closed__5));
v___x_1637_ = lean_string_append(v___x_1635_, v___x_1636_);
v___x_1638_ = l_mkPanicMessageWithDecl(v___x_1627_, v___x_1628_, v___x_1629_, v___x_1630_, v___x_1637_);
lean_dec_ref(v___x_1637_);
v___x_1639_ = l_panic___at___00Lean_ConstantInfo_value_x21_spec__0(v___x_1638_);
return v___x_1639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_value_x21___boxed(lean_object* v_info_1640_, lean_object* v_allowOpaque_1641_){
_start:
{
uint8_t v_allowOpaque_boxed_1642_; lean_object* v_res_1643_; 
v_allowOpaque_boxed_1642_ = lean_unbox(v_allowOpaque_1641_);
v_res_1643_ = l_Lean_ConstantInfo_value_x21(v_info_1640_, v_allowOpaque_boxed_1642_);
lean_dec_ref(v_info_1640_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints(lean_object* v_x_1644_){
_start:
{
if (lean_obj_tag(v_x_1644_) == 1)
{
lean_object* v_val_1645_; lean_object* v_hints_1646_; 
v_val_1645_ = lean_ctor_get(v_x_1644_, 0);
v_hints_1646_ = lean_ctor_get(v_val_1645_, 2);
lean_inc(v_hints_1646_);
return v_hints_1646_;
}
else
{
lean_object* v___x_1647_; 
v___x_1647_ = lean_box(0);
return v___x_1647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_hints___boxed(lean_object* v_x_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_ConstantInfo_hints(v_x_1648_);
lean_dec_ref(v_x_1648_);
return v_res_1649_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isCtor(lean_object* v_x_1650_){
_start:
{
if (lean_obj_tag(v_x_1650_) == 6)
{
uint8_t v___x_1651_; 
v___x_1651_ = 1;
return v___x_1651_;
}
else
{
uint8_t v___x_1652_; 
v___x_1652_ = 0;
return v___x_1652_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isCtor___boxed(lean_object* v_x_1653_){
_start:
{
uint8_t v_res_1654_; lean_object* v_r_1655_; 
v_res_1654_ = l_Lean_ConstantInfo_isCtor(v_x_1653_);
lean_dec_ref(v_x_1653_);
v_r_1655_ = lean_box(v_res_1654_);
return v_r_1655_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isAxiom(lean_object* v_x_1656_){
_start:
{
if (lean_obj_tag(v_x_1656_) == 0)
{
uint8_t v___x_1657_; 
v___x_1657_ = 1;
return v___x_1657_;
}
else
{
uint8_t v___x_1658_; 
v___x_1658_ = 0;
return v___x_1658_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isAxiom___boxed(lean_object* v_x_1659_){
_start:
{
uint8_t v_res_1660_; lean_object* v_r_1661_; 
v_res_1660_ = l_Lean_ConstantInfo_isAxiom(v_x_1659_);
lean_dec_ref(v_x_1659_);
v_r_1661_ = lean_box(v_res_1660_);
return v_r_1661_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isInductive(lean_object* v_x_1662_){
_start:
{
if (lean_obj_tag(v_x_1662_) == 5)
{
uint8_t v___x_1663_; 
v___x_1663_ = 1;
return v___x_1663_;
}
else
{
uint8_t v___x_1664_; 
v___x_1664_ = 0;
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isInductive___boxed(lean_object* v_x_1665_){
_start:
{
uint8_t v_res_1666_; lean_object* v_r_1667_; 
v_res_1666_ = l_Lean_ConstantInfo_isInductive(v_x_1665_);
lean_dec_ref(v_x_1665_);
v_r_1667_ = lean_box(v_res_1666_);
return v_r_1667_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isDefinition(lean_object* v_x_1668_){
_start:
{
if (lean_obj_tag(v_x_1668_) == 1)
{
uint8_t v___x_1669_; 
v___x_1669_ = 1;
return v___x_1669_;
}
else
{
uint8_t v___x_1670_; 
v___x_1670_ = 0;
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isDefinition___boxed(lean_object* v_x_1671_){
_start:
{
uint8_t v_res_1672_; lean_object* v_r_1673_; 
v_res_1672_ = l_Lean_ConstantInfo_isDefinition(v_x_1671_);
lean_dec_ref(v_x_1671_);
v_r_1673_ = lean_box(v_res_1672_);
return v_r_1673_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstantInfo_isTheorem(lean_object* v_x_1674_){
_start:
{
if (lean_obj_tag(v_x_1674_) == 2)
{
uint8_t v___x_1675_; 
v___x_1675_ = 1;
return v___x_1675_;
}
else
{
uint8_t v___x_1676_; 
v___x_1676_ = 0;
return v___x_1676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_isTheorem___boxed(lean_object* v_x_1677_){
_start:
{
uint8_t v_res_1678_; lean_object* v_r_1679_; 
v_res_1678_ = l_Lean_ConstantInfo_isTheorem(v_x_1677_);
lean_dec_ref(v_x_1677_);
v_r_1679_ = lean_box(v_res_1678_);
return v_r_1679_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(lean_object* v_msg_1680_){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = l_Lean_instInhabitedInductiveVal_default;
v___x_1682_ = lean_panic_fn_borrowed(v___x_1681_, v_msg_1680_);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1685_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__1));
v___x_1686_ = lean_unsigned_to_nat(9u);
v___x_1687_ = lean_unsigned_to_nat(515u);
v___x_1688_ = ((lean_object*)(l_Lean_ConstantInfo_inductiveVal_x21___closed__0));
v___x_1689_ = ((lean_object*)(l_Lean_Declaration_definitionVal_x21___closed__0));
v___x_1690_ = l_mkPanicMessageWithDecl(v___x_1689_, v___x_1688_, v___x_1687_, v___x_1686_, v___x_1685_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21(lean_object* v_x_1691_){
_start:
{
if (lean_obj_tag(v_x_1691_) == 5)
{
lean_object* v_val_1692_; 
v_val_1692_ = lean_ctor_get(v_x_1691_, 0);
lean_inc_ref(v_val_1692_);
return v_val_1692_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = lean_obj_once(&l_Lean_ConstantInfo_inductiveVal_x21___closed__2, &l_Lean_ConstantInfo_inductiveVal_x21___closed__2_once, _init_l_Lean_ConstantInfo_inductiveVal_x21___closed__2);
v___x_1694_ = l_panic___at___00Lean_ConstantInfo_inductiveVal_x21_spec__0(v___x_1693_);
return v___x_1694_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_inductiveVal_x21___boxed(lean_object* v_x_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_ConstantInfo_inductiveVal_x21(v_x_1695_);
lean_dec_ref(v_x_1695_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all(lean_object* v_x_1697_){
_start:
{
switch(lean_obj_tag(v_x_1697_))
{
case 5:
{
lean_object* v_val_1698_; lean_object* v_all_1699_; 
v_val_1698_ = lean_ctor_get(v_x_1697_, 0);
v_all_1699_ = lean_ctor_get(v_val_1698_, 3);
lean_inc(v_all_1699_);
return v_all_1699_;
}
case 1:
{
lean_object* v_val_1700_; lean_object* v_all_1701_; 
v_val_1700_ = lean_ctor_get(v_x_1697_, 0);
v_all_1701_ = lean_ctor_get(v_val_1700_, 3);
lean_inc(v_all_1701_);
return v_all_1701_;
}
case 2:
{
lean_object* v_val_1702_; lean_object* v_all_1703_; 
v_val_1702_ = lean_ctor_get(v_x_1697_, 0);
v_all_1703_ = lean_ctor_get(v_val_1702_, 2);
lean_inc(v_all_1703_);
return v_all_1703_;
}
case 3:
{
lean_object* v_val_1704_; lean_object* v_all_1705_; 
v_val_1704_ = lean_ctor_get(v_x_1697_, 0);
v_all_1705_ = lean_ctor_get(v_val_1704_, 2);
lean_inc(v_all_1705_);
return v_all_1705_;
}
default: 
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = l_Lean_ConstantInfo_name(v_x_1697_);
v___x_1707_ = lean_box(0);
v___x_1708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1706_);
lean_ctor_set(v___x_1708_, 1, v___x_1707_);
return v___x_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstantInfo_all___boxed(lean_object* v_x_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_ConstantInfo_all(v_x_1709_);
lean_dec_ref(v_x_1709_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkRecName(lean_object* v_declName_1711_){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1712_ = ((lean_object*)(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Declaration_getNames_spec__1___closed__0));
v___x_1713_ = l_Lean_Name_str___override(v_declName_1711_, v___x_1712_);
return v___x_1713_;
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
