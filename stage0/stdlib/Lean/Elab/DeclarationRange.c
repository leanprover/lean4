// Lean compiler output
// Module: Lean.Elab.DeclarationRange
// Imports: public import Lean.Parser.Command
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
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_getDeclarationSelectionRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__0 = (const lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__0_value;
static const lean_string_object l_Lean_Elab_getDeclarationSelectionRef___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__1 = (const lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__1_value;
static const lean_string_object l_Lean_Elab_getDeclarationSelectionRef___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__2 = (const lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__2_value;
static const lean_string_object l_Lean_Elab_getDeclarationSelectionRef___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instance"};
static const lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__3 = (const lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_getDeclarationSelectionRef___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__3_value),LEAN_SCALAR_PTR_LITERAL(37, 156, 84, 218, 244, 57, 142, 153)}};
static const lean_object* l_Lean_Elab_getDeclarationSelectionRef___closed__4 = (const lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__4_value;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationSelectionRef(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_addDeclarationRanges___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__0;
static const lean_string_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__2_value;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "example"};
static const lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_getDeclarationSelectionRef___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 28, 224, 32, 144, 38, 51, 230)}};
static const lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1_value;
lean_object* l_Lean_Syntax_getKind(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_DeclarationRange_ofStringPositions(x_3, x_4, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = 0;
x_8 = l_Lean_Syntax_getRange_x3f(x_3, x_7);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_getDeclarationRange_x3f___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_6);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_2, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_6, lean_box(0), x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getDeclarationRange_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getDeclarationRange_x3f___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getDeclarationRange_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationSelectionRef(lean_object* x_1) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l_Lean_Elab_getDeclarationSelectionRef___closed__4));
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_8, x_9);
x_11 = l_Lean_Syntax_isIdent(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = l_Lean_Syntax_isIdent(x_8);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_8);
x_13 = l_Lean_Syntax_getArg(x_1, x_9);
lean_dec(x_1);
return x_13;
}
else
{
lean_dec(x_1);
return x_8;
}
}
else
{
lean_dec(x_8);
lean_dec(x_1);
return x_10;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
if (x_16 == 0)
{
if (x_6 == 0)
{
lean_dec(x_15);
goto block_4;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_15, x_17);
lean_dec(x_15);
return x_18;
}
}
else
{
lean_dec(x_15);
goto block_4;
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Syntax_getArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc_ref(x_1);
return x_1;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lean_addDeclarationRanges___redArg(x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec_ref(x_1);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_12, 0, x_10);
lean_inc_ref(x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__1), 5, 4);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
x_14 = l_Lean_Elab_getDeclarationRange_x3f___redArg(x_2, x_5, x_6);
x_15 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_12, x_14);
x_16 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_15, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_8, lean_box(0), x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_3);
lean_inc_ref(x_1);
x_11 = l_Lean_Elab_getDeclarationRange_x3f___redArg(x_1, x_3, x_5);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___lam__2___boxed), 9, 8);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_1);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_3);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_8);
lean_closure_set(x_12, 7, x_10);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_addDeclarationRangesFromSyntax(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_obj_once(&l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__0, &l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__0_once, _init_l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__0);
x_9 = lean_array_push(x_8, x_1);
lean_inc(x_2);
x_10 = lean_array_push(x_9, x_2);
x_11 = ((lean_object*)(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0___closed__2));
x_12 = lean_box(2);
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_10);
x_14 = l_Lean_Elab_getDeclarationSelectionRef(x_2);
x_15 = l_Lean_Elab_addDeclarationRangesFromSyntax___redArg(x_3, x_4, x_5, x_6, x_13, x_14);
lean_dec_ref(x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_6);
x_7 = l_Lean_Syntax_getKind(x_6);
x_8 = ((lean_object*)(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___closed__1));
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_addDeclarationRangesForBuiltin___redArg___lam__0), 7, 6);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_1);
lean_closure_set(x_13, 3, x_2);
lean_closure_set(x_13, 4, x_3);
lean_closure_set(x_13, 5, x_4);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_12, lean_box(0), x_14);
x_16 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_15, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_18, lean_box(0), x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesForBuiltin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_addDeclarationRangesForBuiltin___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* initialize_Lean_Parser_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeclarationRange(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
