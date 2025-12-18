/-! Tests that C trigraphs are not actually interpreted -/

def main := do
  IO.println "??("
  IO.println "??)"
  IO.println "??<"
  IO.println "??>"
  IO.println "??="
  IO.println "??/"
  IO.println "??'"
  IO.println "??!"
  IO.println "??-"
