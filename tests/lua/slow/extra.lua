-- Execute f, and make sure is throws an error
function check_error(f)
    ok, msg = pcall(function ()
        f()
        end)
    if ok then
       error("unexpected success...")
    else
       print("caught expected error: ", msg)
    end
end
