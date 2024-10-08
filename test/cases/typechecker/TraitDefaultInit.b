module TraitDefaultInit

interface {}

extern type ExternType;   // no traits

function test()
{
    var v: ExternType;    // cannot default init
}
