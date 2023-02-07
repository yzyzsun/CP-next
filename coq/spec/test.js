function main() {
    var $1 = {};
    var $2 = {};
    var $r = function () {
        return $2;
    };
    $2[`rcd_x:Int`] = function () {
        var $10 = {};
        $10[`Int`] = 1.0;
        return $10;
    };
    $2[`rcd_y:Int`] = function () {
        var $11 = {};
        var $12 = $r();
        var $13 = {};
        $13[`rcd_x:Int`] = function () {
            var $14 = $12[`rcd_x:Int`]();
            var $15 = {};
            $15[`Int`] = $14[`Int`];
            return $15;
        };
        Object.assign($11, $13[`rcd_x:Int`]());
        return $11;
    };
    var $16 = {};
    $16[`rcd_y:Int`] = function () {
        var $17 = $2[`rcd_y:Int`]();
        var $18 = {};
        $18[`Int`] = $17[`Int`];
        return $18;
    };
    Object.assign($1, $16[`rcd_y:Int`]());
    return $1;
};
