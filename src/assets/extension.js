(function () {
    class MetalExtension extends Extension {
        constructor(ide) {
            super('Metal');
            this.ide = ide;
        }

        onOpenRole() {}

        getMenu() {
            return {
                'Run on Device': async () => {
                    const req = new XMLHttpRequest();
                    req.open('POST', 'http://{{addr}}:{{port}}/run', true);
                    req.send(await this.ide.cloud.exportRole());
                },
            };
        }

        getCategories() {
            return [];
        }

        getPalette() {
            return [];
        }

        getBlocks() {
            return [];
        }

        getLabelParts() {
            return [];
        }
    }

    NetsBloxExtensions.register(MetalExtension);
})();
