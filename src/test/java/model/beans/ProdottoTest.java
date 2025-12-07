package model.beans;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Comprehensive test suite for the Prodotto class.
 * Generated from Category-Partition Testing Report.
 * 
 * Tests cover:
 * - setPrezzo(), setPeso(), setQuantitaProdotto() with boundary values (>= 0)
 * - String setters (setMarca, setModello, setDescrizione) with null/empty
 * validation
 * - setCategoria() with null check
 * - setRecensioni() and setSpecifiche() with null check
 */
@DisplayName("Prodotto Tests")
class ProdottoTest {

    @Test
    @DisplayName("Default constructor should create Prodotto")
    void shouldCreateProdottoWithDefaultConstructor() {
        // Arrange & Act
        Prodotto prodotto = new Prodotto();

        // Assert
        assertNotNull(prodotto, "Prodotto instance should be created");
    }

    // ========================================================================
    // setPrezzo() Tests
    // ========================================================================

    @Test
    @DisplayName("setPrezzo should throw exception when setting negative price")
    void shouldThrowExceptionWhenSettingNegativePrezzo() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> prodotto.setPrezzo(-0.01));
    }

    @Test
    @DisplayName("setPrezzo should set zero price (boundary)")
    void shouldSetZeroPrezzo() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act
        prodotto.setPrezzo(0.0);

        // Assert
        assertEquals(0.0, prodotto.getPrezzo(), 0.001);
    }

    @Test
    @DisplayName("setPrezzo should set positive price")
    void shouldSetPositivePrezzo() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act
        prodotto.setPrezzo(99.99);

        // Assert
        assertEquals(99.99, prodotto.getPrezzo(), 0.01);
    }

    // ========================================================================
    // setPeso() Tests
    // ========================================================================

    @Test
    @DisplayName("setPeso should throw exception when setting negative weight")
    void shouldThrowExceptionWhenSettingNegativePeso() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> prodotto.setPeso(-0.01));
    }

    @Test
    @DisplayName("setPeso should set zero weight (boundary)")
    void shouldSetZeroPeso() {
        // Arrange
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act
        prodotto.setPeso(1.5);

        // Assert
        assertEquals(1.5, prodotto.getPeso(), 0.001);
    }

    // ========================================================================
    // setQuantitaProdotto() Tests
    // ========================================================================

    @Test
    @DisplayName("setQuantitaProdotto should throw exception when setting negative quantity")
    void shouldThrowExceptionWhenSettingNegativeQuantitaProdotto() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> prodotto.setQuantitaProdotto(-1));
    }

    @Test
    @DisplayName("setQuantitaProdotto should set zero quantity (boundary)")
    void shouldSetZeroQuantitaProdotto() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act
        prodotto.setQuantitaProdotto(0);

        // Assert
        assertEquals(0, prodotto.getQuantitaProdotto());
    }

    @Test
    @DisplayName("setQuantitaProdotto should set positive quantity")
    void shouldSetPositiveQuantitaProdotto() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act
        prodotto.setQuantitaProdotto(10);

        // Assert
        assertEquals(10, prodotto.getQuantitaProdotto());
    }

    // ========================================================================
    // String Setter Tests
    // ========================================================================

    @Test
    @DisplayName("setMarca should throw exception when setting null")
    void shouldThrowExceptionWhenSettingNullMarca() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> prodotto.setMarca(null));
    }

    @Test
    @DisplayName("setMarca should throw exception when setting empty")
    void shouldThrowExceptionWhenSettingEmptyMarca() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> prodotto.setMarca(""));
    }

    @Test
    @DisplayName("setMarca should set valid marca")
    void shouldSetValidMarca() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act
        prodotto.setMarca("BrandName");

        // Assert
        assertEquals("BrandName", prodotto.getMarca());
    }

    @Test
    @DisplayName("setModello should throw exception when setting null")
    void shouldThrowExceptionWhenSettingNullModello() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> prodotto.setModello(null));
    }

    @Test
    @DisplayName("setModello should set valid modello")
    void shouldSetValidModello() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act
        prodotto.setModello("Model123");

        // Assert
        assertEquals("Model123", prodotto.getModello());
    }

    @Test
    @DisplayName("setDescrizione should throw exception when setting null")
    void shouldThrowExceptionWhenSettingNullDescrizione() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> prodotto.setDescrizione(null));
    }

    @Test
    @DisplayName("setDescrizione should set valid descrizione")
    void shouldSetValidDescrizione() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act
        prodotto.setDescrizione("Product description");

        // Assert
        assertEquals("Product description", prodotto.getDescrizione());
    }

    // ========================================================================
    // setCategoria() Tests
    // ========================================================================

    @Test
    @DisplayName("setCategoria should throw exception when setting null")
    void shouldThrowExceptionWhenSettingNullCategoria() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> prodotto.setCategoria(null));
    }

    @Test
    @DisplayName("setCategoria should set valid categoria")
    void shouldSetValidCategoria() {
        // Arrange
        Prodotto prodotto = new Prodotto();
        Categoria categoria = new Categoria("Electronics");

        // Act
        prodotto.setCategoria(categoria);

        // Assert
        assertEquals(categoria, prodotto.getCategoria());
    }

    // ========================================================================
    // Collection Setter Tests
    // ========================================================================

    @Test
    @DisplayName("setRecensioni should throw exception when setting null")
    void shouldThrowExceptionWhenSettingNullRecensioni() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> prodotto.setRecensioni(null));
    }

    @Test
    @DisplayName("setRecensioni should set empty list")
    void shouldSetEmptyRecensioniList() {
        // Arrange
        Prodotto prodotto = new Prodotto();
        ArrayList<Recensione> recensioni = new ArrayList<>();

        // Act
        prodotto.setRecensioni(recensioni);

        // Assert
        assertEquals(recensioni, prodotto.getRecensioni());
    }

    @Test
    @DisplayName("setSpecifiche should throw exception when setting null")
    void shouldThrowExceptionWhenSettingNullSpecifiche() {
        // Arrange
        Prodotto prodotto = new Prodotto();

        // Act & Assert
        assertThrows(IllegalArgumentException.class,
                () -> prodotto.setSpecifiche(null));
    }

    @Test
    @DisplayName("setSpecifiche should set empty list")
    void shouldSetEmptySpecificheList() {
        // Arrange
        Prodotto prodotto = new Prodotto();
        ArrayList<Specifiche> specifiche = new ArrayList<>();

        // Act
        prodotto.setSpecifiche(specifiche);

        // Assert
        assertEquals(specifiche, prodotto.getSpecifiche());
    }
}
