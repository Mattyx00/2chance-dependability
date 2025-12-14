package services;

import model.beans.Utente;
import model.dao.UtenteDAO;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;
import org.junit.jupiter.params.provider.NullSource;
import org.junit.jupiter.params.provider.ValueSource;
import org.mockito.InjectMocks;
import org.mockito.Mock;
import org.mockito.MockedStatic;
import org.mockito.junit.jupiter.MockitoExtension;

import java.sql.SQLException;
import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class RegistrazioneServiceTest {

    @Mock
    private UtenteDAO utenteDAO;

    @InjectMocks
    private RegistrazioneService registrazioneService;

    // =================================================================================================
    // Constructor Tests
    // =================================================================================================

    @Test
    @DisplayName("TF1: Should throw exception when UtenteDAO is null")
    void shouldThrowExceptionWhenDaoIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> new RegistrazioneService(null));
        assertTrue(exception.getMessage().contains("UtenteDAO cannot be null"));
    }

    @Test
    @DisplayName("TF2: Should instantiate service when UtenteDAO is not null")
    void shouldInitializeWhenDaoIsNotNull() {
        // Act & Assert
        assertNotNull(registrazioneService);
    }

    // =================================================================================================
    // validateAndRegister Tests
    // =================================================================================================

    @Test
    @DisplayName("TF3: Should throw exception when Nome is null")
    void shouldThrowExceptionWhenNomeIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.validateAndRegister(null, "Rossi", "Pass123!", "test@example.com",
                        "1234567890", "img.jpg"));
        assertTrue(exception.getMessage().contains("Nome cannot be null"));
    }

    @Test
    @DisplayName("TF4: Should throw exception when Cognome is null")
    void shouldThrowExceptionWhenCognomeIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.validateAndRegister("Mario", null, "Pass123!", "test@example.com",
                        "1234567890", "img.jpg"));
        assertTrue(exception.getMessage().contains("Cognome cannot be null"));
    }

    @Test
    @DisplayName("TF5: Should throw exception when Password is null")
    void shouldThrowExceptionWhenPasswordIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.validateAndRegister("Mario", "Rossi", null, "test@example.com", "1234567890",
                        "img.jpg"));
        assertTrue(exception.getMessage().contains("Password cannot be null"));
    }

    @Test
    @DisplayName("TF6: Should throw exception when Email is null")
    void shouldThrowExceptionWhenEmailIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.validateAndRegister("Mario", "Rossi", "Pass123!", null, "1234567890",
                        "img.jpg"));
        assertTrue(exception.getMessage().contains("Email cannot be null"));
    }

    @Test
    @DisplayName("TF7: Should throw exception when Telefono is null")
    void shouldThrowExceptionWhenTelefonoIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.validateAndRegister("Mario", "Rossi", "Pass123!", "test@example.com", null,
                        "img.jpg"));
        assertTrue(exception.getMessage().contains("Telefono cannot be null"));
    }

    @Test
    @DisplayName("TF8: Should throw exception when FileName is null")
    void shouldThrowExceptionWhenFileNameIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.validateAndRegister("Mario", "Rossi", "Pass123!", "test@example.com",
                        "1234567890", null));
        assertTrue(exception.getMessage().contains("FileName cannot be null"));
    }

    @ParameterizedTest
    @DisplayName("TF9, TF10: Should return error when Nome is invalid (Empty or Non-Alphabetic)")
    @ValueSource(strings = { "", "Mario1", "M@rio" })
    void shouldReturnErrorWhenNameIsInvalid(String invalidName) throws SQLException {
        // Arrange
        String validSurname = "Rossi";
        String validPassword = "Pass123!";
        String validEmail = "test@example.com";
        String validPhone = "1234567890";
        String validFileName = "img.jpg";

        // Act
        ArrayList<String> errors = registrazioneService.validateAndRegister(
                invalidName,
                validSurname,
                validPassword,
                validEmail,
                validPhone,
                validFileName);

        // Assert
        assertTrue(errors.contains("Errore nome, riprovare"));
    }

    @ParameterizedTest
    @DisplayName("TF11, TF12: Should return error when Surname is invalid (Empty or Non-Alphabetic)")
    @ValueSource(strings = { "", "Rossi1", "R0ssi" })
    void shouldReturnErrorWhenSurnameIsInvalid(String invalidSurname) throws SQLException {
        // Arrange
        String validName = "Mario";
        String validPassword = "Pass123!";
        String validEmail = "test@example.com";
        String validPhone = "1234567890";
        String validFileName = "img.jpg";

        // Act
        ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                validName,
                invalidSurname,
                validPassword,
                validEmail,
                validPhone,
                validFileName);

        // Assert
        assertTrue(arrayErrors.contains("Errore cognome, riprovare"));
    }

    @ParameterizedTest
    @DisplayName("TF13, TF14, TF15: Should return error when Password is invalid (Empty, Short, No Uppercase)")
    @ValueSource(strings = { "", "Pass", "password", "short", "alllowercase123" })
    void shouldReturnErrorWhenPasswordIsInvalid(String invalidPassword) throws SQLException {
        // Arrange
        String validName = "Mario";
        String validSurname = "Rossi";
        String validEmail = "test@example.com";
        String validPhone = "1234567890";
        String validFileName = "img.jpg";

        // Act
        ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                validName,
                validSurname,
                invalidPassword,
                validEmail,
                validPhone,
                validFileName);

        // Assert
        assertTrue(arrayErrors.contains("Errore password, riprovare"));
    }

    @ParameterizedTest
    @DisplayName("TF16, TF17: Should return error when Email is invalid (Empty or Bad Format)")
    @ValueSource(strings = { "", "mario@", "mario.com", "@domain.com" })
    void shouldReturnErrorWhenEmailIsInvalid(String invalidEmail) throws SQLException {
        // Arrange
        String validName = "Mario";
        String validSurname = "Rossi";
        String validPassword = "Pass123!";
        String validPhone = "1234567890";
        String validFileName = "img.jpg";

        // Act
        ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                validName,
                validSurname,
                validPassword,
                invalidEmail,
                validPhone,
                validFileName);

        // Assert
        assertTrue(arrayErrors.contains("Errore email, riprovare"));
    }

    @Test
    @DisplayName("TF18: Should return error when Email already exists")
    void shouldReturnErrorWhenEmailExisting() throws SQLException {
        // Arrange
        String existingEmail = "duplicate@example.com";
        String validName = "Mario";
        String validSurname = "Rossi";
        String validPassword = "Pass123!";
        String validPhone = "1234567890";
        String validFileName = "img.jpg";

        try (MockedStatic<UtenteDAO> mockedStatic = mockStatic(UtenteDAO.class)) {
            mockedStatic.when(() -> UtenteDAO.isEmailPresent(existingEmail)).thenReturn(true);

            // Act
            ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                    validName,
                    validSurname,
                    validPassword,
                    existingEmail,
                    validPhone,
                    validFileName);

            // Assert
            assertTrue(arrayErrors.contains("Email già in utilizzo"));
        }
    }

    @ParameterizedTest
    @DisplayName("TF19, TF20: Should return error when Telefono is invalid (Empty or Not 10 Digits)")
    @ValueSource(strings = { "", "123", "12345678901", "abcdefghij" })
    void shouldReturnErrorWhenTelefonoIsInvalid(String invalidPhone) throws SQLException {
        // Arrange
        String validName = "Mario";
        String validSurname = "Rossi";
        String validPassword = "Pass123!";
        String validEmail = "test@example.com";
        String validFileName = "img.jpg";

        // Act
        ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                validName,
                validSurname,
                validPassword,
                validEmail,
                invalidPhone,
                validFileName);

        // Assert
        assertTrue(arrayErrors.contains("Errore telefono, riprovare"));
    }

    @Test
    @DisplayName("TF21: Should return multiple errors for multiple invalid fields")
    void shouldReturnMultipleErrors() throws SQLException {
        // Arrange: Invalid Nome and Invalid Password
        String invalidName = "Mario1";
        String invalidPassword = "short";
        String validSurname = "Rossi";
        String validEmail = "test@example.com";
        String validPhone = "1234567890";
        String validFileName = "img.jpg";

        // Act
        ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                invalidName,
                validSurname,
                invalidPassword,
                validEmail,
                validPhone,
                validFileName);

        // Assert
        assertAll("Verify multiple errors",
                () -> assertTrue(arrayErrors.contains("Errore nome, riprovare")),
                () -> assertTrue(arrayErrors.contains("Errore password, riprovare")));
    }

    @Test
    @DisplayName("TF22: Should register user when all inputs are valid and email is unique")
    void shouldRegisterUserWhenAllInputsValid() throws SQLException {
        // Arrange
        String validEmail = "new@example.com";
        String validPassword = "Password123"; // >8 chars, has Upper
        String validName = "Mario";
        String validSurname = "Rossi";
        String validPhone = "1234567890";
        String validFileName = "img.jpg";

        try (MockedStatic<UtenteDAO> mockedStatic = mockStatic(UtenteDAO.class)) {
            mockedStatic.when(() -> UtenteDAO.isEmailPresent(validEmail)).thenReturn(false);

            when(utenteDAO.addUtente(any(Utente.class))).thenReturn(1);

            // Act
            ArrayList<String> arrayErrors = registrazioneService.validateAndRegister(
                    validName,
                    validSurname,
                    validPassword,
                    validEmail,
                    validPhone,
                    validFileName);

            // Assert
            assertTrue(arrayErrors.isEmpty(), "Error list should be empty on success");

            verify(utenteDAO, times(1)).addUtente(any(Utente.class));
        }
    }

    // =================================================================================================
    // getUserByEmailPassword Tests
    // =================================================================================================

    @Test
    @DisplayName("TF23: Should throw exception when Login Email is null")
    void shouldThrowExceptionWhenLoginEmailIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.getUserByEmailPassword(null, "Pass123"));
        assertTrue(exception.getMessage().contains("Email cannot be null"));
    }

    @Test
    @DisplayName("TF24: Should throw exception when Login Password is null")
    void shouldThrowExceptionWhenLoginPasswordIsNull() {
        // Act & Assert
        IllegalArgumentException exception = assertThrows(
                IllegalArgumentException.class,
                () -> registrazioneService.getUserByEmailPassword("email@test.com", null));
        assertTrue(exception.getMessage().contains("Password cannot be null"));
    }

    @Test
    @DisplayName("TF25: Should delegate to DAO when Login inputs are valid")
    void shouldDelegateToDaoWhenLoginInputsValid() throws SQLException {
        // Arrange
        String validEmail = "email@test.com";
        String validPassword = "Pass123";

        Utente expectedUser = new Utente();

        when(utenteDAO.getUserByEmailPassword(validEmail, validPassword)).thenReturn(expectedUser);

        // Act
        Utente user = registrazioneService.getUserByEmailPassword(validEmail, validPassword);

        // Assert
        assertEquals(expectedUser, user);

        verify(utenteDAO).getUserByEmailPassword(validEmail, validPassword);
    }
}
